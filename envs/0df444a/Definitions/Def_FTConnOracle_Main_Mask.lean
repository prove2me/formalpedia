-- Prove2me | Definitions.Def_FTConnOracle_Main_Mask
-- name    : FTConnOracle_Main_Mask
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:40.250071+00:00
-- url     : https://prove2.me/theorems/b72b479e-f0c1-4397-8c36-efbd2da549af
-- title:
--   Masks, D-good masks and mask families (Definitions 4.2, 4.3), the mask hierarchy G_i, F_i, and the level decision procedure of Claim 4.5
-- statement:
--   A **mask** is a graph $M$ on $[n]$; applying it to a graph $H$ on $[n]$ gives $H\cap M$ (the edges common to both). For $D\ge0$, $M$ is **$D$-good for $H$** (Definition 4.2) if
--
--   1. (halving) $|E(H\cap M)|\le\frac12|E(H)|$, and
--   2. (cut approximation) $\big|\,|\delta_H(S)|-2|\delta_{H\cap M}(S)|\,\big|\le D$ for every $S\subseteq[n]$. (4.7)
--
--   A family $\mathcal M_n$ of masks on $[n]$ is **$D$-good** (Definition 4.3) if every graph $H$ on $[n]$ has a mask $M\in\mathcal M_n$ that is $D$-good for $H$.
--
--   Given a graph $G$ and masks $M_1,M_2,\dots$, the **hierarchy** is $G_0=G$, $G_{i+1}=G_i\cap M_{i+1}$, and for a failure set $F$ the level failure sets are $F_0=F$, $F_{i+1}=F_i\cap E(M_{i+1})$. For a cut $S$ write
--
--   $$r_i=|\delta_{F_i\setminus F_{i+1}}(S)|,\qquad f_{i+1}=|\delta_{F_{i+1}}(S)|.$$
--
--   The **level decision procedure** of Claim 4.5 receives the stored data — the vertex sketches $b_v$, the number of levels $L$, the masks $M_1,\dots,M_L$, the level sketches $s_{i,u}$ for $0\le i<L$ — together with $D$, $F$ and $S$, and decides by backward recursion whether $G_i-F_i$ has an edge crossing $S$: level $L$ answers *empty*; at level $i<L$ it answers *nonempty* if level $i+1$ did; otherwise it answers *nonempty* if $f_{i+1}-r_i>D$ (Case 1), and if $f_{i+1}-r_i\le D$ (Case 2) it runs Test-Cut on $S$, $F_i$, $\{(b_u,s_{i,u})\}_{u\in S}$, $\{(b_u,b_v)\}_{(u,v)\in F_i}$ and answers *nonempty* if the test returns $0$, *empty* if it returns $1$.
--
--   These are the objects of the $\tilde O(n^{7/4})$-bit oracle of §4.3 (Lemma 4.6, Observation 4.2, Claim 4.5).
--
--   **Formalization Note.** Intersection of graphs is `H ⊓ M`; halving is written $2|E(H\cap M)|\le|E(H)|$ in $\mathbb N$. Masks are indexed by $\mathbb N$ (`M (i+1)` $=M_{i+1}$); only $M_1,\dots,M_L$ are read. `levelGraph G M i` $=G_i$, `levelFail F M i` $=F_i$, and `levelDecide b L M sk D F S i` returns `true` for *nonempty*; the level sketches are passed as `sk i u` $=s_{i,u}$ and the masks as graphs (a mask identifier determines its mask).
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), pp. 22–25 (PDF 24–27): Definitions 4.2 (4.7) and 4.3, 'Encoding' and 'Deciding on a specific cut candidate' of §4.3, proof of Claim 4.5 (Cases 1 and 2)

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-!
# Masks, the mask hierarchy and the level decoder of the `Õ(n^{7/4})` oracle

Parter, Tzalik, *Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space*,
STOC 2027 submission (manuscript sha256 168306b7…), pp. 22–25 (PDF 24–27): Definitions 4.2,
4.3, the encoding of §4.3, Observation 4.2 and the decision procedure in the proof of Claim 4.5.

* A mask is a graph `M` on `[n]`; applying it to `H` gives `H ∩ M` (`H ⊓ M`).
* The hierarchy is `G_0 = G`, `G_{i+1} = G_i ∩ M_{i+1}`; the failed edges per level are
  `F_0 = F`, `F_{i+1} = F_i ∩ E(M_{i+1})`. Masks are indexed by `ℕ`; only `M 1, …, M L` are read.
* `levelDecide … i` is the backward recursion of the proof of Claim 4.5: `true` means
  "`G_i − F_i` has an edge crossing `S`" (nonempty), `false` means empty.
-/

/-- Definition 4.2: for `D ≥ 0`, the mask `M` is **`D`-good** for `H` if
(1) halving: `|E(H ∩ M)| ≤ |E(H)|/2` (written `2|E(H ∩ M)| ≤ |E(H)|`), and
(2) cut approximation (4.7): `||δ_H(S)| − 2|δ_{H∩M}(S)|| ≤ D` for every `S ⊆ [n]`. -/
def IsDGood {n : ℕ} (D : ℝ) (M H : SimpleGraph (Fin n)) : Prop :=
  2 * (edges (H ⊓ M)).card ≤ (edges H).card ∧
    ∀ S : Finset (Fin n),
      |((delta H S).card : ℝ) - 2 * ((delta (H ⊓ M) S).card : ℝ)| ≤ D

/-- Definition 4.3: a family of masks `𝓜` on `[n]` is **`D`-good** if every graph `H` on `[n]`
has a mask `M ∈ 𝓜` that is `D`-good for `H`. -/
def IsDGoodFamily {n : ℕ} (D : ℝ) (fam : Set (SimpleGraph (Fin n))) : Prop :=
  ∀ H : SimpleGraph (Fin n), ∃ M ∈ fam, IsDGood D M H

/-- The level graphs: `G_0 = G`, `G_{i+1} = G_i ∩ M_{i+1}`. -/
def levelGraph {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → SimpleGraph (Fin n)) :
    ℕ → SimpleGraph (Fin n)
  | 0 => G
  | i + 1 => levelGraph G M i ⊓ M (i + 1)

/-- The failed edges per level: `F_0 = F`, `F_{i+1} = F_i ∩ E(M_{i+1})`. -/
noncomputable def levelFail {n : ℕ} (F : Finset (Sym2 (Fin n))) (M : ℕ → SimpleGraph (Fin n)) :
    ℕ → Finset (Sym2 (Fin n))
  | 0 => F
  | i + 1 => levelFail F M i ∩ edges (M (i + 1))

/-- The level decision procedure of Claim 4.5, from the stored data only: the vertex sketches
`b`, the number of levels `L`, the masks `M 1, …, M L`, the level sketches `sk i` (`= s_{i,·}`)
for `i < L`, the parameter `D`, the query `F` and the cut `S`. At level `L` it answers empty.
At level `i < L` it answers nonempty if level `i + 1` did; otherwise, with
`r_i = |δ_{F_i ∖ F_{i+1}}(S)|` and `f_{i+1} = |δ_{F_{i+1}}(S)|`, it answers nonempty if
`f_{i+1} − r_i > D` (Case 1), and otherwise (Case 2) nonempty iff
`Test-Cut(S, F_i, {(b_u, s_{i,u})}_{u ∈ S}, {(b_u, b_v)}_{(u,v) ∈ F_i})` returns `0`. -/
noncomputable def levelDecide {n r : ℕ} (b : Fin n → Fin r → ℤ) (L : ℕ)
    (M : ℕ → SimpleGraph (Fin n)) (sk : ℕ → Fin n → Fin r → ℤ) (D : ℝ)
    (F : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) (i : ℕ) : Bool :=
  if i < L then
    levelDecide b L M sk D F S (i + 1) ||
      decide (D < ((cutEdges (levelFail F M (i + 1)) S).card : ℝ) -
        ((cutEdges (levelFail F M i \ levelFail F M (i + 1)) S).card : ℝ)) ||
      !testCut b (sk i) S (levelFail F M i)
  else false
termination_by L - i

end FTConnOracle.Main


