-- Prove2me | Definitions.Def_PDynTreeEmbed_Main_Improving
-- name    : PDynTreeEmbed_Main_Improving
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:31:04.134219+00:00
-- url     : https://prove2.me/theorems/89bab082-2ae8-48f0-87ba-6cdcdc303387
-- title:
--   Argmin sets, near-winners W_v(S), shifted distances ρ_i(v), anchors µ_s(v) and epoch improving sets A_i
-- statement:
--   Let $G$ be a weighted graph on $V=\{0,\dots,n-1\}$, $D>0$, $\pi$ a permutation of $V$ (the center at position $i$ is $\pi(i)$) and $R=(R_x)_{x\in V}$ real radii, one per vertex.
--
--   The **argmin set** of a vector $(\beta_0,\dots,\beta_n)$ is $\{j:\beta_j\le\beta_k\text{ for all }k\}$.
--
--   For a vertex $v$ and a set $S$: $\rho_x=\mathrm{dist}_G(x,v)-R_x$, $\mu_{-u}(S)=\min\{0,\min_{x\in S\setminus\{u\}}\rho_x\}$, and the **near-winners** are
--   $$W_v(S)=\{u\in S:\rho_u\le\mu_{-u}(S)+D\}.$$
--
--   For a position $i$ the **shifted distance** is $\rho_i(v)=\mathrm{dist}_G(\pi(i),v)-R_{\pi(i)}$, the **anchor** over the first $s$ centers is $\mu_s(v)=\min\{0,\min_{j\le s}\rho_j(v)\}$ (so $\mu_0=0$), $s(i)$ is the power of two with $s(i)<i\le 2s(i)$ for $i>1$ and $s(1)=0$, and the **epoch improving set** of the center at index $i$ is
--   $$A_i=\{v\in V:\rho_i(v)\le\mu_{s(i)}(v)+D\}.$$
--
--   **Formalization Note.** Positions are `Fin n`, 0-based: position `i` is the paper's index `i + 1`, so `improvingSet … i` uses `s(i+1)` and the anchor over positions `j < s`. Radii are indexed by vertices, as the paper does from p. 20 on; the radius of the center at position `i` is `R (π i)`. Minima over a finite subtype are real infima; over an empty subtype the infimum is `0`, which agrees with the `min{0, ·}`.
-- source:
--   Dorkofikis, Probst Gutenberg, Tight Low-Diameter Decompositions and Tree Embeddings in Partially Dynamic Graphs, STOC 2027 submission (manuscript sha256 bf7ba5b2…), Lemma 2.1 (p. 6), §5.1 and Definition 5.1 (p. 20), Claim 5.3 (p. 21)

import Mathlib
import Definitions.Def_PDynTreeEmbed_Main_Graphs

namespace PDynTreeEmbed.Main

/-! # Minimizer sets, near-winners, shifted distances, anchors and epoch improving sets

Dorkofikis, Probst Gutenberg, *Tight Low-Diameter Decompositions and Tree Embeddings in Partially
Dynamic Graphs*, STOC 2027 submission (manuscript sha256 bf7ba5b2…): Lemma 2.1 (p. 6), §5.1 and
Definition 5.1 (p. 20), Claim 5.3 (p. 21).

**Formalization Note.** Positions in the permutation are `Fin n`, 0-based: position `i` is the
paper's index `i + 1`. Radii are indexed by vertices (p. 20: "we index the radii by vertices rather
than by positions"), so the radius of the center at position `i` is `R (π i)`. Minima over a finite
index set are taken over a subtype; over an empty subtype the real infimum is `0`, which agrees with
the `min{0, ·}` in every definition below. -/

open Classical in
/-- The argmin set `arg min_j β_j` of a finite real vector (a set, since there may be ties). -/
noncomputable def argminSet {m : ℕ} (β : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∀ k, β j ≤ β k

/-- `ρ_x = dist_G(x, v) − R_x` for the vertex `x`. -/
noncomputable def shiftedTo {n : ℕ} (G : WGraph (Fin n)) (R : Fin n → ℝ) (v x : Fin n) : ℝ :=
  G.rdist x v - R x

/-- `µ_{−u}(S) = min{0, min_{x ∈ S∖{u}} ρ_x}` (Claim 5.3). -/
noncomputable def anchorWithout {n : ℕ} (G : WGraph (Fin n)) (R : Fin n → ℝ) (v : Fin n)
    (S : Finset (Fin n)) (u : Fin n) : ℝ :=
  min 0 (⨅ x : {x : Fin n // x ∈ S ∧ x ≠ u}, shiftedTo G R v x.1)

open Classical in
/-- `W_v(S) = {u ∈ S : ρ_u ≤ µ_{−u}(S) + D}` (Claim 5.3): the candidates within `D` of winning. -/
noncomputable def nearWinners {n : ℕ} (G : WGraph (Fin n)) (D : ℝ) (R : Fin n → ℝ)
    (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  S.filter fun u => shiftedTo G R v u ≤ anchorWithout G R v S u + D

/-- `ρ_i(v) = dist_G(π(i), v) − R_{π(i)}` for the center at position `i` (§5.1). -/
noncomputable def shifted {n : ℕ} (G : WGraph (Fin n)) (π : Equiv.Perm (Fin n)) (R : Fin n → ℝ)
    (i : Fin n) (v : Fin n) : ℝ :=
  G.rdist (π i) v - R (π i)

/-- The anchor `µ_s(v) = min{0, min_{j ≤ s} ρ_j(v)}` over the first `s` centers (§5.1);
`µ_0(v) = 0`. -/
noncomputable def anchor {n : ℕ} (G : WGraph (Fin n)) (π : Equiv.Perm (Fin n)) (R : Fin n → ℝ)
    (s : ℕ) (v : Fin n) : ℝ :=
  min 0 (⨅ j : {j : Fin n // j.val < s}, shifted G π R j.1 v)

/-- `s(i)` for the paper's 1-based index `i` (Definition 5.1): the power of two with
`s(i) < i ≤ 2 s(i)` for `i > 1`, and `s(1) = 0`. -/
def epochStart (i : ℕ) : ℕ :=
  if i ≤ 1 then 0 else 2 ^ Nat.log 2 (i - 1)

open Classical in
/-- The epoch improving set `A_i = {v ∈ V : ρ_i(v) ≤ µ_{s(i)}(v) + D}` (Definition 5.1) of the
center at position `i` (the paper's index `i + 1`). -/
noncomputable def improvingSet {n : ℕ} (G : WGraph (Fin n)) (D : ℝ) (π : Equiv.Perm (Fin n))
    (R : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v => shifted G π R i v ≤ anchor G π R (epochStart (i.val + 1)) v + D

end PDynTreeEmbed.Main


