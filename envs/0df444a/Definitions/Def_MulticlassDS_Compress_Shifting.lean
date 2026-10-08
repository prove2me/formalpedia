-- Prove2me | Definitions.Def_MulticlassDS_Compress_Shifting
-- name    : MulticlassDS_Compress_Shifting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:20:24.57881+00:00
-- url     : https://prove2.me/theorems/4dd29525-297c-4653-b2e9-367e88f0681e
-- title:
--   Definitions 18, 21, 24, 25, pp. 12–15 — shifting, exponential dimension, average degrees avd and avd′
-- statement:
--   Let $\mathcal H\subseteq[p]^n$, a class of words of length $n$ over the alphabet $[p]$, ordered as in $\mathbb N$.
--
--   1. **Shifting** (Definition 18). For a direction $i\in[n]$ and $f : [n]\setminus\{i\}\to[p]$, let $e_f$ be the set of words of $\mathcal H$ agreeing with $f$ off $i$. The shifted edge $\mathbb S_i(e_f)$ is the set of all $g\in[p]^n$ agreeing with $f$ off $i$ with $1\le g(i)\le|e_f|$, and $\mathbb S_i(\mathcal H) = \bigcup_f \mathbb S_i(e_f)$.
--   2. **Exponential dimension** (Definition 21). For $\mathcal H\subseteq\mathcal Y^{\mathcal X}$, a sequence $S\in\mathcal X^k$ is *E-shattered* if $|\mathcal H|_S|\ge 2^k$; $d_E(\mathcal H)$ is the maximum length of an E-shattered sequence.
--   3. **Average degree** (Definition 24). With $\deg(v)$ the number of edges of size $>1$ of the one-inclusion graph $\mathcal G(\mathcal H)$ containing $v$,
--   $$\operatorname{avd}(\mathcal H) = \frac1{|V|}\sum_{v\in V}\deg(v).$$
--   4. **Shifting average degree** (Definition 25).
--   $$\operatorname{avd}'(\mathcal H) = \frac1{|V|}\sum_{e\in E}(|e|-1),$$
--   the sum running over all edges of $\mathcal G(\mathcal H)$ in all directions.
--
--   Shifting does not increase projections or the exponential dimension and does not decrease $\operatorname{avd}'$; these facts bound the average degree and so produce orientations of small out-degree (Lemma 17).
--
--   **Formalization Note** The alphabet $[p]$ is `Fin p` $=\{0,\dots,p-1\}$, so the condition $1\le g(i)\le|e_f|$ is written $g(i)<|e_f|$ (a shift of every label by one). Edges are indexed by a direction and a member, `edgesDir H i` being the set of vertex sets of the edges of direction $i$; $\operatorname{avd}'$ sums over the directions and, within each, over these sets. $\deg(v)$ counts the directions $i$ in which $v$ has a neighbour in $\mathcal H$, which is the number of its edges of size $>1$. Divisions by $|V|$ are real divisions; for the empty class both averages are $0$. The exponential dimension is a supremum in `ℕ∞`, finite for classes in $[p]^n$.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 12 Definition 18, p. 14 Definition 21, p. 15 Definitions 24, 25

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_OneInclusion

namespace MulticlassDS.Compress

/-- Definition 18, p. 12: the shifting `S_i(H)` of `H ⊆ [p]ⁿ` in direction `i`. Each edge
`e_f` (the words of `H` agreeing with `f` off `i`) is replaced by the words `g` agreeing with
`f` off `i` whose `i`-th label is among the `|e_f|` smallest. Labels `[p]` are `Fin p`
(0-based), so `1 ≤ g(i) ≤ |e_f|` reads `g(i) < |e_f|`. -/
noncomputable def shift {n p : ℕ} (i : Fin n) (H : Set (Fin n → Fin p)) :
    Set (Fin n → Fin p) :=
  {g | ∃ v ∈ H, AgreeOff i g v ∧ (g i : ℕ) < {u ∈ H | AgreeOff i u v}.ncard}

/-- Definition 21, p. 14: `S ∈ Xᵏ` is E-shattered by `H` if `|H|_S| ≥ 2ᵏ`; the exponential
dimension `d_E(H)` is the maximum size of an E-shattered sequence (`⊤` if unbounded). -/
noncomputable def expDim {X Y : Type*} (H : Set (X → Y)) : ℕ∞ :=
  ⨆ (k : ℕ) (S : Fin k → X) (_ : (2 : ℕ∞) ^ k ≤ (proj H S).encard), (k : ℕ∞)

/-- Definition 24, p. 15: `deg(v)`, the number of edges of size `> 1` of `G(H)` containing `v`,
i.e. of directions `i` in which `v` has a neighbour in `H`. -/
noncomputable def deg {n p : ℕ} (H : Set (Fin n → Fin p)) (v : Fin n → Fin p) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ∃ u ∈ H, u ≠ v ∧ AgreeOff i u v).card

/-- Definition 24, p. 15: the average degree `avd(H) = (1/|V|) Σ_{v ∈ V} deg(v)`. -/
noncomputable def avd {n p : ℕ} (H : Set (Fin n → Fin p)) : ℝ :=
  (∑ᶠ v ∈ H, (deg H v : ℝ)) / H.ncard

/-- Definition 9, p. 8: the vertex sets of the edges of direction `i` of `G(H)`. -/
def edgesDir {n p : ℕ} (H : Set (Fin n → Fin p)) (i : Fin n) : Set (Set (Fin n → Fin p)) :=
  (fun v => {u ∈ H | AgreeOff i u v}) '' H

/-- Definition 25, p. 15: `avd'(H) = (1/|V|) Σ_{e ∈ E} (|e| − 1)`, the sum running over the edges
of every direction. -/
noncomputable def avd' {n p : ℕ} (H : Set (Fin n → Fin p)) : ℝ :=
  (∑ i, ∑ᶠ e ∈ edgesDir H i, ((e.ncard : ℝ) - 1)) / H.ncard

end MulticlassDS.Compress


