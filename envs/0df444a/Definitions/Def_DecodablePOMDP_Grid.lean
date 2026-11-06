-- Prove2me | Definitions.Def_DecodablePOMDP_Grid
-- name    : DecodablePOMDP_Grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:54.131053+00:00
-- url     : https://prove2.me/theorems/42bdef80-c8f4-4e81-bd52-c88147ceb404
-- title:
--   The lattice grid $G_{d,\eta}$ and rounding within a simplex face
-- statement:
--   Let $d$ be the number of coordinates, $0<\eta\le1$ and $n=\lceil 2d/\eta\rceil$. The **lattice grid** is
--
--   $$G_{d,\eta}=\Big\{\big(\tfrac{k_1}{n},\dots,\tfrac{k_d}{n}\big):k_i\in\mathbb Z_{\ge0},\ \textstyle\sum_ik_i=n\Big\}.$$
--
--   **Rounding within a face** $\mathcal A$ with a chosen coordinate $q^*\in\mathcal A$: round every coordinate in $\mathcal A\setminus\{q^*\}$ down to a multiple of $1/n$, give $q^*$ the remaining mass, and keep the coordinates outside $\mathcal A$ at zero. For $\mathcal A$ the whole index set this is the rounding of the proof of Lemma 6.
--
--   **Formalization Note** Coordinates are indexed by a finite type (the planner uses $\mathcal Q$). The paper's "last" coordinate is the parameter $q^*$.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. A.6, p.17

import Mathlib

namespace DecodablePOMDP

open Classical

/-- **Grid resolution** `n = ⌈2d/η⌉` (A.6, p.17), with `d` the number of coordinates.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.6, p.17: "Let n = ⌈2d/η⌉". -/
noncomputable def gridN (ι : Type) [Fintype ι] (η : ℝ) : ℕ :=
  ⌈2 * (Fintype.card ι : ℝ) / η⌉₊

/-- **Lattice grid** `G_{d,η}` (A.6, p.17): the probability vectors whose coordinates are
multiples of `1/n`, `{(k_i / n)_i : k_i ∈ ℤ, k_i ≥ 0, Σ_i k_i = n}`, with `n = ⌈2d/η⌉`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.6, p.17: "Let n = ⌈2d/η⌉ and define
G_{d,η} := {(k1/n, k2/n, . . . , kd/n) : 0 ≤ ki ∈ Z, Σ_{i=1}^d ki = n}."

**Formalization Note.** Coordinates are indexed by a finite type `ι` with `d = |ι|` (the planner
uses `ι = Q`); for `ι = Fin d` this is `G_{d,η} ⊂ ℝ^d`. Each `k_i ≤ n`, so `k` ranges over
`ι → Fin (n + 1)`. -/
noncomputable def latticeGrid (ι : Type) [Fintype ι] [DecidableEq ι] (η : ℝ) : Finset (ι → ℝ) :=
  (Finset.univ.filter (fun k : ι → Fin (gridN ι η + 1) => ∑ i, (k i : ℕ) = gridN ι η)).image
    (fun k i => ((k i : ℕ) : ℝ) / (gridN ι η : ℝ))

/-- **Rounding within a simplex face** (A.6, p.17): for a coordinate set `𝒜` and a coordinate
`q* ∈ 𝒜`, round down every coordinate of `w` in `𝒜` other than `q*` to a multiple of `1/n`, put the
remaining mass at `q*`, and keep all coordinates outside `𝒜` at zero. For `𝒜 = ι` this is the
rounding of the proof of Lemma 6.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.6, p.17: "Given a probability vector
w ∈ ∆d, round down the first d − 1 coordinates to the nearest multiples of 1/n and put the remaining
mass in the last coordinate." and "For a nonempty admissible set Ah(u) of size k ≤ d, use the same
lattice grid restricted to that simplex face. Round down all but one admissible coordinate to
multiples of 1/n, put the remaining mass in the last admissible coordinate, and keep all other
coordinates zero."

**Formalization Note.** The paper's "last" coordinate refers to an unspecified order; the
coordinate `q*` receiving the remaining mass is a parameter, and every statement quantifies over
all `q* ∈ 𝒜`. -/
noncomputable def roundToFace {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (𝒜 : Finset ι)
    (qstar : ι) (w : ι → ℝ) : ι → ℝ :=
  fun q => if q ∈ 𝒜 ∧ q ≠ qstar then (⌊(gridN ι η : ℝ) * w q⌋₊ : ℝ) / gridN ι η
    else if q = qstar then
      1 - ∑ p ∈ 𝒜.erase qstar, (⌊(gridN ι η : ℝ) * w p⌋₊ : ℝ) / gridN ι η
    else 0

end DecodablePOMDP


