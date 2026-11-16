-- Prove2me | Definitions.Def_KhintchineTwoRegime_Supplement_tau
-- name    : KhintchineTwoRegime_Supplement_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:23:48.938174+00:00
-- url     : https://prove2.me/theorems/e22e6518-9375-442b-9896-daa107bed1b7
-- title:
--   Distance to the extremal set, eq. (5): $\tau(\omega)=\min_{i<j}\|\omega\pm e_i/\sqrt2\pm e_j/\sqrt2\|_2$
-- statement:
--   For $n\ge2$ and $\omega\in\mathbb R^n$, the **distance to the extremal set** is
--   $$
--   \tau(\omega)=\min_{1\le i<j\le n}\Bigl\|\omega\pm\tfrac1{\sqrt2}e_i\pm\tfrac1{\sqrt2}e_j\Bigr\|_2,
--   $$
--   where $e_i$ is the $i$-th coordinate vector, $\|\cdot\|_2$ is the Euclidean norm, and the minimum includes all four choices of signs. The extremal set $\{\pm e_i/\sqrt2\pm e_j/\sqrt2\}$ is exactly the set of unit vectors attaining Szarek's sharp bound $K_n(\omega)=1/\sqrt2$, so $\tau(\omega)$ measures how far $\omega$ is from equality in the sharp Khintchine inequality. It is invariant under sign changes and permutations of the coordinates, and for a proper unit vector it equals $\|\omega-\omega^*\|_2$ with $\omega^*=(1/\sqrt2,1/\sqrt2,0,\dots,0)$ (eq. (6)).
--
--   **Formalization Note** The minimum is a finite minimum (`Finset.inf'`) over the pairs $i<j$ and the sign pairs, which is nonempty for $n\ge2$; the definition therefore takes the hypothesis $n\ge2$ as an argument, and has no default value. Indices are 0-based, $e_i$ is `Pi.single i 1`, and the norm is the published Euclidean norm `l2Norm` (not the sup norm of `Fin n → ℝ`).
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, eq. (5), p.4 (used in Theorem 3, p.9)

import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime.Supplement

/-- The real sign `+1` / `−1` of a Boolean (`true ↦ +1`, `false ↦ −1`), the encoding of
`KhintchineTwoRegime.K`. -/
def signR (b : Bool) : ℝ := if b then 1 else -1

/-- The index set of eq. (5): pairs `(i, j)` with `i < j` and the two signs `(σ, σ')`. -/
def extremalIndex (n : ℕ) : Finset ((Fin n × Fin n) × (Bool × Bool)) :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) ×ˢ Finset.univ

/-- For `n ≥ 2` the index set of eq. (5) is nonempty (it contains `(0, 1)`). -/
theorem extremalIndex_nonempty {n : ℕ} (hn : 2 ≤ n) : (extremalIndex n).Nonempty :=
  ⟨((⟨0, by omega⟩, ⟨1, by omega⟩), (true, true)), by
    simp only [extremalIndex, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      and_true]
    exact Fin.mk_lt_mk.mpr (by omega)⟩

/-- The distance `τ(ω)` of `ω ∈ ℝⁿ` to the extremal set `{±eᵢ/√2 ± eⱼ/√2}`, eq. (5)
(Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2, eq. (5), p.4):
`τ(ω) = min_{1 ≤ i < j ≤ n} ‖ω ± eᵢ/√2 ± eⱼ/√2‖₂`, the minimum over all choices of signs.

**Formalization Note** The minimum is the `Finset.inf'` over the finite nonempty index set
`{(i, j) : i < j} × {±1}²`, so the definition takes the paper's standing assumption `n ≥ 2`
as an argument `hn`; there is no junk value. `eᵢ` is `Pi.single i 1`, the signs are
`signR σ`, the norm is the Euclidean norm `l2Norm` (never the sup norm of `Fin n → ℝ`).
Indices are 0-based. Eq. (5) is used for every `ω`, not only for proper ones: on proper
unit vectors it equals `‖ω − ω*‖₂` (eq. (6)), and it is invariant under signs and
permutations. -/
noncomputable def tau {n : ℕ} (hn : 2 ≤ n) (ω : Fin n → ℝ) : ℝ :=
  (extremalIndex n).inf' (extremalIndex_nonempty hn) fun p =>
    l2Norm (ω + (signR p.2.1 / Real.sqrt 2) • (Pi.single p.1.1 (1 : ℝ) : Fin n → ℝ)
      + (signR p.2.2 / Real.sqrt 2) • (Pi.single p.1.2 (1 : ℝ) : Fin n → ℝ))

end KhintchineTwoRegime.Supplement


