-- Prove2me | Definitions.Def_ChapterSqueezedGaussStates
-- name    : ChapterSqueezedGaussStates
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:42:22.497264+00:00
-- url     : https://prove2.me/theorems/08847b26-9159-41a2-972b-fdefefda55eb
-- title:
--   Chapter SqueezedGaussStates
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSqueezedGaussStates.lean`): generated def bundle for ChapterSqueezedGaussStates. See BookProof/ChapterSqueezedGaussStates.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqueezedGaussStates.lean

import Definitions.Def_ChapterGaussCoordCombo
import Mathlib


/-!
# Squeezed states on the Gauss–polynomial core

The Gauss–polynomial core of `L²(ℝᵈ)` consists of the states `p(x) e^{-‖x‖²/4}`.  In the
coordinate `x_i` the Gaussian factor is fixed, so the "width" of a core state in that
coordinate has to be produced by the polynomial factor.  This chapter constructs the family
that does it: the **truncated Hermite expansion of a Gaussian**,

`squeezeState i v M = ∑_{m ≤ M} (vᵐ / m!) He_{2m}(x_i)`,   `|v| < 1/2`,

whose infinite version is `(1+2β)^{-1/2} e^{-βx_i²}` with `v = −β/(1+2β)`.

Two exact algebraic facts drive everything (`Acoef_rec` and `sum_odd_Acoef_le`), and they are
purely combinatorial consequences of the three-term recurrence:

* multiplying by `x_i`, or differentiating, turns the family into an *odd* Hermite
  combination whose interior coefficients are the old ones scaled by
  `κ = α(1+2v) + 2γv` (`opCoef_of_lt`), with only a boundary term left over;
* the weighted sums of `A_m = (vᵐ/m!)²(2m)!` obey `(1−4v²)∑(2m+1)A_m ≤ ∑A_m`
  (`sum_odd_Acoef_le`).

Consequently `⟨x_i²⟩ → 0` as `v → −1/2` (`exists_position_small`) and `⟨π_i²⟩ → 0` as
`v → 1/2` (`exists_momentum_small`): **the Gauss–polynomial core has neither a position nor a
momentum form gap**, even though every one of its elements carries the same fixed Gaussian.
-/

namespace BookProof.SqueezedGaussStates

open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

/-! ## The coefficient family -/

/-- The coefficients `vᵐ/m!` of the squeezed state, truncated at `M`. -/
def sqCoef (v : ℝ) (M : ℕ) : ℕ → ℝ := fun m => if m ≤ M then v ^ m / (m.factorial : ℝ) else 0





/-- The **squeezed core state** in the coordinate `i`. -/
def squeezeState (i : Fin d) (v : ℝ) (M : ℕ) : MvPolynomial (Fin d) ℂ :=
  coordCombo i (sqCoef v M) 0 M

/-! ## Multiplication by a coordinate and differentiation -/







/-! ## The operator `α x_i + γ ∂_i` on a squeezed state -/

/-- The odd coefficients produced by `α x_i + γ ∂_i` from a squeezed state. -/
def opCoef (α γ v : ℝ) (M : ℕ) : ℕ → ℝ := fun k =>
  α * (sqCoef v M k + 2 * (k + 1) * sqCoef v M (k + 1)) + γ * (2 * (k + 1) * sqCoef v M (k + 1))

/-- The interior scaling factor `κ = α(1+2v) + 2γv`. -/
def kappa (α γ v : ℝ) : ℝ := α * (1 + 2 * v) + 2 * γ * v







/-! ## The exact coefficient sums -/

/-- `A_m = (vᵐ/m!)² (2m)!`, the Gaussian square norm of the `m`-th term. -/
def Acoef (v : ℝ) (m : ℕ) : ℝ := (v ^ m / (m.factorial : ℝ)) ^ 2 * (((2 * m).factorial : ℕ) : ℝ)









/-- `V_M = ∑_{m ≤ M} A_m`, the Gaussian square norm of the squeezed state. -/
def Vsum (v : ℝ) (M : ℕ) : ℝ := ∑ m ∈ Finset.range (M + 1), Acoef v m

/-- `U_M = ∑_{m ≤ M} (2m+1) A_m`, the weighted sum controlling the odd combination. -/
def Usum (v : ℝ) (M : ℕ) : ℝ := ∑ m ∈ Finset.range (M + 1), (2 * (m : ℝ) + 1) * Acoef v m











/-! ## The Gaussian square norms of the squeezed state and its images -/





/-! ## The two limits -/







end

end BookProof.SqueezedGaussStates


