-- Prove2me | Definitions.Def_ChapterSchrodingerCutoffEsa
-- name    : ChapterSchrodingerCutoffEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-18T06:17:01.763265+00:00
-- url     : https://prove2.me/theorems/cf01fcd6-ce2e-4577-b369-cfd8b4ae4d92
-- title:
--   Schrödinger cutoff function
-- statement:
--   Formal definitions for the smooth cutoff function used in the Schrödinger equation context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSchrodingerCutoffEsa.lean

import Mathlib


/-!
# The Simader–Faris–Lavine cutoff method for `-d²/dx² + V`

This module carries out, in one space dimension and with no unproved input, the
**cutoff / commutator energy argument** for essential self-adjointness of a
Schrödinger operator `H = -Δ + V` with a potential that is allowed to grow
arbitrarily fast — the motivating example being the non-polynomial
`V(x) = eˣ + e⁻ˣ`, for which none of the polynomial-growth criteria apply.

The mathematical content is the classical energy estimate: if `u` is a
square-integrable classical solution of `-u'' + V u = z u` with
`Re z + 1 ≤ V` pointwise, then testing the equation against `χ_R² ū`,
integrating by parts once, and absorbing the cross term by Young's inequality
gives

  `∫_{[-R,R]} |u|² ≤ ∫ χ_R² (V - Re z) |u|² ≤ (2C²/R²) ‖u‖²_{L²}`,

where `C` bounds `|χ'|` for a fixed smooth cutoff `χ` equal to `1` on `[-1,1]`
and supported in `[-2,2]`, and `χ_R(x) = χ(x/R)`.  Letting `R → ∞` forces
`u = 0`.  Applied to `z = ± i` — whose real part is `0`, so that the hypothesis
`Re z + 1 ≤ V` only asks `V ≥ 1` — this says exactly that the classical
deficiency spaces of `H` are trivial, which is the analytic heart of essential
self-adjointness.

## Contents

* `integral_deriv_eq_zero_of_hasCompactSupport` — the one-dimensional
  integration-by-parts engine: the integral over `ℝ` of the derivative of a
  compactly supported `C¹` function vanishes.
* The section "the cutoff family" — a concrete smooth cutoff `chi` built from
  Mathlib's `ContDiffBump`, its basic properties, the gradient bound
  `exists_deriv_chi_bound`, and the rescaled family `exists_scaled_cutoff`
  (Milestone 3 of the plan: `|χ_R'| ≤ C/R`).
* `hasDerivAt_reInner` — the derivative of the energy density
  `x ↦ Re(conj (u x) · u'(x))`.
* `schrodingerOp`, `integral_conj_secondDeriv_comm` and `schrodingerOp_symmetric`
  — Milestone 2: the operator `H f = -f'' + V f` on the compactly supported
  twice differentiable core, and its Hermitian symmetry there, for an arbitrary
  real continuous `V` (no growth restriction).
* `cutoff_energy_core` — Milestone 4 in its sharpest form: under the weaker
  hypothesis `Re z ≤ V` it bounds *both* the potential energy
  `∫_{[-R,R]} (V - Re z)|u|²` and the Dirichlet energy `∫_{[-R,R]} |u'|²` by a
  multiple of `‖u‖²_{L²}/R²`.
* `cutoff_energy_estimate` — Milestone 4: the estimate displayed above, for an
  arbitrary continuous `V` and arbitrary `z` with `Re z + 1 ≤ V`.
* `l2_classical_solution_eq_zero` — Milestone 5: the limit `R → ∞`, giving
  `u = 0`.
* `l2_classical_solution_eq_zero_of_nonneg` — the same conclusion under the
  weaker hypothesis `Re z ≤ V`, obtained by running the limit on the Dirichlet
  term instead: `u' ≡ 0`, so `u` is constant, and a constant in `L²(ℝ)` is `0`.
* `laplacian_deficiency_trivial` / `..._I` / `..._negI` — the `V = 0`
  specialisation: the free Laplacian `-d²/dx²` on the line has no nonzero
  square-integrable classical solution of `-u'' = z u` when `Re z ≤ 0`, in
  particular for `z = ± i`.
* `Vexp`, `two_le_Vexp` and `schrodinger_exp_deficiency_trivial` /
  `schrodinger_exp_deficiency_trivial_I` / `..._negI` — the motivating
  application: for `V(x) = eˣ + e⁻ˣ` the operator `-d²/dx² + V` has no nonzero
  square-integrable classical solution of `H u = ± i u`.

Nothing here is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.SchrodingerCutoff

open MeasureTheory Filter Complex

/-! ## Integration by parts on the line -/



/-! ## The cutoff family -/

/-- The reference bump: equal to `1` on `[-1,1]`, supported in `[-2,2]`. -/
noncomputable def bump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩

/-- The reference cutoff `χ : ℝ → ℝ`. -/
noncomputable def chi : ℝ → ℝ := fun x => bump0 x























/-! ## The derivative of the energy density -/



/-! ## Milestone 4: the cutoff energy estimate -/





/-! ## Milestone 5: the limit `R → ∞` -/













/-! ## Milestone 2: the operator on the smooth compactly supported core -/

/-- The Schrödinger operator `H f = -f'' + V f` on the line. -/
noncomputable def schrodingerOp (V : ℝ → ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv f) x + (V x : ℂ) * f x







/-! ## The exponential potential -/

/-- The non-polynomial potential `V(x) = eˣ + e⁻ˣ` of the plan. -/
noncomputable def Vexp : ℝ → ℝ := fun x => Real.exp x + Real.exp (-x)











end BookProof.SchrodingerCutoff


