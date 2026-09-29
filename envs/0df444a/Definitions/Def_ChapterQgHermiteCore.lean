-- Prove2me | Definitions.Def_ChapterQgHermiteCore
-- name    : ChapterQgHermiteCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T12:14:20.540024+00:00
-- url     : https://prove2.me/theorems/cc28d518-7c57-4390-9ebe-1b1248fac3e4
-- title:
--   Plan item **§10.6.1, target 1** of `CONSOLIDATED_PLAN.md`: *well-definedness of the gauge-fixed `R + αR²` one-particle H ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgHermiteCore`, source chapter `BookProof/ChapterQgHermiteCore.lean`).
--
--   Plan item **§10.6.1, target 1** of `CONSOLIDATED_PLAN.md`: *well-definedness of the gauge-fixed `R + αR²` one-particle Hamiltonian on the Gauss–polynomial core*.
--
--   The scalaron potential `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` grows **exponentially** as `φ → −∞`, so it is not of temperate growth and the Schwartz-core multiplication theorem does not apply to it. The Gauss–polynomial core `p(x)e^{−x²/4}` — the basis in which the SIRK numerics actually work — is nevertheless a legitimate domain for it, because its Gaussian tail **dominates every exponential**.
--
--   **1. Gaussian dominance of exponentials.** `exp_abs_le_const_mul_exp_sq`: for every `c ≥ 0` and every `x`, `e^{c|x|} ≤ e^{2c²} e^{x²/8}`; hence `exp_abs_mul_gaussH_le` `e^{c|x|}e^{−x²/4} ≤ e^{2c²}e^{−x²/8}`, and `tendsto_exp_abs_mul_gaussH_cocompact` — the product tends to `0` at infinity.
--
--   **2. The exponential growth class.** `ExpBounded f` says `|f x| ≤ C e^{c|x|}` for some constants. It contains every polynomial (`expBounded_poly`), is closed under sums and scalar multiples, and contains the scalaron potential (`expBounded_starobinskyV`) — for which no temperate bound exists.
--
--   **3. Multiplication by such a potential maps the core into `L²`.** `memLp_gaussPoly` (the core lies in `L²`), `memLp_mul_gaussPoly_of_expBounded` (an exp-bounded continuous potential times a core element is in `L²`), and the instances `memLp_starobinskyV_mul_gaussPoly` and `memLp_scalaronFull1D_mul_gaussPoly` for the scalaron potential and for the full one-variable potential `V₃ + V` (conformal-mode parabola plus scalaron).
--
--   **4. The core is invariant under the kinetic term.** `hasDerivAt_gaussPoly` shows the derivative of a Gauss polynomial is the Gauss polynomial of `p' − x p / 2` (`gaussPolyDeriv`), so `deriv_gaussPoly` and `deriv2_gaussPoly` stay in the core, and `memLp_hamiltonian_gaussPoly` concludes: **`H ψ = −ψ'' + Wψ` lands in `L²` for every core element `ψ`**, for every continuous exp-bounded potential `W`, in particular for the scalaron one (`memLp_scalaronHamiltonian_gaussPoly`).
--
--   **6. Symmetry on the core.** `gint_gaussPolyDeriv_antisymm` and `gint_gaussPolyDeriv_two_symm` are the integration-by-parts identities at polynomial level (the boundary terms vanish because of the Gaussian weight), and `integral_kinetic_symm` / `integral_hamiltonian_symm` conclude that `−d²/dx² + W` is **symmetric** on the core for every continuous exp-bounded `W` (`integral_scalaronHamiltonian_symm` for the scalaron). This is the symmetric-operator half of the essential-self-adjointness question; the deficiency half is not proved here (for the potential term alone it is proved, for exponentially growing potentials too, in `BookProof.ChapterScalaronHermiteEsa`).
--
--   **7. Arbitrary dimension.** `ExpBounded` is stated for any normed space, and `memLp_mul_pgFun_of_expBounded` transports item 3 to the project's product Gauss–polynomial core `pgFun` of `L²(ℝᵈ)` (`BookProof.HermiteProductCore`): multiplication by a continuous, exponentially bounded potential maps that core into `L²(ℝᵈ)`. `ExpBounded.comp_coord` and `exists_exp_bound_mvPolyEval` are the two ingredients, and `memLp_scalaronSectorPotential_mul_pgFun` is the instance for the **reduced two-variable sector** `(R_c, φ)` with the potential `V₃(R_c) + V(φ)`.
--
--   This answers, in the Hermite basis, the domain question that §10.3 flags for the raw operator. It does **not** by itself give essential self-adjointness (targets 2–4 of §10.6.1); those remain open.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
import Mathlib

import Mathlib

/-!
# The Gauss–polynomial (Hermite) core: the one-particle Hamiltonian is well defined on it

Plan item **§10.6.1, target 1** of `CONSOLIDATED_PLAN.md`: *well-definedness of the
gauge-fixed `R + αR²` one-particle Hamiltonian on the Gauss–polynomial core*.

The scalaron potential `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` grows **exponentially** as
`φ → −∞`, so it is not of temperate growth and the Schwartz-core multiplication theorem does
not apply to it.  The Gauss–polynomial core `p(x)e^{−x²/4}` — the basis in which the SIRK
numerics actually work — is nevertheless a legitimate domain for it, because its Gaussian
tail **dominates every exponential**.

## What is proved

**1. Gaussian dominance of exponentials.**  `exp_abs_le_const_mul_exp_sq`: for every `c ≥ 0`
and every `x`, `e^{c|x|} ≤ e^{2c²} e^{x²/8}`; hence `exp_abs_mul_gaussH_le`
`e^{c|x|}e^{−x²/4} ≤ e^{2c²}e^{−x²/8}`, and `tendsto_exp_abs_mul_gaussH_cocompact` — the
product tends to `0` at infinity.

**2. The exponential growth class.**  `ExpBounded f` says `|f x| ≤ C e^{c|x|}` for some
constants.  It contains every polynomial (`expBounded_poly`), is closed under sums and
scalar multiples, and contains the scalaron potential (`expBounded_starobinskyV`) — for
which no temperate bound exists.

**3. Multiplication by such a potential maps the core into `L²`.**
`memLp_gaussPoly` (the core lies in `L²`), `memLp_mul_gaussPoly_of_expBounded` (an
exp-bounded continuous potential times a core element is in `L²`), and the instances
`memLp_starobinskyV_mul_gaussPoly` and `memLp_scalaronFull1D_mul_gaussPoly` for the scalaron
potential and for the full one-variable potential `V₃ + V` (conformal-mode parabola plus
scalaron).

**4. The core is invariant under the kinetic term.**  `hasDerivAt_gaussPoly` shows the
derivative of a Gauss polynomial is the Gauss polynomial of `p' − x p / 2`
(`gaussPolyDeriv`), so `deriv_gaussPoly` and `deriv2_gaussPoly` stay in the core, and
`memLp_hamiltonian_gaussPoly` concludes: **`H ψ = −ψ'' + Wψ` lands in `L²` for every core
element `ψ`**, for every continuous exp-bounded potential `W`, in particular for the
scalaron one (`memLp_scalaronHamiltonian_gaussPoly`).

**6. Symmetry on the core.**  `gint_gaussPolyDeriv_antisymm` and
`gint_gaussPolyDeriv_two_symm` are the integration-by-parts identities at polynomial level
(the boundary terms vanish because of the Gaussian weight), and `integral_kinetic_symm` /
`integral_hamiltonian_symm` conclude that `−d²/dx² + W` is **symmetric** on the core for
every continuous exp-bounded `W` (`integral_scalaronHamiltonian_symm` for the scalaron).
This is the symmetric-operator half of the essential-self-adjointness question; the
deficiency half is not proved here (for the potential term alone it is proved, for
exponentially growing potentials too, in `BookProof.ChapterScalaronHermiteEsa`).

**7. Arbitrary dimension.**  `ExpBounded` is stated for any normed space, and
`memLp_mul_pgFun_of_expBounded` transports item 3 to the project's product Gauss–polynomial
core `pgFun` of `L²(ℝᵈ)` (`BookProof.HermiteProductCore`): multiplication by a continuous,
exponentially bounded potential maps that core into `L²(ℝᵈ)`.  `ExpBounded.comp_coord` and
`exists_exp_bound_mvPolyEval` are the two ingredients, and
`memLp_scalaronSectorPotential_mul_pgFun` is the instance for the **reduced two-variable
sector** `(R_c, φ)` with the potential `V₃(R_c) + V(φ)`.

This answers, in the Hermite basis, the domain question that §10.3 flags for the raw
operator.  It does **not** by itself give essential self-adjointness (targets 2–4 of
§10.6.1); those remain open.
-/

namespace BookProof.QgHermiteCore

open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky

/-! ## 1. The Gaussian tail dominates every exponential -/







/-! ## 2. The exponential growth class -/

section ExpBoundedGeneral

variable {E : Type*} [NormedAddCommGroup E]

/-- `ExpBounded f`: `f` is dominated by some exponential, `|f x| ≤ C e^{c‖x‖}`.  This is the
growth class that the Gauss–polynomial core can absorb; it strictly contains the polynomials
and it contains the scalaron potential, which is *not* of temperate growth. -/
def ExpBounded (f : E → ℝ) : Prop :=
  ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖)









end ExpBoundedGeneral









/-! ## 3. The Gauss–polynomial core, and multiplication by such a potential -/

/-- A **Gauss polynomial** `p(x)e^{−x²/4}`: the generic element of the Hermite core. -/
noncomputable def gaussPoly (p : Polynomial ℝ) (x : ℝ) : ℝ := p.eval x * gaussH x













/-! ## 4. The core is invariant under differentiation -/

/-- The polynomial of the derivative of a Gauss polynomial: `(p e^{−x²/4})' =
(p' − x p / 2) e^{−x²/4}`. -/
noncomputable def gaussPolyDeriv (p : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.derivative p - Polynomial.C (1 / 2) * Polynomial.X * p











/-! ## 6. Symmetry of the Hamiltonian on the core -/

















/-! ## 7. Arbitrary dimension: the product Gauss–polynomial core of `L²(ℝᵈ)` -/

section MultiDim

open BookProof.HermiteProductCore

variable {d : ℕ}







/-! ### The reduced `(R_c, φ)` sector -/

/-- The full potential of the reduced two-variable sector of the gauge-fixed `R + αR²`
Hamiltonian: the conformal-mode parabola `V₃` in the first coordinate plus the scalaron
potential in the second. -/
noncomputable def scalaronSectorPotential (M alpha : ℝ) (V3 : Polynomial ℝ) (x : Vd 2) : ℝ :=
  V3.eval (x 0) + starobinskyV M alpha (x 1)







end MultiDim

end BookProof.QgHermiteCore


