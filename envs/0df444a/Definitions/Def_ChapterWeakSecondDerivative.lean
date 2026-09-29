-- Prove2me | Definitions.Def_ChapterWeakSecondDerivative
-- name    : ChapterWeakSecondDerivative
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T11:45:39.648157+00:00
-- url     : https://prove2.me/theorems/b83eb6db-b714-4f58-9707-0255fac09cef
-- title:
--   One-dimensional distributional regularity: `u'' = c·u` in the weak sense
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.WeakSecondDerivative`, source chapter `BookProof/ChapterWeakSecondDerivative.lean`): One-dimensional distributional regularity: `u'' = c·u` in the weak sense
--
--   `CONSOLIDATED_PLAN.md` §10.6.1/§10.6.2 leaves one gap of the quantum-gravity chapter open: the *exponentially growing* scalaron wall. Every route the project has tried so far is a perturbative one — Kato–Rellich on the Gauss–polynomial core, the Carleman flux criterion on the Hermite lattice — and both are refuted or inapplicable for a wall that grows faster than every polynomial (`BookProof/ChapterHermiteExpWall.lean`).
--
--   The classical route that *does* reach an arbitrarily fast growing **non-negative** potential is not perturbative at all: a deficiency vector `u` of `−d²/dx² + V` solves the ordinary differential equation `u'' = (V − z)u`, and a non-negative `V` makes `|u|²` convex — hence, being integrable and non-negative, zero. The step that has to be supplied before the ODE argument can start is *regularity*: the deficiency vector is a priori only an `L²` function and the equation it satisfies is a distributional one.
--
--   This module supplies exactly that step, in one variable, with no reference to the physics:
--
--   * `exists_antideriv` — a test function of vanishing integral is the derivative of a test function (the elementary fact that makes the du Bois-Reymond argument work); * `ae_eq_const_of_integral_deriv_smul_eq_zero` — **du Bois-Reymond**: a locally integrable function orthogonal to the derivative of every test function is a.e. constant; * `ae_eq_affine_of_integral_deriv2_smul_eq_zero` — the second-order version: orthogonal to every *second* derivative means a.e. affine; * `integral_deriv_mul_indefiniteIntegral` — integration by parts against an indefinite integral of a merely locally integrable function (through Mathlib's `AbsolutelyContinuousOnInterval` calculus, since such a primitive is differentiable only almost everywhere); * `exists_ae_eq_doubleAntideriv_add_affine` — the real-valued regularity theorem: a weak solution of `u'' = G` is a.e. the double antiderivative of `G` plus an affine function; * **`exists_deriv2_of_weak_eq`** — the complex-valued statement in the form the Schrödinger argument consumes: if `u` is locally integrable, `c` is continuous and `∫ g'' u = ∫ g c u` for every real test function `g`, then `u` agrees almost everywhere with a genuinely twice differentiable `W` satisfying `W'' = c·W` *everywhere*.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWeakSecondDerivative.lean

import Mathlib


/-!
# One-dimensional distributional regularity: `u'' = c·u` in the weak sense

`CONSOLIDATED_PLAN.md` §10.6.1/§10.6.2 leaves one gap of the quantum-gravity chapter open:
the *exponentially growing* scalaron wall.  Every route the project has tried so far is a
perturbative one — Kato–Rellich on the Gauss–polynomial core, the Carleman flux criterion
on the Hermite lattice — and both are refuted or inapplicable for a wall that grows faster
than every polynomial (`BookProof/ChapterHermiteExpWall.lean`).

The classical route that *does* reach an arbitrarily fast growing **non-negative** potential
is not perturbative at all: a deficiency vector `u` of `−d²/dx² + V` solves the ordinary
differential equation `u'' = (V − z)u`, and a non-negative `V` makes `|u|²` convex — hence,
being integrable and non-negative, zero.  The step that has to be supplied before the ODE
argument can start is *regularity*: the deficiency vector is a priori only an `L²` function
and the equation it satisfies is a distributional one.

This module supplies exactly that step, in one variable, with no reference to the physics:

* `exists_antideriv` — a test function of vanishing integral is the derivative of a test
  function (the elementary fact that makes the du Bois-Reymond argument work);
* `ae_eq_const_of_integral_deriv_smul_eq_zero` — **du Bois-Reymond**: a locally integrable
  function orthogonal to the derivative of every test function is a.e. constant;
* `ae_eq_affine_of_integral_deriv2_smul_eq_zero` — the second-order version: orthogonal to
  every *second* derivative means a.e. affine;
* `integral_deriv_mul_indefiniteIntegral` — integration by parts against an indefinite
  integral of a merely locally integrable function (through Mathlib's
  `AbsolutelyContinuousOnInterval` calculus, since such a primitive is differentiable only
  almost everywhere);
* `exists_ae_eq_doubleAntideriv_add_affine` — the real-valued regularity theorem: a weak
  solution of `u'' = G` is a.e. the double antiderivative of `G` plus an affine function;
* **`exists_deriv2_of_weak_eq`** — the complex-valued statement in the form the Schrödinger
  argument consumes: if `u` is locally integrable, `c` is continuous and `∫ g'' u = ∫ g c u`
  for every real test function `g`, then `u` agrees almost everywhere with a genuinely twice
  differentiable `W` satisfying `W'' = c·W` *everywhere*.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.WeakSecondDeriv

open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

/-- A **test function** on the line: smooth and compactly supported. -/
def IsTestFun (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ HasCompactSupport g

namespace IsTestFun



















end IsTestFun

/-! ## 1. Elementary facts about test functions -/

















/-! ## 2. The du Bois-Reymond lemmas -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]








/-! ## 3. Integration by parts against an indefinite integral -/







/-! ## 4. The real regularity theorem -/

/-- The double antiderivative of a locally integrable function. -/
def doubleAntideriv (G : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, ∫ s in (0 : ℝ)..t, G s







/-! ## 5. Calculus for the double antiderivative -/









/-! ## 6. The complex regularity theorem -/



end

end BookProof.WeakSecondDeriv


