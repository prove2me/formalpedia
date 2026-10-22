-- Prove2me | Definitions.Def_ChapterLimitCircleExample
-- name    : ChapterLimitCircleExample
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T11:23:22.496789+00:00
-- url     : https://prove2.me/theorems/b6c768c3-a992-44bb-a471-be140997dffa
-- title:
--   Chapter LimitCircleExample
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLimitCircleExample.lean`): generated def bundle for ChapterLimitCircleExample. See BookProof/ChapterLimitCircleExample.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLimitCircleExample.lean

import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Mathlib


/-!
# An explicit smooth real potential whose Schrödinger operator is *not* essentially
# self-adjoint

`BookProof/ChapterScalaronWallEsa.lean` proves that `−d²/dx² + V` is essentially self-adjoint
on the compactly supported smooth core of `L²(ℝ)` for **every** smooth `V ≥ 0`, with no growth
hypothesis.  `CONSOLIDATED_PLAN.md`'s QG-2 sign warning is that the *opposite* sign class is
genuinely different: a potential unbounded below can put the operator in the Weyl limit-circle
regime, where both deficiency indices are positive and essential self-adjointness fails.  The
plan's Case B (the densitized conformal direction) is exactly of that kind, and the plan
records it as **false** — but that was an informal appeal to the classical `−d²/dx² − x⁴`
example.

This module removes the appeal by exhibiting a concrete potential and a concrete deficiency
vector, so the failure is a Lean theorem.

## The construction

Instead of starting from a potential and solving the ODE, we start from the solution.  Write
`W = e^{p + iq}` with `p, q` real; then

`W''/W = (p'' + p'² − q'²) + i(q'' + 2p'q')`,

so `W` solves `W'' = (V − i)W` for the *real* potential `V = p'' + p'² − q'²` as soon as
`q'' + 2p'q' = −1`, and `W ∈ L²` as soon as `e^{2p}` is integrable (the phase `q` is
irrelevant to the modulus).  Choosing

`q'(x) = −(1 + x²)/2`,  hence  `p'(x) = (1 − x)/(1 + x²)`,  `p(x) = arctan x − ½log(1 + x²)`,

makes the imaginary equation an identity, and `e^{2p(x)} = e^{2 arctan x}/(1 + x²) ≤ e^{π}/(1 + x²)`
is integrable.  The resulting potential

`V(x) = (2x² − 4x)/(1 + x²)² − (1 + x²)²/4`

is smooth, real, and behaves like `−x⁴/4` at infinity — the classical limit-circle profile.

## What is proved

* `lcSol_isL2Ode` — the explicit `W` is a square-integrable classical solution of
  `W'' = (lcV − i)W`;
* `lcSol_ne_zero` — it never vanishes;
* `lcV_not_deficiencyTrivialAt_I` — hence the deficiency space of `−d²/dx² + lcV` at `i` is
  nontrivial;
* **`lcV_not_essentiallySelfAdjoint`** — so `−d²/dx² + lcV` is **not** essentially
  self-adjoint on the compactly supported smooth core;
* `exists_smooth_potential_not_essentiallySelfAdjoint` — the existence statement: there is a
  smooth real potential on the line whose Schrödinger operator fails to be essentially
  self-adjoint on that core.  Combined with `wallHam_essentiallySelfAdjoint`, this shows the
  non-negativity hypothesis there cannot simply be dropped.
-/

namespace BookProof.LimitCircleExample

open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

/-! ## 1. The real ingredients -/

/-- The log-modulus `p(x) = arctan x − ½ log(1 + x²)` of the solution. -/
def lcP : ℝ → ℝ := fun x => Real.arctan x - Real.log (1 + x ^ 2) / 2

/-- `p'(x) = (1 − x)/(1 + x²)`. -/
def lcP' : ℝ → ℝ := fun x => (1 - x) / (1 + x ^ 2)

/-- `p''(x) = (x² − 2x − 1)/(1 + x²)²`. -/
def lcP'' : ℝ → ℝ := fun x => (x ^ 2 - 2 * x - 1) / (1 + x ^ 2) ^ 2

/-- The phase `q(x) = −(x + x³/3)/2`. -/
def lcQ : ℝ → ℝ := fun x => -(x + x ^ 3 / 3) / 2

/-- `q'(x) = −(1 + x²)/2`. -/
def lcQ' : ℝ → ℝ := fun x => -(1 + x ^ 2) / 2

/-- **The potential** `V(x) = (2x² − 4x)/(1 + x²)² − (1 + x²)²/4`: smooth, real, and
asymptotically `−x⁴/4`. -/
def lcV : ℝ → ℝ := fun x => (2 * x ^ 2 - 4 * x) / (1 + x ^ 2) ^ 2 - (1 + x ^ 2) ^ 2 / 4


/-! ## 2. The solution -/

/-- **The deficiency vector** `W = e^{p + iq}`. -/
def lcSol : ℝ → ℂ := fun x => Complex.exp (((lcP x : ℝ) : ℂ) + Complex.I * ((lcQ x : ℝ) : ℂ))

/-- Its logarithmic derivative `p' + iq'`. -/
def lcLog' : ℝ → ℂ := fun x => ((lcP' x : ℝ) : ℂ) + Complex.I * ((lcQ' x : ℝ) : ℂ)


/-! ## 3. Square integrability -/


/-! ## 4. The conclusion -/


end

/-! ## Audit -/

section Audit


end Audit

end BookProof.LimitCircleExample


