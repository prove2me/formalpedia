-- Prove2me | Definitions.Def_ChapterLimitCircleExamplePromoted
-- name    : ChapterLimitCircleExamplePromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-03T12:28:25.566197+00:00
-- url     : https://prove2.me/theorems/f529c909-2122-4b7d-9f5e-662a69daab03
-- title:
--   Limit-circle potential: smoothness of `lcV`
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLimitCircleExample.lean`): `contDiff_lcV` (the potential `V` is a rational function with nonvanishing denominator, hence smooth), carved out of ChapterLimitCircleExample under the §2.13 new-name route because the served copy predates it, so the three `lcV_not_*` statements die server-side with `Unknown identifier`. Consumers add a single `import Definitions.Def_ChapterLimitCircleExamplePromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLimitCircleExample.lean

-- Generated from ChapterLimitCircleExample.lean — the smoothness of the limit-circle
-- potential, which the platform's served ChapterLimitCircleExample copy predates
-- (§2.13 new-name route: submit-definition rejects an existing name, so the decl
-- lives here instead).  The three `lcV_not_*` statements cite it as the
-- `ContDiff` hypothesis of WallDeficiencyObstruction.
import Definitions.Def_ChapterLimitCircleExample
import Mathlib

namespace BookProof.LimitCircleExample

open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

/-- `V` is smooth: it is a rational function with nonvanishing denominator. -/
lemma contDiff_lcV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) lcV := by
  have hden : ∀ x : ℝ, (1 + x ^ 2) ^ 2 ≠ 0 := fun x => by positivity
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : ℝ => (2 * x ^ 2 - 4 * x) / (1 + x ^ 2) ^ 2 :=
    ContDiff.div (by fun_prop) (by fun_prop) hden
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ => (1 + x ^ 2) ^ 2 / 4 := by fun_prop
  exact h1.sub h2

end

end BookProof.LimitCircleExample


