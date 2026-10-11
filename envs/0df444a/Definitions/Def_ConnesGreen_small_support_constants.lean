-- Prove2me | Definitions.Def_ConnesGreen_small_support_constants
-- name    : ConnesGreen_small_support_constants
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-08T04:20:35.212475+00:00
-- url     : https://prove2.me/theorems/864f63df-9e07-4978-8e08-8cb98ee9f3d6
-- title:
--   Original explicit small-support Weil positivity constants
-- statement:
--   Exact unchanged native positiveGammaCutoff, smallSupportCost and positiveSupportRadius. Uses the original gammaBracket definition. No positivity or RH premise.
-- source:
--   WeilDefect/Connes/SmallSupportPositivity.lean at f02a526d7c7fb8a43356376a2389d6f8afc08e2a; unchanged exact native definition bodies.
--
--   Literature/source audit addendum (2026-10-11; COR-19): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil 1a32f7de3442feb804b4962bb6766304a56b5be8, WeilDefect/Connes/SmallSupportPositivity.lean, SHA256 a0e4ad5424f8aff8d42aab5683747cdd0c9a3e8249ee8a44942ae1b3ecadf8c2. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry. The unchanged graph RHS values were checked against native definitions by Lean rfl. This is source/value custody, not an assertion that contextual literature supplies the whole definition bundle.

import Definitions.Def_Zeta23_ExplicitFormula
noncomputable section
namespace ConnesGreen
noncomputable def positiveGammaCutoff : ℝ := 2 * Real.exp (6 + |Real.log Real.pi|)

noncomputable def smallSupportCost : ℝ :=
  (Zeta23.EF.gammaBracket positiveGammaCutoff - Zeta23.EF.gammaBracket 0) *
    (2 * positiveGammaCutoff / Real.pi) + 4 * Real.exp 1

noncomputable def positiveSupportRadius : ℝ :=
  min (Real.log 2 / 2) (min 1 (1 / (2 * smallSupportCost)))

end ConnesGreen


