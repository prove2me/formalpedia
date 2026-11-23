-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_SmoothTranslate
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_SmoothTranslate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:02.717433+00:00
-- url     : https://prove2.me/theorems/b4d96516-7cfa-40e9-9480-a77f12c4476f
-- title:
--   Smooth Translate
-- statement:
--   Definitions and structural lemmas for Smooth Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/SmoothTranslate.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
end PI.PhMeasCore.UnitaryGroupMassFormula
end


