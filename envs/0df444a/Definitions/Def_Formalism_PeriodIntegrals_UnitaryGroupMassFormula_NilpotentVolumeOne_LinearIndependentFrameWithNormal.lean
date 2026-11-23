-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:13.975812+00:00
-- url     : https://prove2.me/theorems/dfa08482-9b67-4879-aa7d-1074d34dbc3c
-- title:
--   Linear Independent Frame With Normal
-- statement:
--   Definitions and structural lemmas for Linear Independent Frame With Normal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolNzeroOne.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
end Alg
section Frames
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {M r : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (P : Frame E M r) (T : F)
end Frames
end PI.VolNzeroOne.W


