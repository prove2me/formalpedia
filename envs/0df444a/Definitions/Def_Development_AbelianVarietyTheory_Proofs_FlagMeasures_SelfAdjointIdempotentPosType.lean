-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T05:12:53.903104+00:00
-- url     : https://prove2.me/theorems/6a041d53-d08e-4f70-9f2b-b25d812c70f9
-- title:
--   Self Adjoint Idempotent Pos Type
-- statement:
--   Definitions and structural lemmas for Self Adjoint Idempotent Pos Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointIdempotentPosType.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowLev.GroupAlgPos
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
variable {Q : Type} [Group Q]
def adj [Finite Q] (a : MonoidAlgebra ℂ Q) : MonoidAlgebra ℂ Q :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun q => star (a.coeff q⁻¹))
end GlobalTheory.RowLev.GroupAlgPos


