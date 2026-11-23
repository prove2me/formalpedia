-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqIdOfIsUnramifiedAt
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqIdOfIsUnramifiedAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:38.276277+00:00
-- url     : https://prove2.me/theorems/20f96348-1450-483c-9e35-db02159fe3ee
-- title:
--   Eq Id Of Is Unramified At
-- statement:
--   Definitions and structural lemmas for Eq Id Of Is Unramified At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/EqIdOfIsUnramifiedAt.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace GlobalTheory.UnramifiedDiscriminant
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
end GlobalTheory.UnramifiedDiscriminant


