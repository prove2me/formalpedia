-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:40.296997+00:00
-- url     : https://prove2.me/theorems/ea9963ea-be6d-4c74-b363-145b2125dce2
-- title:
--   Finsum Quotient Of Le
-- statement:
--   Definitions and structural lemmas for Finsum Quotient Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
def incl (K κ ι : Type) [Field K] : Matrix κ ι (𝓞 K) →+ Matrix κ ι K :=
  (algebraMap (𝓞 K) K).toAddMonoidHom.mapMatrix
end
end GlobalTheory.SW.HaarLevel
namespace GlobalTheory.SW
end GlobalTheory.SW


