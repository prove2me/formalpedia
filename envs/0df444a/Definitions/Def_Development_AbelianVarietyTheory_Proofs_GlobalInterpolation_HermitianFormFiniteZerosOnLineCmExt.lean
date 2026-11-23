-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:14.449833+00:00
-- url     : https://prove2.me/theorems/24c82e8a-84a1-453f-acc2-1166d4fd4a58
-- title:
--   Hermitian Form Finite Zeros On Line Cm Ext
-- statement:
--   Definitions and structural lemmas for Hermitian Form Finite Zeros On Line Cm Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HermitianFormFiniteZerosOnLineCmExt.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
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
namespace GlobalTheory.HermLineZeros
section Ring
variable {A : Type} [CommRing A] {M : ℕ}
end Ring
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
end GlobalTheory.HermLineZeros


