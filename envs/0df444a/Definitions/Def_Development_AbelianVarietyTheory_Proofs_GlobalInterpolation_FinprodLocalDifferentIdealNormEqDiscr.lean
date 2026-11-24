-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:38.469798+00:00
-- url     : https://prove2.me/theorems/1f981d6b-5aa0-4a77-be37-607a47310f14
-- title:
--   Finprod Local Different Ideal Norm Eq Discr
-- statement:
--   Definitions and structural lemmas for Finprod Local Different Ideal Norm Eq Discr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
namespace GlobalTheory.LocalDifferentProduct
section Local
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
end Local
section Relative
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
end Relative
end GlobalTheory.LocalDifferentProduct


