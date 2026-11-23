-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:37.60336+00:00
-- url     : https://prove2.me/theorems/261c9be3-c085-46b2-b81e-ff4921567eb0
-- title:
--   Tensor Involution Algebra Properties
-- statement:
--   Definitions and structural lemmas for Tensor Involution Algebra Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.KAlg
section Coord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R : Type} [CommRing R] [Algebra F R]
end Coord
end GlobalTheory.CompanionTheory.SW.KAlg


