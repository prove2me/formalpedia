-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:34.05739+00:00
-- url     : https://prove2.me/theorems/1b1afbbd-a34e-471e-92b7-fbe2264c80c4
-- title:
--   Tensor Integer Ring Almost All Places
-- statement:
--   Definitions and structural lemmas for Tensor Integer Ring Almost All Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
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
namespace GlobalTheory.CompanionTheory.SW.GoodRing
section Quad
variable {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) (τ : O →+* O) (δ : O) (D : R)
end Quad
section Lattice
variable {K A : Type} [Field K] [CommRing A] [Algebra K A] (R : Subring K)
end Lattice
section Place
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end Place
end GlobalTheory.CompanionTheory.SW.GoodRing


