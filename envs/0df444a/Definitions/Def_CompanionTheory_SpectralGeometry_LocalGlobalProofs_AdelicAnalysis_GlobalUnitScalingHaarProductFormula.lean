-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormula
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormula
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:06.723282+00:00
-- url     : https://prove2.me/theorems/1a2e114e-a74c-47e9-b412-89c04d587cb5
-- title:
--   Global Unit Scaling Haar Product Formula
-- statement:
--   Definitions and structural lemmas for Global Unit Scaling Haar Product Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GlobalUnitScalingHaarProductFormula.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ProdFormula
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
section Infinite
variable {F : Type} [Field F] [NumberField F]
end Infinite
section Finite
open HeckeCharacterZeroLocus.SiegelWeilU
variable {F : Type} [Field F] [NumberField F]
end Finite
section Main
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
end Main
end GlobalTheory.CompanionTheory.SW.ProdFormula


