-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:43.233801+00:00
-- url     : https://prove2.me/theorems/bf90ecc1-d0ab-48d3-ab56-03a68c50bab4
-- title:
--   Unit Product Closure Properties
-- statement:
--   Definitions and structural lemmas for Unit Product Closure Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean

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
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg
variable {F : Type} [Field F] [NumberField F]
def sqrtHom : ℝ≥0 →* ℝ≥0 where
  toFun := NNReal.sqrt
  map_one' := NNReal.sqrt_one
  map_mul' := NNReal.sqrt_mul
end GlobalTheory.CompanionTheory.SW.UnitProdAlg


