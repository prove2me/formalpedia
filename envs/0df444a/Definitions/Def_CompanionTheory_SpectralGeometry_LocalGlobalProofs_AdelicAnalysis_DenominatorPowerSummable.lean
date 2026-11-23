-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:38.255876+00:00
-- url     : https://prove2.me/theorems/b4bae9eb-6675-472a-a98c-30587f5ed9aa
-- title:
--   Denominator Power Summable
-- statement:
--   Definitions and structural lemmas for Denominator Power Summable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DenominatorPowerSummable.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
namespace GlobalTheory.CompanionTheory.SW.DenSum
variable {F : Type} [Field F] [NumberField F]
noncomputable def dI (b : F) : Ideal (𝓞 F) :=
  Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F b) (1 : Submodule (𝓞 F) F)
end GlobalTheory.CompanionTheory.SW.DenSum


