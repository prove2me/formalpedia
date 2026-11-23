-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:34.338095+00:00
-- url     : https://prove2.me/theorems/68808ad5-67fd-4e86-b6e6-0612c732e415
-- title:
--   Archimedean Fundamental Domain Integers
-- statement:
--   Definitions and structural lemmas for Archimedean Fundamental Domain Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanFundamentalDomainIntegers.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
namespace GlobalTheory.CompanionTheory.Equi
open GlobalTheory.CompanionTheory.SW.RealCoord
section Domain
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
def infToMixed (y : Ainf F) : mixedEmbedding.mixedSpace F := toMixed F (coord F y)
def infDomain : Set (Ainf F) :=
  infToMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
end Domain
end GlobalTheory.CompanionTheory.Equi
end


