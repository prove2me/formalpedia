-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:17.964799+00:00
-- url     : https://prove2.me/theorems/2798620c-ed28-4804-b5f9-2706a9ec2174
-- title:
--   Haar Map Linear Scaling By Determinant
-- statement:
--   Definitions and structural lemmas for Haar Map Linear Scaling By Determinant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMapLinearScalingByDeterminant.lean

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
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DetScale
open Matrix
open scoped Pointwise
section Ring
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]
end Ring
end GlobalTheory.CompanionTheory.SW.DetScale


