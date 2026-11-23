-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:52.485524+00:00
-- url     : https://prove2.me/theorems/1858c1e1-1b5c-430b-90a5-049e3cc80989
-- title:
--   Primitive Vector Lattice Rescale Almost All
-- statement:
--   Definitions and structural lemmas for Primitive Vector Lattice Rescale Almost All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
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
namespace GlobalTheory.CompanionTheory.SW.PrimGood
section Norm
variable {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
end Norm
section Quad
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}
variable (B Δ) in

def nrm (x : K) : L := B.repr x 0 ^ 2 - Δ * B.repr x 1 ^ 2
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
variable (B) in

def idm (s : L) : K := (2⁻¹ : L) • B 0 + ((2 * s)⁻¹ : L) • B 1
variable (B) in

def ev (s : L) (x : K) : L := B.repr x 0 + s * B.repr x 1
end Quad
section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Global
end GlobalTheory.CompanionTheory.SW.PrimGood


