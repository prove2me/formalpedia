-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:49.2638+00:00
-- url     : https://prove2.me/theorems/dc40972c-39d5-49eb-9b50-a4677776718d
-- title:
--   Positive Definite Density
-- statement:
--   Definitions and structural lemmas for Positive Definite Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
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
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
def mhat (χ : V → V → ℂ) (m : Measure V) (y : V) : ℂ := ∫ z, χ z y ∂m
def dens (χ : V → V → ℂ) (μ m : Measure V) (x : V) : ℂ := ∫ y, mhat χ m y * χ (-x) y ∂μ
def coset (L : AddSubgroup V) (a : V) : Set V := {x | x - a ∈ L}
section Top
variable [IsTopologicalAddGroup V]
end Top
section Main
variable [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [BorelSpace V]
end Main
section Ext
variable [IsTopologicalAddGroup V] [T2Space V] [SecondCountableTopology V] [BorelSpace V]
end Ext
end GlobalTheory.CompanionTheory.SW.Core.Density


