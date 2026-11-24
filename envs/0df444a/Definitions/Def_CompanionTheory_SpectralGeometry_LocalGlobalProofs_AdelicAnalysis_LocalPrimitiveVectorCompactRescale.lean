-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:35.99577+00:00
-- url     : https://prove2.me/theorems/f8705942-9bc5-471e-8ef5-97563faa496f
-- title:
--   Local Primitive Vector Compact Rescale
-- statement:
--   Definitions and structural lemmas for Local Primitive Vector Compact Rescale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalPrimitiveVectorCompactRescale.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
def UniP (K : Type*) [CommRing K] [TopologicalSpace K] (M : ℕ) : Prop :=
  ∃ Ω : Set (Fin M → K), IsCompact Ω ∧ ∀ y : Fin M → K, (∃ z : Fin M → K, z ⬝ᵥ y = 1) →
    ∃ (a : Kˣ) (z : Fin M → K), (a : K) • y ∈ Ω ∧ z ∈ Ω ∧ z ⬝ᵥ ((a : K) • y) = 1
section Quad
variable {L K : Type*} [Field L] [CommRing K] [Algebra L K]
def gg (d : K) (p : L × L) : K := p.1 • (1 : K) + p.2 • d
variable (bs : Module.Basis (Fin 2) L K)
def rr (x : K) : L × L := (bs.repr x 0, bs.repr x 1)
end Quad
section Norm
variable {L K : Type*} [NormedField L] [ProperSpace L]
def Nf (D : L) (p : L × L) : L := p.1 ^ 2 - D * p.2 ^ 2
variable [CommRing K] [Algebra L K] [TopologicalSpace K] (bs : Module.Basis (Fin 2) L K)
end Norm
section Delta
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
end Delta
end GlobalTheory.CompanionTheory.SW.PrimV


