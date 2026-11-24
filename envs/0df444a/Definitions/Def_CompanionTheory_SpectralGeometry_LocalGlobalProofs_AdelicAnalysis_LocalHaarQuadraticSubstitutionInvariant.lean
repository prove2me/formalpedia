-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T20:34:59.999394+00:00
-- url     : https://prove2.me/theorems/3c89f808-91c8-4f2f-b8f4-e330a47d48ee
-- title:
--   Local Haar Quadratic Substitution Invariant
-- statement:
--   Definitions and structural lemmas for Local Haar Quadratic Substitution Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalHaarQuadraticSubstitutionInvariant.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
namespace GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
def vball (x : K) (γ : ℤᵐ⁰) : Set K := {y | Valued.v (y - x) < γ}
def IsRadius (K : Type) [Field K] [Valued K ℤᵐ⁰] (γ : ℤᵐ⁰) : Prop :=
  ∃ u : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v : Valuation K ℤᵐ⁰)))ˣ,
    MonoidWithZeroHom.ValueGroup₀.embedding u.1 = γ
variable [MeasurableSpace K] [BorelSpace K]
end GlobalTheory.CompanionTheory.SW.QuadIso


