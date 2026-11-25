-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
-- name    : GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:24.263015+00:00
-- url     : https://prove2.me/theorems/2ec43a16-6108-4c56-ab81-c3acc5582936
-- title:
--   Trace Formula Multiplicity
-- statement:
--   Definitions and structural lemmas for Trace Formula Multiplicity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
namespace GroundTheory.Automorphic
noncomputable section
namespace UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)
section Class
variable {σ : UnitaryRep G K}
abbrev EquivSummands (σ : UnitaryRep G K) : Type _ :=
  {j : J // (π.restrict (V j) (hinv j)).IsEquivalent σ}
def summandEquivL (w : EquivSummands hinv σ) : K →L[ℂ] V w.1 :=
  ((w.2.some.symm.toLinearIsometryEquiv : K ≃ₗᵢ[ℂ] V w.1) : K →L[ℂ] V w.1)
def sumEquivL [Fintype (EquivSummands hinv σ)] (c : EquivSummands hinv σ → ℂ) : K →L[ℂ] H :=
  ∑ w, c w • ((V w.1).subtypeL ∘L summandEquivL hinv w)
end Class
end UnitaryRep
end
end GroundTheory.Automorphic


