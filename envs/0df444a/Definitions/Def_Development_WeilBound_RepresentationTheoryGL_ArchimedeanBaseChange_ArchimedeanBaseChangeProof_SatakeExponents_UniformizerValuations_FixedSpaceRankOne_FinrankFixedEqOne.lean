-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:27.708738+00:00
-- url     : https://prove2.me/theorems/91c51323-d744-4dff-9ca3-19a4ec90a412
-- title:
--   Finrank Fixed Eq One
-- statement:
--   Definitions and structural lemmas for Finrank Fixed Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/FixedSpaceRankOne/FinrankFixedEqOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
namespace PositivityTheory.Rg.BcB.F.EigA
section Sums
end Sums
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
def stabK (K : Subgroup G) (g : G) : Subgroup K := (K.map (MulAut.conj g).toMonoidHom).subgroupOf K
def hop (ρ : Representation ℂ G V) (K : Subgroup G) (g : G) : V →ₗ[ℂ] V :=
  ∑ᶠ q : K ⧸ stabK K g, ρ ((q.out : K) : G) ∘ₗ ρ g
open Classical in

def reps (K : Subgroup G) (g : G) [Fintype (K ⧸ stabK K g)] : Finset G :=
  Finset.image (fun q : K ⧸ stabK K g => ((q.out : K) : G) * g) Finset.univ
def GelPair (K : Subgroup G) : Prop :=
  (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) ∧
    ∃ τ : G → G, (∀ a b, τ (a * b) = τ b * τ a) ∧ (∀ a, τ (τ a) = a) ∧
      (∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) ∧ ∀ k ∈ K, τ k ∈ K
end PositivityTheory.Rg.BcB.F.EigA
end


