-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
-- name    : GroundTheory_AutomorphicForms_TraceFormulaSpectral
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:42:48.04506+00:00
-- url     : https://prove2.me/theorems/bd3f86db-cdac-4eac-8e78-e573237a2c41
-- title:
--   Trace Formula Spectral
-- statement:
--   Definitions and structural lemmas for Trace Formula Spectral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaSpectral.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_refl
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_top_le_topologicalClosure_iSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
namespace GroundTheory.Automorphic
noncomputable section
section Intermediate
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
end Intermediate
namespace UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
section Equiv
variable {μ : Measure G} {σ : UnitaryRep G K} {τ : UnitaryRep G L}
end Equiv
section Decomposition
variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable {π μ f}
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
def collectedHilbertBasis : HilbertBasis (Σ j, (exists_hilbertBasis ℂ (V j)).choose) ℂ H :=
  HilbertBasis.mk (v := fun a => (V a.1).subtypeₗᵢ (stdHilbertBasis ℂ (V a.1) a.2))
    (hsum.OrthogonalFamily.orthonormal_sigma_orthonormal fun j =>
      (stdHilbertBasis ℂ (V j)).orthonormal) (by
    refine le_trans (top_le_topologicalClosure_iSup hsum) (Submodule.topologicalClosure_minimal _
      (iSup_le fun j => ?_) (Submodule.isClosed_topologicalClosure _))
    intro v hv
    have hd := (stdHilbertBasis ℂ (V j)).dense_span
    have hmem : (⟨v, hv⟩ : V j) ∈
        (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).topologicalClosure := by
      rw [hd]; trivial
    have h1 := Submodule.topologicalClosure_map (V j).subtypeL
      (Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j))))
    have h2 : v ∈ ((Submodule.span ℂ (Set.range (stdHilbertBasis ℂ (V j)))).map
        ((V j).subtypeL : V j →ₗ[ℂ] H)).topologicalClosure :=
      h1 ⟨⟨v, hv⟩, hmem, rfl⟩
    refine Submodule.topologicalClosure_mono ?_ h2
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨j, i⟩, rfl⟩)
variable (π) in

def restrictSetoid : Setoid J where
  r j k := (π.restrict (V j) (hinv j)).IsEquivalent (π.restrict (V k) (hinv k))
  iseqv := ⟨fun _ => IsEquivalent.refl _, fun h => h.symm, fun h h' => h.trans h'⟩
variable (π) in

def multiplicity (c : Quotient (restrictSetoid π hinv)) : ℕ :=
  Nat.card {j : J // (Quotient.mk (restrictSetoid π hinv) j) = c}
end Decomposition
end UnitaryRep
end
end GroundTheory.Automorphic


