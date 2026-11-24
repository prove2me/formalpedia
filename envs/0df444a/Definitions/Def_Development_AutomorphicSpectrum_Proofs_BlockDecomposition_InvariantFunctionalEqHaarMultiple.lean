-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:44.872638+00:00
-- url     : https://prove2.me/theorems/0455fb0c-1ab9-452a-b115-8b319d525f47
-- title:
--   Invariant Functional Eq Haar Multiple
-- statement:
--   Definitions and structural lemmas for Invariant Functional Eq Haar Multiple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
namespace GlobalTheory.CompanionTheory.FrobHaarR
section Abstract
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem ind_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Set.indicator (K : Set G) (fun _ => (1 : ℂ)) ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (K : Set G)
  · exact ⟨K, K.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set G)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
def ind (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : SB G :=
  ⟨_, ind_mem K hK⟩
end Abstract
section Integral
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
theorem integrable_sb (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    Integrable (α : G → ℂ) μ :=
  α.2.1.continuous.integrable_of_hasCompactSupport α.2.2
def haarForm (μ : Measure G) [IsFiniteMeasureOnCompacts μ] : SB G →ₗ[ℂ] ℂ where
  toFun α := ∫ x, (α : G → ℂ) x ∂μ
  map_add' α β := integral_add (integrable_sb μ α) (integrable_sb μ β)
  map_smul' c α := integral_const_mul c (α : G → ℂ)
variable [LocallyCompactSpace G]
end Integral
end GlobalTheory.CompanionTheory.FrobHaarR


