-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_BirationalOfBlock
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_BirationalOfBlock
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:12:43.716219+00:00
-- url     : https://prove2.me/theorems/a8abace4-2afb-45e7-9bd7-6bd6f063aac7
-- title:
--   Birational Of Block
-- statement:
--   Definitions and structural lemmas for Birational Of Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/BirationalOfBlock.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_rename_weightedHomogeneousComponent_550dd4a17607

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace BlockImage
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι] in

theorem blockIncl_injective (k₀ : ι) : Function.Injective (blockIncl (n := n) k₀) := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff, heq_iff_eq, true_and] at h
  rw [h]
omit [Fintype ι] [DecidableEq ι] in

theorem const_injective (k₀ : ι) : Function.Injective (fun _ : Unit ↦ k₀) := fun _ _ _ ↦ rfl
omit [Fintype ι] in

theorem rename_component (k₀ : ι) (m : Unit → ℕ) (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    rename (blockIncl k₀) (weightedHomogeneousComponent (coordDeg fun _ : Unit ↦ n k₀) m f) =
      weightedHomogeneousComponent (coordDeg n) (Function.extend (fun _ : Unit ↦ k₀) m 0)
        (rename (blockIncl k₀) f) :=
  FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent (ι := blockIdx fun _ : Unit ↦ n k₀)
    (ι' := blockIdx n) (j := fun _ : Unit ↦ k₀) (g := blockIncl k₀) (fun _ ↦ rfl)
    (const_injective k₀) (blockIncl_injective k₀) m f
def projVariety (P : ArithVariety n) (k₀ : ι) : ArithVariety (fun _ : Unit ↦ n k₀) where
  ideal := P.projIdeal k₀
  isPrime := by
    have := P.isPrime
    exact Ideal.comap_isPrime _ _
  homogeneous f hf m := by
    change rename (blockIncl k₀) _ ∈ P.ideal
    rw [rename_component]
    exact P.homogeneous _ hf _
  relevant k := by
    obtain ⟨i, hi⟩ := P.relevant k₀
    refine ⟨i, fun h ↦ hi ?_⟩
    change rename (blockIncl k₀) (X ⟨k, i⟩) ∈ P.ideal at h
    rwa [rename_X] at h
  horizontal a ha := by
    change rename (blockIncl k₀) (C a) ∈ P.ideal at ha
    rw [rename_C] at ha
    exact P.horizontal a ha
variable {Ω : Type} [Field Ω]
end BlockImage
end
end GroundTheory.Heights₂.Heights


