-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
-- name    : GroundTheory_AutomorphicForms_MeasuresParabolic
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:55:46.674565+00:00
-- url     : https://prove2.me/theorems/744afc2a-1125-4c81-9c9a-a9f05479d28f
-- title:
--   Measures Parabolic
-- statement:
--   Definitions and structural lemmas for Measures Parabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
namespace Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
def lieParabolic : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | A.BlockTriangular β}
  add_mem' ha hb := ha.add hb
  zero_mem' := Matrix.blockTriangular_zero
  smul_mem' c A hA i j hij := by
    simp [hA hij]
abbrev ParabolicIndex : Type := {ij : Fin n × Fin n // ¬ β ij.2 < β ij.1}
noncomputable def parabolicCoord : lieParabolic F n β ≃ₗ[F] (ParabolicIndex n β → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : ¬ β j < β i then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by simp [hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : β j < β i
    · simp [A.2 h]
    · simp [h]
  right_inv x := by
    funext s
    simp [s.2]
@[simp] theorem parabolicCoord_apply (A : lieParabolic F n β) (s : ParabolicIndex n β) :
    parabolicCoord F n β A s = (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 :=
  rfl
noncomputable def parabolicCoordHomeomorph : lieParabolic F n β ≃ₜ (ParabolicIndex n β → F) where
  toEquiv := (parabolicCoord F n β).toEquiv
  continuous_toFun := continuous_pi fun s =>
    (continuous_subtype_val.matrix_elem s.1.1 s.1.2 :
      Continuous fun A : lieParabolic F n β => (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : β j < β i
    · simp only [Matrix.of_apply, h, not_true_eq_false, dite_false]
      exact continuous_const
    · simp only [Matrix.of_apply, h, not_false_eq_true, dite_true]
      exact continuous_apply _
def toLie (p : blockUpper F n β) : lieParabolic F n β :=
  ⟨((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), p.2⟩
theorem isClosed_blockUpper : IsClosed (blockUpper F n β : Set (GL (Fin n) F)) := by
  have : (blockUpper F n β : Set (GL (Fin n) F)) =
      ⋂ i, ⋂ j, ⋂ (_ : β j < β i), (fun g : GL (Fin n) F => g i j) ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, mem_blockUpper, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (GLnLocal.continuous_entry F n i j)
instance locallyCompactSpace_blockUpper : LocallyCompactSpace (blockUpper F n β) :=
  (isClosed_blockUpper F n β).locallyCompactSpace
instance locallyCompactSpace_borel : LocallyCompactSpace (borel F n) :=
  locallyCompactSpace_blockUpper F n id
theorem isOpenEmbedding_toLie : IsOpenEmbedding (toLie F n β) := by
  have hemb : IsEmbedding (toLie F n β) :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (lieParabolic F n β : Set (Matrix (Fin n) (Fin n) F)) fun p : blockUpper F n β => p.2
  refine ⟨hemb, ?_⟩
  have : Set.range (toLie F n β) = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨⟨u, ?_⟩, Subtype.ext hu⟩
      show (u : Matrix (Fin n) (Fin n) F).BlockTriangular β
      rw [hu]
      exact A.2
  rw [this]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtype_val
noncomputable def mulLeftLie (p : blockUpper F n β) : lieParabolic F n β ≃ₗ[F] lieParabolic F n β :=
  (Units.mulLeftLinearEquiv F _ (p : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact p.2.mul hA
    · refine ⟨((p⁻¹ : blockUpper F n β) : GL (Fin n) F) * A, (p⁻¹).2.mul hA, ?_⟩
      simp [← mul_assoc])
noncomputable def mulRightLie (p : blockUpper F n β) :
    lieParabolic F n β ≃ₗ[F] lieParabolic F n β :=
  (Units.mulRightLinearEquiv F (p : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact hA.mul p.2
    · refine ⟨A * ((p⁻¹ : blockUpper F n β) : GL (Fin n) F), hA.mul (p⁻¹).2, ?_⟩
      simp [mul_assoc])
@[simp] theorem coe_mulLeftLie (p : blockUpper F n β) (A : lieParabolic F n β) :
    ((mulLeftLie F n β p A : lieParabolic F n β) : Matrix (Fin n) (Fin n) F) =
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A :=
  rfl
@[simp] theorem coe_mulRightLie (p : blockUpper F n β) (A : lieParabolic F n β) :
    ((mulRightLie F n β p A : lieParabolic F n β) : Matrix (Fin n) (Fin n) F) =
      A * ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl
noncomputable def adLie (p : blockUpper F n β) : lieParabolic F n β ≃ₗ[F] lieParabolic F n β :=
  (mulLeftLie F n β p).trans (mulRightLie F n β p⁻¹)
@[simp] theorem coe_adLie (p : blockUpper F n β) (A : lieParabolic F n β) :
    ((adLie F n β p A : lieParabolic F n β) : Matrix (Fin n) (Fin n) F) =
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl
noncomputable def parabolicChart : LinearChart F (ParabolicIndex n β) (blockUpper F n β) where
  toFun p := parabolicCoord F n β (toLie F n β p)
  isOpenEmbedding := by
    exact (parabolicCoordHomeomorph F n β).isOpenEmbedding.comp (isOpenEmbedding_toLie F n β)
  left p := (parabolicCoord F n β).symm.trans ((mulLeftLie F n β p).trans (parabolicCoord F n β))
  right p := (parabolicCoord F n β).symm.trans
    ((mulRightLie F n β p).trans (parabolicCoord F n β))
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right h x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
variable {F n β}
section Triangular
end Triangular
section Unipotent
variable (F n β)
def lieUnipotent : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, ¬ β i < β j → A i j = 0}
  add_mem' {A B} ha hb i j h := by
    simp [ha i j h, hb i j h]
  zero_mem' _ _ _ := rfl
  smul_mem' c A hA i j h := by
    simp [hA i j h]
abbrev UnipotentIndex : Type := {ij : Fin n × Fin n // β ij.1 < β ij.2}
noncomputable def unipotentCoord : lieUnipotent F n β ≃ₗ[F] (UnipotentIndex n β → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : β i < β j then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by simp [hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : β i < β j
    · simp [h]
    · simp [h, A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]
variable {F n β}
theorem mul_mem_lieUnipotent {p X : Matrix (Fin n) (Fin n) F} (hp : p.BlockTriangular β)
    (hX : X ∈ lieUnipotent F n β) : p * X ∈ lieUnipotent F n β := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : β k < β i
  · rw [hp hik, zero_mul]
  · rw [hX k j fun hkj => hij (lt_of_le_of_lt (not_lt.1 hik) hkj), mul_zero]
theorem mem_lieUnipotent_mul {p X : Matrix (Fin n) (Fin n) F} (hX : X ∈ lieUnipotent F n β)
    (hp : p.BlockTriangular β) : X * p ∈ lieUnipotent F n β := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : β i < β k
  · rw [hp (lt_of_le_of_lt (not_lt.1 hij) hik), mul_zero]
  · rw [hX i k hik, zero_mul]
noncomputable def adUnipotent (p : blockUpper F n β) :
    lieUnipotent F n β ≃ₗ[F] lieUnipotent F n β :=
  ((Units.mulLeftLinearEquiv F _ (p : GL (Fin n) F)).trans
    (Units.mulRightLinearEquiv F ((p : GL (Fin n) F)⁻¹))).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mem_lieUnipotent_mul (mul_mem_lieUnipotent p.2 hA) (p⁻¹).2
    · refine ⟨((p⁻¹ : blockUpper F n β) : GL (Fin n) F) * A * (p : GL (Fin n) F),
        mem_lieUnipotent_mul (mul_mem_lieUnipotent (p⁻¹).2 hA) p.2, ?_⟩
      simp [mul_assoc])
@[simp] theorem coe_adUnipotent (p : blockUpper F n β) (A : lieUnipotent F n β) :
    ((adUnipotent p A : lieUnipotent F n β) : Matrix (Fin n) (Fin n) F) =
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl
noncomputable def adUnipotentHom :
    blockUpper F n β →* (lieUnipotent F n β ≃ₗ[F] lieUnipotent F n β) where
  toFun := adUnipotent
  map_one' := LinearEquiv.ext fun A => Subtype.ext (by simp)
  map_mul' p q := LinearEquiv.ext fun A => Subtype.ext (by
    show ((adUnipotent (p * q) A : lieUnipotent F n β) : Matrix (Fin n) (Fin n) F) =
      ((adUnipotent p (adUnipotent q A) : lieUnipotent F n β) : Matrix (Fin n) (Fin n) F)
    simp [mul_assoc])
end Unipotent
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
noncomputable def haarParabolic (μ₀ : Measure (ParabolicIndex n β → F)) :
    Measure (blockUpper F n β) :=
  (parabolicChart F n β).haar μ₀
variable (μ₀ : Measure (ParabolicIndex n β → F)) [μ₀.IsAddHaarMeasure]
instance isHaarMeasure_haarParabolic : (haarParabolic μ₀).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ₀
end Measures
end GroundTheory.Automorphic


