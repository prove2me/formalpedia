-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaModular
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:31.574863+00:00
-- url     : https://prove2.me/theorems/d9970628-cd1e-4499-ad46-9a2e53574916
-- title:
--   Geometric Lemma Modular
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Modular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_levi
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
section LeviPar
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α α' : Type*} [LinearOrder α] [LinearOrder α'] (γ : Fin n → α) (δ : Fin n → α')
abbrev LeviParIndex : Type := {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ ¬ δ ij.2 < δ ij.1}
def lieLeviPar : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | ∀ i j, ¬ (γ i = γ j ∧ ¬ δ j < δ i) → A i j = 0}
  add_mem' {A B} hA hB i j h := by
    simp [hA i j h, hB i j h]
  zero_mem' _ _ _ := rfl
  smul_mem' c A hA i j h := by
    simp [hA i j h]
abbrev leviPar : Subgroup (GL (Fin n) F) := levi F n γ ⊓ blockUpper F n δ
variable {F n γ δ}
theorem mem_leviPar_iff {g : GL (Fin n) F} :
    g ∈ leviPar F n γ δ ↔ (g : Matrix (Fin n) (Fin n) F) ∈ lieLeviPar F n γ δ := by
  rw [Subgroup.mem_inf, mem_levi, mem_blockUpper]
  constructor
  · rintro ⟨h1, h2⟩ i j h
    by_cases hγ : γ i = γ j
    · exact h2 (by by_contra h'; exact h ⟨hγ, h'⟩)
    · exact h1 i j hγ
  · intro h
    exact ⟨fun i j hij => h i j fun h' => hij h'.1, fun i j hij => h i j fun h' => h'.2 hij⟩
theorem mul_mem_lieLeviPar {A B : Matrix (Fin n) (Fin n) F} (hA : A ∈ lieLeviPar F n γ δ)
    (hB : B ∈ lieLeviPar F n γ δ) : A * B ∈ lieLeviPar F n γ δ := by
  intro i j h
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : γ i = γ k ∧ ¬ δ k < δ i
  · by_cases hkj : γ k = γ j ∧ ¬ δ j < δ k
    · exact absurd ⟨hik.1.trans hkj.1, fun h' => hkj.2 (lt_of_lt_of_le h' (not_lt.1 hik.2))⟩ h
    · rw [hB k j hkj, mul_zero]
  · rw [hA i k hik, zero_mul]
variable (F n γ δ)
noncomputable def leviParCoord : lieLeviPar F n γ δ ≃ₗ[F] (LeviParIndex n γ δ → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : γ i = γ j ∧ ¬ δ j < δ i then x ⟨(i, j), h⟩ else 0,
    fun i j hij => by
      simp only [Matrix.of_apply]
      rw [dif_neg hij]⟩
  map_add' A B := rfl
  map_smul' c A := rfl
  left_inv A := by
    ext i j
    by_cases h : γ i = γ j ∧ ¬ δ j < δ i
    · simp [h]
    · simp [A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]
noncomputable def leviParCoordHomeomorph : lieLeviPar F n γ δ ≃ₜ (LeviParIndex n γ δ → F) where
  toEquiv := (leviParCoord F n γ δ).toEquiv
  continuous_toFun := continuous_pi fun s =>
    (continuous_subtype_val.matrix_elem s.1.1 s.1.2 :
      Continuous fun A : lieLeviPar F n γ δ => (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2)
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : γ i = γ j ∧ ¬ δ j < δ i
    · simp only [Matrix.of_apply, h, not_false_eq_true, and_self, dite_true]
      exact continuous_apply _
    · simp only [Matrix.of_apply, h, dite_false]
      exact continuous_const
def toLieLeviPar (l : leviPar F n γ δ) : lieLeviPar F n γ δ :=
  ⟨((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), mem_leviPar_iff.1 l.2⟩
theorem isClosed_leviPar : IsClosed (leviPar F n γ δ : Set (GL (Fin n) F)) := isClosed_levi.inter (Measures.isClosed_blockUpper F n δ)
instance locallyCompactSpace_leviPar : LocallyCompactSpace (leviPar F n γ δ) :=
  (isClosed_leviPar F n γ δ).locallyCompactSpace
theorem isOpenEmbedding_toLieLeviPar : IsOpenEmbedding (toLieLeviPar F n γ δ) := by
  have hemb : IsEmbedding (toLieLeviPar F n γ δ) :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (lieLeviPar F n γ δ : Set (Matrix (Fin n) (Fin n) F))
      fun l : leviPar F n γ δ => mem_leviPar_iff.1 l.2
  refine ⟨hemb, ?_⟩
  have : Set.range (toLieLeviPar F n γ δ) = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, rfl⟩
    · rintro ⟨u, hu⟩
      refine ⟨⟨u, mem_leviPar_iff.2 ?_⟩, Subtype.ext hu⟩
      rw [hu]
      exact A.2
  rw [this]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtype_val
noncomputable def mulLeftLeviPar (l : leviPar F n γ δ) :
    lieLeviPar F n γ δ ≃ₗ[F] lieLeviPar F n γ δ :=
  (Units.mulLeftLinearEquiv F _ (l : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLeviPar (mem_leviPar_iff.1 l.2) hA
    · refine ⟨((l⁻¹ : leviPar F n γ δ) : GL (Fin n) F) * A,
        mul_mem_lieLeviPar (mem_leviPar_iff.1 (l⁻¹).2) hA, ?_⟩
      simp [← mul_assoc])
noncomputable def mulRightLeviPar (l : leviPar F n γ δ) :
    lieLeviPar F n γ δ ≃ₗ[F] lieLeviPar F n γ δ :=
  (Units.mulRightLinearEquiv F (l : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact mul_mem_lieLeviPar hA (mem_leviPar_iff.1 l.2)
    · refine ⟨A * ((l⁻¹ : leviPar F n γ δ) : GL (Fin n) F),
        mul_mem_lieLeviPar hA (mem_leviPar_iff.1 (l⁻¹).2), ?_⟩
      simp [mul_assoc])
@[simp] theorem coe_mulLeftLeviPar (l : leviPar F n γ δ) (A : lieLeviPar F n γ δ) :
    ((mulLeftLeviPar F n γ δ l A : lieLeviPar F n γ δ) : Matrix (Fin n) (Fin n) F) =
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A :=
  rfl
@[simp] theorem coe_mulRightLeviPar (l : leviPar F n γ δ) (A : lieLeviPar F n γ δ) :
    ((mulRightLeviPar F n γ δ l A : lieLeviPar F n γ δ) : Matrix (Fin n) (Fin n) F) =
      A * ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl
noncomputable def adLeviPar (l : leviPar F n γ δ) :
    lieLeviPar F n γ δ ≃ₗ[F] lieLeviPar F n γ δ :=
  (mulLeftLeviPar F n γ δ l).trans (mulRightLeviPar F n γ δ l⁻¹)
@[simp] theorem coe_adLeviPar (l : leviPar F n γ δ) (A : lieLeviPar F n γ δ) :
    ((adLeviPar F n γ δ l A : lieLeviPar F n γ δ) : Matrix (Fin n) (Fin n) F) =
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (((l : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl
noncomputable def leviParChart :
    LinearChart F (LeviParIndex n γ δ) (leviPar F n γ δ) where
  toFun l := leviParCoord F n γ δ (toLieLeviPar F n γ δ l)
  isOpenEmbedding :=
    (leviParCoordHomeomorph F n γ δ).isOpenEmbedding.comp (isOpenEmbedding_toLieLeviPar F n γ δ)
  left l := (leviParCoord F n γ δ).symm.trans ((mulLeftLeviPar F n γ δ l).trans (leviParCoord F n γ δ))
  right l := (leviParCoord F n γ δ).symm.trans
    ((mulRightLeviPar F n γ δ l).trans (leviParCoord F n γ δ))
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right h x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
variable {F n γ δ}
end LeviPar
section Diagonal
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}
theorem diagPow_mem_leviPar (μ : Fin n → ℤ) : Cartan.diagPow F n μ ∈ leviPar F n γ δ := by
  refine ⟨diagPow_mem_levi μ, fun i j hij => ?_⟩
  have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
  show (Cartan.diagPow F n μ : Matrix (Fin n) (Fin n) F) i j = 0
  rw [Cartan.coe_diagPow, diagonal_apply_ne _ hne]
end Diagonal
end Parabolic
end GroundTheory.Automorphic


