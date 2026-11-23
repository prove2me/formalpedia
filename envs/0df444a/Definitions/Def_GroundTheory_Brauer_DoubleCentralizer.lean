-- Prove2me | Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
-- name    : GroundTheory_Brauer_DoubleCentralizer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:11.786196+00:00
-- url     : https://prove2.me/theorems/b7970d6a-c5c7-4baa-a374-279d6c3c903e
-- title:
--   Double Centralizer
-- statement:
--   Definitions and structural lemmas for Double Centralizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/DoubleCentralizer.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_map_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_map_val_apply
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_bimoduleHom_tmul
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open TensorProduct Module
section EndOfModule
variable {K R M : Type*} [Field K] [Ring R] [Algebra K R] [IsSimpleRing R] [FiniteDimensional K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M] [FiniteDimensional K M]
omit [IsSimpleRing R] [FiniteDimensional K R] in

instance finiteDimensional_end : FiniteDimensional K (Module.End R M) :=
  Module.Finite.of_injective (LinearMap.restrictScalarsₗ K R M M K)
    (fun _ _ h ↦ LinearMap.restrictScalars_injective K h)
variable (K R M) in
include K in

theorem exists_linearEquiv_pi_simple :
    ∃ (S : Submodule R (R × M)) (r m : ℕ), IsSimpleModule R S ∧ 0 < r ∧
      Nonempty (R ≃ₗ[R] (Fin r → S)) ∧ Nonempty (M ≃ₗ[R] (Fin m → S)) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  have : Module.Finite R (R × M) := Module.Finite.of_restrictScalars_finite K R _
  obtain ⟨k, _, S, hS, -⟩ := (IsSimpleRing.isIsotypic R (R × M)).linearEquiv_fun
  have hT : IsIsotypicOfType R (R × M) S := IsSimpleRing.isIsotypic R (R × M) S
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R _
  obtain ⟨r, ⟨eR⟩⟩ :=
    (hT.of_injective (LinearMap.inl R R M) LinearMap.inl_injective).linearEquiv_fun
  obtain ⟨m, ⟨eM⟩⟩ :=
    (hT.of_injective (LinearMap.inr R R M) LinearMap.inr_injective).linearEquiv_fun
  refine ⟨S, r, m, hS, Nat.pos_of_ne_zero ?_, ⟨eR⟩, ⟨eM⟩⟩
  rintro rfl
  exact not_subsingleton R eR.subsingleton
end EndOfModule
section EndOfModule2
variable {K R : Type*} [Field K] [Ring R] [Algebra K R]
theorem finrank_end_pi {S : Type*} [AddCommGroup S] [Module K S] [Module R S]
    [IsScalarTower K R S] [FiniteDimensional K S] (n : ℕ) :
    finrank K (Module.End R (Fin n → S)) = n * n * finrank K (Module.End R S) := by
  rw [(endVecAlgEquivMatrixEnd (Fin n) K R S).toLinearEquiv.finrank_eq, Module.finrank_matrix]
  simp
variable [IsSimpleRing R] [FiniteDimensional K R]
  {M : Type*} [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [FiniteDimensional K M]
variable (K R M) in

theorem finrank_mul_finrank_end :
    finrank K R * finrank K (Module.End R M) = finrank K M ^ 2 := by
  obtain ⟨S, r, m, hS, hr, ⟨eR⟩, ⟨eM⟩⟩ := exists_linearEquiv_pi_simple K R M
  have : FiniteDimensional K S :=
    FiniteDimensional.of_injective ((Submodule.subtype S).restrictScalars K) Subtype.val_injective
  have hR1 : finrank K R = r * finrank K S := by
    rw [(eR.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]; simp
  have hM1 : finrank K M = m * finrank K S := by
    rw [(eM.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]; simp
  have hR2 : finrank K R = r * r * finrank K (Module.End R S) := by
    rw [← (LinearMap.ringLmapEquivSelf R K R).finrank_eq, ← finrank_end_pi,
      (eR.conjAlgEquiv K).toLinearEquiv.finrank_eq]
  have hM2 : finrank K (Module.End R M) = m * m * finrank K (Module.End R S) := by
    rw [← finrank_end_pi, (eM.conjAlgEquiv K).toLinearEquiv.finrank_eq]
  have hs : finrank K S = r * finrank K (Module.End R S) := by
    apply Nat.eq_of_mul_eq_mul_left hr
    rw [← hR1, hR2, mul_assoc]
  rw [hR2, hM2, hM1, hs]
  ring
variable (K R M) in
include K in

theorem isSimpleRing_end [Nontrivial M] : IsSimpleRing (Module.End R M) := by
  classical
  obtain ⟨S, r, m, hS, hr, -, ⟨eM⟩⟩ := exists_linearEquiv_pi_simple K R M
  have : NeZero m := ⟨by rintro rfl; exact not_subsingleton M eM.subsingleton⟩
  have : IsSimpleRing (Module.End R S) := DivisionRing.isSimpleRing (Module.End R S)
  let e : Matrix (Fin m) (Fin m) (Module.End R S) ≃+* Module.End R M :=
    ((eM.conjAlgEquiv K).trans (endVecAlgEquivMatrixEnd (Fin m) K R S)).symm.toRingEquiv
  exact IsSimpleRing.of_ringEquiv (R := Matrix (Fin m) (Fin m) (Module.End R S)) e inferInstance
end EndOfModule2
section Centralizer
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
namespace CentralizerModule
noncomputable def mulRight (c : Subalgebra.centralizer K (B : Set A)) :
    Module.End (A ⊗[K] Bᵐᵒᵖ) (Twist B.val) where
  toFun x := Twist.of _ (x.val * c)
  map_add' x y := add_mul x.val y.val (c : A)
  map_smul' r x := by
    change bimoduleHom B.val r x.val * (c : A) = bimoduleHom B.val r (x.val * c)
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [bimoduleHom_tmul, bimoduleHom_tmul, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
      congr 2
      exact (Subalgebra.mem_centralizer_iff K).mp c.2 _ b.unop.2
    | add r s hr hs => simp only [map_add, LinearMap.add_apply, add_mul, hr, hs]
noncomputable def endAlgEquiv :
    Module.End (A ⊗[K] Bᵐᵒᵖ) (Twist B.val) ≃ₐ[K] (Subalgebra.centralizer K (B : Set A))ᵐᵒᵖ where
  toFun φ := MulOpposite.op ⟨(φ (Twist.of _ 1)).val, by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    have h1 := Twist.map_val φ g
    have h2 := Twist.map_val_apply φ (⟨g, hg⟩ : B)
    exact h1.symm.trans h2⟩
  invFun c := mulRight B c.unop
  left_inv φ := by
    refine LinearMap.ext fun x ↦ ?_
    exact (Twist.map_val φ x.val).symm
  right_inv c := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact one_mul _
  map_mul' φ ψ := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact Twist.map_val φ (ψ (Twist.of _ 1)).val
  map_add' φ ψ := rfl
  commutes' k := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    change (algebraMap K (Module.End (A ⊗[K] Bᵐᵒᵖ) (Twist B.val)) k (Twist.of _ 1)).val = _
    rw [Module.algebraMap_end_apply]
    change k • (1 : A) = _
    simp [Algebra.algebraMap_eq_smul_one]
end CentralizerModule
open CentralizerModule
variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] [IsSimpleRing B]
theorem isSimpleRing_centralizer : IsSimpleRing (Subalgebra.centralizer K (B : Set A)) := by
  have : Nontrivial (Twist B.val) := inferInstanceAs (Nontrivial A)
  have h := isSimpleRing_end K (A ⊗[K] Bᵐᵒᵖ) (Twist B.val)
  have hop : IsSimpleRing (Subalgebra.centralizer K (B : Set A))ᵐᵒᵖ :=
    IsSimpleRing.of_ringEquiv (endAlgEquiv B).toRingEquiv h
  exact IsSimpleRing.of_ringEquiv (RingEquiv.opOp _).symm inferInstance
theorem finrank_mul_finrank_centralizer :
    finrank K B * finrank K (Subalgebra.centralizer K (B : Set A)) = finrank K A := by
  have h := finrank_mul_finrank_end K (A ⊗[K] Bᵐᵒᵖ) (Twist B.val)
  rw [(endAlgEquiv B).toLinearEquiv.finrank_eq, MulOpposite.finrank, Module.finrank_tensorProduct,
    MulOpposite.finrank] at h
  change finrank K A * finrank K B * _ = finrank K A ^ 2 at h
  have hA : 0 < finrank K A := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hA
  rw [← mul_assoc, h, sq]
variable [Algebra.IsCentral K B]
noncomputable def tensorCentralizerHom :
    B ⊗[K] Subalgebra.centralizer K (B : Set A) →ₐ[K] A :=
  Algebra.TensorProduct.lift B.val (Subalgebra.centralizer K (B : Set A)).val fun b c ↦
    ((Subalgebra.mem_centralizer_iff K).mp c.2 b b.2)
noncomputable def tensorCentralizerAlgEquiv :
    B ⊗[K] Subalgebra.centralizer K (B : Set A) ≃ₐ[K] A := by
  have : IsSimpleRing (Subalgebra.centralizer K (B : Set A)) := isSimpleRing_centralizer B
  have hinj := RingHom.injective (tensorCentralizerHom B).toRingHom
  refine AlgEquiv.ofBijective (tensorCentralizerHom B) ⟨hinj, ?_⟩
  have h := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tensorCentralizerHom B).toLinearMap)
    (by rw [Module.finrank_tensorProduct, finrank_mul_finrank_centralizer])
  exact h.mp hinj
end Centralizer
end GroundTheory.Brauer


