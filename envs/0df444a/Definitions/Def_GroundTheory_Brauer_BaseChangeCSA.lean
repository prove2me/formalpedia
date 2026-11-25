-- Prove2me | Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
-- name    : GroundTheory_Brauer_BaseChangeCSA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:09.396391+00:00
-- url     : https://prove2.me/theorems/cff2c7c2-cd7e-4ea0-94f5-8c64186cdad0
-- title:
--   Base Change CSA
-- statement:
--   Definitions and structural lemmas for Base Change CSA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChangeCSA.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Theorems.Thm_GroundTheory_Brauer_center_tensorProduct_eq_map_includeLeft
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open TensorProduct Algebra.TensorProduct
section CentralSimple
variable (K L A : Type*) [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]
theorem center_baseChange_eq_bot [Algebra.IsCentral K A] :
    Subalgebra.center L (L ⊗[K] A) = ⊥ := by
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  have hx' : x ∈ Subalgebra.center K (L ⊗[K] A) := by
    rw [Subalgebra.mem_center_iff] at hx ⊢
    exact hx
  rw [center_tensorProduct_eq_map_includeLeft] at hx'
  obtain ⟨l, -, rfl⟩ := hx'
  exact Algebra.mem_bot.mpr ⟨l, by simp [Algebra.TensorProduct.algebraMap_apply]⟩
instance isCentral_baseChange [Algebra.IsCentral K A] : Algebra.IsCentral L (L ⊗[K] A) :=
  ⟨(center_baseChange_eq_bot K L A).le⟩
instance isSimpleRing_baseChange [Algebra.IsCentral K A] [IsSimpleRing A] :
    IsSimpleRing (L ⊗[K] A) :=
  isSimpleRing_tensorProduct_of_right (K := K) (A := A) (B := L)
example [FiniteDimensional K A] : FiniteDimensional L (L ⊗[K] A) := inferInstance
end CentralSimple
section CSA
universe u v w
noncomputable def baseChangeCSA {K : Type u} [Field K] (L : Type w) [Field L] [Algebra K L]
    (A : CSA.{u, v} K) : CSA.{w, max w v} L where
  toAlgCat := AlgCat.of L (L ⊗[K] A)
@[simp]
theorem baseChangeCSA_carrier {K : Type u} [Field K] (L : Type w) [Field L] [Algebra K L]
    (A : CSA.{u, v} K) : (baseChangeCSA L A : Type (max w v)) = (L ⊗[K] A) := rfl
end CSA
section Tower
variable (K L M A : Type*) [CommSemiring K] [CommSemiring L] [CommSemiring M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Semiring A] [Algebra K A]
noncomputable def baseChangeTower : M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M A).symm
    (by simp [Algebra.TensorProduct.one_def]) <|
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp)
@[simp]
theorem baseChangeTower_tmul (m : M) (l : L) (a : A) :
    baseChangeTower K L M A (m ⊗ₜ (l ⊗ₜ a)) = (l • m) ⊗ₜ a := rfl
@[simp]
theorem baseChangeTower_symm_tmul (m : M) (a : A) :
    (baseChangeTower K L M A).symm (m ⊗ₜ a) = m ⊗ₜ (1 ⊗ₜ a) := rfl
end Tower
section Matrix
variable (K L A : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Semiring A] [Algebra K A]
variable (n : Type*) [Fintype n] [DecidableEq n]
noncomputable def matrixEquivTensorBaseChange :
    Matrix n n (L ⊗[K] A) ≃ₐ[L] (L ⊗[K] A) ⊗[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n K (L ⊗[K] A)).toRingEquiv) fun l ↦ by
    apply (matrixEquivTensor n K (L ⊗[K] A)).symm.injective
    change (matrixEquivTensor n K (L ⊗[K] A)).symm (matrixEquivTensor n K (L ⊗[K] A) _) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.algebraMap_apply,
      matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.algebraMap_eq_diagonal, Matrix.smul_one_eq_diagonal]
    rfl
noncomputable def baseChangeMatrix : L ⊗[K] Matrix n n A ≃ₐ[L] Matrix n n (L ⊗[K] A) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor n K A)).trans <|
    (Algebra.TensorProduct.assoc (R := K) (S := K) (T := L) (A := L) (C := A)
      (D := Matrix n n K)).symm.trans (matrixEquivTensorBaseChange K L A n).symm
@[simp]
theorem baseChangeMatrix_tmul (l : L) (x : Matrix n n A) :
    baseChangeMatrix K L A n (l ⊗ₜ x) = Matrix.of fun i j ↦ l ⊗ₜ x i j := by
  ext i j
  simp [baseChangeMatrix, matrixEquivTensorBaseChange, tmul_sum, map_sum, Matrix.sum_apply,
    Matrix.single_apply]
  rw [Fintype.sum_eq_single (i, j) fun p hp ↦ if_neg fun h ↦ hp (Prod.ext h.1 h.2)]
  simp
end Matrix
section Tensor
variable (K L A B : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Semiring A]
  [Algebra K A] [Semiring B] [Algebra K B]
noncomputable def baseChangeTensor : L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.distribBaseChange K L A B)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)
end Tensor
section CSAIso
universe u v w w'
variable {K : Type u} [Field K]
noncomputable def baseChangeCSATower (L : Type w) (M : Type w') [Field L] [Field M] [Algebra K L]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] (A : CSA.{u, v} K) :
    baseChangeCSA M (baseChangeCSA L A) ≃ₐ[M] baseChangeCSA M A :=
  baseChangeTower K L M A
noncomputable def baseChangeCSATensor (L : Type w) [Field L] [Algebra K L] (A B : CSA.{u, v} K) :
    baseChangeCSA L (tensorCSA A B) ≃ₐ[L] tensorCSA (baseChangeCSA L A) (baseChangeCSA L B) :=
  baseChangeTensor K L A B
end CSAIso
end GroundTheory.Brauer


