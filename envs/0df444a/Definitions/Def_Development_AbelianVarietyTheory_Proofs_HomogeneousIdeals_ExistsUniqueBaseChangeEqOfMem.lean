-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:21.898045+00:00
-- url     : https://prove2.me/theorems/4fe5d00d-be06-4bc5-9aaf-df90101ff393
-- title:
--   Exists Unique Base Change Eq Of Mem
-- statement:
--   Definitions and structural lemmas for Exists Unique Base Change Eq Of Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul


set_option autoImplicit false
open TensorProduct
namespace GlobalTheory
namespace FlatDescent
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
variable (A B N) in

def act : B ⊗[A] N →ₗ[B] N := LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)
@[simp] theorem act_tmul (b : B) (n : N) : act A B N (b ⊗ₜ n) = b • n := by
  simp [act]
structure IsDescentDatum (θ : N →ₗ[B] B ⊗[A] N) : Prop where
  counit : ∀ n, act A B N (θ n) = n
  coassoc : ∀ n, (θ.restrictScalars A).lTensor B (θ n) = (TensorProduct.mk A B N 1).lTensor B (θ n)
def invariants (θ : N →ₗ[B] B ⊗[A] N) : Submodule A N :=
  LinearMap.ker (θ.restrictScalars A - TensorProduct.mk A B N 1)
@[simp] theorem mem_invariants {θ : N →ₗ[B] B ⊗[A] N} {n : N} :
    n ∈ invariants θ ↔ θ n = 1 ⊗ₜ n := by
  simp [invariants, sub_eq_zero]
variable (B) in

def canonical (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[B] B ⊗[A] (B ⊗[A] M) :=
  (TensorProduct.mk A B M 1).baseChange B
@[simp] theorem canonical_tmul {M : Type*} [AddCommGroup M] [Module A M] (b : B) (m : M) :
    canonical B M (b ⊗ₜ[A] m) = b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) := rfl
variable (B) in

def extend (P : Submodule A N) : B ⊗[A] P →ₗ[B] N := LinearMap.liftBaseChange B P.subtype
@[simp] theorem extend_tmul (P : Submodule A N) (b : B) (n : P) :
    extend B P (b ⊗ₜ n) = b • (n : N) := by
  simp [extend]
section Amitsur
variable (B) (M : Type*) [AddCommGroup M] [Module A M]
def toInvariants : M →ₗ[A] invariants (canonical (A := A) B M) :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m => by simp
@[simp] theorem coe_toInvariants (m : M) :
    (toInvariants (A := A) B M m : B ⊗[A] M) = 1 ⊗ₜ m := rfl
def amitsurDiff : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (canonical B M).restrictScalars A - TensorProduct.mk A B (B ⊗[A] M) 1
@[simp] theorem amitsurDiff_tmul (b : B) (m : M) :
    amitsurDiff B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := rfl
end Amitsur
section Morphisms
def IsCompatible (θ : N →ₗ[B] B ⊗[A] N) (θ' : N' →ₗ[B] B ⊗[A] N') (f : N →ₗ[B] N') : Prop :=
  ∀ n, θ' (f n) = (f.restrictScalars A).lTensor B (θ n)
variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
end Morphisms
section Invertible
end Invertible
section Gluing
variable (A) in

def smulRight (b : B) : B ⊗[A] N →ₗ[B] B ⊗[A] N :=
  (Algebra.lsmul A A N b).baseChange B
@[simp] theorem smulRight_tmul (b c : B) (n : N) :
    smulRight A b (c ⊗ₜ[A] n) = c ⊗ₜ[A] (b • n) := rfl
structure IsGluing (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) : Prop where
  bijective : Function.Bijective φ
  map_tmul_mul : ∀ (n : N) (b c : B), φ (n ⊗ₜ (b * c)) = smulRight A b (φ (n ⊗ₜ c))
  cocycle : ∀ (n : N) (b c : B),
    (φ.restrictScalars A).lTensor B (TensorProduct.assoc A B N B (φ (n ⊗ₜ b) ⊗ₜ c)) =
      (TensorProduct.mk A B N b).lTensor B (φ (n ⊗ₜ c))
def datumOfGluing (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) : N →ₗ[B] B ⊗[A] N :=
  φ ∘ₗ (AlgebraTensorModule.mk A B N B).flip 1
@[simp] theorem datumOfGluing_apply (φ : N ⊗[A] B →ₗ[B] B ⊗[A] N) (n : N) :
    datumOfGluing φ n = φ (n ⊗ₜ 1) := rfl
def gluingOfDatum (θ : N →ₗ[B] B ⊗[A] N) : N ⊗[A] B →ₗ[B] B ⊗[A] N :=
  AlgebraTensorModule.lift
    { toFun := fun n =>
        { toFun := fun b => smulRight A b (θ n)
          map_add' := fun b c => by
            induction θ n using TensorProduct.induction_on with
            | zero => simp
            | add x y hx hy => simp only [map_add, hx, hy]; abel
            | tmul b m => simp [add_smul, tmul_add]
          map_smul' := fun a b => by
            induction θ n using TensorProduct.induction_on with
            | zero => simp
            | add x y hx hy => simp only [map_add, hx, hy, smul_add]
            | tmul b m => simp }
      map_add' := fun n n' => by ext; simp
      map_smul' := fun b n => by ext; simp }
@[simp] theorem gluingOfDatum_tmul (θ : N →ₗ[B] B ⊗[A] N) (n : N) (b : B) :
    gluingOfDatum θ (n ⊗ₜ b) = smulRight A b (θ n) := rfl
theorem smulRight_one (x : B ⊗[A] N) : smulRight A (1 : B) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp
theorem smulRight_mul (b c : B) (x : B ⊗[A] N) :
    smulRight A (b * c) x = smulRight A b (smulRight A c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp [mul_smul]
theorem IsGluing.isDescentDatum {φ : N ⊗[A] B →ₗ[B] B ⊗[A] N} (h : IsGluing φ) :
    IsDescentDatum (datumOfGluing φ) := by
  have hco : ∀ n, ((datumOfGluing φ).restrictScalars A).lTensor B (datumOfGluing φ n) =
      (TensorProduct.mk A B N 1).lTensor B (datumOfGluing φ n) := by
    intro n
    rw [datumOfGluing_apply, ← h.cocycle]
    induction φ (n ⊗ₜ 1) using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
    | tmul b m => simp
  refine ⟨fun n => ?_, hco⟩
  have h1 : ∀ x : B ⊗[A] N, act A B _ (((datumOfGluing φ).restrictScalars A).lTensor B x) =
      datumOfGluing φ (act A B N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [← smul_tmul']
  have h2 : ∀ x : B ⊗[A] N, act A B _ ((TensorProduct.mk A B N 1).lTensor B x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [smul_tmul']
  have h3 := congrArg (act A B _) (hco n)
  rw [h1, h2] at h3
  have h4 := congrArg (fun x => act A B N (TensorProduct.comm A N B x)) (h.bijective.1 h3)
  simpa using h4
theorem IsDescentDatum.isGluing {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) :
    IsGluing (gluingOfDatum θ) := by
  let φ : N ⊗[A] B →ₗ[A] B ⊗[A] N := (gluingOfDatum θ).restrictScalars A
  let τ := TensorProduct.comm A B N
  let κ : B ⊗[A] (B ⊗[A] N) →ₗ[A] B ⊗[A] N :=
    ((act A B N).restrictScalars A).lTensor B ∘ₗ (TensorProduct.leftComm A B B N).toLinearMap
  have hκ : ∀ (b : B) (x : B ⊗[A] N), κ (b ⊗ₜ x) = smulRight A b x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
    | tmul b m => simp [κ]
  have h1 : ∀ (b : B) (x : B ⊗[A] N),
      φ (τ (smulRight A b x)) = b • κ ((θ.restrictScalars A).lTensor B x) := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul c m => simp [hκ, φ, τ]
  have h2 : ∀ x : B ⊗[A] N, κ ((TensorProduct.mk A B N 1).lTensor B x) = 1 ⊗ₜ act A B N x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, tmul_add]
    | tmul c m => simp [hκ]
  have h3 : ∀ x, τ (φ (τ (φ x))) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul n b =>
      have : φ (n ⊗ₜ b) = smulRight A b (θ n) := rfl
      rw [this, h1, h.coassoc, h2, h.counit]
      simp [τ, smul_tmul']
  refine ⟨⟨fun x y hxy => ?_, fun y => ⟨τ (φ (τ y)), ?_⟩⟩, fun n b c => ?_, fun n b c => ?_⟩
  · rw [← h3 x, ← h3 y]
    exact congrArg (fun z => τ (φ (τ z))) hxy
  · obtain ⟨y, rfl⟩ := τ.symm.surjective y
    have hτφ : Function.Bijective (fun x => τ (φ x)) := Function.Involutive.bijective h3
    obtain ⟨z, rfl⟩ := hτφ.2 y
    simp only [LinearEquiv.symm_apply_apply]
    rw [h3]
    rfl
  · simp [smulRight_mul]
  · let ψ : B ⊗[A] N →ₗ[A] B ⊗[A] N := (b • smulRight A c : B ⊗[A] N →ₗ[B] B ⊗[A] N).restrictScalars A
    have h4 : ∀ x : B ⊗[A] N, φ.lTensor B (TensorProduct.assoc A B N B (smulRight A b x ⊗ₜ c)) =
        ψ.lTensor B ((θ.restrictScalars A).lTensor B x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
      | tmul d m => simp [φ, ψ]
    have h5 : ∀ x : B ⊗[A] N, ψ.lTensor B ((TensorProduct.mk A B N 1).lTensor B x) =
        (TensorProduct.mk A B N b).lTensor B (smulRight A c x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul d m => simp [ψ, smul_tmul']
    rw [gluingOfDatum_tmul, gluingOfDatum_tmul, ← h5, ← h.coassoc, ← h4]
variable (A B N) in

def gluingEquivDatum : {φ : N ⊗[A] B →ₗ[B] B ⊗[A] N // IsGluing φ} ≃
    {θ : N →ₗ[B] B ⊗[A] N // IsDescentDatum θ} where
  toFun φ := ⟨datumOfGluing φ.1, φ.2.isDescentDatum⟩
  invFun θ := ⟨gluingOfDatum θ.1, θ.2.isGluing⟩
  left_inv φ := by
    ext n b
    simp [← φ.2.map_tmul_mul]
  right_inv θ := by
    ext n
    simp [smulRight_one]
end Gluing
end FlatDescent
end GlobalTheory


