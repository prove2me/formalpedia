-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:13.307713+00:00
-- url     : https://prove2.me/theorems/0db68196-227c-4c0c-be96-2709ff5be7eb
-- title:
--   Exists Unit Smul Eq Of Bijective To Span Singleton
-- statement:
--   Definitions and structural lemmas for Exists Unit Smul Eq Of Bijective To Span Singleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
namespace GlobalTheory
section Ring
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]
instance isInvariant_fixedSubring : Algebra.IsInvariant (FixedPoints.subring A G) A G :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
instance isInvariant_fixedSubalgebra (R : Type*) [CommRing R] [Algebra R A] [SMulCommClass G R A] :
    Algebra.IsInvariant (FixedPoints.subalgebra R A G) A G :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
end Ring
section FlatModule
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]
variable {S} in

def invariantsMap (ρ : Representation R G M) (ρ' : Representation S G M') (f : M →ₗ[R] M')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : ρ.invariants →ₗ[R] ρ'.invariants where
  toFun x := ⟨f x, fun g ↦ by rw [← hf, x.2 g]⟩
  map_add' x y := Subtype.ext (map_add f _ _)
  map_smul' r x := Subtype.ext (map_smul f _ _)
variable {S} in
@[simp] theorem coe_invariantsMap (ρ : Representation R G M) (ρ' : Representation S G M')
    (f : M →ₗ[R] M') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (x : ρ.invariants) :
    (invariantsMap ρ ρ' f hf x : M') = f x := rfl
end FlatModule
section FlatRing
variable (G : Type*) [Group G]
section
variable {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
  [Algebra R S] [Algebra R A] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
  [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A'] [SMulCommClass G S A']
variable (S) in

def fixedSubalgebraMap (f : A →ₐ[R] A') (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    FixedPoints.subalgebra R A G →ₐ[R] FixedPoints.subalgebra S A' G where
  toFun x := ⟨f x, fun g ↦ by rw [← hf, x.2 g]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f _ _)
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f _ _)
  commutes' r := Subtype.ext (f.commutes r)
@[simp] theorem coe_fixedSubalgebraMap (f : A →ₐ[R] A') (hf : ∀ (g : G) a, f (g • a) = g • f a)
    (x : FixedPoints.subalgebra R A G) : (fixedSubalgebraMap G S f hf x : A') = f x := rfl
end
section
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]
@[instance_reducible]
noncomputable def tensorMulSemiringAction : MulSemiringAction G (S ⊗[R] A) where
  smul g x := Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom R A g) x
  one_smul x := by
    change Algebra.TensorProduct.map _ _ x = x
    induction x with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul g h x := by
    change Algebra.TensorProduct.map _ _ x =
      Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ x)
    induction x with
    | zero => simp
    | tmul s a => simp [mul_smul]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  smul_zero g := map_zero (Algebra.TensorProduct.map _ _)
  smul_add g := map_add (Algebra.TensorProduct.map _ _)
  smul_one g := map_one (Algebra.TensorProduct.map _ _)
  smul_mul g := map_mul (Algebra.TensorProduct.map _ _)
theorem tensorMulSemiringAction_includeRight (g : G) (a : A) :
    letI := tensorMulSemiringAction G R S A
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (g • a) =
      g • (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) a := rfl
theorem tensorMulSemiringAction_smulCommClass :
    letI := tensorMulSemiringAction G R S A
    SMulCommClass G S (S ⊗[R] A) :=
  letI := tensorMulSemiringAction G R S A
  ⟨fun g s x ↦ map_smul
    (Algebra.TensorProduct.map (AlgHom.id S S) (MulSemiringAction.toAlgHom R A g)) s x⟩
end
section
variable {A : Type*} [CommRing A] [MulSemiringAction G A]
@[instance_reducible]
noncomputable def localizationMulSemiringAction (U : Submonoid A)
    (hU : ∀ (g : G), ∀ u ∈ U, g • u ∈ U) (A' : Type*) [CommRing A'] [Algebra A A']
    [IsLocalization U A'] : MulSemiringAction G A' where
  smul g x := IsLocalization.map A' (MulSemiringAction.toRingHom G A g)
    (show U ≤ U.comap _ from hU g) x
  one_smul x := by
    change IsLocalization.map _ _ _ x = RingHom.id A' x
    congr 1
    exact IsLocalization.ringHom_ext U (by ext a; simp)
  mul_smul g h x := by
    change IsLocalization.map _ _ _ x =
      ((IsLocalization.map A' (MulSemiringAction.toRingHom G A g)
        (show U ≤ U.comap _ from hU g)).comp (IsLocalization.map A'
          (MulSemiringAction.toRingHom G A h) (show U ≤ U.comap _ from hU h))) x
    congr 1
    exact IsLocalization.ringHom_ext U (by ext a; simp [mul_smul])
  smul_zero g := map_zero (IsLocalization.map A' _ _)
  smul_add g := map_add (IsLocalization.map A' _ _)
  smul_one g := map_one (IsLocalization.map A' _ _)
  smul_mul g := map_mul (IsLocalization.map A' _ _)
variable {B : Type*} [CommRing B] [Algebra B A] [SMulCommClass G B A]
theorem smul_mem_algebraMapSubmonoid (T : Submonoid B) (g : G) :
    ∀ u ∈ Algebra.algebraMapSubmonoid A T, g • u ∈ Algebra.algebraMapSubmonoid A T := by
  rintro _ ⟨t, ht, rfl⟩
  rw [smul_algebraMap]
  exact ⟨t, ht, rfl⟩
end
end FlatRing
section Generator
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
end Generator
section Semilinear
noncomputable def piTensorMapₛₗ {A A' : Type*} [CommRing A] [CommRing A'] (σ : A →+* A')
    {ι : Type*} {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module A' (N i)] (f : ∀ i, M i →ₛₗ[σ] N i) :
    (⨂[A] i, M i) →ₛₗ[σ] ⨂[A'] i, N i where
  __ := PiTensorProduct.liftAddHom
    (fun p : A × ∀ i, M i ↦ σ p.1 • PiTensorProduct.tprod A' fun i ↦ f i (p.2 i))
    (fun r x i hx ↦ by
      rw [MultilinearMap.map_coord_zero _ i (by simp [hx]), smul_zero])
    (fun x ↦ by simp)
    (fun r x i m₁ m₂ ↦ by
      simp only [Function.apply_update (fun i ↦ (f i : M i → N i)), map_add,
        MultilinearMap.map_update_add, smul_add])
    (fun r r' x ↦ by simp [add_smul])
    (fun r x i r' ↦ by
      simp only [Function.apply_update (fun i ↦ (f i : M i → N i)), map_smulₛₗ,
        MultilinearMap.map_update_smul, Function.update_eq_self, map_mul, smul_smul, mul_comm])
  map_smul' r y := by
    induction y using PiTensorProduct.induction_on' with
    | tprodCoeff z x =>
      rw [PiTensorProduct.smul_tprodCoeff']
      change σ (r * z) • (PiTensorProduct.tprod A' fun i ↦ f i (x i)) =
        σ r • σ z • PiTensorProduct.tprod A' fun i ↦ f i (x i)
      rw [map_mul, mul_smul]
    | add x y hx hy =>
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe] at hx hy ⊢
      rw [smul_add, map_add, map_add, hx, hy, smul_add]
@[simp] theorem piTensorMapₛₗ_tprod {A A' : Type*} [CommRing A] [CommRing A'] (σ : A →+* A')
    {ι : Type*} {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module A' (N i)] (f : ∀ i, M i →ₛₗ[σ] N i) (x : ∀ i, M i) :
    piTensorMapₛₗ σ f (PiTensorProduct.tprod A x) =
      PiTensorProduct.tprod A' fun i ↦ f i (x i) := by
  rw [PiTensorProduct.tprod_eq_tprodCoeff_one]
  change σ 1 • (PiTensorProduct.tprod A' fun i ↦ f i (x i)) = _
  rw [map_one, one_smul]
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
section
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
def smulSemilinearMap (g : G) : M →ₛₗ[MulSemiringAction.toRingHom G A g] M where
  toFun x := g • x
  map_add' := smul_add g
  map_smul' a x := smul_distrib_smul g a x
@[simp] theorem smulSemilinearMap_apply (g : G) (x : M) : smulSemilinearMap A M g x = g • x := rfl
theorem smulCommClass_of_smulDistribClass (B : Type*) [CommRing B] [Algebra B A]
    [SMulCommClass G B A] [Module B M] [IsScalarTower B A M] : SMulCommClass G B M :=
  ⟨fun g b x ↦ by
    rw [← algebraMap_smul A b, smul_distrib_smul, smul_algebraMap, algebraMap_smul]⟩
instance smulCommClass_fixedSubring : SMulCommClass G (FixedPoints.subring A G) M :=
  smulCommClass_of_smulDistribClass A M _
variable {A M}
variable (B : Type*) [CommRing B] [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A]
  [Algebra.IsInvariant B A G] [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
end
section
variable (G) {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  [∀ i, DistribMulAction G (M i)] [∀ i, SMulDistribClass G A (M i)]
@[instance_reducible]
noncomputable def piTensorDistribMulAction : DistribMulAction G (⨂[A] i, M i) where
  smul g y := piTensorMapₛₗ _ (fun i ↦ smulSemilinearMap A (M i) g) y
  one_smul y := by
    change piTensorMapₛₗ _ _ y = y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x => simp [map_smulₛₗ]
    | add x y hx hy => rw [map_add, hx, hy]
  mul_smul g h y := by
    change piTensorMapₛₗ _ _ y = piTensorMapₛₗ _ _ (piTensorMapₛₗ _ _ y)
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x => simp [map_smulₛₗ, mul_smul]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  smul_zero g := map_zero (piTensorMapₛₗ _ _)
  smul_add g := map_add (piTensorMapₛₗ _ _)
end
section
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}
omit [MulSemiringAction G A] in

noncomputable def tensorNorm (κ : ι ≃ G) (x : M) : ⨂[A] _ : ι, M :=
  PiTensorProduct.tprod A fun i ↦ κ i • x
variable [SMulDistribClass G A M]
variable {A}
end
end Semilinear
universe u v
end GlobalTheory


