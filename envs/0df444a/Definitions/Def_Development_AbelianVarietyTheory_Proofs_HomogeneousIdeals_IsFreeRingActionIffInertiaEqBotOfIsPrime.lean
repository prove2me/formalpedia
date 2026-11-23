-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:45.832177+00:00
-- url     : https://prove2.me/theorems/c3f377e6-543c-44c3-b3c9-7558a2bf7ffb
-- title:
--   Is Free Ring Action Iff Inertia Eq Bot Of Is Prime
-- statement:
--   Definitions and structural lemmas for Is Free Ring Action Iff Inertia Eq Bot Of Is Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory
def IsFreeRingAction (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A] : Prop :=
  ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤
namespace FreeQuotient
section Basic
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
noncomputable def galoisMap : A ⊗[B] A →ₐ[A] (G → A) :=
  Algebra.TensorProduct.lift (Algebra.ofId A (G → A))
    (Pi.algHom B _ fun g ↦ MulSemiringAction.toAlgHom B A g) fun _ _ ↦ Commute.all _ _
@[simp] theorem galoisMap_tmul (a b : A) (g : G) :
    galoisMap G A B (a ⊗ₜ b) g = a * g • b := rfl
variable {G A} in

theorem exists_galoisMap_separating [Finite G] (P : Ideal A) (H : Set G)
    (hH : ∀ h ∈ H, ∀ a : A, h • a - a ∈ P)
    (hH' : ∀ g ∉ H, P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ e : A ⊗[B] A, (∀ g ∉ H, galoisMap G A B e g = 0) ∧
      ∀ h ∈ H, galoisMap G A B e h - 1 ∈ P := by
  classical
  cases nonempty_fintype G
  have key : ∀ g : G, ∀ c ∈ Ideal.span (Set.range fun a : A ↦ g • a - a),
      ∃ e : A ⊗[B] A, galoisMap G A B e g = 0 ∧ ∀ h ∈ H, galoisMap G A B e h - c ∈ P := by
    intro g c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨(g • a) ⊗ₜ 1 - 1 ⊗ₜ a, by simp, fun h hh ↦ ?_⟩
      have := P.neg_mem (hH h hh a)
      simp only [map_sub, Pi.sub_apply, galoisMap_tmul, smul_one, mul_one, one_mul]
      convert this using 1
      ring
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨e, he, he'⟩ := hx
      obtain ⟨f, hf, hf'⟩ := hy
      refine ⟨e + f, by simp [he, hf], fun h hh ↦ ?_⟩
      have := P.add_mem (he' h hh) (hf' h hh)
      simp only [map_add, Pi.add_apply]
      convert this using 1
      ring
    | smul r x _ hx =>
      obtain ⟨e, he, he'⟩ := hx
      refine ⟨r • e, by simp [he], fun h hh ↦ ?_⟩
      have := P.mul_mem_left r (he' h hh)
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      convert this using 1
      ring
  have key2 : ∀ g ∉ H,
      ∃ e : A ⊗[B] A, galoisMap G A B e g = 0 ∧ ∀ h ∈ H, galoisMap G A B e h - 1 ∈ P := by
    intro g hg
    have h1 : (1 : A) ∈ P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) := by
      rw [hH' g hg]; trivial
    obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp h1
    obtain ⟨e, he, he'⟩ := key g c hc
    refine ⟨e, he, fun h hh ↦ ?_⟩
    have := P.sub_mem (he' h hh) hp
    rw [← hpc]
    convert this using 1
    ring
  choose! e he he' using key2
  refine ⟨∏ g ∈ Finset.univ.filter (· ∉ H), e g, fun g hg ↦ ?_, fun h hh ↦ ?_⟩
  · rw [map_prod, Finset.prod_apply]
    exact Finset.prod_eq_zero (i := g) (by simpa using hg) (he g hg)
  · rw [map_prod, Finset.prod_apply, ← Ideal.Quotient.eq, map_prod, map_one]
    refine Finset.prod_eq_one fun g hg ↦ ?_
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact he' g (by simpa using hg) h hh
variable {G A} in

theorem exists_finset_separating [Finite G] (P : Ideal A) (H : Set G)
    (hH : ∀ h ∈ H, ∀ a : A, h • a - a ∈ P)
    (hH' : ∀ g ∉ H, P ⊔ Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    ∃ s : Finset (A × A), (∀ g ∉ H, ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∀ h ∈ H, ∑ p ∈ s, p.1 * h • p.2 - 1 ∈ P := by
  obtain ⟨e, he, he'⟩ := exists_galoisMap_separating ℤ P H hH hH'
  obtain ⟨s, rfl⟩ := e.exists_finset
  refine ⟨s, fun g hg ↦ ?_, fun h hh ↦ ?_⟩
  · simpa [Finset.sum_apply] using he g hg
  · simpa [Finset.sum_apply] using he' h hh
variable {G A} in

theorem exists_galois_coordinates [Finite G] (h : IsFreeRingAction G A) :
    ∃ s : Finset (A × A), (∀ g : G, g ≠ 1 → ∑ p ∈ s, p.1 * g • p.2 = 0) ∧
      ∑ p ∈ s, p.1 * p.2 = 1 := by
  obtain ⟨s, hs, hs'⟩ := exists_finset_separating (G := G) (⊥ : Ideal A) {1}
    (by rintro _ rfl a; simp) (fun g hg ↦ by rw [h g hg, sup_top_eq])
  exact ⟨s, hs, by simpa [sub_eq_zero] using hs' 1 rfl⟩
end Basic
instance smulDistribClass_self (G : Type*) [Group G] (A : Type*) [CommRing A]
    [MulSemiringAction G A] : SMulDistribClass G A A :=
  ⟨fun g a b ↦ smul_mul' g a b⟩
theorem smul_sum_smul {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    [DistribMulAction G M] (m : M) (g : G) : g • ∑ h : G, h • m = ∑ h : G, h • m := by
  simp only [Finset.smul_sum, smul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft g) fun h ↦ h • m
section Trace
variable (G : Type*) [Group G] [Fintype G] (B : Type*) [CommRing B]
  (M : Type*) [AddCommGroup M] [Module B M] [DistribMulAction G M] [SMulCommClass G B M]
def moduleTrace : M →ₗ[B] (Representation.ofDistribMulAction B G M).invariants where
  toFun m := ⟨∑ g : G, g • m, fun g ↦ smul_sum_smul m g⟩
  map_add' x y := Subtype.ext (by simp [Finset.sum_add_distrib])
  map_smul' b x := Subtype.ext (by simp [Finset.smul_sum, smul_comm _ b])
@[simp] theorem coe_moduleTrace (m : M) : (moduleTrace G B M m : M) = ∑ g : G, g • m := rfl
variable (A : Type*) [CommRing A] [MulSemiringAction G A] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
noncomputable def invariantsRingEquiv :
    B ≃ₗ[B] (Representation.ofDistribMulAction B G A).invariants :=
  LinearEquiv.ofBijective ((Algebra.linearMap B A).codRestrict
      (Representation.ofDistribMulAction B G A).invariants fun b g ↦ smul_algebraMap g b)
    ⟨fun a b hab ↦ FaithfulSMul.algebraMap_injective B A (congrArg Subtype.val hab),
      fun ⟨x, hx⟩ ↦ by
        obtain ⟨b, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) x hx
        exact ⟨b, rfl⟩⟩
omit [Fintype G] in
theorem algebraMap_invariantsRingEquiv_symm
    (x : (Representation.ofDistribMulAction B G A).invariants) :
    algebraMap B A ((invariantsRingEquiv G B A).symm x) = x :=
  congrArg Subtype.val ((invariantsRingEquiv G B A).apply_symm_apply x)
noncomputable def ringTrace : A →ₗ[B] B :=
  (invariantsRingEquiv G B A).symm.toLinearMap ∘ₗ moduleTrace G B A
@[simp] theorem algebraMap_ringTrace (a : A) :
    algebraMap B A (ringTrace G B A a) = ∑ g : G, g • a :=
  algebraMap_invariantsRingEquiv_symm G B A _
end Trace
section Tame
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
theorem sum_smul_sum_smul (s : Finset (A × A)) (m : M) :
    ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) = ∑ g : G, (∑ p ∈ s, p.1 * g • p.2) • g • m := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_distrib_smul, mul_smul]
  exact Finset.sum_comm
end Tame
section DualBasis
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
variable (G) in

def averageMap (f : M →ₗ[A] N) : M →ₗ[A] N where
  toFun m := ∑ g : G, g • f (g⁻¹ • m)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_distrib_smul]
variable (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
end DualBasis
section TameDescent
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
end TameDescent
section Free
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
theorem sum_smul_sum_smul_eq [Fintype G] {M : Type*} [AddCommGroup M] [Module A M]
    [DistribMulAction G M] [SMulDistribClass G A M] {s : Finset (A × A)}
    (hs : ∀ g : G, g ≠ 1 → ∑ p ∈ s, p.1 * g • p.2 = 0) (hs' : ∑ p ∈ s, p.1 * p.2 = 1) (m : M) :
    ∑ p ∈ s, p.1 • ∑ g : G, g • (p.2 • m) = m := by
  rw [sum_smul_sum_smul, Finset.sum_eq_single 1 (fun g _ hg ↦ by rw [hs g hg, zero_smul])
    (by simp)]
  simp [hs']
variable [Finite G] (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
theorem bijective_galoisMap (h : IsFreeRingAction G A) :
    Function.Bijective (galoisMap G A B) := by
  classical
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  constructor
  · have key : ∀ z : A ⊗[B] A,
        ∑ p ∈ s, (∑ g : G, g • p.2 * galoisMap G A B z g) ⊗ₜ[B] p.1 = z := by
      intro z
      induction z with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul,
          hx, hy]
      | tmul a b =>
        conv_rhs => rw [← sum_smul_sum_smul_eq hs hs' b, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [← algebraMap_ringTrace G B A, smul_eq_mul, mul_comm, ← Algebra.smul_def,
          ← TensorProduct.smul_tmul, Algebra.smul_def, algebraMap_ringTrace, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        simp only [galoisMap_tmul, smul_eq_mul, smul_mul']
        ring
    intro x y hxy
    rw [← key x, ← key y, hxy]
  · intro f
    refine ⟨∑ k : G, f k • ∑ p ∈ s, p.1 ⊗ₜ (k⁻¹ • p.2), funext fun g ↦ ?_⟩
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, galoisMap_tmul, smul_smul,
      smul_eq_mul]
    rw [Finset.sum_eq_single g (fun k _ hk ↦ by
      rw [hs _ (fun h ↦ hk (mul_inv_eq_one.mp h).symm), mul_zero]) (by simp)]
    simp [hs']
noncomputable def galoisEquiv (h : IsFreeRingAction G A) : A ⊗[B] A ≃ₐ[A] (G → A) :=
  AlgEquiv.ofBijective _ (bijective_galoisMap B h)
@[simp] theorem galoisEquiv_tmul (h : IsFreeRingAction G A) (a b : A) (g : G) :
    galoisEquiv B h (a ⊗ₜ b) g = a * g • b := rfl
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
end Free
section FullyFaithful
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {B : Type*} [CommRing B] [Algebra B A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
  [Module B N] [IsScalarTower B A N] [SMulCommClass G B N]
end FullyFaithful
section BaseChange
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass B G A]
  (N : Type*) [AddCommGroup N] [Module B N]
instance smulDistribClass_tensorProduct : SMulDistribClass G A (A ⊗[B] N) where
  smul_distrib_smul g a z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul b n => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']
variable [SMulCommClass G B A]
noncomputable def toInvariantsTensor :
    N →ₗ[B] (Representation.ofDistribMulAction B G (A ⊗[B] N)).invariants :=
  (TensorProduct.mk B A N 1).codRestrict
    (Representation.ofDistribMulAction B G (A ⊗[B] N)).invariants fun n g ↦ by
      change g • ((1 : A) ⊗ₜ[B] n) = 1 ⊗ₜ[B] n
      rw [TensorProduct.smul_tmul', smul_one]
variable [FaithfulSMul B A] [Algebra.IsInvariant B A G]
end BaseChange
end FreeQuotient
universe w v u
open CategoryTheory
structure SemilinearModule (G : Type v) [Group G] (A : Type u) [CommRing A]
    [MulSemiringAction G A] where

  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  [action : DistribMulAction G carrier]
  [semilinear : SMulDistribClass G A carrier]
namespace SemilinearModule
attribute [instance] addCommGroup module action semilinear
variable (G : Type v) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]
def self : SemilinearModule.{u} G A := ⟨A⟩
instance : Category (SemilinearModule.{w} G A) where
  Hom M N := {f : M.carrier →ₗ[A] N.carrier // ∀ (g : G) m, f (g • m) = g • f m}
  id _ := ⟨LinearMap.id, fun _ _ ↦ rfl⟩
  comp f f' := ⟨f'.1 ∘ₗ f.1, fun g m ↦ by
    rw [LinearMap.comp_apply, f.2, f'.2, LinearMap.comp_apply]⟩
instance smulCommClass_fixedSubring' : SMulCommClass (FixedPoints.subring A G) G A :=
  .symm _ _ _
noncomputable def baseChange (N : Type w) [AddCommGroup N] [Module (FixedPoints.subring A G) N] :
    SemilinearModule.{max w u} G A :=
  ⟨A ⊗[FixedPoints.subring A G] N⟩
noncomputable def invariantsFunctor :
    SemilinearModule.{w} G A ⥤ ModuleCat.{w} (FixedPoints.subring A G) where
  obj M := ModuleCat.of _
    (Representation.ofDistribMulAction (FixedPoints.subring A G) G M.carrier).invariants
  map f := ModuleCat.ofHom (invariantsMap _ _ (f.1.restrictScalars _) f.2)
variable {G A}
end SemilinearModule
@[instance_reducible]
def translationAction (G R : Type*) [Group G] [CommRing R] : MulSemiringAction G (G → R) where
  smul g f := fun x ↦ f (g⁻¹ * x)
  one_smul f := funext fun x ↦ by
    change f (1⁻¹ * x) = f x
    rw [inv_one, one_mul]
  mul_smul g h f := funext fun x ↦ by
    change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl
end GlobalTheory


