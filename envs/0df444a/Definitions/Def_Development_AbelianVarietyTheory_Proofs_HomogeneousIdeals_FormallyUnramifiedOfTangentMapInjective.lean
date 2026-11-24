-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:54.040688+00:00
-- url     : https://prove2.me/theorems/f2191df0-15e5-40d3-bb59-2f90f8211fe6
-- title:
--   Formally Unramified Of Tangent Map Injective
-- statement:
--   Definitions and structural lemmas for Formally Unramified Of Tangent Map Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
namespace GlobalTheory.TangentCrit
section Alg
variable {R A B k : Type*} [CommRing R] [CommRing A] [CommRing B]
section Der
variable [CommRing k] [Algebra R A] [Algebra A k] [Algebra R k] [IsScalarTower R A k]
def derToDual (D : Derivation R A k) : A →+* DualNumber k where
  toFun a := TrivSqZeroExt.inl (algebraMap A k a) + TrivSqZeroExt.inr (D a)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
@[simp] lemma fst_derToDual (D : Derivation R A k) (a : A) :
    (derToDual D a).fst = algebraMap A k a := by simp [derToDual]
@[simp] lemma snd_derToDual (D : Derivation R A k) (a : A) :
    (derToDual D a).snd = D a := by simp [derToDual]
def dualToDer (φ : A →+* DualNumber k) (h₁ : ∀ a, (φ a).fst = algebraMap A k a)
    (h₂ : ∀ r, (φ (algebraMap R A r)).snd = 0) : Derivation R A k :=
  Derivation.mk'
    { toFun a := (φ a).snd
      map_add' a b := by simp
      map_smul' r a := by
        rw [Algebra.smul_def, map_mul, DualNumber.snd_mul, h₂, h₁, ← IsScalarTower.algebraMap_apply]
        simp [Algebra.smul_def] }
    (fun a b => by
      simp [h₁, Algebra.smul_def, mul_comm])
@[simp] lemma dualToDer_apply (φ : A →+* DualNumber k) (h₁ : ∀ a, (φ a).fst = algebraMap A k a)
    (h₂ : ∀ r, (φ (algebraMap R A r)).snd = 0) (a : A) :
    dualToDer φ h₁ h₂ a = (φ a).snd := rfl
end Der
lemma lTensor_injective_of_extend {κ M N : Type*} [Field κ] [Field k] [Algebra B κ] [Algebra B k]
    [Algebra κ k] [IsScalarTower B κ k] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (l : M →ₗ[B] N) (H : ∀ φ : M →ₗ[B] k, ∃ ψ : N →ₗ[B] k, ψ ∘ₗ l = φ) :
    Function.Injective (l.lTensor κ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [← Module.forall_dual_apply_eq_zero_iff κ]
  intro χ
  obtain ⟨ψ, hψ⟩ := H ((Algebra.linearMap κ k ∘ₗ χ).restrictScalars B ∘ₗ TensorProduct.mk B κ M 1)
  have : ∀ z : κ ⊗[B] M, ψ.liftBaseChange κ (l.lTensor κ z) = algebraMap κ k (χ z) := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      have h := LinearMap.congr_fun hψ m
      simp only [LinearMap.comp_apply] at h
      have e : c ⊗ₜ[B] m = c • ((1 : κ) ⊗ₜ[B] m) := by simp [smul_tmul']
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, h, e, map_smul]
      simp [Algebra.smul_def]
  have h := this z
  rw [hz, map_zero] at h
  exact (algebraMap κ k).injective (by rw [← h, map_zero])
theorem formallyUnramified_of_dual_const.{u} {A B : Type u} [CommRing A] [CommRing B]
    (β : A →+* B) (hβ : β.EssFiniteType)
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : B →+* DualNumber k),
      (∀ a, (φ (β a)).snd = 0) → ∀ b, (φ b).snd = 0) : β.FormallyUnramified := by
  algebraize [β]
  refine ⟨?_⟩
  rw [← Module.support_eq_empty_iff (R := B), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  let κ := p.asIdeal.ResidueField
  let k := AlgebraicClosure κ
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor κ) :=
    lTensor_injective_of_extend (k := k) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B k := χ.compDer (KaehlerDifferential.D A B)
      have := H k (derToDual D) (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : κ ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))
end Alg
section Sch
open AlgebraicGeometry CategoryTheory Limits
universe u
abbrev dualPt (k : Type u) [CommRing k] : Spec (.of k) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
abbrev dualBase (k : Type u) [CommRing k] : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
@[reassoc]
lemma dualPt_dualBase (k : Type u) [CommRing k] : dualPt k ≫ dualBase k = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1
end Sch
end GlobalTheory.TangentCrit
namespace GlobalTheory.GrpTangent
section Grp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit
section Ring
variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [GrpObj H]
def epsZero (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (dualPt R) (dualPt_dualBase R)
def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
@[simp] lemma epsScale_left (c : R) : (epsScale c).left = spMap (epsScaleR c) := rfl
lemma isTangent_iff (w : epsR R ⟶ G) : IsTangent w ↔ epsZero R ≫ w = 1 := by
  rw [← one_eq_one]
  exact ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩
lemma isTangent_comp {w : epsR R ⟶ G} (hw : IsTangent w) (f : G ⟶ H) [IsMonHom f] :
    IsTangent (w ≫ f) := by
  rw [isTangent_iff] at hw ⊢
  rw [← Category.assoc, hw, one_comp]
def tangentMap (f : G ⟶ H) [IsMonHom f] (w : {w : epsR R ⟶ G // IsTangent w}) :
    {w : epsR R ⟶ H // IsTangent w} := ⟨w.1 ≫ f, isTangent_comp w.2 f⟩
@[simp] lemma tangentMap_coe (f : G ⟶ H) [IsMonHom f] (w : {w : epsR R ⟶ G // IsTangent w}) :
    (tangentMap f w).1 = w.1 ≫ f := rfl
@[reassoc]
lemma epsZero_epsScale (c : R) : epsZero R ≫ epsScale c = epsZero R := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp [epsScaleR]
@[reassoc]
lemma epsScale_mul (a b : R) : epsScale a ≫ epsScale b = epsScale (a * b) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  ext <;> simp [epsScaleR, _root_.mul_assoc]
def sqZeroMap {M N : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N] (l : M →ₗ[R] N) :
    Over.mk (spMap (algebraMap R (TrivSqZeroExt R N))) ⟶
      Over.mk (spMap (algebraMap R (TrivSqZeroExt R M))) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)
end Ring
section Base
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
theorem mulN_eq_pow (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = 𝟙 G ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl
theorem comp_mulN {T : Over S} (x : T ⟶ G) (n : ℕ) : x ≫ mulN G n = x ^ n := by
  rw [mulN_eq_pow, comp_pow, Category.comp_id]
instance isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) where
  one_hom := by rw [comp_mulN, one_eq_one, one_pow]
  mul_hom := by
    rw [comp_mulN, mul_eq_mul, comp_mul, mul_pow]
    congr 1 <;> simp [comp_mulN]
@[reassoc]
lemma one_pullback_left_fst {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    η[(Over.pullback p).obj G].left ≫ pullback.fst G.hom p = p ≫ η[G].left := by
  rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)
section Field
variable {k : Type} [CommRing k] (p : Sp k ⟶ S)
def toFibre {X : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) : epsR k ⟶ (Over.pullback p).obj X :=
  Over.homMk (pullback.lift w.left (dualBase k) (Over.w w)) (pullback.lift_snd _ _ _)
@[reassoc]
lemma toFibre_left_fst {X : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) :
    (toFibre p w).left ≫ pullback.fst X.hom p = w.left := pullback.lift_fst _ _ _
def epsZeroAt : Over.mk p ⟶ Over.mk (dualBase k ≫ p) :=
  Over.homMk (dualPt k) (by simp [dualPt_dualBase_assoc])
def epsBaseAt : Over.mk (dualBase k ≫ p) ⟶ Over.mk p := Over.homMk (dualBase k) rfl
variable (f : G ⟶ H) [IsMonHom f]
end Field
end Base
section MulN
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
end MulN
end Grp
end GlobalTheory.GrpTangent


