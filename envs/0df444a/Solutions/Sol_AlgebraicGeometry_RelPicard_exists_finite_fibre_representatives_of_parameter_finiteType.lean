-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_finite_fibre_representatives_of_parameter_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-11T15:45:17.238851+00:00
-- url     : https://prove2.me/submissions/8573f000-4c97-439a-a31a-a9ec29e27512

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Noetherian.Basic
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

section
-- Reused implementation: Solutions.PhilipponFiniteAlgEquivQuotient

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.FiniteAlgEquivQuotient
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u v w

/-- The image of a homomorphism into a finitely generated abelian group
has a universe-zero representative, with exactly the original fibres. -/
theorem exists_small_finite_image
    {L : Type u} [AddCommGroup L] [Module ℤ L]
    {B : Type v} [AddCommGroup B] [Module ℤ B] [Module.Finite ℤ B]
    (φ : L →ₗ[ℤ] B) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y ↔ φ x = φ y := by
  letI : Module ℤ φ.range := φ.range.module
  letI : Module.Finite ℤ φ.range := inferInstance
  letI : Small.{0} φ.range := Module.Finite.small ℤ φ.range
  letI : Module ℤ (Shrink.{0} φ.range) := Shrink.instModule
  let e := Shrink.linearEquiv ℤ φ.range
  let q := e.symm.toLinearMap.comp φ.rangeRestrict
  refine ⟨Shrink.{0} φ.range, inferInstance, inferInstance, inferInstance, q,
    e.symm.surjective.comp φ.surjective_rangeRestrict, ?_⟩
  intro x y
  change e.symm (φ.rangeRestrict x) = e.symm (φ.rangeRestrict y) ↔ _
  rw [e.symm.injective.eq_iff, Subtype.ext_iff]
  rfl

/-- The elementary image and tensor-class steps of the Néron--Severi
application. The geometric classification map and its finite generation are
explicit inputs here, and remain obligations in the full external theorem. -/
theorem of_finite_classification
    {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
    {L : Type v} [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l))
    {B : Type w} [AddCommGroup B] [Module ℤ B] [Module.Finite ℤ B]
    (ν : L →ₗ[ℤ] B) (hν : ∀ l, ν l = 0 → RelPicard.IsAlgEquivZero π (ℓ l)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∃ N : X.Modules,
        Scheme.Modules.IsInvertible N ∧ RelPicard.IsAlgEquivZero π N ∧
          Nonempty (ℓ x ≅ N ⊗ ℓ y) := by
  obtain ⟨A, instA, modA, finA, q, hq, he⟩ := exists_small_finite_image ν
  letI := instA
  letI := modA
  letI := finA
  refine ⟨A, instA, modA, finA, q, hq, ?_⟩
  intro x y hxy
  refine ⟨ℓ (x - y), hℓ _, hν _ ?_, ?_⟩
  · rw [map_sub, (he x y).mp hxy, sub_self]
  · apply toSkeleton_eq_toSkeleton_iff.mp
    rw [Skeleton.toSkeleton_tensorObj, hclass, hclass, hclass,
      ← map_mul, ← ofAdd_add, sub_add_cancel]

end PhilipponMultiplicity.FiniteAlgEquivQuotient
end
end

section
-- Reused implementation: Solutions.PhilipponAlgebraicEquivalenceFamilies

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicEquivalenceFamilies
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open RelPicard NeronModelInfra
universe u

/-- Integral fibres persist under composition when the first map is flat
and open and the second is locally of finite type. -/
theorem geometricallyIntegral_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [GeometricallyIntegral g] [LocallyOfFiniteType g] :
    GeometricallyIntegral (f ≫ g) := by
  letI : ObjectProperty.IsClosedUnderIsomorphisms (IsIntegral : Scheme.{u} → Prop) :=
    ⟨fun e h => by letI := h; exact IsIntegral.of_isIso e.hom⟩
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  haveI : IsLocallyNoetherian (pullback g x) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g x)
  haveI : IsIntegral (pullback g x) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback g x)
  haveI : IsIntegral (pullback f (pullback.fst g x)) := inferInstance
  exact IsIntegral.of_isIso (pullbackRightPullbackFstIso g x f).hom

variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

theorem unit_algEquivZero : IsAlgEquivZero π (𝟙_ X.Modules) := by
  refine ⟨Spec (.of K), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec K,
    𝟙_ (pullback π (𝟙 (Spec (.of K)))).Modules,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨𝟙 _, Category.comp_id _⟩, ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm

/-- Pullback of a parameter-family sheaf along two successive parameter maps. -/
def parameterPullbackIso {T T' T'' : Scheme.{u}}
    {h : T ⟶ Spec (.of K)} {h' : T' ⟶ Spec (.of K)} {h'' : T'' ⟶ Spec (.of K)}
    (p : SchemeHomOver h' h) (r : SchemeHomOver h'' h')
    (t : SchemeHomOver h'' h) (ht : postComp p r = t)
    (M : (pullback π h).Modules) :
    (Scheme.Modules.pullback (baseChangeSnd π r)).obj
      ((Scheme.Modules.pullback (baseChangeSnd π p)).obj M) ≅
        (Scheme.Modules.pullback (baseChangeSnd π t)).obj M :=
  (Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr
      ((baseChangeSnd_comp π p r).trans (congrArg (baseChangeSnd π) ht))).app M

def pairPoint {T T' : Scheme.{u}} (h : T ⟶ Spec (.of K)) (h' : T' ⟶ Spec (.of K))
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h)
    (t' : SchemeHomOver (𝟙 (Spec (.of K))) h') :
    SchemeHomOver (𝟙 (Spec (.of K))) (pullback.fst h h' ≫ h) :=
  ⟨pullback.lift t.1 t'.1 (t.2.trans t'.2.symm), by
    rw [← Category.assoc, pullback.lift_fst, t.2]⟩

theorem tensor_algEquivZero {L N : X.Modules}
    (hL : IsAlgEquivZero π L) (hN : IsAlgEquivZero π N) :
    IsAlgEquivZero π (L ⊗ N) := by
  obtain ⟨T, h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL
  obtain ⟨T', h', hft', hgi', M', hM', t₀', t₁', ⟨e₀'⟩, ⟨e₁'⟩⟩ := hN
  letI := hft
  letI := hgi
  letI := hft'
  letI := hgi'
  let hP := pullback.fst h h' ≫ h
  let p : SchemeHomOver hP h := ⟨pullback.fst h h', rfl⟩
  let p' : SchemeHomOver hP h' := ⟨pullback.snd h h', pullback.condition.symm⟩
  let F := (Scheme.Modules.pullback (baseChangeSnd π p)).obj M
  let F' := (Scheme.Modules.pullback (baseChangeSnd π p')).obj M'
  have hF := hM.pullback (baseChangeSnd π p)
  have hF' := hM'.pullback (baseChangeSnd π p')
  let r₀ := pairPoint h h' t₀ t₀'
  let r₁ := pairPoint h h' t₁ t₁'
  have hleft : ∀ t t', postComp p (pairPoint h h' t t') = t := by
    intro t t'
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  have hright : ∀ t t', postComp p' (pairPoint h h' t t') = t' := by
    intro t t'
    apply Subtype.ext
    exact pullback.lift_snd _ _ _
  refine ⟨pullback h h', hP, inferInstance,
    geometricallyIntegral_comp (pullback.fst h h') h,
    F ⊗ F', hF.tensor_monoidalV2 hF', r₀, r₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso _ F F' ≪≫
      ((parameterPullbackIso π p r₀ t₀ (hleft t₀ t₀') M ≪≫ e₀) ⊗ᵢ
        (parameterPullbackIso π p' r₀ t₀' (hright t₀ t₀') M' ≪≫ e₀')) ≪≫ λ_ _
  · exact Scheme.Modules.pullbackTensorObjIso _ F F' ≪≫
      ((parameterPullbackIso π p r₁ t₁ (hleft t₁ t₁') M ≪≫ e₁) ⊗ᵢ
        (parameterPullbackIso π p' r₁ t₁' (hright t₁ t₁') M' ≪≫ e₁')) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ L N).symm

/-- Tensor inverses are algebraically trivial: twist a connecting family
by the inverse bundle and exchange its two marked points. -/
theorem inverse_algEquivZero {L N : X.Modules}
    (hL : IsAlgEquivZero π L) (hN : Scheme.Modules.IsInvertible N)
    (e : L ⊗ N ≅ 𝟙_ X.Modules) : IsAlgEquivZero π N := by
  obtain ⟨T, h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL
  let F := M ⊗ (Scheme.Modules.pullback (pullback.fst π h)).obj N
  have hF := hM.tensor_monoidalV2 (hN.pullback (pullback.fst π h))
  have hc : ∀ t : SchemeHomOver (𝟙 (Spec (.of K))) h,
      baseChangeSnd π t ≫ pullback.fst π h = pullback.fst π (𝟙 _) := by
    intro t
    unfold baseChangeSnd
    simp only [pullback.lift_fst, Category.comp_id]
  let E (t : SchemeHomOver (𝟙 (Spec (.of K))) h) :
      (Scheme.Modules.pullback (baseChangeSnd π t)).obj
        ((Scheme.Modules.pullback (pullback.fst π h)).obj N) ≅
          (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj N :=
    (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr (hc t)).app N
  refine ⟨T, h, hft, hgi, F, hF, t₁, t₀, ⟨?_⟩, ⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (e₁ ⊗ᵢ E t₁) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ L N).symm ≪≫
      (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (e₀ ⊗ᵢ E t₀) ≪≫ λ_ _

end PhilipponMultiplicity.AlgebraicEquivalenceFamilies
end
end

section
-- Reused implementation: Solutions.PhilipponAlgebraicEquivalenceQuotient

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicEquivalenceFamilies
open AlgebraicGeometry CategoryTheory MonoidalCategory
open RelPicard
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))
    {L : Type v} [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l))

/-- The actual algebraically trivial members of an integer family form
a subgroup, using the explicitly constructed connecting families. -/
def algebraicSubgroup : AddSubgroup L where
  carrier := {l | IsAlgEquivZero π (ℓ l)}
  zero_mem' := by
    have he : toSkeleton (𝟙_ X.Modules) = toSkeleton (ℓ 0) := by
      rw [hclass, ofAdd_zero, map_one]
      rfl
    exact (unit_algEquivZero π).of_iso (toSkeleton_eq_toSkeleton_iff.mp he).some
  add_mem' := by
    intro x y hx hy
    have he : toSkeleton (ℓ x ⊗ ℓ y) = toSkeleton (ℓ (x + y)) := by
      rw [Skeleton.toSkeleton_tensorObj, hclass, hclass, hclass, ofAdd_add, map_mul]
    exact (tensor_algEquivZero π hx hy).of_iso (toSkeleton_eq_toSkeleton_iff.mp he).some
  neg_mem' := by
    intro x hx
    have he : toSkeleton (ℓ x ⊗ ℓ (-x)) = toSkeleton (𝟙_ X.Modules) := by
      rw [Skeleton.toSkeleton_tensorObj, hclass, hclass, ← map_mul, ← ofAdd_add,
        add_neg_cancel, ofAdd_zero, map_one]
      rfl
    exact inverse_algEquivZero π hx (hℓ (-x)) (toSkeleton_eq_toSkeleton_iff.mp he).some

/-- The concrete algebraic-equivalence kernel of this family. -/
def algebraicKernel : Submodule ℤ L :=
  { (algebraicSubgroup π φ ℓ hℓ hclass).toAddSubmonoid with
    smul_mem' := by
      intro n x hx
      exact (congrArg (fun y => y ∈ algebraicSubgroup π φ ℓ hℓ hclass)
        (int_smul_eq_zsmul (inferInstance : Module ℤ L) n x)).mpr
          ((algebraicSubgroup π φ ℓ hℓ hclass).zsmul_mem hx n) }

abbrev AlgebraicQuotient := L ⧸ algebraicKernel π φ ℓ hℓ hclass

def algebraicMap : L →ₗ[ℤ] AlgebraicQuotient π φ ℓ hℓ hclass where
  toFun := (algebraicKernel π φ ℓ hℓ hclass).mkQ
  map_add' := fun x y => map_add _ x y
  map_smul' := fun n x =>
    (congrArg (fun y => (algebraicKernel π φ ℓ hℓ hclass).mkQ y)
      (int_smul_eq_zsmul (inferInstance : Module ℤ L) n x)).trans
        (map_zsmul (algebraicKernel π φ ℓ hℓ hclass).mkQ n x)

theorem algebraicMap_eq_zero (l : L) :
    algebraicMap π φ ℓ hℓ hclass l = 0 ↔ IsAlgEquivZero π (ℓ l) :=
  Submodule.Quotient.mk_eq_zero _

/-- Once this concrete quotient is finitely generated, all remaining
image, universe, representative and tensor-isomorphism steps are proved. -/
theorem finite_quotient_of_finite_algebraicQuotient
    [Module.Finite ℤ (AlgebraicQuotient π φ ℓ hℓ hclass)] :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∃ N : X.Modules,
        Scheme.Modules.IsInvertible N ∧ IsAlgEquivZero π N ∧
          Nonempty (ℓ x ≅ N ⊗ ℓ y) := by
  apply FiniteAlgEquivQuotient.of_finite_classification π φ ℓ hℓ hclass
    (algebraicMap π φ ℓ hℓ hclass)
  intro l hl
  exact (algebraicMap_eq_zero π φ ℓ hℓ hclass l).mp hl

/-- Conversely, any finite quotient whose kernel is algebraically trivial
proves finite generation of the concrete algebraic-equivalence quotient. -/
theorem finite_algebraicQuotient_of_finite_map
    {A : Type*} [AddCommGroup A] [Module ℤ A] [Module.Finite ℤ A]
    (q : L →ₗ[ℤ] A) (hq : Function.Surjective q)
    (hzero : ∀ l, q l = 0 → IsAlgEquivZero π (ℓ l)) :
    Module.Finite ℤ (AlgebraicQuotient π φ ℓ hℓ hclass) := by
  have hk : LinearMap.ker q ≤ LinearMap.ker (algebraicMap π φ ℓ hℓ hclass) := by
    intro l hl
    exact (algebraicMap_eq_zero π φ ℓ hℓ hclass l).mpr (hzero l hl)
  letI : Module ℤ (L ⧸ LinearMap.ker q) := Submodule.Quotient.module _
  letI : Module.Finite ℤ (L ⧸ LinearMap.ker q) :=
    Module.Finite.equiv (LinearMap.quotKerEquivOfSurjective q hq).symm
  apply Module.Finite.of_surjective ((LinearMap.ker q).liftQ
    (algebraicMap π φ ℓ hℓ hclass) hk)
  intro z
  obtain ⟨l, rfl⟩ := (algebraicKernel π φ ℓ hℓ hclass).mkQ_surjective z
  exact ⟨Submodule.Quotient.mk l, rfl⟩

/-- The explicit family-based condition in the published finiteness target
also implies finite generation of this same concrete quotient. -/
theorem finite_algebraicQuotient_of_finite_relations
    {A : Type*} [AddCommGroup A] [Module ℤ A] [Module.Finite ℤ A]
    (q : L →ₗ[ℤ] A) (hq : Function.Surjective q)
    (he : ∀ x y, q x = q y → ∃ N : X.Modules,
      Scheme.Modules.IsInvertible N ∧ IsAlgEquivZero π N ∧ Nonempty (ℓ x ≅ N ⊗ ℓ y)) :
    Module.Finite ℤ (AlgebraicQuotient π φ ℓ hℓ hclass) := by
  apply finite_algebraicQuotient_of_finite_map π φ ℓ hℓ hclass q hq
  intro l hl
  obtain ⟨N, _, hN, ⟨e⟩⟩ := he l 0 (hl.trans (map_zero q).symm)
  have hz : toSkeleton (ℓ 0) = toSkeleton (𝟙_ X.Modules) := by
    rw [hclass, ofAdd_zero, map_one]
    rfl
  let e0 := (toSkeleton_eq_toSkeleton_iff.mp hz).some
  exact hN.of_iso (e ≪≫ (Iso.refl N ⊗ᵢ e0) ≪≫ ρ_ N).symm

end PhilipponMultiplicity.AlgebraicEquivalenceFamilies
end
end

section
-- Reused implementation: Solutions.PhilipponInvertibleClassLattice

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.InvertibleClassLattice
open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules
universe u v
variable {X : Scheme.{u}}

theorem isInvertible_of_iso {M N : X.Modules} (e : M ≅ N) (hM : IsInvertible M) :
    IsInvertible N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨eU⟩⟩ := hM.exists_trivialization x
  exact ⟨U, hx, ⟨(pullback U.ι).mapIso e.symm ≪≫ eU⟩⟩

/-- An actual invertible sheaf determines a unit in the tensor monoid of
module isomorphism classes, using its already proved tensor inverse. -/
def unitClass (M : X.Modules) (hM : IsInvertible M) : (Skeleton X.Modules)ˣ := by
  let N := hM.exists_tensor_inverse_monoidalV2.choose
  let e := hM.exists_tensor_inverse_monoidalV2.choose_spec.2.some
  have he : toSkeleton M * toSkeleton N = 1 :=
    (Skeleton.toSkeleton_tensorObj M N).symm.trans (congr_toSkeleton_of_iso e)
  exact ⟨toSkeleton M, toSkeleton N, he, by rw [mul_comm]; exact he⟩

theorem unitClass_val (M : X.Modules) (hM : IsInvertible M) :
    (unitClass M hM).val = toSkeleton M := rfl

end PhilipponMultiplicity.InvertibleClassLattice
end
end

section
-- Reused implementation: Solutions.PhilipponSchemePicardGroup

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open AlgebraicGeometry CategoryTheory MonoidalCategory
open PhilipponMultiplicity Scheme.Modules InvertibleClassLattice
universe u v

/-- Units of the tensor-class monoid represented by actual invertible
sheaves. The representative condition uses the existing local definition. -/
def invertibleUnits (X : Scheme.{u}) : Subgroup (Skeleton X.Modules)ˣ where
  carrier := {a | ∃ M : X.Modules, IsInvertible M ∧ toSkeleton M = a.val}
  one_mem' := ⟨𝟙_ X.Modules, isInvertible_unit X, rfl⟩
  mul_mem' := by
    rintro a b ⟨M, hM, hm⟩ ⟨N, hN, hn⟩
    refine ⟨M ⊗ N, hM.tensor_monoidalV2 hN, ?_⟩
    rw [Skeleton.toSkeleton_tensorObj, hm, hn]
    rfl
  inv_mem' := by
    rintro a ⟨M, hM, hm⟩
    obtain ⟨N, hN, ⟨e⟩⟩ := hM.exists_tensor_inverse_monoidalV2
    refine ⟨N, hN, ?_⟩
    have he : a.val * toSkeleton N = 1 := by
      rw [← hm, ← Skeleton.toSkeleton_tensorObj]
      exact congr_toSkeleton_of_iso e
    change toSkeleton N = a.inv
    calc
      _ = a.inv * (a.val * toSkeleton N) := by rw [← mul_assoc, a.inv_val, one_mul]
      _ = a.inv := by rw [he, mul_one]

/-- The actual Picard group, written additively. Its objects are isomorphism
classes of invertible sheaves and addition is tensor product. -/
abbrev Group (X : Scheme.{u}) := Additive (invertibleUnits X)

variable {X : Scheme.{u}}

def value (a : Group X) : Skeleton X.Modules := a.toMul.val.val

theorem value_injective : Function.Injective (value (X := X)) := by
  intro a b h
  exact Subtype.ext (Units.ext h)

theorem value_zero : value (0 : Group X) = 1 := rfl

theorem value_add (a b : Group X) : value (a + b) = value a * value b := rfl

def classOf (M : X.Modules) (hM : IsInvertible M) : Group X :=
  Additive.ofMul ⟨unitClass M hM, M, hM, rfl⟩

theorem value_classOf (M : X.Modules) (hM : IsInvertible M) :
    value (classOf M hM) = toSkeleton M := rfl

theorem classOf_eq_iff (M N : X.Modules) (hM : IsInvertible M) (hN : IsInvertible N) :
    classOf M hM = classOf N hN ↔ Nonempty (M ≅ N) := by
  rw [← toSkeleton_eq_toSkeleton_iff]
  exact value_injective.eq_iff.symm

theorem classOf_tensor (M N : X.Modules) (hM : IsInvertible M) (hN : IsInvertible N) :
    classOf (M ⊗ N) (hM.tensor_monoidalV2 hN) = classOf M hM + classOf N hN := by
  apply value_injective
  exact Skeleton.toSkeleton_tensorObj M N

def representative (a : Group X) : X.Modules := a.toMul.property.choose

theorem representative_isInvertible (a : Group X) : IsInvertible (representative a) :=
  a.toMul.property.choose_spec.1

theorem representative_value (a : Group X) : toSkeleton (representative a) = value a :=
  a.toMul.property.choose_spec.2

theorem classOf_representative (a : Group X) :
    classOf (representative a) (representative_isInvertible a) = a :=
  value_injective (representative_value a)

def classHom (X : Scheme.{u}) : Multiplicative (Group X) →* Skeleton X.Modules where
  toFun := fun a => value a.toAdd
  map_one' := value_zero
  map_mul' := fun a b => value_add a.toAdd b.toAdd

theorem representative_class (a : Group X) :
    toSkeleton (representative a) = classHom X (Multiplicative.ofAdd a) :=
  representative_value a

variable {K : Type u} [Field K] (π : X ⟶ Spec (.of K))

/-- Algebraic equivalence to the trivial sheaf inside the actual Picard
group. Closure uses the previously constructed parameter families. -/
def picardZero : Submodule ℤ (Group X) :=
  AlgebraicEquivalenceFamilies.algebraicKernel π (classHom X) representative
    representative_isInvertible representative_class

/-- The concrete Néron--Severi group. No finiteness is asserted here. -/
abbrev NeronSeveri := Group X ⧸ picardZero π

def classMap : Group X →ₗ[ℤ] NeronSeveri π :=
  AlgebraicEquivalenceFamilies.algebraicMap π (classHom X) representative
    representative_isInvertible representative_class

theorem classMap_surjective : Function.Surjective (classMap π) :=
  (picardZero π).mkQ_surjective

theorem classMap_classOf_eq_zero_iff (M : X.Modules) (hM : IsInvertible M) :
    classMap π (classOf M hM) = 0 ↔ RelPicard.IsAlgEquivZero π M := by
  have hq : classMap π (classOf M hM) = 0 ↔
      RelPicard.IsAlgEquivZero π (representative (classOf M hM)) :=
    AlgebraicEquivalenceFamilies.algebraicMap_eq_zero π (classHom X) representative
      representative_isInvertible representative_class (classOf M hM)
  have he : toSkeleton (representative (classOf M hM)) = toSkeleton M :=
    representative_value _
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.mp he
  exact hq.trans ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end AlgebraicGeometry.SchemePicard
end
end

section
-- Reused implementation: Solutions.PhilipponFamilyFibrePicard

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra RelPicard
open PhilipponMultiplicity.AlgebraicEquivalenceFamilies
universe u
variable {K : Type u} [Field K] {X T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) {h : T ⟶ Spec (.of K)}

/-- The inclusion of a rational fibre into the product with a parameter scheme. -/
def familyFibreMap (t : SchemeHomOver (𝟙 (Spec (.of K))) h) :
    X ⟶ pullback π h :=
  pullback.lift (𝟙 X) (π ≫ t.1) (by simp [t.2])

/-- The actual sheaf on `X` obtained by specializing the parameter. -/
def familyFibre (M : (pullback π h).Modules)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h) : X.Modules :=
  (Scheme.Modules.pullback (familyFibreMap π t)).obj M

theorem familyFibre_isInvertible (M : (pullback π h).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h) :
    Scheme.Modules.IsInvertible (familyFibre π M t) :=
  hM.pullback (familyFibreMap π t)

/-- Comparison with the base-change presentation used by algebraic equivalence. -/
def familyFibreIso (M : (pullback π h).Modules)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h) :
    (Scheme.Modules.pullback (baseChangeSnd π t)).obj M ≅
      (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj (familyFibre π M t) := by
  refine (Scheme.Modules.pullbackCongr ?_).app M ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M).symm
  apply pullback.hom_ext
  · simp [familyFibreMap, baseChangeSnd]
  · simp only [familyFibreMap, baseChangeSnd, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Category.assoc, pullback.condition, Category.comp_id]

/-- Twisting a parameter family by a fixed sheaf specializes to the same
twist of each fibre. -/
def familyConstantIso (N : X.Modules)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h) :
    (Scheme.Modules.pullback (baseChangeSnd π t)).obj
      ((Scheme.Modules.pullback (pullback.fst π h)).obj N) ≅
        (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj N :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫
    (Scheme.Modules.pullbackCongr (by simp [baseChangeSnd])).app N

/-- Two fibres of a geometrically integral parameter family differ by an
algebraically trivial line bundle. The witness is the original family,
twisted by an inverse of its first fibre. -/
theorem familyFibre_tensor_inverse_algEquivZero
    [LocallyOfFiniteType h] [GeometricallyIntegral h]
    (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M)
    (t₀ t₁ : SchemeHomOver (𝟙 (Spec (.of K))) h)
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N)
    (e : familyFibre π M t₀ ⊗ N ≅ 𝟙_ X.Modules) :
    RelPicard.IsAlgEquivZero π (familyFibre π M t₁ ⊗ N) := by
  let F := M ⊗ (Scheme.Modules.pullback (pullback.fst π h)).obj N
  refine ⟨T, h, inferInstance, inferInstance, F,
    hM.tensor_monoidalV2 (hN.pullback _), t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (familyFibreIso π M t₀ ⊗ᵢ familyConstantIso π N t₀) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (familyFibreIso π M t₁ ⊗ᵢ familyConstantIso π N t₁) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

def familyClass (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h) : NeronSeveri π :=
  classMap π (classOf (familyFibre π M t) (familyFibre_isInvertible π M hM t))

/-- All rational fibres in a geometrically integral parameter family have
the same class modulo the concrete algebraic-equivalence relation. -/
theorem familyClass_eq [LocallyOfFiniteType h] [GeometricallyIntegral h]
    (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M)
    (t₀ t₁ : SchemeHomOver (𝟙 (Spec (.of K))) h) :
    familyClass π M hM t₀ = familyClass π M hM t₁ := by
  obtain ⟨N, hN, ⟨e⟩⟩ :=
    (familyFibre_isInvertible π M hM t₀).exists_tensor_inverse_monoidalV2
  have h₀ : familyClass π M hM t₀ + classMap π (classOf N hN) = 0 := by
    rw [familyClass, ← map_add, ← classOf_tensor,
      classMap_classOf_eq_zero_iff]
    exact (unit_algEquivZero π).of_iso e.symm
  have h₁ : familyClass π M hM t₁ + classMap π (classOf N hN) = 0 := by
    rw [familyClass, ← map_add, ← classOf_tensor,
      classMap_classOf_eq_zero_iff]
    exact familyFibre_tensor_inverse_algEquivZero π M hM t₀ t₁ N hN e
  exact add_right_cancel (h₀.trans h₁.symm)

/-- Parameter base change preserves the specialized sheaf. -/
def familyFibreBaseChangeIso {T' : Scheme.{u}} {h' : T' ⟶ Spec (.of K)}
    (p : SchemeHomOver h' h)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h') (M : (pullback π h).Modules) :
    familyFibre π ((Scheme.Modules.pullback (baseChangeSnd π p)).obj M) t ≅
      familyFibre π M (postComp p t) := by
  refine (Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr ?_).app M
  apply pullback.hom_ext <;>
    simp [familyFibreMap, baseChangeSnd, postComp, Category.assoc]

theorem familyClass_baseChange {T' : Scheme.{u}} {h' : T' ⟶ Spec (.of K)}
    (p : SchemeHomOver h' h)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h') (M : (pullback π h).Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    familyClass π ((Scheme.Modules.pullback (baseChangeSnd π p)).obj M)
      (hM.pullback _) t = familyClass π M hM (postComp p t) := by
  unfold familyClass
  congr 1
  exact (classOf_eq_iff _ _ _ _).mpr ⟨familyFibreBaseChangeIso π p t M⟩

end AlgebraicGeometry.SchemePicard
end
end

section
-- Reused implementation: Solutions.PhilipponReducedParameterCover

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicEquivalenceFamilies
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.IdealSheafData NeronModelInfra RelPicard
open TopologicalSpace
universe u

/-- A morphism from a reduced scheme factors through the reduced closed
subscheme determined by any closed set containing its image. -/
theorem exists_lift_reduced_closed {Y T : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ T) (Z : TopologicalSpace.Closeds T)
    (hf : Set.range f ⊆ Z) :
    ∃ g : Y ⟶ (vanishingIdeal Z).subscheme,
      g ≫ (vanishingIdeal Z).subschemeι = f := by
  have hker : f.ker = vanishingIdeal (.closure (Set.range f)) := by
    rw [← map_bot, ← Scheme.nilradical_eq_bot, ← vanishingIdeal_top,
      map_vanishingIdeal]
    congr 1
    simp
  have hle : (vanishingIdeal Z).subschemeι.ker ≤ f.ker := by
    rw [ker_subschemeι, hker]
    apply vanishingIdeal_antimono
    exact TopologicalSpace.Closeds.closure_le.mpr hf
  exact ⟨IsClosedImmersion.lift _ f hle, IsClosedImmersion.lift_fac _ f hle⟩

/-- Finitely many integral closed parameter schemes cover every rational
parameter point. Reduction is essential because parameter schemes can
carry nilpotents. -/
theorem exists_finite_integral_parameter_cover
    {K : Type u} [Field K] {T : Scheme.{u}} [NoetherianSpace T]
    (h : T ⟶ Spec (.of K)) :
    ∃ (ι : Type u) (_ : Finite ι) (C : ι → Scheme.{u})
      (c : ∀ i, C i ⟶ T),
      (∀ i, IsIntegral (C i)) ∧ (∀ i, IsClosedImmersion (c i)) ∧
        ∀ t : SchemeHomOver (𝟙 (Spec (.of K))) h,
          ∃ i, ∃ s : SchemeHomOver (𝟙 (Spec (.of K))) (c i ≫ h),
            postComp (⟨c i, rfl⟩ : SchemeHomOver (c i ≫ h) h) s = t := by
  classical
  obtain ⟨S, hS, hcover⟩ :=
    NoetherianSpace.exists_finset_irreducible (⊤ : TopologicalSpace.Closeds T)
  let C (i : S) := (vanishingIdeal i.val).subscheme
  let c (i : S) : C i ⟶ T := (vanishingIdeal i.val).subschemeι
  refine ⟨S, inferInstance, C, c, ?_, ?_, ?_⟩
  · exact fun i => Scheme.isIntegral_subscheme_vanishingIdeal i.val (hS i)
  · intro i
    exact inferInstanceAs (IsClosedImmersion (vanishingIdeal i.val).subschemeι)
  · intro t
    let x₀ : Spec (.of K) := Classical.choice inferInstance
    have hx : t.1 x₀ ∈ (S.sup id : TopologicalSpace.Closeds T) := by
      rw [← hcover]
      trivial
    have hx' : ∃ Z ∈ S, t.1 x₀ ∈ (Z : Set T) := by
      change t.1 x₀ ∈ ((S.sup id : TopologicalSpace.Closeds T) : Set T) at hx
      rw [TopologicalSpace.Closeds.coe_finset_sup] at hx
      rw [Finset.sup_eq_iSup] at hx
      change t.1 x₀ ∈ ⋃ Z ∈ S, (Z : Set T) at hx
      simpa only [Set.mem_iUnion, exists_prop] using hx
    obtain ⟨Z, hZ, hxZ⟩ := hx'
    have hrange : Set.range t.1 ⊆ (Z : Set T) := by
      rintro _ ⟨x, rfl⟩
      simpa only [Subsingleton.elim x x₀] using hxZ
    obtain ⟨g, hg⟩ := exists_lift_reduced_closed t.1 Z hrange
    refine ⟨⟨Z, hZ⟩, ⟨g, ?_⟩, ?_⟩
    · change g ≫ ((vanishingIdeal Z).subschemeι ≫ h) = 𝟙 _
      rw [← Category.assoc, hg]
      exact t.2
    · apply Subtype.ext
      exact hg

end PhilipponMultiplicity.AlgebraicEquivalenceFamilies
end
end

section
-- Reused implementation: Solutions.PhilipponFiniteParameterClasses

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra RelPicard
open TopologicalSpace PhilipponMultiplicity.AlgebraicEquivalenceFamilies
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (h : T ⟶ Spec (.of K))

/-- A noetherian parameter scheme of locally finite type carries only
finitely many fibre classes modulo algebraic equivalence. This uses the
actual fibres and the defining integral parameter families. -/
theorem familyClass_range_finite_of_noetherian [NoetherianSpace T]
    [LocallyOfFiniteType h]
    (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M) :
    (Set.range (familyClass π M hM)).Finite := by
  obtain ⟨ι, hι, C, c, hC, hc, hcover⟩ := exists_finite_integral_parameter_cover h
  letI := hι
  let p (i : ι) : SchemeHomOver (c i ≫ h) h := ⟨c i, rfl⟩
  let M' (i : ι) := (Scheme.Modules.pullback (baseChangeSnd π (p i))).obj M
  have hM' (i : ι) : Scheme.Modules.IsInvertible (M' i) := hM.pullback _
  have hfinite (i : ι) : (Set.range (familyClass π (M' i) (hM' i))).Finite := by
    letI := hC i
    letI := hc i
    letI : GeometricallyIntegral (c i ≫ h) := geometricallyIntegral_of_isAlgClosed _
    apply Set.Subsingleton.finite
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact familyClass_eq π (M' i) (hM' i) s t
  apply (Set.finite_iUnion hfinite).subset
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, s, hs⟩ := hcover t
  apply Set.mem_iUnion.mpr
  refine ⟨i, s, ?_⟩
  change familyClass π ((Scheme.Modules.pullback (baseChangeSnd π (p i))).obj M)
    (hM.pullback _) s = familyClass π M hM t
  rw [familyClass_baseChange, hs]

/-- In particular, every finite-type parameter family has finite image
in the Néron--Severi group, without any properness assumption on `X`. -/
theorem familyClass_range_finite [LocallyOfFiniteType h] [QuasiCompact h]
    (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M) :
    (Set.range (familyClass π M hM)).Finite := by
  letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
  letI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace h
  letI : IsNoetherian T := ⟨⟩
  exact familyClass_range_finite_of_noetherian π h M hM

end AlgebraicGeometry.SchemePicard
end
end

section
-- Reused implementation: Solutions.PhilipponFiniteFamilyWitnesses

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra RelPicard
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K))

/-- Equality in the concrete quotient gives an actual algebraically
trivial tensor difference, without a finiteness assumption. -/
theorem exists_tensor_difference_of_classMap_eq
    (M N : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N)
    (he : classMap π (classOf M hM) = classMap π (classOf N hN)) :
    ∃ L : X.Modules, Scheme.Modules.IsInvertible L ∧ IsAlgEquivZero π L ∧
      Nonempty (M ≅ L ⊗ N) := by
  let a := classOf M hM - classOf N hN
  have ha : classMap π a = 0 := by simp only [a, map_sub, he, sub_self]
  refine ⟨representative a, representative_isInvertible a, ?_, ?_⟩
  · apply (classMap_classOf_eq_zero_iff π (representative a)
      (representative_isInvertible a)).mp
    rwa [classOf_representative]
  · apply (classOf_eq_iff _ _ hM
      ((representative_isInvertible a).tensor_monoidalV2 hN)).mp
    rw [classOf_tensor (representative a) N (representative_isInvertible a) hN,
      classOf_representative]
    exact (sub_add_cancel _ _).symm

end AlgebraicGeometry.SchemePicard

namespace AlgebraicGeometry.RelPicard
open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra SchemePicard
universe u

/-- A finite-type family has finitely many fibres up to algebraically
trivial tensor differences. The conclusion is stated using the original
base-change sheaves and the existing concrete definition of algebraic equivalence. -/
theorem exists_finite_fibre_representatives_of_parameter_finiteType_proof
    (K : Type u) [Field K] [IsAlgClosed K] {X T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (h : T ⟶ Spec (.of K))
    [LocallyOfFiniteType h] [QuasiCompact h]
    (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ s : Finset (SchemeHomOver (𝟙 (Spec (.of K))) h),
      ∀ t : SchemeHomOver (𝟙 (Spec (.of K))) h, ∃ r ∈ s,
        ∃ N : X.Modules, Scheme.Modules.IsInvertible N ∧ IsAlgEquivZero π N ∧
          Nonempty ((Scheme.Modules.pullback (baseChangeSnd π t)).obj M ≅
            (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj N ⊗
              (Scheme.Modules.pullback (baseChangeSnd π r)).obj M) := by
  classical
  let I := Set.range (familyClass π M hM)
  have hI : I.Finite := familyClass_range_finite π h M hM
  letI : Fintype I := hI.fintype
  choose repr hrepr using fun a : I => a.property
  refine ⟨Finset.univ.image repr, ?_⟩
  intro t
  let a : I := ⟨familyClass π M hM t, ⟨t, rfl⟩⟩
  refine ⟨repr a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ?_⟩
  have he : familyClass π M hM t = familyClass π M hM (repr a) := (hrepr a).symm
  obtain ⟨N, hN, hzero, ⟨e⟩⟩ := exists_tensor_difference_of_classMap_eq π
    (familyFibre π M t) (familyFibre π M (repr a))
    (familyFibre_isInvertible π M hM t) (familyFibre_isInvertible π M hM (repr a)) he
  refine ⟨N, hN, hzero, ⟨?_⟩⟩
  exact familyFibreIso π M t ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ (familyFibreIso π M (repr a)).symm)

end AlgebraicGeometry.RelPicard
end
end

open AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory CategoryTheory.Limits
open MonoidalCategory NeronModelInfra
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (h : T ⟶ Spec (.of K))
    [LocallyOfFiniteType h] [QuasiCompact h]
    (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ s : Finset (SchemeHomOver (𝟙 (Spec (.of K))) h),
      ∀ t : SchemeHomOver (𝟙 (Spec (.of K))) h, ∃ r ∈ s,
        ∃ N : X.Modules, Scheme.Modules.IsInvertible N ∧ IsAlgEquivZero π N ∧
          Nonempty ((Scheme.Modules.pullback (baseChangeSnd π t)).obj M ≅
            (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj N ⊗
              (Scheme.Modules.pullback (baseChangeSnd π r)).obj M) := by
  exact exists_finite_fibre_representatives_of_parameter_finiteType_proof K π h M hM
