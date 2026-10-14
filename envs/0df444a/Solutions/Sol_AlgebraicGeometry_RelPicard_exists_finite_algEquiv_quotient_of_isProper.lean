-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_finite_algEquiv_quotient_of_isProper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:45:31.884996+00:00
-- url     : https://prove2.me/submissions/7ca45f57-def5-429d-92e6-db20fcd21a0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.Noetherian.Basic
import Theorems.Thm_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_bounded_numerically_trivial_family_of_isProper
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_curve_degree_tests_of_isProper
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_fibre_representatives_of_parameter_finiteType
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

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
-- Reused implementation: Solutions.PhilipponSchemePicardClassification

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory MonoidalCategory
open PhilipponMultiplicity
universe u v
variable {X : Scheme.{u}} {L : Type v} [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l))

/-- An integer family with tensor-compatible classes gives its actual
class homomorphism to the Picard group. -/
def familyAddHom : L →+ Group X where
  toFun := fun l => classOf (ℓ l) (hℓ l)
  map_zero' := by
    apply value_injective
    change toSkeleton (ℓ 0) = 1
    rw [hclass, ofAdd_zero, map_one]
  map_add' := by
    intro l m
    apply value_injective
    change toSkeleton (ℓ (l + m)) = toSkeleton (ℓ l) * toSkeleton (ℓ m)
    rw [hclass, hclass, hclass, ofAdd_add, map_mul]

def familyLinearMap : L →ₗ[ℤ] Group X where
  toFun := familyAddHom φ ℓ hℓ hclass
  map_add' := (familyAddHom φ ℓ hℓ hclass).map_add
  map_smul' := fun n l =>
    (congrArg (familyAddHom φ ℓ hℓ hclass)
      (int_smul_eq_zsmul (inferInstance : Module ℤ L) n l)).trans
        (map_zsmul (familyAddHom φ ℓ hℓ hclass) n l)

variable {K : Type u} [Field K] (π : X ⟶ Spec (.of K))

def familyClassMap : L →ₗ[ℤ] NeronSeveri π :=
  (classMap π).comp (familyLinearMap φ ℓ hℓ hclass)

theorem familyClassMap_eq_zero_iff (l : L) :
    familyClassMap φ ℓ hℓ hclass π l = 0 ↔ RelPicard.IsAlgEquivZero π (ℓ l) :=
  classMap_classOf_eq_zero_iff π (ℓ l) (hℓ l)

/-- The family quotient is exactly the image of its genuine class map to
the Néron--Severi group, with no geometric finiteness assumption. -/
theorem familyClassMap_ker :
    LinearMap.ker (familyClassMap φ ℓ hℓ hclass π) =
      AlgebraicEquivalenceFamilies.algebraicKernel π φ ℓ hℓ hclass := by
  ext l
  exact familyClassMap_eq_zero_iff φ ℓ hℓ hclass π l

include φ hℓ hclass in
/-- Néron--Severi finite generation supplies exactly the published target's
finite quotient, including the universe-zero image and family witnesses. -/
theorem exists_finite_algEquiv_quotient_of_finite_neronSeveri
    [Module.Finite ℤ (NeronSeveri π)] :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∃ N : X.Modules,
        Scheme.Modules.IsInvertible N ∧ RelPicard.IsAlgEquivZero π N ∧
          Nonempty (ℓ x ≅ N ⊗ ℓ y) := by
  apply FiniteAlgEquivQuotient.of_finite_classification π φ ℓ hℓ hclass
    (familyClassMap φ ℓ hℓ hclass π)
  intro l hl
  exact (familyClassMap_eq_zero_iff φ ℓ hℓ hclass π l).mp hl

end AlgebraicGeometry.SchemePicard
end
end

section
-- Reused implementation: Solutions.PhilipponCurveNeronSeveri

set_option autoImplicit false
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory MonoidalCategory
universe u v
variable {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (𝒱 : X.TwoAffineOpenCover)

/-- The actual two-chart Euler characteristic, with the existing section
modules and their existing kernel and cokernel. -/
def curveEuler (M : X.Modules) : ℤ :=
  (Module.finrank K (𝒱.sectionsOf π M).H0 : ℤ) -
    Module.finrank K (𝒱.sectionsOf π M).H1

theorem curveEuler_iso {M N : X.Modules} (e : M ≅ N) :
    curveEuler π 𝒱 M = curveEuler π 𝒱 N := by
  obtain ⟨𝒲, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso π π
      (Iso.refl X) (by simp) 𝒱 N M (e ≪≫ ((Scheme.Modules.pullbackId X).app N).symm)
  have h0' : 𝒲.U0 = 𝒱.U0 := by simpa using h0
  have h1' : 𝒲.U1 = 𝒱.U1 := by simpa using h1
  have hW : 𝒲 = 𝒱 := by
    cases 𝒲
    cases 𝒱
    simp_all
  subst 𝒲
  unfold curveEuler
  rw [e0.finrank_eq, e1.finrank_eq]

/-- Euler degree on genuine isomorphism classes of invertible sheaves. -/
def curveDegree (a : Group X) : ℤ :=
  curveEuler π 𝒱 (representative a) - curveEuler π 𝒱 (𝟙_ X.Modules)

theorem curveDegree_classOf (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    curveDegree π 𝒱 (classOf M hM) =
      curveEuler π 𝒱 M - curveEuler π 𝒱 (𝟙_ X.Modules) := by
  have h : toSkeleton (representative (classOf M hM)) = toSkeleton M :=
    representative_value _
  exact congrArg (fun t => t - curveEuler π 𝒱 (𝟙_ X.Modules))
    (curveEuler_iso π 𝒱 (toSkeleton_eq_toSkeleton_iff.mp h).some)

theorem curveDegree_zero : curveDegree π 𝒱 (0 : Group X) = 0 := by
  have h : toSkeleton (representative (0 : Group X)) = toSkeleton (𝟙_ X.Modules) :=
    representative_value _
  unfold curveDegree
  rw [curveEuler_iso π 𝒱 (toSkeleton_eq_toSkeleton_iff.mp h).some, sub_self]

variable [IsAlgClosed K] [IsIntegral X] [IsProper π] [SmoothOfRelativeDimension 1 π]

theorem curveDegree_add (a b : Group X) :
    curveDegree π 𝒱 (a + b) = curveDegree π 𝒱 a + curveDegree π 𝒱 b := by
  have h : toSkeleton (representative (a + b)) =
      toSkeleton (representative a ⊗ representative b) := by
    rw [Skeleton.toSkeleton_tensorObj, representative_value, representative_value,
      representative_value, value_add]
  have he := curveEuler_iso π 𝒱 (toSkeleton_eq_toSkeleton_iff.mp h).some
  have ht := Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub K π
    (representative a) (representative b)
    (representative_isInvertible a) (representative_isInvertible b) 𝒱
  change curveEuler π 𝒱 (representative a ⊗ representative b) =
    curveEuler π 𝒱 (representative a) + curveEuler π 𝒱 (representative b) -
      curveEuler π 𝒱 (𝟙_ X.Modules) at ht
  unfold curveDegree
  rw [he, ht]
  omega

def curveDegreeHom : Group X →ₗ[ℤ] ℤ :=
  ({ toFun := curveDegree π 𝒱
     map_zero' := curveDegree_zero π 𝒱
     map_add' := curveDegree_add π 𝒱 } : Group X →+ ℤ).toIntLinearMap

theorem curveDegree_eq_zero_iff (a : Group X) :
    curveDegree π 𝒱 a = 0 ↔ RelPicard.IsAlgEquivZero π (representative a) := by
  rw [curveDegree, sub_eq_zero]
  exact (RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq K π
    (representative a) (representative_isInvertible a) 𝒱).symm

/-- On a smooth proper integral curve, algebraic equivalence is exactly
the kernel of the integer Euler-degree map. -/
theorem curveDegreeHom_ker : LinearMap.ker (curveDegreeHom π 𝒱) = picardZero π := by
  ext a
  exact curveDegree_eq_zero_iff π 𝒱 a

/-- The concrete Néron--Severi group embeds in the integers. -/
def neronSeveriCurveDegree : NeronSeveri π →ₗ[ℤ] ℤ :=
  (picardZero π).liftQ (curveDegreeHom π 𝒱) (curveDegreeHom_ker π 𝒱).ge

theorem neronSeveriCurveDegree_injective :
    Function.Injective (neronSeveriCurveDegree π 𝒱) := by
  apply LinearMap.ker_eq_bot.mp
  exact (picardZero π).ker_liftQ_eq_bot' (curveDegreeHom π 𝒱)
    (curveDegreeHom_ker π 𝒱).symm

include 𝒱 in
/-- Néron--Severi finite generation for smooth proper integral curves,
proved from the existing curve Euler theorems and Noetherianity of ℤ. -/
theorem finite_neronSeveri_of_smoothProperCurve : Module.Finite ℤ (NeronSeveri π) :=
  Module.Finite.of_injective (neronSeveriCurveDegree π 𝒱)
    (neronSeveriCurveDegree_injective π 𝒱)

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
-- Reused implementation: Solutions.PhilipponSchemePicardPullback

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SchemePicard
open CategoryTheory MonoidalCategory
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback of the actual Picard group, obtained by reusing the class map
of the tensor-compatible family of pulled-back representatives. -/
def pullback : Group Y →ₗ[ℤ] Group X :=
  familyLinearMap ((Skeleton.monoidHom (Scheme.Modules.pullback f)).comp (classHom Y))
    (fun a => (Scheme.Modules.pullback f).obj (representative a))
    (fun a => (representative_isInvertible a).pullback f)
    (fun a => by
      rw [← Functor.mapSkeleton_obj_toSkeleton, representative_class]
      rfl)

theorem pullback_classOf (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) :
    pullback f (classOf M hM) =
      classOf ((Scheme.Modules.pullback f).obj M) (hM.pullback f) := by
  apply value_injective
  change toSkeleton ((Scheme.Modules.pullback f).obj (representative (classOf M hM))) = _
  rw [← Functor.mapSkeleton_obj_toSkeleton, representative_value]
  exact Functor.mapSkeleton_obj_toSkeleton (Scheme.Modules.pullback f) M

theorem pullback_representative (a : Group Y) :
    pullback f a = classOf ((Scheme.Modules.pullback f).obj (representative a))
      ((representative_isInvertible a).pullback f) := rfl

end AlgebraicGeometry.SchemePicard
end
end

section
-- Reused implementation: Solutions.PhilipponNeronSeveriGeometricReduction

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace AlgebraicGeometry.SchemePicard.GeometricReduction
open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open PhilipponMultiplicity
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K))

def degreeHom (t : CurveDegreeTests.Probe π) : Group X →ₗ[ℤ] ℤ :=
  (curveDegreeHom t.toBase t.cover).comp (SchemePicard.pullback t.toScheme)

theorem degreeHom_classOf (t : CurveDegreeTests.Probe π)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    degreeHom π t (classOf M hM) = t.degree M := by
  change curveDegree t.toBase t.cover (SchemePicard.pullback t.toScheme (classOf M hM)) = _
  rw [pullback_classOf, curveDegree_classOf]
  rfl

def numericalKernel : Submodule ℤ (Group X) :=
  ⨅ t : CurveDegreeTests.Probe π, LinearMap.ker (degreeHom π t)

theorem mem_numericalKernel (a : Group X) :
    a ∈ numericalKernel π ↔ ∀ t, degreeHom π t a = 0 := by
  simp [numericalKernel]

theorem numericalKernel_representative (a : Group X) :
    a ∈ numericalKernel π ↔ CurveDegreeTests.NumericallyTrivial π (representative a) := by
  rw [mem_numericalKernel]
  apply forall_congr'
  intro t
  rw [← degreeHom_classOf π t _ (representative_isInvertible a), classOf_representative]

theorem picardZero_le_numericalKernel : picardZero π ≤ numericalKernel π := by
  intro a ha
  change RelPicard.IsAlgEquivZero π (representative a) at ha
  rw [mem_numericalKernel]
  intro t
  change curveDegree t.toBase t.cover (SchemePicard.pullback t.toScheme a) = 0
  rw [pullback_representative, curveDegree_classOf, sub_eq_zero]
  exact (RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq K t.toBase _
    ((representative_isInvertible a).pullback t.toScheme) t.cover).mp
      (ha.pullback t.toScheme t.over_base)

abbrev NumericalQuotient := Group X ⧸ numericalKernel π

def numericalMap : NeronSeveri π →ₗ[ℤ] NumericalQuotient π :=
  (picardZero π).liftQ (numericalKernel π).mkQ (by
    rw [Submodule.ker_mkQ]
    exact picardZero_le_numericalKernel π)

theorem numericalMap_surjective : Function.Surjective (numericalMap π) := by
  intro z
  obtain ⟨a, rfl⟩ := (numericalKernel π).mkQ_surjective z
  exact ⟨classMap π a, rfl⟩

/-- Finite curve detection embeds the numerical quotient into a finite
integer lattice; no assertion about the algebraic-equivalence kernel is used. -/
theorem finite_numericalQuotient_of_finite_tests
    (s : Finset (CurveDegreeTests.Probe π))
    (hs : ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
      (∀ t ∈ s, t.degree M = 0) → CurveDegreeTests.NumericallyTrivial π M) :
    Module.Finite ℤ (NumericalQuotient π) := by
  classical
  let q : Group X →ₗ[ℤ] (s → ℤ) := LinearMap.pi fun t => degreeHom π t.val
  have hk : LinearMap.ker q = numericalKernel π := by
    ext a
    rw [LinearMap.mem_ker, numericalKernel_representative]
    constructor
    · intro ha
      apply hs _ (representative_isInvertible a)
      intro t ht
      rw [← degreeHom_classOf π t _ (representative_isInvertible a), classOf_representative]
      exact congrFun ha ⟨t, ht⟩
    · intro ha
      funext t
      have h := ha t.val
      rw [← degreeHom_classOf π t.val _ (representative_isInvertible a), classOf_representative] at h
      exact h
  let f : NumericalQuotient π →ₗ[ℤ] (s → ℤ) := (numericalKernel π).liftQ q hk.ge
  apply Module.Finite.of_injective f
  intro a b hab
  obtain ⟨x, rfl⟩ := (numericalKernel π).mkQ_surjective a
  obtain ⟨y, rfl⟩ := (numericalKernel π).mkQ_surjective b
  apply (Submodule.Quotient.eq (numericalKernel π)).mpr
  rw [← hk, LinearMap.mem_ker, map_sub]
  exact sub_eq_zero.mpr hab

/-- Pullback to the product with the base field reflects isomorphisms. -/
def reflect_base_iso {A B : X.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj A ≅
      (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj B) : A ≅ B := by
  let j : X ⟶ Limits.pullback π (𝟙 (Spec (.of K))) :=
    pullback.lift (𝟙 X) π (by simp)
  let undo (M : X.Modules) :
      (Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (by simp [j])).app M ≪≫
        (Scheme.Modules.pullbackId X).app M
  exact (undo A).symm ≪≫ (Scheme.Modules.pullback j).mapIso e ≪≫ undo B

/-- Reuse the public finite-family theorem with its exact base-change
conclusion to obtain a finite image in the concrete quotient. -/
theorem finite_family_image {T : Scheme.{u}} (h : T ⟶ Spec (.of K))
    [LocallyOfFiniteType h] [QuasiCompact h]
    (M : (Limits.pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M) :
    (Set.range (familyClass π M hM)).Finite := by
  classical
  obtain ⟨s, hs⟩ := RelPicard.exists_finite_fibre_representatives_of_parameter_finiteType K π h M hM
  apply (s.finite_toSet.image (familyClass π M hM)).subset
  rintro _ ⟨t, rfl⟩
  obtain ⟨r, hr, N, hN, hzero, ⟨e⟩⟩ := hs t
  refine ⟨r, hr, ?_⟩
  let e' : familyFibre π M t ≅ N ⊗ familyFibre π M r :=
    reflect_base_iso π ((familyFibreIso π M t).symm ≪≫ e ≪≫
      (Iso.refl _ ⊗ᵢ familyFibreIso π M r) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm)
  have he := (classOf_eq_iff _ _ (familyFibre_isInvertible π M hM t)
    (hN.tensor_monoidalV2 (familyFibre_isInvertible π M hM r))).mpr ⟨e'⟩
  have hn : classMap π (classOf N hN) = 0 := (classMap_classOf_eq_zero_iff π N hN).mpr hzero
  have hc := congrArg (classMap π) he
  rw [classOf_tensor _ _ hN (familyFibre_isInvertible π M hM r), map_add, hn, zero_add] at hc
  exact hc.symm

/-- Boundedness gives a finite numerical kernel modulo algebraic equivalence. -/
theorem finite_kernel_of_bounded_family {T : Scheme.{u}} (h : T ⟶ Spec (.of K))
    [LocallyOfFiniteType h] [QuasiCompact h]
    (M : (Limits.pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hcover : ∀ N : X.Modules, Scheme.Modules.IsInvertible N →
      CurveDegreeTests.NumericallyTrivial π N →
        ∃ t : SchemeHomOver (𝟙 (Spec (.of K))) h,
          Nonempty (CurveDegreeTests.fibre h M t ≅ N)) :
    Finite (LinearMap.ker (numericalMap π)) := by
  apply (Set.finite_range_iff
    (Subtype.val_injective (p := fun a => a ∈ LinearMap.ker (numericalMap π)))).mp
  apply (finite_family_image π h M hM).subset
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := classMap_surjective π a.val
  have hn : b ∈ numericalKernel π := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change numericalMap π (classMap π b) = 0
    rw [hb]
    exact a.property
  obtain ⟨t, ⟨e⟩⟩ := hcover (representative b) (representative_isInvertible b)
    ((numericalKernel_representative π b).mp hn)
  refine ⟨t, ?_⟩
  have he := (classOf_eq_iff _ _ (familyFibre_isInvertible π M hM t)
    (representative_isInvertible b)).mpr ⟨e⟩
  change classMap π (classOf (familyFibre π M t) _) = a.val
  rw [he, classOf_representative, hb]

theorem finite_neronSeveri_of_geometric_inputs [IsProper π] :
    Module.Finite ℤ (NeronSeveri π) := by
  obtain ⟨s, hs⟩ := RelPicard.exists_finite_curve_degree_tests_of_isProper K π
  letI := finite_numericalQuotient_of_finite_tests π s hs
  obtain ⟨T, h, hft, hqc, M, hM, hcover⟩ :=
    RelPicard.exists_bounded_numerically_trivial_family_of_isProper K π
  letI := hft
  letI := hqc
  letI := finite_kernel_of_bounded_family π h M hM hcover
  apply Module.Finite.of_exact (f := (LinearMap.ker (numericalMap π)).subtype)
    (g := numericalMap π) ?_ (numericalMap_surjective π)
  rw [LinearMap.exact_iff, Submodule.range_subtype]

end AlgebraicGeometry.SchemePicard.GeometricReduction

open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (L : Type u) [AddCommGroup L] [Module ℤ L]
    (φ : Multiplicative L →* Skeleton X.Modules)
    (ℓ : L → X.Modules) (hℓ : ∀ l, Scheme.Modules.IsInvertible (ℓ l))
    (hclass : ∀ l, toSkeleton (ℓ l) = φ (Multiplicative.ofAdd l)) :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ A) (_ : Module.Finite ℤ A)
      (q : L →ₗ[ℤ] A), Function.Surjective q ∧
      ∀ x y, q x = q y → ∃ N : X.Modules,
        Scheme.Modules.IsInvertible N ∧ RelPicard.IsAlgEquivZero π N ∧
          Nonempty (ℓ x ≅ N ⊗ ℓ y) := by
  letI := SchemePicard.GeometricReduction.finite_neronSeveri_of_geometric_inputs π
  exact SchemePicard.exists_finite_algEquiv_quotient_of_finite_neronSeveri φ ℓ hℓ hclass π
end
end
