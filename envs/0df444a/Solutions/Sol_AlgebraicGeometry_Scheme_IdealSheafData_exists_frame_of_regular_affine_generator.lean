-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.exists_frame_of_regular_affine_generator
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-07T12:45:33.084929+00:00
-- url     : https://prove2.me/submissions/df936ac7-bf54-435f-846c-a1e6b1530074

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_MvPolynomial_CrossingResolution
import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective

universe u v

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponIdealModuleSections

variable {X : Scheme.{u}} (I : X.IdealSheafData)

lemma app_injective (U : X.Opens) : Function.Injective (I.moduleι.app U) := by
  haveI : Mono I.moduleι := by
    dsimp only [Scheme.IdealSheafData.moduleι]
    infer_instance
  haveI : Mono ((Scheme.Modules.toPresheaf X).map I.moduleι) := inferInstance
  change Function.Injective (((Scheme.Modules.toPresheaf X).map I.moduleι).app (op U))
  rw [← AddCommGrpCat.mono_iff_injective]
  infer_instance

lemma app_res {U V : X.Opens} (h : U ≤ V) (s : Γ(I.module, V)) :
    I.moduleι.app U (I.module.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (I.moduleι.app V s) := by
  exact congrArg (fun f => f s) (I.moduleι.mapPresheaf.naturality (homOfLE h).op)

/-- Affine membership in the registered ideal gives a unique actual
section of its registered kernel module on an arbitrary open. -/
theorem existsUnique_lift (U : X.Opens) (r : Γ(X, U))
    (hr : ∀ (W : X.affineOpens) (h : (W : X.Opens) ≤ U),
      (X.presheaf.map (homOfLE h).op).hom r ∈ I.ideal W) :
    ∃! s : Γ(I.module, U), I.moduleι.app U s = r := by
  choose V haff hxV hVU using fun x : U => exists_isAffineOpen_mem_and_subset x.prop
  let A : U → X.affineOpens := fun x => ⟨V x, haff x⟩
  have hcover : U ≤ ⨆ x, V x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hex : ∀ x : U, ∃ s : Γ(I.module, V x),
      I.moduleι.app (V x) s = (X.presheaf.map (homOfLE (hVU x)).op).hom r := by
    intro x
    have hm : (X.presheaf.map (homOfLE (hVU x)).op).hom r ∈
        (I.ideal (A x) : Set Γ(X, A x)) := hr (A x) (hVU x)
    rw [← (I.range_moduleIota_app_and_injective (A x)).1] at hm
    exact hm
  choose s hs using hex
  have hcompat : TopCat.Presheaf.IsCompatible I.module.presheaf V s := by
    intro x y
    apply app_injective I (V x ⊓ V y)
    change I.moduleι.app _ (I.module.presheaf.map (homOfLE inf_le_left).op (s x)) =
      I.moduleι.app _ (I.module.presheaf.map (homOfLE inf_le_right).op (s y))
    rw [app_res, app_res, hs, hs]
    change (X.presheaf.map (homOfLE (hVU x)).op ≫
      X.presheaf.map (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)).op) r =
      (X.presheaf.map (homOfLE (hVU y)).op ≫
        X.presheaf.map (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)).op) r
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl
  let MS : TopCat.Sheaf AddCommGrpCat X := ⟨I.module.presheaf, I.module.isSheaf⟩
  obtain ⟨z, hz, -⟩ := MS.existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) hcover s hcompat
  have hzr : I.moduleι.app U z = r := by
    apply X.sheaf.eq_of_locally_eq' V U (fun x => homOfLE (hVU x)) hcover
    intro x
    change X.presheaf.map (homOfLE (hVU x)).op (I.moduleι.app U z) =
      X.presheaf.map (homOfLE (hVU x)).op r
    exact (app_res I (hVU x) z).symm.trans
      ((congrArg (I.moduleι.app (V x)) (hz x)).trans (hs x))
  exact ⟨z, hzr, fun t ht => app_injective I U (ht.trans hzr.symm)⟩

end PhilipponIdealModuleSections

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace


namespace PhilipponCartierSections

variable {X : Scheme.{u}}

abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma res_res {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (s : Γ(X, U)) :
    res k (res h s) = res (k.trans h) s := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom s = _
  rw [← Functor.map_comp]
  rfl

/-- A section regular at every germ is regular on the whole open set. -/
theorem regular_of_germs {U : X.Opens} (r : Γ(X, U))
    (hr : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    r ∈ nonZeroDivisors Γ(X, U) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro s hs
  apply TopCat.Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0
  rw [map_zero]
  apply (mem_nonZeroDivisors_iff_left.mp (hr x hx))
  simpa only [map_mul, map_zero] using congrArg (X.presheaf.germ U x hx) hs

lemma regular_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U))
    (hr : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    res h r ∈ nonZeroDivisors Γ(X, V) := by
  apply regular_of_germs
  intro x hx
  simpa only [res, TopCat.Presheaf.germ_res_apply] using hr x (h hx)

/-- Divisibility of two germs spreads to an actual quotient on a neighborhood. -/
lemma exists_local_quotient {U : X.Opens} (r t : Γ(X, U)) (x : X) (hx : x ∈ U)
    (hdiv : ∃ s : X.presheaf.stalk x,
      X.presheaf.germ U x hx r * s = X.presheaf.germ U x hx t) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ s : Γ(X, V), res hVU r * s = res hVU t := by
  obtain ⟨s, hs⟩ := hdiv
  obtain ⟨V, hVU, hxV, v, hv⟩ := X.presheaf.exists_le_germ_eq s hx
  have hg : X.presheaf.germ V x hxV (res hVU r * v) =
      X.presheaf.germ V x hxV (res hVU t) := by
    rw [map_mul, hv]
    simpa only [res, TopCat.Presheaf.germ_res_apply] using hs
  obtain ⟨W, hxW, j, k, heq⟩ := X.presheaf.germ_eq x hxV hxV _ _ hg
  have hjk : k = j := Subsingleton.elim _ _
  subst k
  refine ⟨W, j.le.trans hVU, hxW, res j.le v, ?_⟩
  have heq' : res j.le (res hVU r * v) = res j.le (res hVU t) := heq
  simpa only [map_mul, res_res] using heq'

/-- Germwise division by a regular section gives a unique actual section.
No affine, Noetherian, integral or reduced hypothesis on the scheme is used. -/
theorem existsUnique_quotient {U : X.Opens} (r t : Γ(X, U))
    (hr : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x))
    (hdiv : ∀ x (hx : x ∈ U), ∃ s : X.presheaf.stalk x,
      X.presheaf.germ U x hx r * s = X.presheaf.germ U x hx t) :
    ∃! s : Γ(X, U), r * s = t := by
  choose V hVU hxV sf hsf using fun x : U => exists_local_quotient r t x.1 x.2 (hdiv x.1 x.2)
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro x y
    change res (inf_le_left : V x ⊓ V y ≤ V x) (sf x) =
      res (inf_le_right : V x ⊓ V y ≤ V y) (sf y)
    apply (isRegular_iff_mem_nonZeroDivisors.mpr
      (regular_res (inf_le_left.trans (hVU x) : V x ⊓ V y ≤ U) r hr)).left
    have hx := congrArg (res (inf_le_left : V x ⊓ V y ≤ V x)) (hsf x)
    have hy := congrArg (res (inf_le_right : V x ⊓ V y ≤ V y)) (hsf y)
    simp only [map_mul, res_res] at hx hy
    exact hx.trans hy.symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun x => homOfLE (hVU x)) hcover sf hcompat
  change Γ(X, U) at s
  have hst : r * s = t := by
    apply X.sheaf.eq_of_locally_eq' V U (fun x => homOfLE (hVU x)) hcover
    intro x
    change res (hVU x) (r * s) = res (hVU x) t
    have hxs : res (hVU x) s = sf x := hs x
    rw [map_mul, hxs]
    exact hsf x
  refine ⟨s, hst, ?_⟩
  intro z hz
  exact (isRegular_iff_mem_nonZeroDivisors.mpr (regular_of_germs r hr)).left (hz.trans hst.symm)

end PhilipponCartierSections

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial MvPolynomial.CrossingQuotient
open AlgebraicGeometry CategoryTheory
namespace PhilipponCrossingPointHom
variable {R : Type u} [CommRing R]
variable {A : Type*} [CommRing A]


lemma mk_C_eq_algebraMap (s : R) (r : R) : mk s (C r) = algebraMap R _ r :=
  (mk s).commutes r

theorem eval₂Hom_rel (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    eval₂Hom f ![a, b] (X 0 * X 1 - C s : MvPolynomial (Fin 2) R) = 0 := by
  rw [map_sub, map_mul, eval₂Hom_X', eval₂Hom_X', eval₂Hom_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]

noncomputable def pointHom (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    CrossingQuotient R s →+* A :=
  Ideal.Quotient.lift (Ideal.span {(X 0 * X 1 - C s : MvPolynomial (Fin 2) R)}) (eval₂Hom f ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, eval₂Hom_rel s f a b h, mul_zero])

theorem pointHom_mk (s : R) (f : R →+* A) (a b : A) (h : a * b = f s)
    (p : MvPolynomial (Fin 2) R) :
    pointHom s f a b h (mk s p) = eval₂Hom f ![a, b] p := rfl

theorem pointHom_algebraMap (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) (w : R) :
    pointHom s f a b h (algebraMap R _ w) = f w := by
  rw [← mk_C_eq_algebraMap, pointHom_mk, eval₂Hom_C]

theorem pointHom_U (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (U s) = a := by
  change pointHom s f a b h (mk s (X 0)) = a
  rw [pointHom_mk, eval₂Hom_X']
  rfl

theorem pointHom_V (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (V s) = b := by
  change pointHom s f a b h (mk s (X 1)) = b
  rw [pointHom_mk, eval₂Hom_X']
  rfl

theorem ringHom_ext {s : R} {f g : CrossingQuotient R s →+* A}
    (hR : ∀ w : R, f (algebraMap R _ w) = g (algebraMap R _ w))
    (hU : f (U s) = g (U s)) (hV : f (V s) = g (V s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change f (mk s (C w)) = g (mk s (C w))
    rw [mk_C_eq_algebraMap]
    exact hR w
  · intro j
    fin_cases j
    · exact hU
    · exact hV


lemma specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]


end PhilipponCrossingPointHom
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponNodeFactorCharts

variable {R : Type u} [CommRing R]

lemma chart_ext {t : R} {A : Type*} [CommRing A] [Algebra R A]
    {f g : CrossingQuotient R t →ₐ[R] A}
    (hU : f (U t) = g (U t)) (hV : f (V t) = g (V t)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hU
  · exact hV

def toLeft (a b : R) : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R a :=
  lift (a * b) (U a) (algebraMap R _ b * V a) (by
    rw [mul_left_comm, U_mul_V, map_mul]
    ring)

def toRight (a b : R) : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R b :=
  lift (a * b) (algebraMap R _ a * U b) (V b) (by
    rw [mul_assoc, U_mul_V, map_mul])

@[simp] lemma toLeft_U (a b : R) : toLeft a b (U (a * b)) = U a := lift_U _ _ _ _
@[simp] lemma toLeft_V (a b : R) :
    toLeft a b (V (a * b)) = algebraMap R _ b * V a := lift_V _ _ _ _
@[simp] lemma toRight_U (a b : R) :
    toRight a b (U (a * b)) = algebraMap R _ a * U b := lift_U _ _ _ _
@[simp] lemma toRight_V (a b : R) : toRight a b (V (a * b)) = V b := lift_V _ _ _ _

abbrev LeftOverlap (a : R) := Localization.Away (V a)
abbrev RightOverlap (b : R) := Localization.Away (U b)

def rightToLeftOverlap (a b : R) : CrossingQuotient R b →ₐ[R] LeftOverlap a :=
  lift b (IsLocalization.Away.invSelf (V a))
    (algebraMap R _ b * algebraMap (CrossingQuotient R a) _ (V a)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (V a)),
        IsLocalization.Away.mul_invSelf, mul_one])

def leftToRightOverlap (a b : R) : CrossingQuotient R a →ₐ[R] RightOverlap b :=
  lift a (algebraMap R _ a * algebraMap (CrossingQuotient R b) _ (U b))
    (IsLocalization.Away.invSelf (U b)) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one])

lemma leftToRight_isUnit (a b : R) : IsUnit ((leftToRightOverlap a b).toRingHom (V a)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, leftToRightOverlap, lift_V]
  exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (U b))

lemma rightToLeft_isUnit (a b : R) : IsUnit ((rightToLeftOverlap a b).toRingHom (U b)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rightToLeftOverlap, lift_U]
  exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V a))

def overlapToRightRing (a b : R) : LeftOverlap a →+* RightOverlap b :=
  IsLocalization.Away.lift (S := LeftOverlap a) (V a)
    (g := (leftToRightOverlap a b).toRingHom) (leftToRight_isUnit a b)

def overlapToLeftRing (a b : R) : RightOverlap b →+* LeftOverlap a :=
  IsLocalization.Away.lift (S := RightOverlap b) (U b)
    (g := (rightToLeftOverlap a b).toRingHom) (rightToLeft_isUnit a b)

lemma overlapToRightRing_algebraMap (a b : R) (z : CrossingQuotient R a) :
    overlapToRightRing a b (algebraMap _ _ z) = leftToRightOverlap a b z :=
  IsLocalization.Away.lift_eq (S := LeftOverlap a) _ (leftToRight_isUnit a b) z

lemma overlapToLeftRing_algebraMap (a b : R) (z : CrossingQuotient R b) :
    overlapToLeftRing a b (algebraMap _ _ z) = rightToLeftOverlap a b z :=
  IsLocalization.Away.lift_eq (S := RightOverlap b) _ (rightToLeft_isUnit a b) z

def overlapToRight (a b : R) : LeftOverlap a →ₐ[R] RightOverlap b :=
  { overlapToRightRing a b with
    commutes' := fun r => by
      change overlapToRightRing a b (algebraMap R (LeftOverlap a) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) r]
      rw [overlapToRightRing_algebraMap]
      exact (leftToRightOverlap a b).commutes r }

def overlapToLeft (a b : R) : RightOverlap b →ₐ[R] LeftOverlap a :=
  { overlapToLeftRing a b with
    commutes' := fun r => by
      change overlapToLeftRing a b (algebraMap R (RightOverlap b) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b) r]
      rw [overlapToLeftRing_algebraMap]
      exact (rightToLeftOverlap a b).commutes r }

@[simp] lemma overlapToRight_algebraMap (a b : R) (z : CrossingQuotient R a) :
    overlapToRight a b (algebraMap _ _ z) = leftToRightOverlap a b z :=
  overlapToRightRing_algebraMap a b z

@[simp] lemma overlapToLeft_algebraMap (a b : R) (z : CrossingQuotient R b) :
    overlapToLeft a b (algebraMap _ _ z) = rightToLeftOverlap a b z :=
  overlapToLeftRing_algebraMap a b z

lemma overlapToRight_inv (a b : R) :
    overlapToRight a b (IsLocalization.Away.invSelf (V a)) =
      algebraMap (CrossingQuotient R b) (RightOverlap b) (U b) := by
  have h := congrArg (overlapToRight a b) (IsLocalization.Away.mul_invSelf (V a))
  simp only [map_mul, overlapToRight_algebraMap, leftToRightOverlap, lift_V, map_one] at h
  have h' := IsLocalization.Away.mul_invSelf (S := RightOverlap b) (U b)
  linear_combination (algebraMap (CrossingQuotient R b) (RightOverlap b) (U b)) * h -
    (overlapToRight a b (IsLocalization.Away.invSelf (V a))) * h'

lemma overlapToLeft_inv (a b : R) :
    overlapToLeft a b (IsLocalization.Away.invSelf (U b)) =
      algebraMap (CrossingQuotient R a) (LeftOverlap a) (V a) := by
  have h := congrArg (overlapToLeft a b) (IsLocalization.Away.mul_invSelf (U b))
  simp only [map_mul, overlapToLeft_algebraMap, rightToLeftOverlap, lift_U, map_one] at h
  have h' := IsLocalization.Away.mul_invSelf (S := LeftOverlap a) (V a)
  linear_combination (algebraMap (CrossingQuotient R a) (LeftOverlap a) (V a)) * h -
    (overlapToLeft a b (IsLocalization.Away.invSelf (U b))) * h'

lemma overlap_left_right (a b : R) :
    (overlapToLeft a b).comp (overlapToRight a b) = AlgHom.id R (LeftOverlap a) := by
  have h : ((overlapToLeft a b).comp (overlapToRight a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)) =
      IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a) := by
    apply chart_ext
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToRight_algebraMap,
        leftToRightOverlap, lift_U, map_mul, AlgHom.commutes, overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_U]
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) a,
        ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToRight_algebraMap,
        leftToRightOverlap, lift_V, overlapToLeft_inv]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (V a)) (S := LeftOverlap a)
  exact RingHom.ext fun z => congrArg (fun f : CrossingQuotient R a →ₐ[R] LeftOverlap a => f z) h

lemma overlap_right_left (a b : R) :
    (overlapToRight a b).comp (overlapToLeft a b) = AlgHom.id R (RightOverlap b) := by
  have h : ((overlapToRight a b).comp (overlapToLeft a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R b) (RightOverlap b)) =
      IsScalarTower.toAlgHom R (CrossingQuotient R b) (RightOverlap b) := by
    apply chart_ext
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_U, overlapToRight_inv]
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_V, map_mul, AlgHom.commutes, overlapToRight_algebraMap,
        leftToRightOverlap, lift_V]
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b) b,
        ← U_mul_V, map_mul]
      rw [mul_comm (algebraMap _ _ (U b)), mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (U b)) (S := RightOverlap b)
  exact RingHom.ext fun z => congrArg (fun f : CrossingQuotient R b →ₐ[R] RightOverlap b => f z) h

def overlapEquiv (a b : R) : LeftOverlap a ≃ₐ[R] RightOverlap b :=
  AlgEquiv.ofAlgHom (overlapToRight a b) (overlapToLeft a b)
    (overlap_right_left a b) (overlap_left_right a b)

lemma charts_agree_on_overlap (a b : R) :
    (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)).comp (toLeft a b) =
      (rightToLeftOverlap a b).comp (toRight a b) := by
  apply chart_ext
  · simp only [AlgHom.comp_apply, toLeft_U, toRight_U, map_mul, AlgHom.commutes,
      rightToLeftOverlap, lift_U, IsScalarTower.coe_toAlgHom']
    symm
    rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) a,
      ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  · simp only [AlgHom.comp_apply, toLeft_V, toRight_V, map_mul, AlgHom.commutes,
      rightToLeftOverlap, lift_V, IsScalarTower.coe_toAlgHom']

end PhilipponNodeFactorCharts

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
open MvPolynomial MvPolynomial.CrossingQuotient


namespace PhilipponNodeCartierLocalLift

variable {A : Type v} [CommRing A]

lemma cancel_regular {r x y : A} (hr : r ∈ nonZeroDivisors A)
    (h : r * x = r * y) : x = y := by
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp hr) (x - y)
  rw [mul_sub, h, sub_self]

/-- A two-generated effective Cartier ideal in a local ring is generated by one
of its two specified generators. The chosen generator is a non-zero-divisor. -/
lemma regular_generator_or [IsLocalRing A] {u a r : A}
    (hI : Ideal.span ({u, a} : Set A) = Ideal.span ({r} : Set A))
    (hr : r ∈ nonZeroDivisors A) :
    (u ∈ nonZeroDivisors A ∧ u ∣ a) ∨
      (a ∈ nonZeroDivisors A ∧ a ∣ u) := by
  have hu : u ∈ Ideal.span ({r} : Set A) := by
    rw [← hI]
    exact Ideal.subset_span (by simp)
  have ha : a ∈ Ideal.span ({r} : Set A) := by
    rw [← hI]
    exact Ideal.subset_span (by simp)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hu
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp ha
  have hrI : r ∈ Ideal.span ({u, a} : Set A) := by
    rw [hI]
    exact Ideal.subset_span (by simp)
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.mp hrI
  have hst : p * s + q * t = 1 := by
    apply cancel_regular hr
    calc
      r * (p * s + q * t) = p * u + q * a := by rw [hs, ht]; ring
      _ = r * 1 := by simpa using hpq
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hst with hps | hqt
  · have hsunit : IsUnit s := isUnit_of_mul_isUnit_right hps
    left
    refine ⟨?_, ?_⟩
    · rw [hs]
      exact mul_mem_nonZeroDivisors.mpr ⟨hr, hsunit.mem_nonZeroDivisors⟩
    · obtain ⟨sunit, rfl⟩ := hsunit
      refine ⟨(sunit⁻¹ : Aˣ) * t, ?_⟩
      rw [hs, ht]
      simp [mul_assoc]
  · have htunit : IsUnit t := isUnit_of_mul_isUnit_right hqt
    right
    refine ⟨?_, ?_⟩
    · rw [ht]
      exact mul_mem_nonZeroDivisors.mpr ⟨hr, htunit.mem_nonZeroDivisors⟩
    · obtain ⟨tunit, rfl⟩ := htunit
      refine ⟨(tunit⁻¹ : Aˣ) * s, ?_⟩
      rw [hs, ht]
      simp [mul_assoc]

variable {R : Type u} [CommRing R]
open PhilipponNodeFactorCharts PhilipponCrossingPointHom

/-- In the chart where the pullback of `u` generates the Cartier ideal,
the map to the left nodal chart exists and is unique. -/
lemma existsUnique_left_lift (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (hu : ψ (U (a * b)) ∈ nonZeroDivisors A)
    (hdiv : ψ (U (a * b)) ∣ ψ (algebraMap R _ a)) :
    ∃! φ : CrossingQuotient R a →+* A,
      φ.comp (toLeft a b).toRingHom = ψ := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hρ (r : R) : ρ r = ψ (algebraMap R _ r) := rfl
  obtain ⟨z, hz⟩ := hdiv
  have hrel : ψ (U (a * b)) * z = ρ a := hz.symm
  have hprod : ψ (U (a * b)) * ψ (V (a * b)) = ρ a * ρ b := by
    rw [← map_mul, U_mul_V, ← hρ, map_mul]
  have hbz : ρ b * z = ψ (V (a * b)) := by
    apply cancel_regular hu
    calc
      ψ (U (a * b)) * (ρ b * z) = (ψ (U (a * b)) * z) * ρ b := by ring
      _ = ψ (U (a * b)) * ψ (V (a * b)) := by rw [hrel, hprod]
  refine ⟨pointHom a ρ (ψ (U (a * b))) z hrel, ?_, ?_⟩
  · apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      change pointHom a ρ _ _ hrel (toLeft a b (algebraMap R _ r)) = _
      rw [AlgHom.commutes, pointHom_algebraMap, hρ]
    · change pointHom a ρ _ _ hrel (toLeft a b (U (a * b))) = _
      rw [toLeft_U, pointHom_U]
    · change pointHom a ρ _ _ hrel (toLeft a b (V (a * b))) = _
      rw [toLeft_V, map_mul, pointHom_algebraMap, pointHom_V, hbz]
  · intro φ hφ
    have hφR (r : R) : φ (algebraMap R _ r) = ρ r := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (algebraMap R _ r)) hφ
      change φ (toLeft a b (algebraMap R _ r)) = _ at h
      rw [AlgHom.commutes] at h
      exact h
    have hφU : φ (U a) = ψ (U (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (U (a * b))) hφ
      change φ (toLeft a b (U (a * b))) = _ at h
      rwa [toLeft_U] at h
    apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      rw [pointHom_algebraMap]
      exact hφR r
    · rw [pointHom_U]
      exact hφU
    · rw [pointHom_V]
      apply cancel_regular hu
      calc
        ψ (U (a * b)) * φ (V a) = φ (U a) * φ (V a) :=
          congrArg (fun t : A => t * φ (V a)) hφU.symm
        _ = φ (U a * V a) := (map_mul φ _ _).symm
        _ = ρ a := by rw [U_mul_V, hφR]
        _ = ψ (U (a * b)) * z := hrel.symm

/-- In the chart where the pullback of `a` generates the Cartier ideal,
the map to the right nodal chart exists and is unique. -/
lemma existsUnique_right_lift (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (ha : ψ (algebraMap R _ a) ∈ nonZeroDivisors A)
    (hdiv : ψ (algebraMap R _ a) ∣ ψ (U (a * b))) :
    ∃! φ : CrossingQuotient R b →+* A,
      φ.comp (toRight a b).toRingHom = ψ := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hρ (r : R) : ρ r = ψ (algebraMap R _ r) := rfl
  obtain ⟨w, hw⟩ := hdiv
  have hprod : ψ (U (a * b)) * ψ (V (a * b)) = ρ a * ρ b := by
    rw [← map_mul, U_mul_V, ← hρ, map_mul]
  have hrel : w * ψ (V (a * b)) = ρ b := by
    apply cancel_regular ha
    calc
      ψ (algebraMap R _ a) * (w * ψ (V (a * b))) =
          ψ (U (a * b)) * ψ (V (a * b)) := by rw [← mul_assoc, ← hw]
      _ = ψ (algebraMap R _ a) * ρ b := hprod
  refine ⟨pointHom b ρ w (ψ (V (a * b))) hrel, ?_, ?_⟩
  · apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      change pointHom b ρ _ _ hrel (toRight a b (algebraMap R _ r)) = _
      rw [AlgHom.commutes, pointHom_algebraMap, hρ]
    · change pointHom b ρ _ _ hrel (toRight a b (U (a * b))) = _
      rw [toRight_U, map_mul, pointHom_algebraMap, pointHom_U]
      exact hw.symm
    · change pointHom b ρ _ _ hrel (toRight a b (V (a * b))) = _
      rw [toRight_V, pointHom_V]
  · intro φ hφ
    have hφR (r : R) : φ (algebraMap R _ r) = ρ r := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (algebraMap R _ r)) hφ
      change φ (toRight a b (algebraMap R _ r)) = _ at h
      rw [AlgHom.commutes] at h
      exact h
    have hφV : φ (V b) = ψ (V (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (V (a * b))) hφ
      change φ (toRight a b (V (a * b))) = _ at h
      rwa [toRight_V] at h
    have hφU : ρ a * φ (U b) = ψ (U (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (U (a * b))) hφ
      change φ (toRight a b (U (a * b))) = _ at h
      rwa [toRight_U, map_mul, hφR] at h
    apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      rw [pointHom_algebraMap]
      exact hφR r
    · rw [pointHom_U]
      apply cancel_regular ha
      calc
        ψ (algebraMap R _ a) * φ (U b) = ψ (U (a * b)) := hφU
        _ = ψ (algebraMap R _ a) * w := hw
    · rw [pointHom_V]
      exact hφV

/-- Effective Cartier pullback of `(u,a)` gives a unique factorization through
at least one of the two specified affine charts of the actual nodal model. -/
theorem exists_unique_chart_lift [IsLocalRing A] (a b : R)
    (ψ : CrossingQuotient R (a * b) →+* A) (r : A)
    (hI : Ideal.span ({ψ (U (a * b)), ψ (algebraMap R _ a)} : Set A) =
      Ideal.span ({r} : Set A)) (hr : r ∈ nonZeroDivisors A) :
    (∃! φ : CrossingQuotient R a →+* A, φ.comp (toLeft a b).toRingHom = ψ) ∨
      (∃! φ : CrossingQuotient R b →+* A, φ.comp (toRight a b).toRingHom = ψ) := by
  rcases regular_generator_or hI hr with ⟨hu, hdiv⟩ | ⟨ha, hdiv⟩
  · exact Or.inl (existsUnique_left_lift a b ψ hu hdiv)
  · exact Or.inr (existsUnique_right_lift a b ψ ha hdiv)

/-- Two affine lifts over a Cartier generator meet in the actual localized
overlap, with both ring-map equations. No reducedness hypothesis is needed. -/
lemma chart_lifts_overlap (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (hu : ψ (U (a * b)) ∈ nonZeroDivisors A)
    (φL : CrossingQuotient R a →+* A) (φR : CrossingQuotient R b →+* A)
    (hL : φL.comp (toLeft a b).toRingHom = ψ)
    (hR : φR.comp (toRight a b).toRingHom = ψ) :
    ∃ ell : LeftOverlap a →+* A,
      ell.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) = φL ∧
      ell.comp (rightToLeftOverlap a b).toRingHom = φR := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hφLR (r : R) : φL (algebraMap R _ r) = ρ r := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (algebraMap R _ r)) hL
    change φL (toLeft a b (algebraMap R _ r)) = _ at h
    rw [AlgHom.commutes] at h
    exact h
  have hφRR (r : R) : φR (algebraMap R _ r) = ρ r := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (algebraMap R _ r)) hR
    change φR (toRight a b (algebraMap R _ r)) = _ at h
    rw [AlgHom.commutes] at h
    exact h
  have hφLU : φL (U a) = ψ (U (a * b)) := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (U (a * b))) hL
    change φL (toLeft a b (U (a * b))) = _ at h
    rwa [toLeft_U] at h
  have hleft : ψ (U (a * b)) * φL (V a) = ρ a := by
    calc
      ψ (U (a * b)) * φL (V a) = φL (U a) * φL (V a) :=
        congrArg (fun t : A => t * φL (V a)) hφLU.symm
      _ = φL (U a * V a) := (map_mul φL _ _).symm
      _ = ρ a := by rw [U_mul_V, hφLR]
  have hright : ρ a * φR (U b) = ψ (U (a * b)) := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (U (a * b))) hR
    change φR (toRight a b (U (a * b))) = _ at h
    rwa [toRight_U, map_mul, hφRR] at h
  have hinv : φL (V a) * φR (U b) = 1 := by
    apply cancel_regular hu
    calc
      ψ (U (a * b)) * (φL (V a) * φR (U b)) =
          (ψ (U (a * b)) * φL (V a)) * φR (U b) := (mul_assoc _ _ _).symm
      _ = ψ (U (a * b)) * 1 := by rw [hleft, hright, mul_one]
  have hz : IsUnit (φL (V a)) := IsUnit.of_mul_eq_one _ hinv
  let ell : LeftOverlap a →+* A := IsLocalization.Away.lift (V a) (g := φL) hz
  have hellL : ell.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) = φL := by
    apply RingHom.ext
    intro x
    exact IsLocalization.Away.lift_eq (V a) hz x
  have hcharts :
      (algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp (toLeft a b).toRingHom =
        (rightToLeftOverlap a b).toRingHom.comp (toRight a b).toRingHom :=
    congrArg AlgHom.toRingHom (charts_agree_on_overlap a b)
  have hellR : (ell.comp (rightToLeftOverlap a b).toRingHom).comp
      (toRight a b).toRingHom = ψ := by
    calc
      _ = ell.comp ((rightToLeftOverlap a b).toRingHom.comp (toRight a b).toRingHom) := rfl
      _ = ell.comp ((algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp
          (toLeft a b).toRingHom) := by rw [hcharts]
      _ = φL.comp (toLeft a b).toRingHom := by rw [← RingHom.comp_assoc, hellL]
      _ = ψ := hL
  have ha : ψ (algebraMap R _ a) ∈ nonZeroDivisors A :=
    (mul_mem_nonZeroDivisors.mp (hright.symm ▸ hu)).1
  have hdiv : ψ (algebraMap R _ a) ∣ ψ (U (a * b)) := ⟨φR (U b), hright.symm⟩
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_right_lift a b ψ ha hdiv
  exact ⟨ell, hellL, (huniq _ hellR).trans (huniq _ hR).symm⟩

end PhilipponNodeCartierLocalLift

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponCartierSections


namespace PhilipponCartierLocalGenerator

variable {X : Scheme.{u}} {U : X.Opens}

lemma regular_germs_of_affine (hU : IsAffineOpen U) (r : Γ(X, U))
    (hr : r ∈ nonZeroDivisors Γ(X, U)) :
    ∀ x (hx : x ∈ U), X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  intro x hx
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  change algebraMap Γ(X, U) (X.presheaf.stalk x) r ∈ nonZeroDivisors (X.presheaf.stalk x)
  exact IsLocalization.nonZeroDivisors_le_comap
    (hU.primeIdealOf (⟨x, hx⟩ : U)).asIdeal.primeCompl (X.presheaf.stalk x) hr

/-- A regular divisor relation at one germ spreads to regular actual
sections on an affine neighborhood on a germ-injective scheme. -/
lemma exists_regular_neighborhood [X.IsGermInjective] (r t : Γ(X, U))
    (x : X) (hx : x ∈ U)
    (hr : X.presheaf.germ U x hx r ∈ nonZeroDivisors (X.presheaf.stalk x))
    (hdiv : X.presheaf.germ U x hx r ∣ X.presheaf.germ U x hx t) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ IsAffineOpen W ∧
      (∀ y (hy : y ∈ W), X.presheaf.germ W y hy (res hWU r) ∈
        nonZeroDivisors (X.presheaf.stalk y)) ∧
      ∃ c : Γ(X, W), res hWU r * c = res hWU t := by
  obtain ⟨c, hc⟩ := hdiv
  obtain ⟨V, hVU, hxV, v, hv⟩ := exists_local_quotient r t x hx ⟨c, hc.symm⟩
  obtain ⟨W, hxW, hW, hWV, hginj⟩ := X.exists_le_and_germ_injective x V hxV
  have hrW : res (hWV.trans hVU) r ∈ nonZeroDivisors Γ(X, W) := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    apply hginj
    rw [map_zero]
    have hr' : X.presheaf.germ W x hxW (res (hWV.trans hVU) r) ∈
        nonZeroDivisors (X.presheaf.stalk x) := by
      simpa only [res, TopCat.Presheaf.germ_res_apply] using hr
    apply mem_nonZeroDivisors_iff_left.mp hr'
    simpa only [map_mul, map_zero] using congrArg (X.presheaf.germ W x hxW) ha
  refine ⟨W, hWV.trans hVU, hxW, hW, regular_germs_of_affine hW _ hrW, res hWV v, ?_⟩
  simpa only [map_mul, res_res] using congrArg (res hWV) hv

/-- A two-generated Cartier ideal in one stalk gives an actual regular
local equation on a whole affine neighborhood, with the specified ideal
identity at every point of that neighborhood. -/
theorem exists_local_generator [X.IsGermInjective] (r t : Γ(X, U))
    (x : X) (hx : x ∈ U)
    (hCartier : ∃ a : X.presheaf.stalk x,
      Ideal.span ({X.presheaf.germ U x hx r, X.presheaf.germ U x hx t} :
        Set (X.presheaf.stalk x)) = Ideal.span ({a} : Set (X.presheaf.stalk x)) ∧
      a ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧ IsAffineOpen W ∧ ∃ e : Γ(X, W),
      (∀ y (hy : y ∈ W), X.presheaf.germ W y hy e ∈ nonZeroDivisors (X.presheaf.stalk y)) ∧
      ∀ y (hy : y ∈ W),
        Ideal.span ({X.presheaf.germ W y hy e} : Set (X.presheaf.stalk y)) =
          Ideal.span ({X.presheaf.germ U y (hWU hy) r,
            X.presheaf.germ U y (hWU hy) t} : Set (X.presheaf.stalk y)) := by
  obtain ⟨a, ha, hreg⟩ := hCartier
  rcases PhilipponNodeCartierLocalLift.regular_generator_or ha hreg with ⟨hr, hrt⟩ | ⟨ht, htr⟩
  · obtain ⟨W, hWU, hxW, hW, hregular, c, hc⟩ := exists_regular_neighborhood r t x hx hr hrt
    refine ⟨W, hWU, hxW, hW, res hWU r, hregular, ?_⟩
    intro y hy
    have hI : Ideal.span ({res hWU r, res hWU t} : Set Γ(X, W)) =
        Ideal.span ({res hWU r} : Set Γ(X, W)) :=
      Ideal.span_pair_eq_span_left_iff_dvd.mpr ⟨c, hc.symm⟩
    have hm := congrArg (Ideal.map (X.presheaf.germ W y hy).hom) hI.symm
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      res, TopCat.Presheaf.germ_res_apply] using hm
  · obtain ⟨W, hWU, hxW, hW, hregular, c, hc⟩ := exists_regular_neighborhood t r x hx ht htr
    refine ⟨W, hWU, hxW, hW, res hWU t, hregular, ?_⟩
    intro y hy
    have hI : Ideal.span ({res hWU r, res hWU t} : Set Γ(X, W)) =
        Ideal.span ({res hWU t} : Set Γ(X, W)) :=
      Ideal.span_pair_eq_span_right_iff_dvd.mpr ⟨c, hc.symm⟩
    have hm := congrArg (Ideal.map (X.presheaf.germ W y hy).hom) hI.symm
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      res, TopCat.Presheaf.germ_res_apply] using hm

end PhilipponCartierLocalGenerator

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PhilipponIdealModuleSections PhilipponCartierSections


namespace PhilipponIdealModuleFrames

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- A regular affine generator of the actual registered ideal lifts to
a frame of its actual kernel module, with precisely that image in O_X.
No integral or reduced hypothesis is needed. -/
theorem isFrameOn_of_ideal_eq_span (W : X.affineOpens) (e : Γ(X, W))
    (hr : e ∈ nonZeroDivisors Γ(X, W)) (hI : I.ideal W = Ideal.span {e})
    (m : Γ(I.module, W)) (hm : I.moduleι.app W m = e) :
    Scheme.Modules.IsFrameOn m W := by
  have hreg := PhilipponCartierLocalGenerator.regular_germs_of_affine W.prop e hr
  intro T hTW _
  have he : I.moduleι.app T (I.module.presheaf.map (homOfLE hTW).op m) = res hTW e :=
    (app_res I hTW m).trans (congrArg (res hTW) hm)
  constructor
  · intro a b hab
    have hmap := congrArg (I.moduleι.app T) hab
    simp only [Scheme.Modules.Hom.app_smul, he] at hmap
    change a * res hTW e = b * res hTW e at hmap
    exact (isRegular_iff_mem_nonZeroDivisors.mpr (regular_res hTW e hreg)).right hmap
  · intro s
    let t : Γ(X, T) := I.moduleι.app T s
    have hdiv : ∀ x (hx : x ∈ T), ∃ c : X.presheaf.stalk x,
        X.presheaf.germ T x hx (res hTW e) * c = X.presheaf.germ T x hx t := by
      intro x hx
      obtain ⟨A, hA, hxA, hsub⟩ := exists_isAffineOpen_mem_and_subset hx
      have hAT : A ≤ T := hsub
      let V : X.affineOpens := ⟨A, hA⟩
      let z : Γ(I.module, A) := I.module.presheaf.map (homOfLE hAT).op s
      have hz : I.moduleι.app A z ∈ (I.ideal V : Set Γ(X, V)) := by
        rw [← (I.range_moduleIota_app_and_injective V).1]
        exact ⟨z, rfl⟩
      have hVW : (V : X.Opens) ≤ W := hAT.trans hTW
      rw [← I.map_ideal hVW, hI, Ideal.map_span, Set.image_singleton] at hz
      obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton (α := Γ(X, V))).mp hz
      refine ⟨X.presheaf.germ A x hxA c, ?_⟩
      have hg := congrArg (X.presheaf.germ A x hxA) hc
      have hz' : I.moduleι.app A z = res hAT t := app_res I hAT s
      rw [hz', map_mul] at hg
      have heG : X.presheaf.germ A x hxA
          ((X.presheaf.map (homOfLE hVW).op).hom e) =
          X.presheaf.germ W x (hVW hxA) e :=
        X.presheaf.germ_res_apply (homOfLE hVW) x hxA e
      have htG : X.presheaf.germ A x hxA (res hAT t) = X.presheaf.germ T x hx t :=
        X.presheaf.germ_res_apply (homOfLE hAT) x hxA t
      have heT : X.presheaf.germ T x hx (res hTW e) =
          X.presheaf.germ W x (hTW hx) e :=
        X.presheaf.germ_res_apply (homOfLE hTW) x hx e
      let μ : X.presheaf.stalk x → X.presheaf.stalk x :=
        fun z => z * X.presheaf.germ A x hxA c
      exact (congrArg μ heT).trans ((congrArg μ heG).symm.trans (hg.symm.trans htG))
    have hregT : ∀ x (hx : x ∈ T),
        X.presheaf.germ T x hx (res hTW e) ∈ nonZeroDivisors (X.presheaf.stalk x) := by
      intro x hx
      simpa only [res, TopCat.Presheaf.germ_res_apply] using hreg x (hTW hx)
    obtain ⟨a, ha, -⟩ := existsUnique_quotient (res hTW e) t hregT hdiv
    refine ⟨a, app_injective I T ?_⟩
    simp only [Scheme.Modules.Hom.app_smul, he]
    change a * res hTW e = t
    rw [mul_comm]
    exact ha

theorem exists_frame_of_ideal_eq_span (W : X.affineOpens) (e : Γ(X, W))
    (hr : e ∈ nonZeroDivisors Γ(X, W)) (hI : I.ideal W = Ideal.span {e}) :
    ∃ m : Γ(I.module, W), I.moduleι.app W m = e ∧ Scheme.Modules.IsFrameOn m W := by
  obtain ⟨m, hm, -⟩ := existsUnique_lift I W e (by
    intro A h
    rw [← I.map_ideal h, hI, Ideal.map_span, Set.image_singleton]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))
  exact ⟨m, hm, isFrameOn_of_ideal_eq_span I W e hr hI m hm⟩

end PhilipponIdealModuleFrames

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory

theorem solution
    {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.affineOpens) (g : Γ(X, W))
    (hg : g ∈ nonZeroDivisors Γ(X, W)) (hI : I.ideal W = Ideal.span {g}) :
    ∃ m : Γ(I.module, W), I.moduleι.app W m = g ∧ Scheme.Modules.IsFrameOn m W := by
  exact PhilipponIdealModuleFrames.exists_frame_of_ideal_eq_span I W g hg hI
