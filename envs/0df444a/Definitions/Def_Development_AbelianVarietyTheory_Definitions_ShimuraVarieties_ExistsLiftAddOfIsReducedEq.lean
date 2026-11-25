-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:10.241193+00:00
-- url     : https://prove2.me/theorems/63d62d6a-8bc2-585c-91bb-613e7180f7cc
-- title:
--   Exists Lift Add Of Is Reduced Eq
-- statement:
--   Definitions and structural lemmas for Exists Lift Add Of Is Reduced Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsLiftAddOfIsReducedEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_self
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_smul
import Theorems.Thm_GlobalTheory_AddLaw_map_diagXYZ
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
import Theorems.Thm_GlobalTheory_WeierstrassCurve_IsSumTriple_equation_of_isReduced
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_comp_ptOver_eq_fieldAdd
import Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_law_notMem
import Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_sum
import Theorems.Thm_GlobalTheory_WeierstrassCurve_fieldAdd_ptOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isSumTriple_addXYZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isSumTriple_diagXYZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_ptOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_toUnit_zeroUnit
import Theorems.Thm_GlobalTheory_exists_eq_specOverMap
import Theorems.Thm_GlobalTheory_hom_ext_of_isLocalRing
import Theorems.Thm_GlobalTheory_isCommMonObj_of_isPullback
import Theorems.Thm_GlobalTheory_mul_left_comp_of_pullbackPointEquiv_mul
import Theorems.Thm_GlobalTheory_over_hom_eq_iff_forall_field_algebra
import Theorems.Thm_GlobalTheory_pullbackPointEquiv_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
namespace GlobalTheory
namespace WeierstrassCurve
open AddLaw
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
instance isSeparated_over_hom : IsSeparated (schemeOver W).hom :=
  inferInstanceAs (IsSeparated (toSpec W))
theorem isReduced_pullback_toSpec {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of R)) :
    IsReduced (pullback f (toSpec W)) := by
  have : ∀ i, IsReduced ((X.affineOpenCover.openCover.pullback₁
      (pullback.fst f (toSpec W))).X i) := fun i => by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
    have : _root_.IsReduced (X.affineOpenCover.X i) :=
      (affine_isReduced_iff _).mp (@isReduced_of_isOpenImmersion _ _ _
        (X.affineOpenCover.map_prop i) _)
    have h := (IsPullback.of_hasPullback (pullback.fst f (toSpec W))
      (X.affineOpenCover.f i)).paste_horiz (IsPullback.of_hasPullback f (toSpec W)).flip
    rw [← hφ] at h
    have := isReduced_scheme (W.map φ.hom)
    let e : _ ≅ scheme (W.map φ.hom) := h.isoIsPullback _ _ (isPullback_mapHom W φ.hom rfl)
    exact @isReduced_of_isOpenImmersion _ _ e.hom (@IsOpenImmersion.of_isIso _ _ _ e.isIso_hom) _
  exact .of_openCover _ (X.affineOpenCover.openCover.pullback₁ (pullback.fst f (toSpec W)))
instance isReduced_tensor_left (T : Over (Spec (.of R))) [IsReduced T.left] :
    IsReduced (T ⊗ schemeOver W).left :=
  isReduced_pullback_toSpec W T.hom
instance isReduced_over_left [_root_.IsReduced R] : IsReduced (schemeOver W).left :=
  isReduced_scheme W
section Reduced
variable [_root_.IsReduced R] [W.IsElliptic]
def addOfIsReduced : schemeOver W ⊗ schemeOver W ⟶ schemeOver W :=
  (exists_sum W (fst (schemeOver W) (schemeOver W)) (snd _ _)).choose
theorem lift_addOfIsReduced (k : Type u) [Field k] [Algebra R k]
    (a b : specOver R k ⟶ schemeOver W) : lift a b ≫ addOfIsReduced W = fieldAdd W k a b := by
  have h := (exists_sum W (fst (schemeOver W) (schemeOver W)) (snd _ _)).choose_spec k (lift a b)
  rwa [lift_fst, lift_snd] at h
@[instance_reducible]
def grpObjOfIsReduced : GrpObj (schemeOver W) :=
  grpObjOfFieldPoints (zeroUnit W) (addOfIsReduced W) (negOver W) fun k _ _ =>
    ⟨(W.baseChange k).toProjective.Point, inferInstance, projectivePointEquiv W k,
      (toUnit_zeroUnit W k).trans (ofProjectivePoint_zero W k).symm,
      fun a b => by
        rw [lift_addOfIsReduced, fieldAdd, Equiv.symm_apply_apply, Equiv.symm_apply_apply],
      by
        rintro @⟨⟨P⟩, hP⟩
        exact ptOver_negOver W P (.of_nonsingular hP)⟩
theorem isCommMonObj_of_isReduced :
    letI := grpObjOfIsReduced W
    IsCommMonObj (schemeOver W) := by
  let := grpObjOfIsReduced W
  refine ⟨over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => ?_⟩
  rw [← lift_comp_fst_snd x, lift_braiding_hom_assoc]
  change lift _ _ ≫ addOfIsReduced W = lift _ _ ≫ addOfIsReduced W
  rw [lift_addOfIsReduced, lift_addOfIsReduced, fieldAdd, fieldAdd, add_comm]
theorem exists_lift_addOfIsReduced_eq {A : Type u} [CommRing A] [IsLocalRing A] [Algebra R A]
    {P Q : Fin 3 → A} (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    ∃ (S : Fin 3 → A) (hS : IsUnimodularSol (W.baseChange A) S),
      (S = (W.baseChange A).toProjective.addXYZ P Q ∨
        S = diagXYZ (W.baseChange A).toProjective P Q) ∧
      lift (ptOver W P hP) (ptOver W Q hQ) ≫ addOfIsReduced W = ptOver W S hS := by
  set z := lift (ptOver W P hP) (ptOver W Q hQ) with hz
  let t := z.left (IsLocalRing.closedPoint A)
  let B : Type u := (schemeOver W ⊗ schemeOver W).left.presheaf.stalk t
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective
    ((schemeOver W ⊗ schemeOver W).left.fromSpecStalk t ≫ (schemeOver W ⊗ schemeOver W).hom)
  let : Algebra R B := ρ.hom.toAlgebra
  let j : specOver R B ⟶ schemeOver W ⊗ schemeOver W :=
    Over.homMk ((schemeOver W ⊗ schemeOver W).left.fromSpecStalk t) hρ.symm
  have e₀ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) z.left
  let x : specOver R A ⟶ specOver R B :=
    Over.homMk (Spec.map (Scheme.stalkClosedPointTo (R := .of A) z.left)) (by
      refine (congrArg (_ ≫ ·) hρ).trans ?_
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e₀)).trans (Over.w z))
  have hx : x ≫ j = z := Over.OverMorphism.ext e₀
  obtain ⟨g, hg⟩ := exists_eq_specOverMap x
  obtain ⟨P₀, hP₀, eP⟩ := exists_eq_ptOver W (j ≫ fst _ _)
  obtain ⟨Q₀, hQ₀, eQ⟩ := exists_eq_ptOver W (j ≫ snd _ _)
  have : IsReduced (specOver R B).left := inferInstanceAs (IsReduced (Spec (.of B)))
  have key : ∀ S₀, IsSumTriple (W.baseChange B) P₀ Q₀ S₀ →
      (∃ i, S₀ i ∉ IsLocalRing.maximalIdeal B) →
      ∃ hS : IsUnimodularSol (W.baseChange A) (g ∘ S₀),
        z ≫ addOfIsReduced W = ptOver W (g ∘ S₀) hS := by
    rintro S₀ h ⟨i, hi⟩
    have hS₀ : IsUnimodularSol (W.baseChange B) S₀ :=
      .of_isUnit (h.equation_of_isReduced hP₀ hQ₀) i (IsLocalRing.notMem_maximalIdeal.mp hi)
    have : j ≫ addOfIsReduced W = ptOver W S₀ hS₀ :=
      over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ y => by
        rw [comp_ptOver_eq_fieldAdd W hP₀ hQ₀ hS₀ h, ← lift_addOfIsReduced, ← eP, ← eQ,
          ← comp_lift, lift_comp_fst_snd, Category.assoc]
    exact ⟨hS₀.baseChange g, by rw [← hx, Category.assoc, this, hg, specOverMap_ptOver]⟩
  obtain ⟨a, ha⟩ := (ptOver_eq_ptOver_iff W (hP₀.baseChange g) hP).mp (by
    rw [← specOverMap_ptOver W g P₀ hP₀, ← eP, ← hg, ← Category.assoc, hx, hz, lift_fst])
  obtain ⟨b, hb⟩ := (ptOver_eq_ptOver_iff W (hQ₀.baseChange g) hQ).mp (by
    rw [← specOverMap_ptOver W g Q₀ hQ₀, ← eQ, ← hg, ← Category.assoc, hx, hz, lift_snd])
  have hu : IsUnit (((a : A) * b) ^ 2) := (a.isUnit.mul b.isUnit).pow 2
  have hW : (W.baseChange B).map (g : B →+* A) = W.baseChange A :=
    WeierstrassCurve.map_baseChange ..
  rcases exists_law_notMem hP₀ hQ₀ (IsLocalRing.maximalIdeal B) with h | h
  · obtain ⟨hS, e⟩ := key _ (isSumTriple_addXYZ hP₀.equation hQ₀.equation) h
    refine ⟨_, hS.smul hu, Or.inl ?_, e.trans (Over.OverMorphism.ext (pt_smul W _ hS hu).symm)⟩
    rw [ha, hb, WeierstrassCurve.Projective.addXYZ_smul, ← hW]
    exact congrArg _ (WeierstrassCurve.Projective.map_addXYZ (g : B →+* A) P₀ Q₀).symm
  · obtain ⟨hS, e⟩ := key _ (isSumTriple_diagXYZ hP₀.equation hQ₀.equation) h
    refine ⟨_, hS.smul hu, Or.inr ?_, e.trans (Over.OverMorphism.ext (pt_smul W _ hS hu).symm)⟩
    rw [ha, hb, diagXYZ_smul, ← hW]
    exact congrArg _ (map_diagXYZ (g : B →+* A) P₀ Q₀).symm
end Reduced
section Universal
def genericCurve : WeierstrassCurve (MvPolynomial (ULift.{u} (Fin 5)) ℤ) :=
  ⟨.X ⟨0⟩, .X ⟨1⟩, .X ⟨2⟩, .X ⟨3⟩, .X ⟨4⟩⟩
abbrev UniversalRing : Type u := Localization.Away genericCurve.{u}.Δ
def universalCurve : WeierstrassCurve UniversalRing.{u} :=
  genericCurve.map (algebraMap _ UniversalRing.{u})
instance isElliptic_universalCurve : universalCurve.{u}.IsElliptic :=
  ⟨by
    rw [universalCurve, WeierstrassCurve.map_Δ]
    exact IsLocalization.Away.algebraMap_isUnit _⟩
def coeffHom : MvPolynomial (ULift.{u} (Fin 5)) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) fun i => ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆] i.down
theorem map_coeffHom : genericCurve.map (coeffHom W) = W := by
  ext <;> simp [genericCurve, coeffHom]
def classifyingHom [W.IsElliptic] : UniversalRing.{u} →+* R :=
  IsLocalization.Away.lift genericCurve.Δ (g := coeffHom W) (by
    rw [← WeierstrassCurve.map_Δ, map_coeffHom]
    exact W.isUnit_Δ)
theorem map_classifyingHom [W.IsElliptic] : universalCurve.map (classifyingHom W) = W := by
  rw [universalCurve, WeierstrassCurve.map_map, classifyingHom, IsLocalization.Away.lift_comp,
    map_coeffHom]
theorem isPullback_universalCurve [W.IsElliptic] :
    IsPullback (mapHom universalCurve (classifyingHom W) (map_classifyingHom W))
      (schemeOver W).hom (schemeOver universalCurve).hom
      (Spec.map (CommRingCat.ofHom (classifyingHom W))) :=
  isPullback_mapHom ..
end Universal
variable [W.IsElliptic]
instance grpObj : GrpObj (schemeOver W) :=
  @grpObjOfIsPullback _ _ (schemeOver universalCurve) (schemeOver W) _ _
    (grpObjOfIsReduced universalCurve) (isPullback_universalCurve W)
instance isCommMonObj : IsCommMonObj (schemeOver W) :=
  @isCommMonObj_of_isPullback _ _ (schemeOver universalCurve) (schemeOver W) _ _
    (grpObjOfIsReduced universalCurve) (isCommMonObj_of_isReduced universalCurve)
    (isPullback_universalCurve W)
theorem one_eq_zeroUnit : η[schemeOver W] = zeroUnit W := by
  refine Over.OverMorphism.ext ((isPullback_universalCurve W).hom_ext ?_
    ((Over.w _).trans (Over.w _).symm))
  refine ((isPullback_universalCurve W).lift_fst ..).trans ?_
  refine Eq.trans ?_ (zero_mapHom ..).symm
  exact congrArg (· ≫ zero universalCurve) (Category.id_comp _)
theorem inv_eq_negOver : ι[schemeOver W] = negOver W := by
  refine Over.OverMorphism.ext ((isPullback_universalCurve W).hom_ext ?_
    ((Over.w _).trans (Over.w _).symm))
  refine ((isPullback_universalCurve W).lift_fst ..).trans ?_
  refine Eq.trans ?_ (negHom_mapHom ..).symm
  exact congrArg (· ≫ negHom universalCurve) (Category.id_comp _)
@[simp] theorem one_left : η[schemeOver W].left = zero W := congrArg (·.left) (one_eq_zeroUnit W)
@[simp] theorem inv_left : ι[schemeOver W].left = negHom W := congrArg (·.left) (inv_eq_negOver W)
theorem hom_one_left (T : Over (Spec (.of R))) :
    (1 : T ⟶ schemeOver W).left = T.hom ≫ zero W := by
  rw [Hom.one_def, one_eq_zeroUnit]
  rfl
theorem mul_left_mapHom_universal {T' : Over (Spec (.of R))}
    {T : Over (Spec (.of UniversalRing.{u}))} (t : T'.left ⟶ T.left) {x' y' : T' ⟶ schemeOver W}
    {x y : T ⟶ schemeOver universalCurve}
    (hx : x'.left ≫ mapHom universalCurve (classifyingHom W) (map_classifyingHom W) = t ≫ x.left)
    (hy : y'.left ≫ mapHom universalCurve (classifyingHom W) (map_classifyingHom W) = t ≫ y.left) :
    (x' * y').left ≫ mapHom universalCurve (classifyingHom W) (map_classifyingHom W) =
      t ≫ (lift x y ≫ addOfIsReduced universalCurve).left :=
  @mul_left_comp_of_pullbackPointEquiv_mul _ _ (schemeOver universalCurve) (schemeOver W) _ _
    (grpObjOfIsReduced universalCurve) (grpObj W) (isPullback_universalCurve W) _ _ t _ _ _ _
    (@pullbackPointEquiv_mul _ _ (schemeOver universalCurve) (schemeOver W) _ _
      (grpObjOfIsReduced universalCurve) (isPullback_universalCurve W) _ x' y') hx hy
section BaseChange
variable {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'} [W'.IsElliptic] (f : R →+* R')
  (h : W.map f = W')
end BaseChange
section Ring
variable {A : Type u} [CommRing A] [Algebra R A] {P Q T : Fin 3 → A}
theorem one_eq_zeroOver : (1 : specOver R A ⟶ schemeOver W) = zeroOver W A :=
  Over.OverMorphism.ext (hom_one_left W _)
theorem one_eq_ptOver :
    (1 : specOver R A ⟶ schemeOver W) = ptOver W ![0, 1, 0] (isUnimodularSol_zero _) :=
  (one_eq_zeroOver W).trans (zeroOver_eq_ptOver W A)
theorem ptOver_inv (hP : IsUnimodularSol (W.baseChange A) P) :
    (ptOver W P hP)⁻¹ = ptOver W ((W.baseChange A).toProjective.neg P) hP.neg := by
  rw [Hom.inv_def, inv_eq_negOver, ptOver_negOver]
theorem exists_ptOver_mul_ptOver_eq [IsLocalRing A] (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) :
    ∃ (S : Fin 3 → A) (hS : IsUnimodularSol (W.baseChange A) S),
      (S = (W.baseChange A).toProjective.addXYZ P Q ∨
        S = diagXYZ (W.baseChange A).toProjective P Q) ∧
      ptOver W P hP * ptOver W Q hQ = ptOver W S hS := by
  let : Algebra UniversalRing.{u} A := ((algebraMap R A).comp (classifyingHom W)).toAlgebra
  have e : universalCurve.baseChange A = W.baseChange A := map_comp_eq (map_classifyingHom W) _
  have key : ∀ (S : Fin 3 → A) (hS : IsUnimodularSol (W.baseChange A) S)
      (hS' : IsUnimodularSol (universalCurve.baseChange A) S),
      pt W S hS ≫ mapHom universalCurve (classifyingHom W) (map_classifyingHom W) =
        𝟙 _ ≫ pt universalCurve S hS' := fun S hS hS' =>
    (ptHom_mapHom ..).trans (Category.id_comp _).symm
  obtain ⟨S, hS, h, eS⟩ := exists_lift_addOfIsReduced_eq universalCurve (e ▸ hP) (e ▸ hQ)
  rw [e] at h
  refine ⟨S, e ▸ hS, h, Over.OverMorphism.ext ((isPullback_universalCurve W).hom_ext ?_
    ((Over.w _).trans (Over.w _).symm))⟩
  refine (mul_left_mapHom_universal W (𝟙 _) (x := ptOver universalCurve P (e ▸ hP))
    (y := ptOver universalCurve Q (e ▸ hQ)) (key P hP (e ▸ hP)) (key Q hQ (e ▸ hQ))).trans ?_
  rw [eS]
  exact (key S (e ▸ hS) hS).symm
theorem ptOver_mul_ptOver (hP : IsUnimodularSol (W.baseChange A) P)
    (hQ : IsUnimodularSol (W.baseChange A) Q) (hT : IsUnimodularSol (W.baseChange A) T)
    (h : IsSumTriple (W.baseChange A) P Q T) :
    ptOver W P hP * ptOver W Q hQ = ptOver W T hT := by
  refine Over.OverMorphism.ext (hom_ext_of_isLocalRing fun B _ _ φ => ?_)
  let : Algebra R B := (φ.comp (algebraMap R A)).toAlgebra
  let g : A →ₐ[R] B := ⟨φ, fun _ => rfl⟩
  suffices specOverMap g ≫ (ptOver W P hP * ptOver W Q hQ) = specOverMap g ≫ ptOver W T hT from
    congrArg (·.left) this
  obtain ⟨S, hS, h', e⟩ := exists_ptOver_mul_ptOver_eq W (hP.baseChange g) (hQ.baseChange g)
  rw [MonObj.comp_mul, specOverMap_ptOver, specOverMap_ptOver, specOverMap_ptOver, e]
  refine Over.OverMorphism.ext ((pt_eq_pt_iff_minors W (hT.baseChange g) hS).mpr ?_).symm
  rcases h' with rfl | rfl
  exacts [(h.baseChange g).add, (h.baseChange g).diag]
theorem IsSumTriple.equation {V : WeierstrassCurve A} [V.IsElliptic] (h : IsSumTriple V P Q T)
    (hP : IsUnimodularSol V P) (hQ : IsUnimodularSol V Q) : V.toProjective.Equation T := by
  refine eq_zero_of_localization _ fun p _ => ?_
  let g := algebraMap A (Localization.AtPrime p)
  obtain ⟨S, hS, h', -⟩ := exists_ptOver_mul_ptOver_eq V (A := Localization.AtPrime p)
    (hP.map g) (hQ.map g)
  have hp : Proportional (g ∘ T) S := by
    rcases h' with rfl | rfl
    exacts [(h.map g).add, (h.map g).diag]
  obtain ⟨i, v, hv⟩ := hS.exists_isUnit
  have e : g ∘ T = ((g ∘ T) i * (v⁻¹ : (Localization.AtPrime p)ˣ)) • S := by
    ext j
    rw [Pi.smul_apply, smul_eq_mul, mul_right_comm, hp i j, ← hv, Units.mul_inv_cancel_right]
  have h₀ : (V.toProjective.map g).Equation (g ∘ T) := by
    have h₁ : MvPolynomial.eval₂ (RingHom.id _) S (V.map g).toProjective.polynomial = 0 :=
      hS.equation
    have h₂ := eval₂_smul_of_isHomogeneous (RingHom.id _) (isHomogeneous_polynomial (V.map g))
      ((g ∘ T) i * (v⁻¹ : (Localization.AtPrime p)ˣ)) S
    rw [← e, h₁, mul_zero] at h₂
    exact h₂
  rwa [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp] at h₀
theorem ptOver_mul_self (hP : IsUnimodularSol (W.baseChange A) P)
    (hT : IsUnimodularSol (W.baseChange A) T)
    (h : Proportional T ((W.baseChange A).toProjective.dblXYZ P)) :
    ptOver W P hP * ptOver W P hP = ptOver W T hT := by
  refine ptOver_mul_ptOver W hP hP hT ⟨fun i j => ?_, (diagXYZ_self hP.equation).symm ▸ h⟩
  rw [WeierstrassCurve.Projective.addXYZ_self]
  fin_cases i <;> fin_cases j <;> simp
end Ring
section Field
variable (k : Type u) [Field k] [Algebra R k]
theorem ofProjectivePoint_add (p q : (W.baseChange k).toProjective.Point) :
    ofProjectivePoint W k (p + q) = ofProjectivePoint W k p * ofProjectivePoint W k q := by
  obtain @⟨⟨P⟩, hP⟩ := p
  obtain @⟨⟨Q⟩, hQ⟩ := q
  have hP' : IsUnimodularSol (W.baseChange k) P := .of_nonsingular hP
  have hQ' : IsUnimodularSol (W.baseChange k) Q := .of_nonsingular hQ
  obtain ⟨S, hS, h, e⟩ := exists_ptOver_mul_ptOver_eq W hP' hQ'
  have h' : IsSumTriple (W.baseChange k) P Q S := by
    rcases h with rfl | rfl
    exacts [isSumTriple_addXYZ hP'.equation hQ'.equation,
      isSumTriple_diagXYZ hP'.equation hQ'.equation]
  refine Eq.trans ?_ ((fieldAdd_ptOver W hP' hQ' hS h').trans e.symm)
  rw [fieldAdd, projectivePointEquiv_symm_ptOver, projectivePointEquiv_symm_ptOver]
  rfl
def projectivePointMulEquiv :
    Multiplicative (W.baseChange k).toProjective.Point ≃* (specOver R k ⟶ schemeOver W) where
  toEquiv := Multiplicative.toAdd.trans (projectivePointEquiv W k)
  map_mul' p q := ofProjectivePoint_add W k p.toAdd q.toAdd
@[simp] theorem projectivePointMulEquiv_ofAdd (p : (W.baseChange k).toProjective.Point) :
    projectivePointMulEquiv W k (.ofAdd p) = ofProjectivePoint W k p := rfl
variable [DecidableEq k]
theorem ofAffinePoint_add (p q : (W.baseChange k).toAffine.Point) :
    ofAffinePoint W k (p + q) = ofAffinePoint W k p * ofAffinePoint W k q :=
  (congrArg (ofProjectivePoint W k) (map_add (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W.baseChange k).toProjective).symm p q)).trans (ofProjectivePoint_add W k _ _)
def affinePointMulEquiv :
    Multiplicative (W.baseChange k).toAffine.Point ≃* (specOver R k ⟶ schemeOver W) where
  toEquiv := Multiplicative.toAdd.trans (affinePointEquiv W k)
  map_mul' p q := ofAffinePoint_add W k p.toAdd q.toAdd
@[simp] theorem affinePointMulEquiv_ofAdd (p : (W.baseChange k).toAffine.Point) :
    affinePointMulEquiv W k (.ofAdd p) = ofAffinePoint W k p := rfl
end Field
section ReducedBase
variable [_root_.IsReduced R]
end ReducedBase
section Examples
def sampleCurve : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩
instance : sampleCurve.IsElliptic := ⟨Ne.isUnit (by
  norm_num [sampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩
theorem sample_sol {a b : ℚ} (h : b ^ 2 + b = a ^ 3 - a) :
    IsUnimodularSol (sampleCurve.baseChange ℚ) ![a, b, 1] :=
  isUnimodularSol_some (by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [sampleCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_zero, map_one,
      map_neg]
    linear_combination h)
example : (ptOver sampleCurve ![0, 0, 1] (sample_sol (by norm_num)))⁻¹ =
    ptOver sampleCurve (A := ℚ) ![0, -1, 1] (sample_sol (by norm_num)) := by
  rw [ptOver_inv]
  congr 1
  simp [WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY, sampleCurve,
    WeierstrassCurve.baseChange]
example : ptOver sampleCurve ![0, 0, 1] (sample_sol (by norm_num)) *
    ptOver sampleCurve ![0, 0, 1] (sample_sol (by norm_num)) =
    ptOver sampleCurve (A := ℚ) ![1, 0, 1] (sample_sol (by norm_num)) := by
  refine ptOver_mul_self _ _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [WeierstrassCurve.Projective.dblXYZ, WeierstrassCurve.Projective.dblX,
      WeierstrassCurve.Projective.dblY, WeierstrassCurve.Projective.dblZ,
      WeierstrassCurve.Projective.negDblY, WeierstrassCurve.Projective.negY, sampleCurve,
      WeierstrassCurve.baseChange] <;> norm_num
example : ptOver sampleCurve (A := ℚ) ![0, 0, 1] (sample_sol (by norm_num)) ≠ 1 := by
  rw [one_eq_ptOver]
  intro e
  obtain ⟨v, hv⟩ := (ptOver_eq_ptOver_iff _ _ _).mp e
  simpa using congrFun hv 1
end Examples
end WeierstrassCurve
end GlobalTheory


