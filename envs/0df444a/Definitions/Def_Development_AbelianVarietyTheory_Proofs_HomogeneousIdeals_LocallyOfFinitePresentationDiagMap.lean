-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:16.419894+00:00
-- url     : https://prove2.me/theorems/285f0bb0-6163-5fac-977a-13de3e7eea43
-- title:
--   Locally Of Finite Presentation Diag Map
-- statement:
--   Definitions and structural lemmas for Locally Of Finite Presentation Diag Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentationDiagMap.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
namespace GlobalTheory.Diag
variable (S : Scheme.{u}) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
omit [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] in

theorem isPullback_toUnit_of_lift {K G H : Over S} {i : K ⟶ G} {f : G ⟶ H} {e : 𝟙_ (Over S) ⟶ H}
    (hw : i ≫ f = toUnit _ ≫ e)
    (hmono : ∀ {T : Over S} {a b : T ⟶ K}, a ≫ i = b ≫ i → a = b)
    (hl : ∀ {T : Over S} (t : T ⟶ G), t ≫ f = toUnit _ ≫ e → ∃ l : T ⟶ K, l ≫ i = t) :
    IsPullback i (toUnit _) f e := by
  have hs : ∀ s : PullbackCone f e, s.fst ≫ f = toUnit _ ≫ e := fun s => by
    rw [s.condition, toUnit_unique s.snd (toUnit _)]
  exact ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (hl s.fst (hs s)).choose)
    (fun s => (hl s.fst (hs s)).choose_spec) (fun s => toUnit_unique _ _)
    (fun s m h _ => hmono (h.trans (hl s.fst (hs s)).choose_spec.symm))⟩⟩
def ringMap (u : Y →+ X) : torusRing ZU Y ⟶ torusRing ZU X :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom ZU.{u} u)
theorem ringMap_single (u : Y →+ X) (y : Y) (r : ZU.{u}) :
    (ringMap u).hom (AddMonoidAlgebra.single y r) = AddMonoidAlgebra.single (u y) r :=
  AddMonoidAlgebra.mapDomain_single
def affMap (u : Y →+ X) : splitTorusAff ZU X ⟶ splitTorusAff ZU Y :=
  Spec.mapMulEquiv (R := ZU.{u}) (S := AddMonoidAlgebra ZU.{u} Y) (T := AddMonoidAlgebra ZU.{u} X)
    (WithConv.toConv (AddMonoidAlgebra.mapDomainAlgHom ZU.{u} ZU.{u} u))
instance (u : Y →+ X) : IsMonHom (affMap u) :=
  ((bialgSpec ZU.{u}).map (CommBialgCat.ofHom
    (AddMonoidAlgebra.mapDomainBialgHom ZU.{u} u)).op).isMonHom_hom
theorem affMap_add (u v : Y →+ X) : affMap (u + v) = affMap u * affMap v := by
  rw [affMap, affMap, affMap]
  refine Eq.trans (congrArg _ ?_) (map_mul (Spec.mapMulEquiv (R := ZU.{u})
    (S := AddMonoidAlgebra ZU.{u} Y) (T := AddMonoidAlgebra ZU.{u} X)) _ _)
  ext y : 2
  · rw [AddMonoidAlgebra.convMul_algHom_single_one]
    simp [AddMonoidAlgebra.single_mul_single]
  · exact Subsingleton.elim _ _
def diagMap (u : Y →+ X) : splitTorus S X ⟶ splitTorus S Y :=
  (Over.pullback (toZ S)).map (affMap u)
instance diagMap_isMonHom (u : Y →+ X) : IsMonHom (diagMap S u) :=
  Functor.map.instIsMonHom (F := Over.pullback (toZ S)) (f := affMap u)
instance isCommMonObj (X : Type u) [AddCommGroup X] : IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))
theorem diagMap_add (u v : Y →+ X) : diagMap S (u + v) = diagMap S u * diagMap S v := by
  rw [diagMap, affMap_add]
  exact Functor.map_mul (Over.pullback (toZ S)) _ _
theorem diagMap_zero : diagMap S (0 : Y →+ X) = 1 := by
  have h := diagMap_add S (0 : Y →+ X) 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm
theorem diagMap_left_torusFst (u : Y →+ X) :
    (diagMap S u).left ≫ torusFst S Y = torusFst S X ≫ Spec.map (ringMap u) :=
  pullback.lift_fst _ _ _
theorem isPullback_torusFst (X : Type u) [AddCommGroup X] :
    IsPullback (torusFst S X) (splitTorus S X).hom (splitTorusAff ZU X).hom (toZ S) :=
  IsPullback.of_hasPullback _ _
theorem isPullback_diagMap (u : Y →+ X) :
    IsPullback (torusFst S X) (diagMap S u).left (Spec.map (ringMap u)) (torusFst S Y) := by
  refine IsPullback.of_bot ?_ (diagMap_left_torusFst S u).symm (isPullback_torusFst S Y)
  have e : Spec.map (ringMap u) ≫ (splitTorusAff ZU Y).hom = (splitTorusAff ZU X).hom :=
    specULiftZIsTerminal.hom_ext _ _
  rw [Over.w, e]
  exact isPullback_torusFst S X
variable {S} in
theorem coord_comp_diagMap {T : Over S} (t : T ⟶ splitTorus S X) (u : Y →+ X) :
    coord (t ≫ diagMap S u) = ringMap u ≫ coord t := by
  simp only [coord, Over.comp_left, Category.assoc, diagMap_left_torusFst, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
variable {S} in
theorem coord_comp_diagMap_single {T : Over S} (t : T ⟶ splitTorus S X) (u : Y →+ X) (y : Y) :
    (coord (t ≫ diagMap S u)).hom (AddMonoidAlgebra.single y 1) =
      (coord t).hom (AddMonoidAlgebra.single (u y) 1) := by
  rw [coord_comp_diagMap, CommRingCat.hom_comp, RingHom.comp_apply, ringMap_single]
variable {S} in

theorem hom_ext {T : Over S} {s t : T ⟶ splitTorus S X}
    (h : ∀ x, (coord s).hom (AddMonoidAlgebra.single x 1) =
      (coord t).hom (AddMonoidAlgebra.single x 1)) : s = t :=
  coord_injective (CommRingCat.hom_ext (ringHom_ext_ZU h))
theorem diagMap_id : diagMap S (AddMonoidHom.id X) = 𝟙 _ :=
  hom_ext fun x => by rw [← Category.id_comp (diagMap S _), coord_comp_diagMap_single]; rfl
theorem diagMap_comp (u : Y →+ X) (v : Z →+ Y) : diagMap S (u.comp v) = diagMap S u ≫ diagMap S v :=
  hom_ext fun x => by
    rw [coord_comp_diagMap_single, ← Category.id_comp (diagMap S u), coord_comp_diagMap_single,
      ← Category.id_comp (diagMap S (u.comp v)), coord_comp_diagMap_single]; rfl
variable {S} in

theorem coord_one (T : Over S) (x : X) :
    (coord (1 : T ⟶ splitTorus S X)).hom (AddMonoidAlgebra.single x 1) = 1 := by
  rw [← MonObj.comp_one (1 : T ⟶ splitTorus S X), ← diagMap_zero, coord_comp_diagMap_single,
    AddMonoidHom.zero_apply, ← AddMonoidAlgebra.one_def, map_one]
variable {S} in

def ofCoord (T : Over S) (φ : torusRing ZU X ⟶ Γ(T.left, ⊤)) : T ⟶ splitTorus S X :=
  Over.homMk (pullback.lift (T.left.toSpecΓ ≫ Spec.map φ) T.hom (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)
variable {S} in
theorem coord_ofCoord (T : Over S) (φ : torusRing ZU X ⟶ Γ(T.left, ⊤)) :
    coord (ofCoord T φ) = φ := by
  have : (ofCoord T φ).left ≫ torusFst S X = T.left.toSpecΓ ≫ Spec.map φ := pullback.lift_fst _ _ _
  rw [coord, this, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  simp
variable {S} in

def ofChar (T : Over S) (g : Multiplicative X →* Γ(T.left, ⊤)) : T ⟶ splitTorus S X :=
  ofCoord T (CommRingCat.ofHom (AddMonoidAlgebra.liftNCRingHom
    ((Int.castRingHom _).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom) g
      fun _ _ => .all _ _))
theorem mulN_eq_diagMap (n : ℕ) : mulN (splitTorus S X) n = diagMap S (nsmulAddMonoidHom n : X →+ X) := by
  induction n with
  | zero =>
    have : (nsmulAddMonoidHom 0 : X →+ X) = 0 := by ext; simp
    rw [this, diagMap_zero]; rfl
  | succ n ih =>
    have : (nsmulAddMonoidHom (n + 1) : X →+ X) = nsmulAddMonoidHom n + AddMonoidHom.id X := by
      ext; simp [succ_nsmul]
    rw [this, diagMap_add, ← ih, diagMap_id]; rfl
theorem isPullback_of_exact (u : Y →+ X) (q : X →+ Z) (hq : Function.Surjective q)
    (h : Function.Exact u q) :
    IsPullback (diagMap S q) (toUnit _) (diagMap S u) (η : 𝟙_ (Over S) ⟶ splitTorus S Y) := by
  have hw : diagMap S q ≫ diagMap S u = toUnit _ ≫ η := by
    have : q.comp u = 0 := by ext y; exact (h _).2 ⟨y, rfl⟩
    rw [← diagMap_comp, this, diagMap_zero]; rfl
  have hmono : ∀ {T : Over S} {a b : T ⟶ splitTorus S Z}, a ≫ diagMap S q = b ≫ diagMap S q → a = b := by
    intro T a b hab
    refine hom_ext fun z => ?_
    obtain ⟨x, rfl⟩ := hq z
    rw [← coord_comp_diagMap_single, hab, coord_comp_diagMap_single]
  refine isPullback_toUnit_of_lift S hw hmono fun {T} t ht => ?_
  have h1 : ∀ y, (coord t).hom (AddMonoidAlgebra.single (u y) 1) = 1 := fun y => by
    rw [← coord_comp_diagMap_single, ht]; exact coord_one T y
  have h2 : ∀ x x', q x = q x' → (coord t).hom (AddMonoidAlgebra.single x 1) =
      (coord t).hom (AddMonoidAlgebra.single x' 1) := fun x x' hx => by
    obtain ⟨y, hy⟩ := (h (x - x')).1 (by rw [map_sub, hx, sub_self])
    rw [show x = u y + x' by rw [hy, sub_add_cancel], ← _root_.one_mul (1 : ZU.{u}),
      ← AddMonoidAlgebra.single_mul_single, map_mul, h1, _root_.one_mul, _root_.one_mul]
  let σ := Function.surjInv hq
  have hσ : ∀ z, q (σ z) = z := Function.surjInv_eq hq
  let g : Multiplicative Z →* Γ(T.left, ⊤) :=
    { toFun := fun z => (coord t).hom (AddMonoidAlgebra.single (σ z.toAdd) 1)
      map_one' := by
        rw [h2 _ 0 (by rw [hσ, _root_.map_zero]; rfl), ← AddMonoidAlgebra.one_def, map_one]
      map_mul' := fun a b => by
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, _root_.one_mul]
        exact h2 _ _ (by rw [_root_.map_add, hσ, hσ, hσ]; rfl) }
  let c : ULift.{u} ℤ →+* Γ(T.left, ⊤) :=
    (Int.castRingHom _).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
  let φ : AddMonoidAlgebra (ULift.{u} ℤ) Z →+* Γ(T.left, ⊤) :=
    AddMonoidAlgebra.liftNCRingHom c g fun _ _ => .all _ _
  refine ⟨ofCoord T (CommRingCat.ofHom φ), hom_ext fun x => ?_⟩
  rw [coord_comp_diagMap_single, coord_ofCoord]
  have : φ (AddMonoidAlgebra.single (q x) 1) = g (Multiplicative.ofAdd (q x)) := by
    simp [φ, AddMonoidAlgebra.liftNCRingHom]
  exact this.trans (h2 _ _ (hσ _))
theorem isPullback_ker (u : Y →+ X) :
    IsPullback (diagMap S (QuotientAddGroup.mk' u.range)) (toUnit _) (diagMap S u)
      (η : 𝟙_ (Over S) ⟶ splitTorus S Y) :=
  isPullback_of_exact S u _ (QuotientAddGroup.mk'_surjective _) fun x =>
    QuotientAddGroup.eq_zero_iff x
theorem isPullback_torsion (n : ℕ) :
    IsPullback (diagMap S (QuotientAddGroup.mk' (nsmulAddMonoidHom n : X →+ X).range)) (toUnit _)
      (mulN (splitTorus S X) n) (η : 𝟙_ (Over S) ⟶ splitTorus S X) := by
  rw [mulN_eq_diagMap]; exact isPullback_ker S _
variable (X) in

def torsionIso (n : ℕ) :
    torsion (splitTorus S X) n ≅ splitTorus S (X ⧸ (nsmulAddMonoidHom n : X →+ X).range) :=
  (isPullback_torsion S n).isoPullback.symm
theorem of_ringMap (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (u : Y →+ X)
    (h : P (Spec.map (ringMap u))) : P (diagMap S u).left :=
  P.of_isPullback (isPullback_diagMap S u) h
instance isAffineHom_diagMap (u : Y →+ X) : IsAffineHom (diagMap S u).left :=
  of_ringMap S @IsAffineHom u inferInstance
section Affine
variable (R : Type u) [CommRing R] (X : Type u) [AddCommGroup X]
abbrev intAlgebra : Algebra ZU.{u} R := ULift.algebra' ℤ R
attribute [local instance] intAlgebra
open scoped AlgebraMonoidAlgebra
theorem isScalarTower_groupRing :
    IsScalarTower ZU.{u} (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra R X) :=
  ⟨fun r a b => by
    obtain ⟨n⟩ := r
    change (n • a) • b = n • (a • b)
    simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩
theorem isPullback_groupRing :
    IsPullback (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X (algebraMap ZU.{u} R))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))))
      (splitTorusAff ZU X).hom (toZ (Spec (.of R))) := by
  have := isScalarTower_groupRing R X
  have : Algebra.IsPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) R (AddMonoidAlgebra R X) :=
    AddMonoidAlgebra.instIsPushout'
  rw [show toZ (Spec (.of R)) = Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} R)) from
    specULiftZIsTerminal.hom_ext _ _]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) R (AddMonoidAlgebra R X))
end Affine
theorem of_affine (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (X : Type u)
    [AddCommGroup X]
    (h : P (Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X))))) :
    P (splitTorus S X).hom :=
  P.of_isPullback (isPullback_torusFst S X) h
instance isAffineHom_hom (X : Type u) [AddCommGroup X] : IsAffineHom (splitTorus S X).hom :=
  of_affine S @IsAffineHom X inferInstance
instance flat_hom (X : Type u) [AddCommGroup X] : Flat (splitTorus S X).hom :=
  of_affine S @Flat X (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))
instance surjective_hom (X : Type u) [AddCommGroup X] : Surjective (splitTorus S X).hom :=
  ⟨fun s => ⟨(η : 𝟙_ (Over S) ⟶ splitTorus S X).left s, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
instance locallyOfFinitePresentation_hom (X : Type u) [AddCommGroup X] [Module.Finite ℤ X] :
    LocallyOfFinitePresentation (splitTorus S X).hom := by
  refine of_affine S @LocallyOfFinitePresentation X
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 ?_)
  have : IsNoetherianRing ZU.{u} :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm
  have : AddGroup.FG X := Module.Finite.iff_addGroup_fg.1 ‹_›
  have : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 this
  exact RingHom.finitePresentation_algebraMap.2
    (Algebra.FinitePresentation.of_finiteType.1 inferInstance)
instance isFinite_hom (X : Type u) [AddCommGroup X] [Finite X] : IsFinite (splitTorus S X).hom :=
  of_affine S @IsFinite X ((IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance))
instance geometricallyIntegral_hom (X : Type u) [AddCommGroup X] [UniqueSums X] :
    GeometricallyIntegral (splitTorus S X).hom := by
  refine ⟨fun K _ y W fst snd h => ?_⟩
  have h2 := h.paste_horiz (isPullback_torusFst S X)
  rw [show y ≫ toZ S = toZ _ from specULiftZIsTerminal.hom_ext _ _] at h2
  have : IsDomain (AddMonoidAlgebra K X) := NoZeroDivisors.to_isDomain _
  exact IsIntegral.of_isIso ((isPullback_groupRing K X).isoIsPullback _ _ h2).hom
instance geometricallyConnected_hom (X : Type u) [AddCommGroup X] [UniqueSums X] :
    GeometricallyConnected (splitTorus S X).hom :=
  ⟨fun _ _ y _ fst snd h =>
    have := (geometricallyIntegral_hom S X).1 y fst snd h
    inferInstance⟩
section Mul
variable (X : Type u) [AddCommGroup X] {n : ℕ}
end Mul
section BaseChange
variable {S} {S' : Scheme.{u}} (f : S' ⟶ S)
theorem isPullback_baseChange (X : Type u) [AddCommGroup X] :
    IsPullback (pullback.fst (splitTorus S X).hom f ≫ torusFst S X)
      ((Over.pullback f).obj (splitTorus S X)).hom (splitTorusAff ZU X).hom (toZ S') := by
  rw [show toZ S' = f ≫ toZ S from specULiftZIsTerminal.hom_ext _ _]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_torusFst S X)
def baseChangeIso (X : Type u) [AddCommGroup X] :
    (Over.pullback f).obj (splitTorus S X) ≅ splitTorus S' X :=
  Over.isoMk (isPullback_baseChange f X).isoPullback
    (isPullback_baseChange f X).isoPullback_hom_snd
theorem baseChangeIso_hom_torusFst (X : Type u) [AddCommGroup X] :
    (baseChangeIso f X).hom.left ≫ torusFst S' X =
      pullback.fst (splitTorus S X).hom f ≫ torusFst S X :=
  (isPullback_baseChange f X).isoPullback_hom_fst
omit [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] in

theorem isMonHom_of_comp {B : Scheme.{u}} (h : S ⟶ B) (g : S' ⟶ B) (e : g = f ≫ h) (G : Over B)
    [GrpObj G] (φ : (Over.pullback f).obj ((Over.pullback h).obj G) ⟶ (Over.pullback g).obj G)
    (hφ : φ.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _) : IsMonHom φ := by
  subst e
  let m := (Functor.mapMonNatIso (Over.pullbackComp f h) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
  have hφ' : φ = m.inv.hom := by
    ext1
    apply pullback.hom_ext
    · rw [hφ]
      simp [m, Over.pullbackComp]
      erw [Category.id_comp]
      simp [Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]
    · exact (Over.w φ).trans (Over.w m.inv.hom).symm
  rw [hφ']
  exact m.inv.isMonHom_hom
instance baseChangeIso_isMonHom (X : Type u) [AddCommGroup X] : IsMonHom (baseChangeIso f X).hom :=
  isMonHom_of_comp f (toZ S) (toZ S') (specULiftZIsTerminal.hom_ext _ _) _ _
    (baseChangeIso_hom_torusFst f X)
end BaseChange
end GlobalTheory.Diag
namespace GlobalTheory.Diag
variable (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
instance smoothOfRelativeDimension_hom :
    SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom :=
  ReciprocityTheory.ChartRestriction.G.H1.torus_dim S X
instance smooth_hom : Smooth (splitTorus S X).hom :=
  (smoothOfRelativeDimension_hom S X).smooth
theorem isAbelianScheme_unit : IsAbelianScheme (𝟙_ (Over S)) :=
  (ReciprocityTheory.ChartRestriction.G.Out.Inh.zeroPolAV S).isAb
def torusExtension {K : Type} [Field K] (p : Spec (.of K) ⟶ S) :
    TorusExtension ((Over.pullback p).obj (splitTorus S X)) where
  X := X
  B := 𝟙_ _
  isAbelian := isAbelianScheme_unit _
  q := toUnit _
  q_hom := inferInstance
  q_flat := by rw [toUnit_left]; exact inferInstanceAs (Flat (pullback.snd _ _))
  q_surjective := by rw [toUnit_left]; exact inferInstanceAs (Surjective (pullback.snd _ _))
  q_quasiCompact := by rw [toUnit_left]; exact inferInstanceAs (QuasiCompact (pullback.snd _ _))
  i := (baseChangeIso p X).inv
  i_hom := inferInstance
  isKernel := isPullback_toUnit_of_lift _ (toUnit_unique _ _) (fun h => (cancel_mono _).1 h)
    fun t _ => ⟨t ≫ (baseChangeIso p X).hom, by simp⟩
instance isSemiAbelian : IsSemiAbelian (splitTorus S X) where
  comm := inferInstance
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  geomConnected := inferInstance
  fibres := fun _ _ _ p => ⟨torusExtension S X p⟩
end GlobalTheory.Diag
namespace GlobalTheory
open Diag
end GlobalTheory


