-- Prove2me | solution 1 for AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9b6c9f3d-d0fe-50f3-a138-4b3edc9b48f6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace FBC0

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
  (A : Type u) [CommRing A] [Algebra k A]

abbrev bc : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

def toSec (U : X.Opens) : CommRingCat.of k ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appLE ⊤ U le_top

theorem appLE_top_top {Y : Scheme.{u}} (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_top = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem toSec_top : toSec fX ⊤ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop := by
  rw [toSec, appLE_top_top]

@[reassoc (attr := simp)]
theorem toSec_map {U V : X.Opens} (i : Opposite.op U ⟶ Opposite.op V) :
    toSec fX U ≫ X.presheaf.map i = toSec fX V := by
  rw [toSec, Category.assoc, Scheme.Hom.appLE_map]
  rfl

abbrev toSecA (U : X.Opens) :
    CommRingCat.of A ⟶ Γ(pullback fX (bc A), (pullback.fst fX (bc A)) ⁻¹ᵁ U) :=
  toSec (pullback.snd fX (bc A)) ((pullback.fst fX (bc A)) ⁻¹ᵁ U)

theorem appLE_congrHom {Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

theorem toSec_app (U : X.Opens) :
    toSec fX U ≫ (pullback.fst fX (bc A)).app U =
      CommRingCat.ofHom (algebraMap k A) ≫ toSecA fX A U := by
  rw [toSec, toSecA, toSec, Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congrHom pullback.condition, ← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ _ le_top,
    appLE_top_top, ← Scheme.ΓSpecIso_inv_naturality_assoc]

theorem isPushout_toSec_app {U : X.Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (algebraMap k A)) (toSec fX U) (toSecA fX A U)
      ((pullback.fst fX (bc A)).app U) := by
  set fst := pullback.fst fX (bc A) with hfst
  set snd := pullback.snd fX (bc A) with hsnd
  haveI : IsAffineHom fst := MorphismProperty.pullback_fst _ _ inferInstance
  have hU' : IsAffineOpen (fst ⁻¹ᵁ U) := hU.preimage fst
  haveI : IsAffine U := hU
  haveI : IsAffine (fst ⁻¹ᵁ U) := hU'

  have sq : IsPullback (fst ∣_ U) ((fst ⁻¹ᵁ U).ι ≫ snd) (U.ι ≫ fX) (bc A) :=
    (isPullback_morphismRestrict fst U).paste_vert (IsPullback.of_hasPullback fX (bc A))

  have c1 : (fst ∣_ U) ≫ hU.isoSpec.hom = hU'.isoSpec.hom ≫ Spec.map (fst.app U) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec fst hU hU' (le_refl (fst ⁻¹ᵁ U))
    rw [Scheme.Hom.appLE_eq_app, IsAffineOpen.fromSpec, IsAffineOpen.fromSpec,
      Category.assoc, ← morphismRestrict_ι] at h
    simp only [← Category.assoc] at h
    rw [cancel_mono] at h

    rw [← cancel_mono hU.isoSpec.inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, h, Iso.hom_inv_id_assoc]
  have c2 : ((fst ⁻¹ᵁ U).ι ≫ snd) ≫ (Iso.refl _).hom = hU'.isoSpec.hom ≫ Spec.map (toSecA fX A U) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec snd (isAffineOpen_top _) hU' le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, IsAffineOpen.fromSpec,
      Category.assoc] at h
    rw [Iso.refl_hom, Category.comp_id, toSecA, toSec, Spec.map_comp, ← cancel_epi hU'.isoSpec.inv,
      Iso.inv_hom_id_assoc, h]
  have c3 : (U.ι ≫ fX) ≫ (Iso.refl _).hom = hU.isoSpec.hom ≫ Spec.map (toSec fX U) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec fX (isAffineOpen_top _) hU le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, IsAffineOpen.fromSpec,
      Category.assoc] at h
    rw [Iso.refl_hom, Category.comp_id, toSec, Spec.map_comp, ← cancel_epi hU.isoSpec.inv,
      Iso.inv_hom_id_assoc, h]
  have sq' : IsPullback (Spec.map (fst.app U)) (Spec.map (toSecA fX A U)) (Spec.map (toSec fX U))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    sq.of_iso hU'.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) c1 c2 c3 (by simp)

  have sq'' : IsPullback (fst.app U).op (toSecA fX A U).op (toSec fX U).op
      (CommRingCat.ofHom (algebraMap k A)).op :=
    IsPullback.of_map Scheme.Spec (congrArg Quiver.Hom.op (toSec_app fX A U)) sq'
  exact sq''.unop

end FBC0

namespace FBC0

section Over

variable (k : Type u) [CommRing k]

scoped instance secAlgebra (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (U : X.Opens) :
    Algebra k Γ(X, U) :=
  (toSec (X ↘ Spec (CommRingCat.of k)) U).hom.toAlgebra

theorem algebraMap_sec (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (U : X.Opens) :
    algebraMap k Γ(X, U) = (toSec (X ↘ Spec (CommRingCat.of k)) U).hom := rfl

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

def resAlgHom {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →ₐ[k] Γ(X, V) :=
  { (X.presheaf.map (homOfLE h).op).hom with
    commutes' := fun a => by
      change (toSec (X ↘ Spec (CommRingCat.of k)) U ≫ X.presheaf.map (homOfLE h).op) a =
        toSec (X ↘ Spec (CommRingCat.of k)) V a
      rw [toSec_map] }

@[scoped simp] theorem resAlgHom_apply {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    resAlgHom k X h s = X.presheaf.map (homOfLE h).op s := rfl

abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →ₗ[k] Γ(X, V) := (resAlgHom k X h).toLinearMap

@[scoped simp] theorem res_apply {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) :
    res k X h s = X.presheaf.map (homOfLE h).op s := rfl

variable (A : Type u) [CommRing A] [Algebra k A]

abbrev XA : Scheme.{u} := pullback (X ↘ Spec (CommRingCat.of k)) (bc A)

abbrev fstA : XA k X A ⟶ X := pullback.fst (X ↘ Spec (CommRingCat.of k)) (bc A)

example : (XA k X A ↘ Spec (CommRingCat.of A)) = pullback.snd (X ↘ Spec (CommRingCat.of k)) (bc A) :=
  rfl

scoped instance secAlgebraK (W : (XA k X A).Opens) : Algebra k Γ(XA k X A, W) :=
  ((algebraMap A Γ(XA k X A, W)).comp (algebraMap k A)).toAlgebra

scoped instance isScalarTower_secK (W : (XA k X A).Opens) : IsScalarTower k A Γ(XA k X A, W) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def appAlgHom (V : X.Opens) : Γ(X, V) →ₐ[k] Γ(XA k X A, (fstA k X A) ⁻¹ᵁ V) :=
  { ((fstA k X A).app V).hom with
    commutes' := fun a => by
      change (toSec (X ↘ Spec (CommRingCat.of k)) V ≫ (fstA k X A).app V) a =
        (CommRingCat.ofHom (algebraMap k A) ≫ toSecA (X ↘ Spec (CommRingCat.of k)) A V) a
      rw [toSec_app] }

@[scoped simp] theorem appAlgHom_apply (V : X.Opens) (s : Γ(X, V)) :
    appAlgHom k X A V s = (fstA k X A).app V s := rfl

scoped instance appAlgebra (V : X.Opens) : Algebra Γ(X, V) Γ(XA k X A, (fstA k X A) ⁻¹ᵁ V) :=
  ((fstA k X A).app V).hom.toAlgebra

scoped instance isScalarTower_app (V : X.Opens) : IsScalarTower k Γ(X, V) Γ(XA k X A, (fstA k X A) ⁻¹ᵁ V) :=
  IsScalarTower.of_algebraMap_eq fun a => ((appAlgHom k X A V).commutes a).symm

def baseChangeSections (V : X.Opens) : A ⊗[k] Γ(X, V) →ₐ[A] Γ(XA k X A, (fstA k X A) ⁻¹ᵁ V) :=
  Algebra.TensorProduct.lift (Algebra.ofId A _) (appAlgHom k X A V) fun _ _ => Commute.all _ _

@[scoped simp] theorem baseChangeSections_tmul (V : X.Opens) (a : A) (s : Γ(X, V)) :
    baseChangeSections k X A V (a ⊗ₜ s) = algebraMap A _ a * (fstA k X A).app V s :=
  Algebra.TensorProduct.lift_tmul _ _ _ a s

theorem preimage_mono {U V : X.Opens} (h : V ≤ U) : (fstA k X A) ⁻¹ᵁ V ≤ (fstA k X A) ⁻¹ᵁ U :=
  fun _ hx => h hx

theorem res_baseChangeSections {U V : X.Opens} (h : V ≤ U) (x : A ⊗[k] Γ(X, U)) :
    res A (XA k X A) (preimage_mono k X A h) (baseChangeSections k X A U x) =
      baseChangeSections k X A V (LinearMap.lTensor A (res k X h) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [LinearMap.lTensor_tmul, res_apply, baseChangeSections_tmul, baseChangeSections_tmul,
      res_apply, map_mul]
    congr 1
    · change (toSec (XA k X A ↘ _) _ ≫ (XA k X A).presheaf.map _) a = toSec (XA k X A ↘ _) _ a
      rw [toSec_map]
    · exact (ConcreteCategory.congr_hom ((fstA k X A).naturality (homOfLE h).op) s).symm

theorem isPushout_sections {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.IsPushout k A Γ(X, U) Γ(XA k X A, (fstA k X A) ⁻¹ᵁ U) :=
  CommRingCat.isPushout_iff_isPushout.mp (isPushout_toSec_app (X ↘ Spec (CommRingCat.of k)) A hU)

theorem baseChangeSections_eq_equiv {U : X.Opens} (hU : IsAffineOpen U) :
    haveI := isPushout_sections k X A hU
    (baseChangeSections k X A U : A ⊗[k] Γ(X, U) → _) =
      Algebra.IsPushout.equiv k A Γ(X, U) (Γ(XA k X A, (fstA k X A) ⁻¹ᵁ U)) := by
  haveI := isPushout_sections k X A hU
  have : baseChangeSections k X A U = (Algebra.IsPushout.equiv k A Γ(X, U)
      Γ(XA k X A, (fstA k X A) ⁻¹ᵁ U)).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a s
    rw [baseChangeSections_tmul]
    change _ = Algebra.IsPushout.equiv k A Γ(X, U) Γ(XA k X A, (fstA k X A) ⁻¹ᵁ U) (a ⊗ₜ s)
    rw [Algebra.IsPushout.equiv_tmul]
    rfl
  exact congrArg (fun f : _ →ₐ[A] _ => (f : A ⊗[k] Γ(X, U) → _)) this

theorem bijective_baseChangeSections {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (baseChangeSections k X A U) := by
  haveI := isPushout_sections k X A hU
  rw [baseChangeSections_eq_equiv k X A hU]
  exact (Algebra.IsPushout.equiv k A Γ(X, U) _).bijective

end Over

end FBC0
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0"

namespace FBC0

open TopologicalSpace Opposite

section Sheaf

variable {Y : Scheme.{u}} {ι : Type u} (W : ι → Y.Opens) (V : Y.Opens) (hle : ∀ i, W i ≤ V) (hV : V ≤ iSup W)

include hV in

theorem sections_ext (s t : Γ(Y, V)) (h : ∀ i, Y.presheaf.map (homOfLE (hle i)).op s = Y.presheaf.map (homOfLE (hle i)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' Y.sheaf W V (fun i => homOfLE (hle i)) hV s t h

include hV in

theorem sections_glue (p : ∀ i, Γ(Y, W i))
    (hp : ∀ i j, Y.presheaf.map (homOfLE inf_le_left).op (p i) = Y.presheaf.map (homOfLE inf_le_right).op (p j)) :
    ∃ s : Γ(Y, V), ∀ i, Y.presheaf.map (homOfLE (hle i)).op s = p i := by
  have hc : TopCat.Presheaf.IsCompatible Y.sheaf.1 W p := fun i j => hp i j
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf W V (fun i => homOfLE (hle i)) hV p hc
  exact ⟨s, hs⟩

end Sheaf
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0"

theorem bijective_of_flat_of_exact
    {k : Type u} [CommRing k] {A : Type u} [CommRing A] [Algebra k A] [Module.Flat k A]
    {M P Q : Type u} [AddCommGroup M] [AddCommGroup P] [AddCommGroup Q] [Module k M] [Module k P] [Module k Q]
    {M' P' Q' : Type u} [AddCommGroup M'] [AddCommGroup P'] [AddCommGroup Q']
    [Module k M'] [Module k P'] [Module k Q']
    (ρ : M →ₗ[k] P) (δ : P →ₗ[k] Q) (hρ : Function.Injective ρ) (hex : Function.Exact ρ δ)
    (ρ' : M' →ₗ[k] P') (δ' : P' →ₗ[k] Q') (hρ' : Function.Injective ρ') (hex' : Function.Exact ρ' δ')
    (α : A ⊗[k] M →ₗ[k] M') (β : A ⊗[k] P →ₗ[k] P') (γ : A ⊗[k] Q →ₗ[k] Q')
    (hαβ : β ∘ₗ (ρ.lTensor A) = ρ' ∘ₗ α) (hβγ : γ ∘ₗ (δ.lTensor A) = δ' ∘ₗ β)
    (hβ : Function.Bijective β) (hγ : Function.Injective γ) :
    Function.Bijective α := by
  have hρA : Function.Injective (ρ.lTensor A) := Module.Flat.lTensor_preserves_injective_linearMap ρ hρ
  have hexA : Function.Exact (ρ.lTensor A) (δ.lTensor A) := Module.Flat.lTensor_exact A hex
  constructor
  · intro x y hxy
    apply hρA
    apply hβ.1
    have := congrArg ρ' hxy
    rwa [← LinearMap.comp_apply (f := ρ'), ← LinearMap.comp_apply (f := ρ'), ← hαβ] at this
  · intro m'
    obtain ⟨p, hp⟩ := hβ.2 (ρ' m')
    have hδp : δ.lTensor A p = 0 := by
      apply hγ
      rw [map_zero, ← LinearMap.comp_apply, hβγ, LinearMap.comp_apply, hp]
      exact hex' |>.apply_apply_eq_zero m'
    obtain ⟨m, rfl⟩ := (hexA p).mp hδp
    refine ⟨m, hρ' ?_⟩
    rw [← LinearMap.comp_apply, ← hαβ, LinearMap.comp_apply, hp]

section Cech

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  (A : Type u) [CommRing A] [Algebra k A]

abbrev resPi {ι : Type u} {V : X.Opens} (W : ι → X.Opens) (hle : ∀ i, W i ≤ V) :
    Γ(X, V) →ₗ[k] (∀ i, Γ(X, W i)) :=
  LinearMap.pi fun i => res k X (hle i)

theorem injective_resPi {ι : Type u} {V : X.Opens} (W : ι → X.Opens) (hle : ∀ i, W i ≤ V) (hV : V ≤ iSup W) :
    Function.Injective (resPi k X W hle) := by
  intro s t hst
  refine sections_ext W V hle hV s t fun i => ?_
  have := congrFun hst i
  exact this

theorem piRight_lTensor_resPi {ι : Type u} [Fintype ι] [DecidableEq ι] {V : X.Opens} (W : ι → X.Opens)
    (hle : ∀ i, W i ≤ V) (x : A ⊗[k] Γ(X, V)) (i : ι) :
    TensorProduct.piRight k k A (fun i => Γ(X, W i)) (LinearMap.lTensor A (resPi k X W hle) x) i =
      LinearMap.lTensor A (res k X (hle i)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a s => simp [TensorProduct.piRight_apply]

theorem injective_baseChangeSections [Module.Flat k A] {V : X.Opens} (hV : IsCompact (V : Set X)) :
    Function.Injective (baseChangeSections k X A V) := by
  classical

  have hbasis := X.isBasis_affineOpens
  obtain ⟨ι, hfin, W, hWaff, hWle, hVW⟩ : ∃ (ι : Type u) (_ : Fintype ι) (W : ι → X.Opens),
      (∀ i, IsAffineOpen (W i)) ∧ (∀ i, W i ≤ V) ∧ V ≤ iSup W := by

    have hcov : (V : Set X) ⊆ ⋃ U ∈ {U : X.Opens | IsAffineOpen U ∧ U ≤ V}, (U : Set X) := by
      intro x hx
      obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp hbasis hx
      exact Set.mem_biUnion (x := U) (show U ∈ {U : X.Opens | IsAffineOpen U ∧ U ≤ V} from ⟨hU, hUV⟩) hxU
    obtain ⟨t, htsub, htfin, hVt⟩ := hV.elim_finite_subcover_image (fun U hU => U.isOpen) hcov
    haveI := htfin.fintype
    refine ⟨t, inferInstance, fun U => U.1, fun U => (htsub U.2).1, fun U => (htsub U.2).2, ?_⟩
    intro x hx
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (hVt hx)
    exact Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩
  haveI := hfin
  intro x y hxy

  have hcomp : LinearMap.lTensor A (resPi k X W hWle) x = LinearMap.lTensor A (resPi k X W hWle) y := by
    apply (TensorProduct.piRight k k A (fun i => Γ(X, W i))).injective
    funext i
    rw [piRight_lTensor_resPi, piRight_lTensor_resPi]
    apply (bijective_baseChangeSections k X A (hWaff i)).1
    rw [← res_baseChangeSections, ← res_baseChangeSections, hxy]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (injective_resPi k X W hWle hVW) hcomp

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    res k X h₂ (res k X h₁ s) = res k X (h₂.trans h₁) s := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op) s = X.presheaf.map _ s
  rw [← Functor.map_comp]
  rfl

theorem exists_finite_affine_cover {V : X.Opens} (hV : IsCompact (V : Set X)) :
    ∃ (ι : Type u) (_ : Fintype ι) (W : ι → X.Opens), (∀ i, IsAffineOpen (W i)) ∧ (∀ i, W i ≤ V) ∧ V ≤ iSup W := by
  classical
  have hbasis := X.isBasis_affineOpens
  have hcov : (V : Set X) ⊆ ⋃ U ∈ {U : X.Opens | IsAffineOpen U ∧ U ≤ V}, (U : Set X) := by
    intro x hx
    obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp hbasis hx
    exact Set.mem_biUnion (x := U) (show U ∈ {U : X.Opens | IsAffineOpen U ∧ U ≤ V} from ⟨hU, hUV⟩) hxU
  obtain ⟨t, htsub, htfin, hVt⟩ := hV.elim_finite_subcover_image (fun U hU => U.isOpen) hcov
  haveI := htfin.fintype
  refine ⟨t, inferInstance, fun U => U.1, fun U => (htsub U.2).1, fun U => (htsub U.2).2, ?_⟩
  intro x hx
  obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (hVt hx)
  exact Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩

abbrev cechDiff {ι : Type u} (U : ι → X.Opens) :
    (∀ i, Γ(X, U i)) →ₗ[k] (∀ ij : ι × ι, Γ(X, U ij.1 ⊓ U ij.2)) :=
  LinearMap.pi fun ij => res k X inf_le_left ∘ₗ LinearMap.proj ij.1 - res k X inf_le_right ∘ₗ LinearMap.proj ij.2

theorem exact_resPi_cechDiff {ι : Type u} {V : X.Opens} (U : ι → X.Opens) (hle : ∀ i, U i ≤ V) (hV : V ≤ iSup U) :
    Function.Exact (resPi k X U hle) (cechDiff k X U) := by
  intro p
  constructor
  · intro hp
    have hp' : ∀ i j, X.presheaf.map (homOfLE inf_le_left).op (p i) = X.presheaf.map (homOfLE inf_le_right).op (p j) :=
      fun i j => sub_eq_zero.mp (congrFun hp (i, j))
    obtain ⟨s, hs⟩ := sections_glue U V hle hV p hp'
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext ij
    change res k X _ (res k X _ s) - res k X _ (res k X _ s) = 0
    rw [res_res, res_res, sub_self]

theorem bijective_baseChangeSections_top [CompactSpace X] [QuasiSeparatedSpace X] [Module.Flat k A] :
    Function.Bijective (baseChangeSections k X A ⊤) := by
  classical
  obtain ⟨ι, hfin, U, hUaff, -, hXU⟩ := exists_finite_affine_cover X (V := ⊤) (by simpa using isCompact_univ)
  haveI := hfin

  let U' : ι → (XA k X A).Opens := fun i => (fstA k X A) ⁻¹ᵁ (U i)
  have hle' : ∀ i, U' i ≤ (fstA k X A) ⁻¹ᵁ ⊤ := fun i => preimage_mono k X A le_top
  have hXU' : (fstA k X A) ⁻¹ᵁ ⊤ ≤ iSup U' := by
    intro x _
    have hx : (fstA k X A).base x ∈ (iSup U : X.Opens) := hXU trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩

  let ρ := resPi k X U (fun _ => le_top)
  let δ := cechDiff k X U
  let ρ' : Γ(XA k X A, (fstA k X A) ⁻¹ᵁ ⊤) →ₗ[k] (∀ i, Γ(XA k X A, U' i)) :=
    (resPi A (XA k X A) U' hle').restrictScalars k
  let δ' : (∀ i, Γ(XA k X A, U' i)) →ₗ[k] (∀ ij : ι × ι, Γ(XA k X A, U' ij.1 ⊓ U' ij.2)) :=
    (cechDiff A (XA k X A) U').restrictScalars k

  let α : A ⊗[k] Γ(X, ⊤) →ₗ[k] Γ(XA k X A, (fstA k X A) ⁻¹ᵁ ⊤) :=
    (baseChangeSections k X A ⊤).toLinearMap.restrictScalars k
  let eP := TensorProduct.piRight k k A (fun i => Γ(X, U i))
  let eQ := TensorProduct.piRight k k A (fun ij : ι × ι => Γ(X, U ij.1 ⊓ U ij.2))
  let β : A ⊗[k] (∀ i, Γ(X, U i)) →ₗ[k] (∀ i, Γ(XA k X A, U' i)) :=
    (LinearMap.pi fun i => (baseChangeSections k X A (U i)).toLinearMap.restrictScalars k ∘ₗ LinearMap.proj i) ∘ₗ
      eP.toLinearMap
  let γ : A ⊗[k] (∀ ij : ι × ι, Γ(X, U ij.1 ⊓ U ij.2)) →ₗ[k] (∀ ij : ι × ι, Γ(XA k X A, U' ij.1 ⊓ U' ij.2)) :=
    (LinearMap.pi fun ij => (baseChangeSections k X A (U ij.1 ⊓ U ij.2)).toLinearMap.restrictScalars k ∘ₗ
      LinearMap.proj ij) ∘ₗ eQ.toLinearMap
  have hαβ : β ∘ₗ (ρ.lTensor A) = ρ' ∘ₗ α := by
    apply TensorProduct.ext'
    intro a s
    funext i
    change baseChangeSections k X A (U i) (eP (a ⊗ₜ ρ s) i) = res A (XA k X A) (hle' i) (baseChangeSections k X A ⊤ (a ⊗ₜ s))
    rw [res_baseChangeSections, LinearMap.lTensor_tmul]
    simp only [eP, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    rfl
  have hβγ : γ ∘ₗ (δ.lTensor A) = δ' ∘ₗ β := by
    apply TensorProduct.ext'
    intro a p
    funext ij
    change baseChangeSections k X A _ (eQ (a ⊗ₜ δ p) ij) =
      res A (XA k X A) _ (baseChangeSections k X A (U ij.1) (eP (a ⊗ₜ p) ij.1)) -
        res A (XA k X A) _ (baseChangeSections k X A (U ij.2) (eP (a ⊗ₜ p) ij.2))
    rw [res_baseChangeSections, res_baseChangeSections]
    simp only [eP, eQ, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    change baseChangeSections k X A _ (a ⊗ₜ (res k X _ (p ij.1) - res k X _ (p ij.2))) = _
    rw [TensorProduct.tmul_sub, map_sub]
    rfl
  have hρ : Function.Injective ρ := injective_resPi k X U _ hXU
  have hex : Function.Exact ρ δ := exact_resPi_cechDiff k X U _ hXU
  have hρ' : Function.Injective ρ' := injective_resPi A (XA k X A) U' hle' hXU'
  have hex' : Function.Exact ρ' δ' := exact_resPi_cechDiff A (XA k X A) U' hle' hXU'
  have hβ : Function.Bijective β := by
    have hg : Function.Bijective (fun (q : ∀ i, A ⊗[k] Γ(X, U i)) (i : ι) => baseChangeSections k X A (U i) (q i)) :=
      ⟨fun q q' h => funext fun i => (bijective_baseChangeSections k X A (hUaff i)).1 (congrFun h i),
       fun r => ⟨fun i => ((bijective_baseChangeSections k X A (hUaff i)).2 (r i)).choose,
         funext fun i => ((bijective_baseChangeSections k X A (hUaff i)).2 (r i)).choose_spec⟩⟩
    have hβeq : (β : A ⊗[k] (∀ i, Γ(X, U i)) → ∀ i, Γ(XA k X A, U' i)) =
        (fun (q : ∀ i, A ⊗[k] Γ(X, U i)) (i : ι) => baseChangeSections k X A (U i) (q i)) ∘ eP := rfl
    rw [hβeq]
    exact hg.comp eP.bijective
  have hγ : Function.Injective γ := by
    intro x y hxy
    apply eQ.injective
    funext ij
    have hc : IsCompact ((U ij.1 ⊓ U ij.2 : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (U ij.1).isOpen (hUaff ij.1).isCompact (U ij.2).isOpen (hUaff ij.2).isCompact
    exact injective_baseChangeSections k X A hc (congrFun hxy ij)
  exact bijective_of_flat_of_exact ρ δ hρ hex ρ' δ' hρ' hex' α β γ hαβ hβγ hβ hγ

end Cech
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0"

section Final

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
  (A : Type u) [CommRing A] [Algebra k A]

theorem isPushout_appTop [CompactSpace X] [QuasiSeparatedSpace X] [Module.Flat k A] :
    IsPushout (CommRingCat.ofHom (algebraMap k A))
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)
      (pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop := by
  letI : X.Over (Spec (CommRingCat.of k)) := ⟨fX⟩
  have hbij := bijective_baseChangeSections_top k X A
  let e : A ⊗[k] Γ(X, ⊤) ≃ₐ[A] Γ(XA k X A, (fstA k X A) ⁻¹ᵁ ⊤) :=
    AlgEquiv.ofBijective (baseChangeSections k X A ⊤) hbij
  have h0 := CommRingCat.isPushout_tensorProduct k A Γ(X, ⊤)
  refine IsPushout.of_iso h0 (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    (by simp) ?_ ?_ ?_
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, ← toSec_top]
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    change e (a ⊗ₜ 1) = _
    change baseChangeSections k X A ⊤ (a ⊗ₜ 1) = _
    rw [baseChangeSections_tmul, map_one, mul_one]
    change (toSec (pullback.snd (X ↘ Spec (CommRingCat.of k)) (bc A)) ⊤) a = _
    rw [toSec_top]
    rfl
  · rw [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    refine RingHom.ext fun s => ?_
    change e (1 ⊗ₜ s) = _
    change baseChangeSections k X A ⊤ (1 ⊗ₜ s) = _
    rw [baseChangeSections_tmul, map_one, one_mul]
    rfl

theorem bijective_appTop_snd {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom := by
  have h := isPushout_appTop fX A
  haveI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop) := by
    haveI : IsIso ((forget CommRingCat).map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop)) :=
      (isIso_iff_bijective _).mpr hX
    exact isIso_of_reflects_iso _ (forget CommRingCat)
  haveI := h.isIso_inl_of_isIso
  exact ConcreteCategory.bijective_of_isIso _

end Final
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0"

end FBC0
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop.FBC0"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom :=
  FBC0.bijective_appTop_snd fX hX A

end S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop (solution)
