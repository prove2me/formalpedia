-- Prove2me | solution 1 for AlgebraicGeometry.exists_root_fromNormalization_kummer_existsUnique_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b58fb063-380a-5f93-9f4a-4f9de7619e47

import Mathlib
import Theorems.Thm_AlgebraicGeometry_existsUnique_lift_fromNormalization_kummer_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial TopologicalSpace Opposite"

namespace KummerLift

variable {X : Scheme.{u}} [IsIntegral X]

theorem genericPoint_mem (V : X.Opens) [hV : Nonempty V] : genericPoint X ∈ V :=
  ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)

theorem preimage_eq_top {A : CommRingCat.{u}} (φ : X.functionField ⟶ A) (V : X.Opens) [hV : Nonempty V] :
    (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V = ⊤ := by
  apply top_le_iff.mp
  intro p _
  change (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)) p ∈ V
  have hmem : (X.fromSpecStalk (genericPoint X)) ((Spec.map φ) p) ∈
      Set.range (X.fromSpecStalk (genericPoint X)) := Set.mem_range_self _
  rw [Scheme.range_fromSpecStalk] at hmem
  rw [Scheme.Hom.comp_apply]
  exact hmem.mem_open V.isOpen (genericPoint_mem V)

theorem app_eq {A : CommRingCat.{u}} (φ : X.functionField ⟶ A) (V : X.Opens) [hV : Nonempty V] :
    (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)).app V =
      X.presheaf.germ V (genericPoint X) (genericPoint_mem V) ≫ φ ≫ (Scheme.ΓSpecIso A).inv ≫
        (Spec A).presheaf.map (homOfLE (le_top :
          (Spec.map φ ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V ≤ ⊤)).op := by
  rw [Scheme.Hom.comp_app, Scheme.fromSpecStalk_app (genericPoint_mem V)]
  simp only [Category.assoc]
  have hnat := (Spec.map φ).naturality
    (homOfLE (le_top : (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ V ≤ ⊤)).op
  rw [Quiver.Hom.unop_op] at hnat
  erw [hnat]
  have h2 : (Scheme.ΓSpecIso _).inv ≫ (Spec.map φ).app ⊤ = φ ≫ (Scheme.ΓSpecIso A).inv :=
    (Scheme.ΓSpecIso_inv_naturality φ).symm
  rw [← Category.assoc (Scheme.ΓSpecIso _).inv, h2]
  erw [Category.assoc]
  rfl

section KummerAlgebra

variable (k : ℕ) (g : X.functionField)

abbrev KA : Type u := AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)

noncomputable abbrev φK : X.functionField ⟶ CommRingCat.of (KA k g) :=
  CommRingCat.ofHom (algebraMap X.functionField (KA k g))

noncomputable abbrev fK : Spec (CommRingCat.of (KA k g)) ⟶ X :=
  Spec.map (φK k g) ≫ X.fromSpecStalk (genericPoint X)

noncomputable def secIso (V : X.Opens) [Nonempty V] :
    Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V) ≅ CommRingCat.of (KA k g) :=
  (Spec (CommRingCat.of (KA k g))).presheaf.mapIso (eqToIso (preimage_eq_top (φK k g) V).symm).op ≪≫
    Scheme.ΓSpecIso _

theorem secIso_inv (V : X.Opens) [Nonempty V] :
    (secIso k g V).inv = (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv ≫
      (Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE (le_top : (fK k g) ⁻¹ᵁ V ≤ ⊤)).op := by
  simp only [secIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv]
  congr 2

theorem secIso_hom (V : X.Opens) [Nonempty V] :
    (secIso k g V).hom = (Spec (CommRingCat.of (KA k g))).presheaf.map
        (homOfLE (le_of_eq (preimage_eq_top (φK k g) V).symm) : ⊤ ⟶ (fK k g) ⁻¹ᵁ V).op ≫
      (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).hom := by
  simp only [secIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
  congr 2

theorem secIso_hom_app (V : X.Opens) [Nonempty V] (r : Γ(X, V)) :
    (secIso k g V).hom (((fK k g).app V) r) = algebraMap X.functionField (KA k g) (X.germToFunctionField V r) := by
  have h1 : ((fK k g).app V) r = (secIso k g V).inv (algebraMap X.functionField (KA k g) (X.germToFunctionField V r)) := by
    rw [secIso_inv]
    change ((fK k g).app V) r = ((φK k g) ≫ (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv ≫
      (Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE (le_top : (fK k g) ⁻¹ᵁ V ≤ ⊤)).op)
        (X.germToFunctionField V r)
    rw [← CommRingCat.comp_apply]
    erw [app_eq (φK k g) V]
  rw [h1, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

theorem secIso_hom_res {V V' : X.Opens} [Nonempty V] [Nonempty V'] (i : (fK k g) ⁻¹ᵁ V' ⟶ (fK k g) ⁻¹ᵁ V)
    (z : Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V)) :
    (secIso k g V').hom ((Spec (CommRingCat.of (KA k g))).presheaf.map i.op z) = (secIso k g V).hom z := by
  have hc : (Spec (CommRingCat.of (KA k g))).presheaf.map i.op ≫ (Spec (CommRingCat.of (KA k g))).presheaf.map
      (homOfLE (le_of_eq (preimage_eq_top (φK k g) V').symm) : ⊤ ⟶ (fK k g) ⁻¹ᵁ V').op =
      (Spec (CommRingCat.of (KA k g))).presheaf.map
        (homOfLE (le_of_eq (preimage_eq_top (φK k g) V).symm) : ⊤ ⟶ (fK k g) ⁻¹ᵁ V).op := by
    rw [← Functor.map_comp]; rfl
  rw [secIso_hom, secIso_hom, CommRingCat.comp_apply, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply ((Spec (CommRingCat.of (KA k g))).presheaf.map i.op), hc]

noncomputable def secAlgEquiv (V : X.Opens) [Nonempty V] :
    letI := ((fK k g).app V).hom.toAlgebra
    Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V) ≃ₐ[Γ(X, V)] KA k g :=
  letI := ((fK k g).app V).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := (secIso k g V).commRingCatIsoToRingEquiv) (fun r => by
    change (secIso k g V).hom (((fK k g).app V) r) = _
    rw [secIso_hom_app, IsScalarTower.algebraMap_apply Γ(X, V) X.functionField (KA k g)]
    rfl)

theorem secAlgEquiv_apply (V : X.Opens) [Nonempty V] (z : Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V)) :
    letI := ((fK k g).app V).hom.toAlgebra
    secAlgEquiv k g V z = (secIso k g V).hom z := rfl

end KummerAlgebra

theorem algebraMap_germ (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) =
      @Scheme.germToFunctionField X _ U ⟨⟨x, hx⟩⟩ s := by
  rw [RingHom.algebraMap_toAlgebra]
  change (X.presheaf.germ U x hx ≫ X.presheaf.stalkSpecializes _) s = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

def HasValue (U : X.Opens) (s : Γ(X, U)) (t : X.functionField) : Prop :=
  ∀ (x : X) (hx : x ∈ U), algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = t

theorem hasValue_iff_of_mem (U : X.Opens) (s : Γ(X, U)) (t : X.functionField) (x : X) (hx : x ∈ U) :
    HasValue U s t ↔ @Scheme.germToFunctionField X _ U ⟨⟨x, hx⟩⟩ s = t := by
  constructor
  · intro h; rw [← algebraMap_germ U x hx s]; exact h x hx
  · intro h y hy
    rw [algebraMap_germ U y hy s]
    exact h

theorem HasValue.germToFunctionField_eq {U : X.Opens} {s : Γ(X, U)} {t : X.functionField} (h : HasValue U s t)
    [hU : Nonempty U] : X.germToFunctionField U s = t := by
  obtain ⟨⟨x, hx⟩⟩ := hU
  exact (hasValue_iff_of_mem U s t x hx).mp h

theorem HasValue.res {U V : X.Opens} {s : Γ(X, U)} {t : X.functionField} (h : HasValue U s t) (i : V ⟶ U) :
    HasValue V (X.presheaf.map i.op s) t := by
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact h x (i.le hx)

theorem HasValue.mul {U : X.Opens} {s s' : Γ(X, U)} {t t' : X.functionField} (h : HasValue U s t)
    (h' : HasValue U s' t') : HasValue U (s * s') (t * t') := by
  intro x hx
  rw [map_mul, map_mul, h x hx, h' x hx]

theorem HasValue.pow {U : X.Opens} {s : Γ(X, U)} {t : X.functionField} (h : HasValue U s t) (n : ℕ) :
    HasValue U (s ^ n) (t ^ n) := by
  intro x hx
  rw [map_pow, map_pow, h x hx]

theorem HasValue.eq {U : X.Opens} {s s' : Γ(X, U)} {t : X.functionField} (h : HasValue U s t)
    (h' : HasValue U s' t) : s = s' := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  change algebraMap _ _ (X.presheaf.germ U x hx s) = algebraMap _ _ (X.presheaf.germ U x hx s')
  rw [h x hx, h' x hx]

theorem HasValue.isUnit {U : X.Opens} {s : Γ(X, U)} {t : X.functionField} (h : HasValue U s t) (ht : t ≠ 0)
    (hinv : ∀ (x : X), x ∈ U → t⁻¹ ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) : IsUnit s := by
  apply AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ X.toLocallyRingedSpace.toRingedSpace U s
  intro x hx
  obtain ⟨tx, htx⟩ := hinv x hx
  refine isUnit_iff_exists_inv.mpr ⟨tx, ?_⟩
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, map_one, htx]
  change algebraMap _ _ (X.presheaf.germ U x hx s) * t⁻¹ = 1
  rw [h x hx, mul_inv_cancel₀ ht]

theorem exists_hasValue (U : X.Opens) (t : X.functionField)
    (ht : ∀ (x : X), x ∈ U → t ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ s : Γ(X, U), HasValue U s t := by
  classical

  have hloc : ∀ x : U, ∃ (V : X.Opens) (_ : x.1 ∈ V) (_ : V ≤ U) (s : Γ(X, V)), HasValue V s t := by
    rintro ⟨x, hx⟩
    obtain ⟨sx, hsx⟩ := ht x hx
    obtain ⟨V, hVU, hxV, s, hs⟩ := X.presheaf.exists_le_germ_eq sx hx
    refine ⟨V, hxV, hVU, s, (hasValue_iff_of_mem V s t x hxV).mpr ?_⟩
    rw [← algebraMap_germ V x hxV s, hs, hsx]
  choose V hxV hVU sf hsf using hloc
  have hcover : U ≤ iSup V := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
    intro i j
    exact ((hsf i).res _).eq ((hsf j).res _)
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf V U (fun i => homOfLE (hVU i)) hcover sf hcompat
  refine ⟨s, fun x hx => ?_⟩
  have hres : X.presheaf.map (homOfLE (hVU ⟨x, hx⟩)).op s = sf ⟨x, hx⟩ := hs ⟨x, hx⟩
  have := (hsf ⟨x, hx⟩) x (hxV ⟨x, hx⟩)
  rw [← hres, TopCat.Presheaf.germ_res_apply] at this
  exact this

section Yside

variable (k : ℕ) (g : X.functionField)

theorem root_pow : (AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)) ^ k =
    algebraMap X.functionField (KA k g) g := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
  rw [h]; rfl

noncomputable def yval (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) :
    Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V) →+* KA k g :=
  letI := ((fK k g).app V).hom.toAlgebra
  ((secIso k g V).hom.hom.comp
    (integralClosure Γ(X, V) Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V)).val.toRingHom).comp
    ((fK k g).normalizationObjIso hV).hom.hom

theorem yval_apply (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) :
    letI := ((fK k g).app V).hom.toAlgebra
    yval k g V hV s = (secIso k g V).hom (((fK k g).normalizationObjIso hV).hom s).val := rfl

theorem yval_injective (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) : Function.Injective (yval k g V hV) := by
  letI := ((fK k g).app V).hom.toAlgebra
  intro s s' hss'
  rw [yval_apply, yval_apply] at hss'
  have h1 := (secIso k g V).commRingCatIsoToRingEquiv.injective hss'
  have h2 := Subtype.val_injective h1
  exact ((fK k g).normalizationObjIso hV).commRingCatIsoToRingEquiv.injective h2

theorem preimage_toNormalization (V : X.Opens) :
    (fK k g).toNormalization ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ V) = (fK k g) ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]

theorem yval_eq_appLE (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) :
    yval k g V hV s = (secIso k g V).hom ((fK k g).toNormalization.appLE ((fK k g).fromNormalization ⁻¹ᵁ V)
      ((fK k g) ⁻¹ᵁ V) (preimage_toNormalization k g V).ge s) := by
  letI := ((fK k g).app V).hom.toAlgebra
  rw [yval_apply, ← (fK k g).normalizationObjIso_hom_val hV]
  rfl

theorem yval_res {V V' : X.Opens} [Nonempty V] [Nonempty V'] (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (i : (fK k g).fromNormalization ⁻¹ᵁ V' ⟶ (fK k g).fromNormalization ⁻¹ᵁ V)
    (s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) :
    yval k g V' hV' (((fK k g).normalization).presheaf.map i.op s) = yval k g V hV s := by
  have hi : (fK k g) ⁻¹ᵁ V' ≤ (fK k g) ⁻¹ᵁ V := by
    rw [preimage_eq_top, preimage_eq_top]
  rw [yval_eq_appLE, yval_eq_appLE, ← CommRingCat.comp_apply (((fK k g).normalization).presheaf.map i.op),
    Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_map _ (preimage_toNormalization k g V).ge (homOfLE hi).op,
    CommRingCat.comp_apply, secIso_hom_res]

theorem yval_app (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) (r : Γ(X, V)) :
    yval k g V hV ((fK k g).fromNormalization.app V r) = algebraMap X.functionField (KA k g) (X.germToFunctionField V r) := by
  letI := ((fK k g).app V).hom.toAlgebra
  have h1 : ((fK k g).normalizationObjIso hV).hom ((fK k g).fromNormalization.app V r) =
      algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(Spec (CommRingCat.of (KA k g)), (fK k g) ⁻¹ᵁ V)) r := by
    rw [(fK k g).fromNormalization_app hV]
    change (((fK k g).normalizationObjIso hV).inv ≫ ((fK k g).normalizationObjIso hV).hom) (algebraMap _ _ r) = _
    rw [Iso.inv_hom_id]
    rfl
  rw [yval_apply, h1, ← secIso_hom_app]
  rfl

theorem exists_yval_eq_root (hk : k ≠ 0) (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V) (h : X.functionField)
    (uV : Γ(X, V)) (huV : X.germToFunctionField V uV = g / h ^ k) :
    ∃ T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V),
      yval k g V hV T = algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _ := by
  letI := ((fK k g).app V).hom.toAlgebra
  set e := secAlgEquiv k g V with he
  set ρ : KA k g := algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _ with hρ
  have hρk : ρ ^ k = algebraMap X.functionField (KA k g) (g / h ^ k) := by
    rw [hρ, mul_pow, root_pow, ← map_pow, ← map_mul, div_eq_mul_inv, mul_comm, inv_pow]
  have hint : IsIntegral Γ(X, V) (e.symm ρ) := by
    refine ⟨Polynomial.X ^ k - Polynomial.C uV, Polynomial.monic_X_pow_sub_C uV hk, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero, ← map_pow, hρk, ← huV]
    apply e.injective
    rw [e.apply_symm_apply, e.commutes, IsScalarTower.algebraMap_apply Γ(X, V) X.functionField (KA k g)]
    rfl
  refine ⟨((fK k g).normalizationObjIso hV).inv ⟨e.symm ρ, hint⟩, ?_⟩
  rw [yval_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  change e (e.symm ρ) = ρ
  exact e.apply_symm_apply ρ

end Yside

section YGlue

variable (k : ℕ) (g : X.functionField)

theorem map_map {Z : Scheme.{u}} {A B C : Z.Opens} (i : B ⟶ A) (j : C ⟶ B) (l : C ⟶ A) (s : Γ(Z, A)) :
    Z.presheaf.map j.op (Z.presheaf.map i.op s) = Z.presheaf.map l.op s := by
  have hl : j ≫ i = l := Subsingleton.elim _ _
  rw [← hl, op_comp, Functor.map_comp, CommRingCat.comp_apply]

def GoodIdx (W₀ : X.Opens) : Type u := {V : X.Opens // IsAffineOpen V ∧ Nonempty V ∧ V ≤ W₀}

theorem preimage_le_iSup (W₀ : X.Opens) :
    (fK k g).fromNormalization ⁻¹ᵁ W₀ ≤ ⨆ i : GoodIdx W₀, (fK k g).fromNormalization ⁻¹ᵁ i.1 := by
  intro y hy
  have hy' : (fK k g).fromNormalization y ∈ (W₀ : Set X) := hy
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hyV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy' W₀.isOpen
  exact Opens.mem_iSup.mpr ⟨⟨V, hVaff, ⟨⟨_, hyV⟩⟩, hVle⟩, hyV⟩

def HasYVal (W₀ : X.Opens) (s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀)) (t : KA k g) : Prop :=
  ∀ (V : X.Opens) (hV : IsAffineOpen V) (hne : Nonempty V) (hle : V ≤ W₀),
    @yval X _ k g V hne hV (((fK k g).normalization).presheaf.map
      (homOfLE ((fK k g).fromNormalization.preimage_mono hle)).op s) = t

variable {k g}

theorem hasYVal_of_yval_eq {V₀ : X.Opens} [Nonempty V₀] (hV₀ : IsAffineOpen V₀)
    {T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V₀)} {t : KA k g} (hT : yval k g V₀ hV₀ T = t) :
    HasYVal k g V₀ T t := by
  intro V hV hne hle
  rw [yval_res k g hV₀ hV]
  exact hT

theorem HasYVal.res {W₀ W₁ : X.Opens} {s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀)} {t : KA k g}
    (h : HasYVal k g W₀ s t) (hW : W₁ ≤ W₀) :
    HasYVal k g W₁ (((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono hW)).op s) t := by
  intro V hV hne hle
  rw [map_map]
  exact h V hV hne (hle.trans hW)

theorem HasYVal.mul {W₀ : X.Opens} {s s' : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀)} {t t' : KA k g}
    (h : HasYVal k g W₀ s t) (h' : HasYVal k g W₀ s' t') : HasYVal k g W₀ (s * s') (t * t') := by
  intro V hV hne hle
  rw [map_mul, map_mul, h V hV hne hle, h' V hV hne hle]

theorem HasYVal.pow {W₀ : X.Opens} {s : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀)} {t : KA k g}
    (h : HasYVal k g W₀ s t) (n : ℕ) : HasYVal k g W₀ (s ^ n) (t ^ n) := by
  intro V hV hne hle
  rw [map_pow, map_pow, h V hV hne hle]

theorem HasYVal.eq {W₀ : X.Opens} {s s' : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀)} {t : KA k g}
    (h : HasYVal k g W₀ s t) (h' : HasYVal k g W₀ s' t) : s = s' := by
  apply TopCat.Sheaf.eq_of_locally_eq' ((fK k g).normalization).sheaf
    (fun i : GoodIdx W₀ => (fK k g).fromNormalization ⁻¹ᵁ i.1) _
    (fun i => homOfLE ((fK k g).fromNormalization.preimage_mono i.2.2.2)) (preimage_le_iSup k g W₀)
  intro i
  haveI := i.2.2.1
  apply yval_injective k g i.1 i.2.1
  exact (h i.1 i.2.1 i.2.2.1 i.2.2.2).trans (h' i.1 i.2.1 i.2.2.1 i.2.2.2).symm

theorem hasYVal_app {W₀ : X.Opens} {u : Γ(X, W₀)} {t : X.functionField} (hu : HasValue W₀ u t) :
    HasYVal k g W₀ ((fK k g).fromNormalization.app W₀ u) (algebraMap X.functionField (KA k g) t) := by
  intro V hV hne hle
  have hnat : ((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono hle)).op
      ((fK k g).fromNormalization.app W₀ u) = (fK k g).fromNormalization.app V (X.presheaf.map (homOfLE hle).op u) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
    erw [← Scheme.Hom.naturality]
  rw [hnat, yval_app, (hu.res _).germToFunctionField_eq]

theorem exists_hasYVal_root (hk : k ≠ 0) (W₀ : X.Opens) (h : X.functionField) (u : Γ(X, W₀))
    (hu : HasValue W₀ u (g / h ^ k)) :
    ∃ T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀),
      HasYVal k g W₀ T (algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _) := by
  set t : KA k g := algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _ with ht
  have hloc : ∀ i : GoodIdx W₀, ∃ T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ i.1),
      @yval X _ k g i.1 i.2.2.1 i.2.1 T = t := by
    intro i
    haveI := i.2.2.1
    exact exists_yval_eq_root k g hk i.1 i.2.1 h (X.presheaf.map (homOfLE i.2.2.2).op u)
      ((hu.res _).germToFunctionField_eq)
  choose T hT using hloc
  have hTval : ∀ i : GoodIdx W₀, @HasYVal X _ k g i.1 (T i) t := fun i => by
    haveI := i.2.2.1
    exact hasYVal_of_yval_eq i.2.1 (hT i)
  have hcompat : TopCat.Presheaf.IsCompatible ((fK k g).normalization).sheaf.1
      (fun i : GoodIdx W₀ => (fK k g).fromNormalization ⁻¹ᵁ i.1) T := by
    intro i j
    have h1 := (hTval i).res (inf_le_left : i.1 ⊓ j.1 ≤ i.1)
    have h2 := (hTval j).res (inf_le_right : i.1 ⊓ j.1 ≤ j.1)
    exact h1.eq h2
  obtain ⟨T₀, hT₀, -⟩ := TopCat.Sheaf.existsUnique_gluing' ((fK k g).normalization).sheaf
    (fun i : GoodIdx W₀ => (fK k g).fromNormalization ⁻¹ᵁ i.1) ((fK k g).fromNormalization ⁻¹ᵁ W₀)
    (fun i => homOfLE ((fK k g).fromNormalization.preimage_mono i.2.2.2)) (preimage_le_iSup k g W₀) T hcompat
  refine ⟨T₀, fun V hV hne hle => ?_⟩
  have := hT₀ ⟨V, hV, hne, hle⟩
  change ((fK k g).normalization).presheaf.map _ T₀ = _ at this
  rw [this]
  exact hT ⟨V, hV, hne, hle⟩

end YGlue

section Data

variable (k : ℕ) (g : X.functionField)

theorem root_div_pow (h : X.functionField) :
    (algebraMap X.functionField (KA k g) h⁻¹ * AdjoinRoot.root _) ^ k = algebraMap X.functionField (KA k g) (g / h ^ k) := by
  rw [mul_pow, root_pow, ← map_pow, ← map_mul, div_eq_mul_inv, mul_comm, inv_pow]

variable {k g}

theorem mem_range_div (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hk0 : k ≠ 0) (hg : g ≠ 0)
    {ha hb : X.functionField} (x : X)
    (h1 : g / ha ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range)
    (h2 : hb ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    hb / ha ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  haveI := hnorm x
  have hpow : (hb / ha) ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
    have heq : hb ^ k / g * (g / ha ^ k) = (hb / ha) ^ k := by
      rw [div_mul_div_comm, mul_comm (hb ^ k) g, mul_div_mul_left _ _ hg, div_pow]
    rw [← heq]
    exact mul_mem h2 h1
  obtain ⟨y, hy⟩ := hpow
  have hint : IsIntegral (X.presheaf.stalk x) ((hb / ha) ^ k) := hy ▸ isIntegral_algebraMap
  exact IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (Nat.pos_of_ne_zero hk0) hint

theorem exists_data (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hk0 : k ≠ 0) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ (u : ∀ a, Γ(X, U a)) (T : ∀ a, Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ (U a))),
      (∀ a, HasValue (U a) (u a) (g / h a ^ k)) ∧
      (∀ a, IsUnit (u a)) ∧
      (∀ a, HasYVal k g (U a) (T a) (algebraMap X.functionField (KA k g) (h a)⁻¹ * AdjoinRoot.root _)) ∧
      (∀ a, T a ^ k = (fK k g).fromNormalization.app (U a) (u a)) ∧
      (∀ a b, ∃ w : Γ(X, U a ⊓ U b), HasValue (U a ⊓ U b) w (h b / h a) ∧
        X.presheaf.map (homOfLE inf_le_left).op (u a) = w ^ k * X.presheaf.map (homOfLE inf_le_right).op (u b) ∧
        ((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono inf_le_left)).op (T a) =
          (fK k g).fromNormalization.app (U a ⊓ U b) w *
          ((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono inf_le_right)).op (T b)) := by

  have hu : ∀ a, ∃ ua : Γ(X, U a), HasValue (U a) ua (g / h a ^ k) := fun a =>
    exists_hasValue (U a) _ (fun x hx => (hdiv a x hx).1)
  choose u hu using hu
  have huunit : ∀ a, IsUnit (u a) := fun a =>
    (hu a).isUnit (div_ne_zero hg (pow_ne_zero _ (hh a))) (fun x hx => by rw [inv_div]; exact (hdiv a x hx).2)

  have hT : ∀ a, ∃ Ta : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ (U a)),
      HasYVal k g (U a) Ta (algebraMap X.functionField (KA k g) (h a)⁻¹ * AdjoinRoot.root _) := fun a =>
    exists_hasYVal_root hk0 (U a) (h a) (u a) (hu a)
  choose T hT using hT
  refine ⟨u, T, hu, huunit, hT, fun a => ?_, fun a b => ?_⟩
  ·
    apply ((hT a).pow k).eq
    rw [root_div_pow]
    exact hasYVal_app (hu a)
  ·
    have hw : ∃ w : Γ(X, U a ⊓ U b), HasValue (U a ⊓ U b) w (h b / h a) :=
      exists_hasValue _ _ (fun x hx => mem_range_div hnorm hk0 hg x (hdiv a x hx.1).1 (hdiv b x hx.2).2)
    obtain ⟨w, hw⟩ := hw
    refine ⟨w, hw, ?_, ?_⟩
    · apply ((hu a).res _).eq
      have hval : (h b / h a) ^ k * (g / h b ^ k) = g / h a ^ k := by
        rw [div_pow, div_mul_div_comm, mul_comm (h b ^ k) g, mul_div_mul_right _ _ (pow_ne_zero _ (hh b))]
      rw [← hval]
      exact (hw.pow k).mul ((hu b).res _)
    · apply ((hT a).res inf_le_left).eq
      have hval : algebraMap X.functionField (KA k g) (h b / h a) *
          (algebraMap X.functionField (KA k g) (h b)⁻¹ * AdjoinRoot.root _) =
          algebraMap X.functionField (KA k g) (h a)⁻¹ * AdjoinRoot.root _ := by
        rw [← mul_assoc, ← map_mul, div_mul_eq_mul_div, mul_inv_cancel₀ (hh b), one_div]
      rw [← hval]
      exact (hasYVal_app hw).mul ((hT b).res inf_le_right)

end Data

section Lift

variable (k : ℕ) (g : X.functionField)

omit [IsIntegral X] in

theorem map_injective_of_eq {Z : Scheme.{u}} {A B : Z.Opens} (e : A = B) (i : A ⟶ B) :
    Function.Injective (Z.presheaf.map i.op) := by
  subst e
  rw [Subsingleton.elim i (𝟙 _), op_id, Z.presheaf.map_id]
  exact fun _ _ h => h

omit [IsIntegral X] in

theorem app_map {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) {A B : Z.Opens} (i : B ⟶ A) (j : q ⁻¹ᵁ B ⟶ q ⁻¹ᵁ A)
    (x : Γ(Z, A)) : q.app B (Z.presheaf.map i.op x) = Z'.presheaf.map j.op (q.app A x) := by
  have hn := q.naturality i.op
  have hj : (Opens.map q.base).map i.op.unop = j := Subsingleton.elim _ _
  rw [hj] at hn
  have h2 := ConcreteCategory.congr_hom hn x
  exact h2

def RootHyp (W : X.Opens) (uW : Γ(X, W)) (Z : Scheme.{u}) (z : Z ⟶ X) (τ : Γ(Z, ⊤)) : Prop :=
  Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app W uW

def LiftProp (W : X.Opens) (TW : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W))
    (Z : Scheme.{u}) (z : Z ⟶ X) (τ : Γ(Z, ⊤)) (s : Z ⟶ (fK k g).normalization) : Prop :=
  s ≫ (fK k g).fromNormalization = z ∧
    s.app ((fK k g).fromNormalization ⁻¹ᵁ W) TW = Z.presheaf.map (homOfLE le_top).op τ

def HasLift (W : X.Opens) (uW : Γ(X, W)) (TW : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W)) : Prop :=
  ∀ (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ W = ⊤ → ∀ τ : Γ(Z, ⊤), RootHyp k W uW Z z τ →
    ∃! s : Z ⟶ (fK k g).normalization, LiftProp k g W TW Z z τ s

variable {k g}

omit [IsIntegral X] in
theorem rootHyp_comp {W : X.Opens} {uW : Γ(X, W)} {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) {z : Z ⟶ X} {τ : Γ(Z, ⊤)}
    (h : RootHyp k W uW Z z τ) : RootHyp k W uW Z' (q ≫ z) (q.appTop τ) := by
  unfold RootHyp at h ⊢
  have e1 : (q ≫ z).app W uW = q.app (z ⁻¹ᵁ W) (z.app W uW) := rfl
  rw [e1, ← h, map_pow]
  congr 1
  show Z'.presheaf.map (homOfLE (le_top : q ⁻¹ᵁ (z ⁻¹ᵁ W) ≤ ⊤)).op (q.app ⊤ τ) =
    q.app (z ⁻¹ᵁ W) (Z.presheaf.map (homOfLE le_top).op τ)
  exact (app_map q (B := z ⁻¹ᵁ W) (homOfLE le_top) (homOfLE le_top) τ).symm

theorem liftProp_comp {W : X.Opens} {TW : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W)}
    {Z Z' : Scheme.{u}} (q : Z' ⟶ Z) {z : Z ⟶ X} {τ : Γ(Z, ⊤)} {s : Z ⟶ (fK k g).normalization}
    (h : LiftProp k g W TW Z z τ s) : LiftProp k g W TW Z' (q ≫ z) (q.appTop τ) (q ≫ s) := by
  refine ⟨by rw [Category.assoc, h.1], ?_⟩
  have e1 : (q ≫ s).app ((fK k g).fromNormalization ⁻¹ᵁ W) TW =
      q.app _ (s.app ((fK k g).fromNormalization ⁻¹ᵁ W) TW) := rfl
  rw [e1, h.2]
  exact app_map q (homOfLE le_top) (homOfLE le_top) τ

omit [IsIntegral X] in
theorem rootHyp_res {W W' : X.Opens} (hle : W' ≤ W) {uW : Γ(X, W)} {Z : Scheme.{u}} {z : Z ⟶ X} {τ : Γ(Z, ⊤)}
    (h : RootHyp k W uW Z z τ) : RootHyp k W' (X.presheaf.map (homOfLE hle).op uW) Z z τ := by
  unfold RootHyp at h ⊢
  rw [app_map z (homOfLE hle) (homOfLE (z.preimage_mono hle)) uW, ← h, map_pow,
    map_map _ _ (homOfLE le_top)]

theorem app_res_iff {W W' : X.Opens} (hle : W' ≤ W) {TW : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W)}
    {Z : Scheme.{u}} {z : Z ⟶ X} (hz : z ⁻¹ᵁ W' = ⊤) {τ : Γ(Z, ⊤)} {s : Z ⟶ (fK k g).normalization}
    (hs : s ≫ (fK k g).fromNormalization = z) :
    s.app ((fK k g).fromNormalization ⁻¹ᵁ W) TW = Z.presheaf.map (homOfLE le_top).op τ ↔
      s.app ((fK k g).fromNormalization ⁻¹ᵁ W')
        (((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono hle)).op TW) =
        Z.presheaf.map (homOfLE le_top).op τ := by
  have htop' : s ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ W') = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hs, hz]
  have htop : s ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ W) = ⊤ :=
    top_le_iff.mp (htop'.ge.trans (s.preimage_mono ((fK k g).fromNormalization.preimage_mono hle)))
  set j : s ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ W') ⟶ s ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ W) :=
    homOfLE (s.preimage_mono ((fK k g).fromNormalization.preimage_mono hle)) with hj
  rw [app_map s (homOfLE ((fK k g).fromNormalization.preimage_mono hle)) j TW]
  constructor
  · intro h
    rw [h, map_map _ _ (homOfLE le_top)]
  · intro h
    refine map_injective_of_eq (htop'.trans htop.symm) j ?_
    exact h.trans (map_map (homOfLE le_top) j (homOfLE le_top) τ).symm

omit [IsIntegral X] in

theorem isOpenCover_preimage (W₀ : X.Opens) {Z : Scheme.{u}} (z : Z ⟶ X) (hz : z ⁻¹ᵁ W₀ = ⊤) :
    IsOpenCover (fun i : GoodIdx W₀ => z ⁻¹ᵁ i.1) := by
  apply IsOpenCover.mk
  apply top_le_iff.mp
  rw [← hz]
  intro y hy
  have hy' : z y ∈ (W₀ : Set X) := hy
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hyV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy' W₀.isOpen
  exact Opens.mem_iSup.mpr ⟨⟨V, hVaff, ⟨⟨_, hyV⟩⟩, hVle⟩, hyV⟩

theorem lift_unique {W₀ : X.Opens} {u₀ : Γ(X, W₀)}
    {T₀ : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀)}
    (hloc : ∀ i : GoodIdx W₀, HasLift k g i.1 (X.presheaf.map (homOfLE i.2.2.2).op u₀)
      (((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono i.2.2.2)).op T₀))
    {Z : Scheme.{u}} {z : Z ⟶ X} (hz : z ⁻¹ᵁ W₀ = ⊤) {τ : Γ(Z, ⊤)} (hτ : RootHyp k W₀ u₀ Z z τ)
    {s₁ s₂ : Z ⟶ (fK k g).normalization} (h₁ : LiftProp k g W₀ T₀ Z z τ s₁) (h₂ : LiftProp k g W₀ T₀ Z z τ s₂) :
    s₁ = s₂ := by
  apply Scheme.Cover.hom_ext (Z.openCoverOfIsOpenCover _ (isOpenCover_preimage W₀ z hz))
  intro i
  change (z ⁻¹ᵁ i.1).ι ≫ s₁ = (z ⁻¹ᵁ i.1).ι ≫ s₂
  have hz' : ((z ⁻¹ᵁ i.1).ι ≫ z) ⁻¹ᵁ i.1 = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
  have hτ' : RootHyp k i.1 (X.presheaf.map (homOfLE i.2.2.2).op u₀) _ ((z ⁻¹ᵁ i.1).ι ≫ z) ((z ⁻¹ᵁ i.1).ι.appTop τ) :=
    rootHyp_res i.2.2.2 (rootHyp_comp _ hτ)
  obtain ⟨s, -, hsuniq⟩ := hloc i _ ((z ⁻¹ᵁ i.1).ι ≫ z) hz' ((z ⁻¹ᵁ i.1).ι.appTop τ) hτ'
  have h₁' := liftProp_comp (z ⁻¹ᵁ i.1).ι h₁
  have h₂' := liftProp_comp (z ⁻¹ᵁ i.1).ι h₂
  have e₁ := hsuniq ((z ⁻¹ᵁ i.1).ι ≫ s₁) ⟨h₁'.1, (app_res_iff i.2.2.2 hz' h₁'.1).mp h₁'.2⟩
  have e₂ := hsuniq ((z ⁻¹ᵁ i.1).ι ≫ s₂) ⟨h₂'.1, (app_res_iff i.2.2.2 hz' h₂'.1).mp h₂'.2⟩
  rw [e₁, e₂]

theorem hasLift_of_forall {W₀ : X.Opens} {u₀ : Γ(X, W₀)}
    {T₀ : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ W₀)}
    (hloc : ∀ i : GoodIdx W₀, HasLift k g i.1 (X.presheaf.map (homOfLE i.2.2.2).op u₀)
      (((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono i.2.2.2)).op T₀)) :
    HasLift k g W₀ u₀ T₀ := by
  intro Z z hz τ hτ
  refine existsUnique_of_exists_of_unique ?_ (fun s₁ s₂ h₁ h₂ => lift_unique hloc hz hτ h₁ h₂)
  let 𝒰 := Z.openCoverOfIsOpenCover _ (isOpenCover_preimage W₀ z hz)

  have hloc' : ∀ i : GoodIdx W₀, ∃ s : (𝒰.X i) ⟶ (fK k g).normalization,
      LiftProp k g W₀ T₀ _ (𝒰.f i ≫ z) ((𝒰.f i).appTop τ) s := by
    intro i
    change ∃ s : ↑(z ⁻¹ᵁ i.1) ⟶ (fK k g).normalization,
      LiftProp k g W₀ T₀ _ ((z ⁻¹ᵁ i.1).ι ≫ z) (((z ⁻¹ᵁ i.1).ι).appTop τ) s
    have hz' : ((z ⁻¹ᵁ i.1).ι ≫ z) ⁻¹ᵁ i.1 = ⊤ := by
      rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
    have hτ' : RootHyp k i.1 (X.presheaf.map (homOfLE i.2.2.2).op u₀) _ ((z ⁻¹ᵁ i.1).ι ≫ z)
        ((z ⁻¹ᵁ i.1).ι.appTop τ) :=
      rootHyp_res i.2.2.2 (rootHyp_comp _ hτ)
    obtain ⟨s, hs, -⟩ := hloc i _ ((z ⁻¹ᵁ i.1).ι ≫ z) hz' ((z ⁻¹ᵁ i.1).ι.appTop τ) hτ'
    exact ⟨s, hs.1, (app_res_iff i.2.2.2 hz' hs.1).mpr hs.2⟩
  choose sf hsf using hloc'

  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ sf i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ sf j := by
    intro i j
    have hzz : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (𝒰.f i ≫ z) = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (𝒰.f j ≫ z) := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    have hττ : (pullback.fst (𝒰.f i) (𝒰.f j)).appTop ((𝒰.f i).appTop τ) =
        (pullback.snd (𝒰.f i) (𝒰.f j)).appTop ((𝒰.f j).appTop τ) := by
      have e1 : (pullback.fst (𝒰.f i) (𝒰.f j)).appTop ((𝒰.f i).appTop τ) =
          (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).appTop τ := rfl
      have e2 : (pullback.snd (𝒰.f i) (𝒰.f j)).appTop ((𝒰.f j).appTop τ) =
          (pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j).appTop τ := rfl
      rw [e1, e2, pullback.condition]
    have hz'' : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ (𝒰.f i ≫ z)) ⁻¹ᵁ W₀ = ⊤ := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hz]
      rfl
    have h₁ := liftProp_comp (pullback.fst (𝒰.f i) (𝒰.f j)) (hsf i)
    have h₂ := liftProp_comp (pullback.snd (𝒰.f i) (𝒰.f j)) (hsf j)
    rw [← hzz, ← hττ] at h₂
    exact lift_unique hloc hz'' (rootHyp_comp _ (rootHyp_comp _ hτ)) h₁ h₂
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 sf hcompat, ?_, ?_⟩
  · apply Scheme.Cover.hom_ext 𝒰
    intro i
    rw [Scheme.Cover.ι_glueMorphisms_assoc, (hsf i).1]
  · apply Scheme.OpenCover.ext_elem _ _ 𝒰
    intro i
    have hgl := Scheme.Cover.ι_glueMorphisms 𝒰 sf hcompat i
    have e1 : (𝒰.f i).app _ ((Scheme.Cover.glueMorphisms 𝒰 sf hcompat).app ((fK k g).fromNormalization ⁻¹ᵁ W₀) T₀) =
        (𝒰.f i ≫ Scheme.Cover.glueMorphisms 𝒰 sf hcompat).app ((fK k g).fromNormalization ⁻¹ᵁ W₀) T₀ := rfl
    rw [e1, Scheme.Hom.congr_app hgl]
    erw [CommRingCat.comp_apply]
    rw [(hsf i).2, map_map _ _ (homOfLE le_top), app_map (𝒰.f i) (homOfLE le_top) (homOfLE le_top) τ]
    rfl

end Lift

section Bridge

variable (k : ℕ) (g : X.functionField)

theorem toNormalization_app_eq (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (T : Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ V)) (ρ : KA k g) (hT : yval k g V hV T = ρ) :
    (fK k g).toNormalization.app ((fK k g).fromNormalization ⁻¹ᵁ V) T =
      (Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv ρ) := by
  set W := (fK k g).toNormalization ⁻¹ᵁ ((fK k g).fromNormalization ⁻¹ᵁ V) with hWdef
  set x := (fK k g).toNormalization.app ((fK k g).fromNormalization ⁻¹ᵁ V) T with hx
  have hW : W = ⊤ := by rw [hWdef, preimage_toNormalization, preimage_eq_top]
  have h1 : yval k g V hV T = (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).hom
      ((Spec (CommRingCat.of (KA k g))).presheaf.map (homOfLE hW.ge).op x) := by
    rw [yval_eq_appLE, secIso_hom, Scheme.Hom.appLE]
    change (Scheme.ΓSpecIso _).hom ((Spec _).presheaf.map _ ((Spec _).presheaf.map _ x)) = _
    rw [map_map _ _ (homOfLE hW.ge)]
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (KA k g))).inv (h1.symm.trans hT)
  rw [Iso.hom_inv_id_apply] at h2
  rw [← h2, map_map _ _ (𝟙 W), op_id, CategoryTheory.Functor.map_id]
  rfl

end Bridge

end KummerLift

open KummerLift in
theorem solution
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of R))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (k : ℕ) (hk : IsUnit ((k : ℕ) : R))
    (g : X.functionField) (hg : g ≠ 0)
    (r : ℕ) (U : Fin r → X.Opens) (hU : (⨆ a, U a) = ⊤) (h : Fin r → X.functionField) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (x : X), x ∈ U a →
      g / h a ^ k ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range ∧
      h a ^ k / g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    let π := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).fromNormalization
    let Y := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g : Polynomial X.functionField)))) ≫
      X.fromSpecStalk (genericPoint X)).normalization
    ∃ (u : ∀ a, Γ(X, U a)) (T : ∀ a, Γ(Y, π ⁻¹ᵁ (U a))),

      (∀ a (x : X) (hx : x ∈ U a),
        algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a) x hx (u a)) = g / h a ^ k) ∧
      (∀ a, IsUnit (u a)) ∧

      (∀ a, T a ^ k = π.app (U a) (u a)) ∧

      (∀ a b, ∃ w : Γ(X, U a ⊓ U b),
        (∀ (x : X) (hx : x ∈ U a ⊓ U b),
          algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a ⊓ U b) x hx w) = h b / h a) ∧
        X.presheaf.map (homOfLE inf_le_left).op (u a) = w ^ k * X.presheaf.map (homOfLE inf_le_right).op (u b) ∧
        Y.presheaf.map (homOfLE (π.preimage_mono inf_le_left)).op (T a) =
          π.app (U a ⊓ U b) w * Y.presheaf.map (homOfLE (π.preimage_mono inf_le_right)).op (T b)) ∧

      (∀ a (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ (U a) = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app (U a) (u a) →
          ∃! s : Z ⟶ Y, s ≫ π = z ∧ s.app (π ⁻¹ᵁ (U a)) (T a) = Z.presheaf.map (homOfLE le_top).op τ) := by
  intro π Y
  change ∃ (u : ∀ a, Γ(X, U a)) (T : ∀ a, Γ((fK k g).normalization, (fK k g).fromNormalization ⁻¹ᵁ (U a))),
      (∀ a (x : X) (hx : x ∈ U a),
        algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a) x hx (u a)) = g / h a ^ k) ∧
      (∀ a, IsUnit (u a)) ∧
      (∀ a, T a ^ k = (fK k g).fromNormalization.app (U a) (u a)) ∧
      (∀ a b, ∃ w : Γ(X, U a ⊓ U b),
        (∀ (x : X) (hx : x ∈ U a ⊓ U b),
          algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ (U a ⊓ U b) x hx w) = h b / h a) ∧
        X.presheaf.map (homOfLE inf_le_left).op (u a) = w ^ k * X.presheaf.map (homOfLE inf_le_right).op (u b) ∧
        ((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono inf_le_left)).op (T a) =
          (fK k g).fromNormalization.app (U a ⊓ U b) w *
          ((fK k g).normalization).presheaf.map (homOfLE ((fK k g).fromNormalization.preimage_mono inf_le_right)).op (T b)) ∧
      (∀ a (Z : Scheme.{u}) (z : Z ⟶ X), z ⁻¹ᵁ (U a) = ⊤ →
        ∀ τ : Γ(Z, ⊤), Z.presheaf.map (homOfLE le_top).op τ ^ k = z.app (U a) (u a) →
          ∃! s : Z ⟶ (fK k g).normalization, s ≫ (fK k g).fromNormalization = z ∧
            s.app ((fK k g).fromNormalization ⁻¹ᵁ (U a)) (T a) = Z.presheaf.map (homOfLE le_top).op τ)
  have hkX : ∀ V : X.Opens, IsUnit ((k : ℕ) : Γ(X, V)) := fun V => by
    have := hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V le_top).hom
    rwa [map_natCast] at this
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 := hkX ⊤
    rw [Nat.cast_zero, isUnit_zero_iff] at h1
    exact zero_ne_one h1
  obtain ⟨u, T, hrest⟩ := exists_data (k := k) (g := g) hnorm hk0 hg r U h hh hdiv
  refine ⟨u, T, fun a x hx => hrest.1 a x hx, hrest.2.1, hrest.2.2.2.1, fun a b => ?_, fun a => ?_⟩
  · exact (hrest.2.2.2.2 a b).elim fun w hw => ⟨w, hw.1, hw.2.1, hw.2.2⟩
  ·
    have hu : HasValue (U a) (u a) (g / h a ^ k) := hrest.1 a
    have huunit : IsUnit (u a) := hrest.2.1 a
    have hT : HasYVal k g (U a) (T a) (algebraMap X.functionField (KA k g) (h a)⁻¹ * AdjoinRoot.root _) :=
      hrest.2.2.1 a
    have hL : HasLift k g (U a) (u a) (T a) := by
      apply hasLift_of_forall
      intro i
      haveI := i.2.2.1
      have hchar := toNormalization_app_eq k g i.1 i.2.1 _ _ (hT i.1 i.2.1 i.2.2.1 i.2.2.2)
      have hmain := AlgebraicGeometry.existsUnique_lift_fromNormalization_kummer_of_isAffineOpen hnorm k g i.1 i.2.1
        i.2.2.1 (hkX i.1) (X.presheaf.map (homOfLE i.2.2.2).op (u a)) (huunit.map _) (h a) (hh a)
        (hu.res (homOfLE i.2.2.2)) _ hchar
      intro Z z hz τ hτ
      exact hmain Z z hz τ hτ
    intro Z z hz τ hτ
    exact hL Z z hz τ hτ

end S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift
end P2MW
export P2MW.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift (solution)
