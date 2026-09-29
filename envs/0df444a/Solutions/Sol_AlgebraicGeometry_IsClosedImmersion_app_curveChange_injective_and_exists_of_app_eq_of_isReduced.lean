-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.app_curveChange_injective_and_exists_of_app_eq_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6992bc4d-71a6-5761-b070-5fb283dc8714

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard TopologicalSpace Opposite

namespace MilnorBC

section Generic

variable {X Y₁ Y₂ Z : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) (j₁ : Z ⟶ Y₁) (j₂ : Z ⟶ Y₂) (hsq : j₁ ≫ i₁ = j₂ ≫ i₂)

def ExistsClause (U : X.Opens) : Prop :=
  ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
    Z.presheaf.map
        (eqToHom (show j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq])).op
      ((j₁.app (i₁ ⁻¹ᵁ U)) g₁) = (j₂.app (i₂ ⁻¹ᵁ U)) g₂ →
    ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂

theorem iSup_affineOpens_le (U : X.Opens) :
    ⨆ (V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U}), (V : X.Opens) = U := by
  apply le_antisymm
  · exact iSup_le fun V => V.2.2
  · intro p hp
    obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p) (U := U) hp
    exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWU⟩, hpW⟩

theorem app_apply_map_op {X' Y' : Scheme.{u}} (f : Y' ⟶ X') {U V : X'.Opens} (ι : V ⟶ U) (s : Γ(X', U)) :
    f.app V (X'.presheaf.map ι.op s) = Y'.presheaf.map ((Opens.map f.base).map ι).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality ι.op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  exact h

theorem exists_of_forall_isAffineOpen (U : X.Opens)
    (hinj : ∀ V : X.Opens, V ≤ U → Function.Injective (fun f : Γ(X, V) => ((i₁.app V) f, (i₂.app V) f)))
    (hex : ∀ V : X.Opens, IsAffineOpen V → V ≤ U → ExistsClause i₁ i₂ j₁ j₂ hsq V) :
    ExistsClause i₁ i₂ j₁ j₂ hsq U := by
  classical
  intro g₁ g₂ hagree

  let ι : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ U}
  let V : ι → X.Opens := fun j => j.1

  let r₁ : ∀ j : ι, Γ(Y₁, i₁ ⁻¹ᵁ V j) := fun j => Y₁.presheaf.map (homOfLE (i₁.preimage_mono j.2.2)).op g₁
  let r₂ : ∀ j : ι, Γ(Y₂, i₂ ⁻¹ᵁ V j) := fun j => Y₂.presheaf.map (homOfLE (i₂.preimage_mono j.2.2)).op g₂

  have hagreeV : ∀ j : ι,
      Z.presheaf.map
          (eqToHom (show j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ V j) = j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ V j) by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq])).op
        (j₁.app (i₁ ⁻¹ᵁ V j) (r₁ j)) = j₂.app (i₂ ⁻¹ᵁ V j) (r₂ j) := by
    intro j
    simp only [r₁, r₂]
    rw [app_apply_map_op, app_apply_map_op, ← hagree]
    generalize j₁.app (i₁ ⁻¹ᵁ U) g₁ = t
    simp only [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

  choose fV hfV₁ hfV₂ using fun j : ι => hex (V j) j.2.1 j.2.2 (r₁ j) (r₂ j) (hagreeV j)

  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V fV := by
    intro j j'
    apply hinj (V j ⊓ V j') (inf_le_left.trans j.2.2)
    change ((i₁.app _) (X.presheaf.map _ (fV j)), (i₂.app _) (X.presheaf.map _ (fV j))) =
      ((i₁.app _) (X.presheaf.map _ (fV j')), (i₂.app _) (X.presheaf.map _ (fV j')))
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [app_apply_map_op, app_apply_map_op, hfV₁, hfV₁]
      simp only [r₁, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    · rw [app_apply_map_op, app_apply_map_op, hfV₂, hfV₂]
      simp only [r₂, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl

  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' V U (fun j => homOfLE j.2.2)
    (le_of_eq (iSup_affineOpens_le U).symm) fV hcompat
  refine ⟨f, ?_, ?_⟩
  ·
    fapply Y₁.sheaf.eq_of_locally_eq' (fun j : ι => i₁ ⁻¹ᵁ V j) (i₁ ⁻¹ᵁ U)
      (fun j => homOfLE (i₁.preimage_mono j.2.2))
    · rw [← Scheme.Hom.preimage_iSup]
      exact i₁.preimage_mono (le_of_eq (iSup_affineOpens_le U).symm)
    · intro j
      have e1 : (i₁.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₁ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₁]
      rw [app_apply_map_op] at e1
      exact e1
  · fapply Y₂.sheaf.eq_of_locally_eq' (fun j : ι => i₂ ⁻¹ᵁ V j) (i₂ ⁻¹ᵁ U)
      (fun j => homOfLE (i₂.preimage_mono j.2.2))
    · rw [← Scheme.Hom.preimage_iSup]
      exact i₂.preimage_mono (le_of_eq (iSup_affineOpens_le U).symm)
    · intro j
      have e2 : (i₂.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₂ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₂]
      rw [app_apply_map_op] at e2
      exact e2

theorem ker_pullback_fst_comp [IsClosedImmersion i₁] [IsClosedImmersion i₂] :
    (pullback.fst i₁ i₂ ≫ i₁).ker = i₁.ker ⊔ i₂.ker := by
  apply le_antisymm
  · set J : X.IdealSheafData := i₁.ker ⊔ i₂.ker
    have h₁ : i₁.ker ≤ J.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have h₂ : i₂.ker ≤ J.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let w : J.subscheme ⟶ pullback i₁ i₂ :=
      pullback.lift (IsClosedImmersion.lift i₁ J.subschemeι h₁) (IsClosedImmersion.lift i₂ J.subschemeι h₂)
        (by rw [IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac])
    have hw : w ≫ (pullback.fst i₁ i₂ ≫ i₁) = J.subschemeι := by
      rw [← Category.assoc, pullback.lift_fst, IsClosedImmersion.lift_fac]
    calc (pullback.fst i₁ i₂ ≫ i₁).ker ≤ (w ≫ (pullback.fst i₁ i₂ ≫ i₁)).ker := Scheme.Hom.le_ker_comp _ _
      _ = J := by rw [hw, Scheme.IdealSheafData.ker_subschemeι]
  · refine sup_le (Scheme.Hom.le_ker_comp _ _) ?_
    rw [pullback.condition]
    exact Scheme.Hom.le_ker_comp _ _

theorem exists_of_isAffineOpen [IsClosedImmersion i₁] [IsClosedImmersion i₂] (hZ : IsPullback j₁ j₂ i₁ i₂)
    (U : X.Opens) (hU : IsAffineOpen U) : ExistsClause i₁ i₂ j₁ j₂ hZ.w U := by
  haveI : IsClosedImmersion j₁ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hZ.flip inferInstance

  have hk₁ : RingHom.ker (i₁.app U).hom = i₁.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₁ ⟨U, hU⟩).symm
  have hk₂ : RingHom.ker (i₂.app U).hom = i₂.ker.ideal ⟨U, hU⟩ := (Scheme.Hom.ker_apply i₂ ⟨U, hU⟩).symm
  have hkerZ : (j₁ ≫ i₁).ker = i₁.ker ⊔ i₂.ker := by
    rw [← hZ.isoPullback_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso, ker_pullback_fst_comp]
  have hkπ : RingHom.ker ((j₁ ≫ i₁).app U).hom = i₁.ker.ideal ⟨U, hU⟩ ⊔ i₂.ker.ideal ⟨U, hU⟩ := by
    rw [← Scheme.Hom.ker_apply _ ⟨U, hU⟩, hkerZ, Scheme.IdealSheafData.ideal_sup]
    rfl
  intro g₁ g₂ h
  obtain ⟨a₁, rfl⟩ := i₁.app_surjective U hU g₁
  obtain ⟨a₂, rfl⟩ := i₂.app_surjective U hU g₂

  have key : ∀ a : Γ(X, U), Z.presheaf.map
      (eqToHom (show j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hZ.w])).op
      (j₁.app (i₁ ⁻¹ᵁ U) ((i₁.app U) a)) = j₂.app (i₂ ⁻¹ᵁ U) ((i₂.app U) a) := by
    intro a
    change ((i₁.app U ≫ j₁.app (i₁ ⁻¹ᵁ U)) ≫ Z.presheaf.map (eqToHom _).op) a = (i₂.app U ≫ j₂.app (i₂ ⁻¹ᵁ U)) a
    rw [← Scheme.Hom.comp_app, ← Scheme.Hom.comp_app, Scheme.Hom.congr_app hZ.w.symm U]
    rfl
  have hF : j₁.app (i₁ ⁻¹ᵁ U) ((i₁.app U) a₁) = j₁.app (i₁ ⁻¹ᵁ U) ((i₁.app U) a₂) := by
    rw [← key a₂] at h
    haveI : IsIso (Z.presheaf.map (eqToHom (show j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hZ.w])).op) := by
      rw [eqToHom_op, eqToHom_map]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).1 h
  have hπ : ((j₁ ≫ i₁).app U) a₁ = ((j₁ ≫ i₁).app U) a₂ := by
    rw [Scheme.Hom.comp_app]
    exact hF
  have hdiff : a₁ - a₂ ∈ i₁.ker.ideal ⟨U, hU⟩ ⊔ i₂.ker.ideal ⟨U, hU⟩ := by
    rw [← hkπ, RingHom.mem_ker, map_sub, sub_eq_zero]; exact hπ
  obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := Submodule.mem_sup.mp hdiff
  refine ⟨a₁ - u₁, ?_, ?_⟩
  · rw [map_sub, sub_eq_self]
    exact (RingHom.mem_ker.mp (hk₁ ▸ hu₁ : u₁ ∈ RingHom.ker (i₁.app U).hom))
  · have : a₁ - u₁ = a₂ + u₂ := by linear_combination -hu
    rw [this, map_add, add_eq_left]
    exact (RingHom.mem_ker.mp (hk₂ ▸ hu₂ : u₂ ∈ RingHom.ker (i₂.app U).hom))

end Generic

section BaseChange

variable {k : Type u} [Field k] {X Y₁ Y₂ Z T : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
  (y₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (y₂ : Y₂ ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ Spec (CommRingCat.of k))
  (i₁ : SchemeHomOver y₁ x) (i₂ : SchemeHomOver y₂ x) (j₁ : SchemeHomOver z y₁) (j₂ : SchemeHomOver z y₂)
  (t : T ⟶ Spec (CommRingCat.of k))

theorem isPullback_curveChange_fst {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c = c')
    (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (curveChange f hf t) (pullback.fst c' t) (pullback.fst c t) f := by
  have big : IsPullback (curveChange f hf t ≫ pullback.snd c t) (pullback.fst c' t) t (f ≫ c) := by
    rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c' t).flip
  have hcomm : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
    simp only [curveChange, pullback.lift_fst]
  exact IsPullback.of_right big hcomm (IsPullback.of_hasPullback c t).flip

scoped instance isClosedImmersion_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c = c')
    (t : T ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion f] : IsClosedImmersion (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_curveChange_fst f hf t).flip inferInstance

theorem isPullback_curveChange (hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1) :
    IsPullback (curveChange j₁.1 j₁.2 t) (curveChange j₂.1 j₂.2 t) (curveChange i₁.1 i₁.2 t)
      (curveChange i₂.1 i₂.2 t) := by

  have a := isPullback_curveChange_fst (c := y₂) j₂.1 j₂.2 t
  have outer : IsPullback (pullback.fst z t ≫ j₁.1) (curveChange j₂.1 j₂.2 t) i₁.1 (pullback.fst y₂ t ≫ i₂.1) :=
    a.flip.paste_horiz hZ

  have e1 : pullback.fst z t ≫ j₁.1 = curveChange j₁.1 j₁.2 t ≫ pullback.fst y₁ t := by
    simp only [curveChange, pullback.lift_fst]
  have e2 : pullback.fst y₂ t ≫ i₂.1 = curveChange i₂.1 i₂.2 t ≫ pullback.fst x t := by
    simp only [curveChange, pullback.lift_fst]
  rw [e1, e2] at outer
  have hj : j₁.1 ≫ i₁.1 = j₂.1 ≫ i₂.1 := hZ.w
  have hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t =
      curveChange j₂.1 j₂.2 t ≫ curveChange i₂.1 i₂.2 t := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hj]
    · simp only [curveChange, Category.assoc, pullback.lift_snd, Category.comp_id]
  exact IsPullback.of_right outer hsq (isPullback_curveChange_fst i₁.1 i₁.2 t).flip

lemma map_eq_zero_of_app_eq_zero {P W : Scheme.{u}} (l : W ⟶ P) [IsOpenImmersion l] {V : P.Opens} (s : Γ(P, V))
    (hs : l.app V s = 0) :
    P.presheaf.map (homOfLE (show l ''ᵁ l ⁻¹ᵁ V ≤ V by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right)).op s = 0 := by
  have h := Scheme.Hom.appLE_appIso_inv l (U := V) (V := l ⁻¹ᵁ V) le_rfl
  have h' := congrArg (fun φ => (ConcreteCategory.hom φ) s) h
  simp only [CategoryTheory.comp_apply] at h'
  rw [← Scheme.Hom.app_eq_appLE] at h'
  rw [hs, map_zero] at h'
  rw [← h']

theorem app_curveChange_injective [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1] (hXred : IsReduced X)
    (hjs : ∀ p : X, p ∈ Set.range i₁.1.base ∨ p ∈ Set.range i₂.1.base) (U : (Limits.pullback x t).Opens) :
    Function.Injective (fun f : Γ(Limits.pullback x t, U) =>
      ((curveChange i₁.1 i₁.2 t).app U f, (curveChange i₂.1 i₂.2 t).app U f)) := by
  classical
  haveI : IsReduced X := hXred

  set f : Y₁ ⨿ Y₂ ⟶ X := coprod.desc i₁.1 i₂.1 with hf
  haveI : Surjective f := ⟨fun p => by
    rcases hjs p with ⟨y, hy⟩ | ⟨y, hy⟩
    · refine ⟨(coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂).base y, ?_⟩
      change (coprod.inl ≫ f).base y = p
      rw [hf, coprod.inl_desc]; exact hy
    · refine ⟨(coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂).base y, ?_⟩
      change (coprod.inr ≫ f).base y = p
      rw [hf, coprod.inr_desc]; exact hy⟩
  haveI : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  haveI : QuasiCompact f := by rw [hf]; infer_instance

  set p : Limits.pullback x t ⟶ X := pullback.fst x t with hp
  haveI : IsSchemeTheoreticallyDominant (pullback.snd f p) := IsSchemeTheoreticallyDominant.pullbackSnd f p
  have hinjP : ∀ V, Function.Injective ((pullback.snd f p).app V) := fun V => (pullback.snd f p).app_injective V

  set l₁ : Limits.pullback y₁ t ⟶ Limits.pullback f p :=
    pullback.lift (pullback.fst y₁ t ≫ coprod.inl) (curveChange i₁.1 i₁.2 t)
      (by rw [Category.assoc, hf, coprod.inl_desc, hp]; simp only [curveChange, pullback.lift_fst]) with hl₁
  set l₂ : Limits.pullback y₂ t ⟶ Limits.pullback f p :=
    pullback.lift (pullback.fst y₂ t ≫ coprod.inr) (curveChange i₂.1 i₂.2 t)
      (by rw [Category.assoc, hf, coprod.inr_desc, hp]; simp only [curveChange, pullback.lift_fst]) with hl₂
  have hl₁snd : l₁ ≫ pullback.snd f p = curveChange i₁.1 i₁.2 t := by rw [hl₁, pullback.lift_snd]
  have hl₂snd : l₂ ≫ pullback.snd f p = curveChange i₂.1 i₂.2 t := by rw [hl₂, pullback.lift_snd]
  have hl₁fst : l₁ ≫ pullback.fst f p = pullback.fst y₁ t ≫ coprod.inl := by rw [hl₁, pullback.lift_fst]
  have hl₂fst : l₂ ≫ pullback.fst f p = pullback.fst y₂ t ≫ coprod.inr := by rw [hl₂, pullback.lift_fst]

  have sq₁ : IsPullback l₁ (pullback.fst y₁ t) (pullback.fst f p) coprod.inl := by
    refine IsPullback.of_right ?_ hl₁fst (IsPullback.of_hasPullback f p).flip
    rw [hl₁snd, hf, coprod.inl_desc]
    exact isPullback_curveChange_fst i₁.1 i₁.2 t
  have sq₂ : IsPullback l₂ (pullback.fst y₂ t) (pullback.fst f p) coprod.inr := by
    refine IsPullback.of_right ?_ hl₂fst (IsPullback.of_hasPullback f p).flip
    rw [hl₂snd, hf, coprod.inr_desc]
    exact isPullback_curveChange_fst i₂.1 i₂.2 t
  haveI : IsOpenImmersion l₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq₁.flip inferInstance
  haveI : IsOpenImmersion l₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq₂.flip inferInstance

  have hcov : ∀ q : ↥(Limits.pullback f p), q ∈ l₁.opensRange ∨ q ∈ l₂.opensRange := by
    intro q
    have hq : (pullback.fst f p).base q ∈ Set.range (coprod.inl : Y₁ ⟶ Y₁ ⨿ Y₂).base ⊔
        Set.range (coprod.inr : Y₂ ⟶ Y₁ ⨿ Y₂).base := by
      rw [(isCompl_range_inl_inr Y₁ Y₂).sup_eq_top]; trivial
    rcases hq with ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst f p) (g := coprod.inl) q y
        hy.symm
      exact Scheme.Hom.mem_opensRange.mpr ⟨sq₁.isoPullback.inv.base w, by
        rw [← Scheme.Hom.comp_apply, sq₁.isoPullback_inv_fst]; exact hw⟩
    · right
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst f p) (g := coprod.inr) q y
        hy.symm
      exact Scheme.Hom.mem_opensRange.mpr ⟨sq₂.isoPullback.inv.base w, by
        rw [← Scheme.Hom.comp_apply, sq₂.isoPullback_inv_fst]; exact hw⟩

  have hvan : ∀ (V : (Limits.pullback f p).Opens) (s : Γ(Limits.pullback f p, V)),
      l₁.app V s = 0 → l₂.app V s = 0 → s = 0 := by
    intro V s h₁ h₂
    let O : Bool → (Limits.pullback f p).Opens := fun b => bif b then l₁ ''ᵁ l₁ ⁻¹ᵁ V else l₂ ''ᵁ l₂ ⁻¹ᵁ V
    have hO : ∀ b, O b ≤ V := by
      intro b
      cases b
      · change l₂ ''ᵁ l₂ ⁻¹ᵁ V ≤ V
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right
      · change l₁ ''ᵁ l₁ ⁻¹ᵁ V ≤ V
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right
    have hVO : V ≤ ⨆ b, O b := by
      intro q hq
      rw [Opens.mem_iSup]
      rcases hcov q with h | h
      · refine ⟨true, ?_⟩
        change q ∈ l₁ ''ᵁ l₁ ⁻¹ᵁ V
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact ⟨h, hq⟩
      · refine ⟨false, ?_⟩
        change q ∈ l₂ ''ᵁ l₂ ⁻¹ᵁ V
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact ⟨h, hq⟩
    apply (Limits.pullback f p).sheaf.eq_of_locally_eq' O V (fun b => homOfLE (hO b)) hVO
    intro b
    change (Limits.pullback f p).presheaf.map (homOfLE (hO b)).op s =
      (Limits.pullback f p).presheaf.map (homOfLE (hO b)).op 0
    rw [map_zero]
    cases b
    · exact map_eq_zero_of_app_eq_zero l₂ s h₂
    · exact map_eq_zero_of_app_eq_zero l₁ s h₁

  intro u u' huu
  simp only [Prod.mk.injEq] at huu
  obtain ⟨h₁, h₂⟩ := huu
  rw [← sub_eq_zero]
  apply hinjP U
  rw [map_zero]
  apply hvan
  · have e := Scheme.Hom.congr_app hl₁snd U
    rw [Scheme.Hom.comp_app] at e
    have e' := CategoryTheory.ConcreteCategory.congr_hom e (u - u')
    rw [CategoryTheory.ConcreteCategory.comp_apply] at e'
    erw [CategoryTheory.ConcreteCategory.comp_apply] at e'
    rw [e', map_sub, h₁, sub_self, map_zero]
  · have e := Scheme.Hom.congr_app hl₂snd U
    rw [Scheme.Hom.comp_app] at e
    have e' := CategoryTheory.ConcreteCategory.congr_hom e (u - u')
    rw [CategoryTheory.ConcreteCategory.comp_apply] at e'
    erw [CategoryTheory.ConcreteCategory.comp_apply] at e'
    rw [e', map_sub, h₂, sub_self, map_zero]

end BaseChange

end MilnorBC
p2m_reactivate "P2MW.S_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced.MilnorBC"

theorem solution
    {k : Type u} [Field k] {X Y₁ Y₂ Z : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (y₁ : Y₁ ⟶ Spec (CommRingCat.of k)) (y₂ : Y₂ ⟶ Spec (CommRingCat.of k)) (z : Z ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver y₁ x) (i₂ : SchemeHomOver y₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ p : X, p ∈ Set.range i₁.1.base ∨ p ∈ Set.range i₂.1.base)
    (j₁ : SchemeHomOver z y₁) (j₂ : SchemeHomOver z y₂) (hZ : IsPullback j₁.1 j₂.1 i₁.1 i₂.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (hsq : curveChange j₁.1 j₁.2 t ≫ curveChange i₁.1 i₁.2 t = curveChange j₂.1 j₂.2 t ≫ curveChange i₂.1 i₂.2 t)
    (U : (Limits.pullback x t).Opens) :
    Function.Injective (fun f : Γ(Limits.pullback x t, U) =>
      ((curveChange i₁.1 i₁.2 t).app U f, (curveChange i₂.1 i₂.2 t).app U f)) ∧
      ∀ (g₁ : Γ(Limits.pullback y₁ t, (curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U))
        (g₂ : Γ(Limits.pullback y₂ t, (curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U)),
        (Limits.pullback z t).presheaf.map
            (eqToHom (show (curveChange j₂.1 j₂.2 t) ⁻¹ᵁ ((curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U) =
                (curveChange j₁.1 j₁.2 t) ⁻¹ᵁ ((curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq])).op
          ((curveChange j₁.1 j₁.2 t).app ((curveChange i₁.1 i₁.2 t) ⁻¹ᵁ U) g₁) =
          (curveChange j₂.1 j₂.2 t).app ((curveChange i₂.1 i₂.2 t) ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(Limits.pullback x t, U),
          (curveChange i₁.1 i₁.2 t).app U f = g₁ ∧ (curveChange i₂.1 i₂.2 t).app U f = g₂ :=
  ⟨MilnorBC.app_curveChange_injective x y₁ y₂ i₁ i₂ t hXred hjs U,
    MilnorBC.exists_of_forall_isAffineOpen _ _ _ _ hsq U
      (fun V _ => MilnorBC.app_curveChange_injective x y₁ y₂ i₁ i₂ t hXred hjs V)
      (fun V hV _ => MilnorBC.exists_of_isAffineOpen _ _ _ _ (MilnorBC.isPullback_curveChange x y₁ y₂ z i₁ i₂ j₁ j₂ t hZ)
        V hV)⟩

end S_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_app_curveChange_injective_and_exists_of_app_eq_of_isReduced (solution)
