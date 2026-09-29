-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5f69a35e-41f1-53e8-99e6-0c1eacc7f985

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj

set_option autoImplicit false

p2m_open "CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme"

namespace P1R0

universe w u

variable {S : Scheme.{u}}

theorem map_map {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (t : P.obj (op Z)) :
    P.map a.op (P.map b.op t) = P.map (a ≫ b).op t := by
  simp only [op_comp, Functor.map_comp, types_comp_apply]

noncomputable def objOf {Y : Scheme.{u}} (a : Y ⟶ S) (ha : fppfProperty a) : S.Fppf :=
  MorphismProperty.Over.mk ⊤ a ha

noncomputable def homOf {Y : Scheme.{u}} {a : Y ⟶ S} {ha : fppfProperty a} (Z : S.Fppf)
    (k : Y ⟶ Z.left) (w : k ≫ Z.hom = a) : objOf a ha ⟶ Z :=
  MorphismProperty.Over.homMk k w trivial

theorem isSheaf_comp (P : Scheme.{u}ᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf Scheme.fppfTopology P) :
    Presieve.IsSheaf (smallFppfTopology S)
      ((Scheme.Fppf.forget S ⋙ Over.forget S).op ⋙ P) := by
  intro U T hT x hx

  have hT₁ : Sieve.overEquiv ((Scheme.Fppf.forget S).obj U)
      (T.functorPushforward (Scheme.Fppf.forget S)) ∈
        Scheme.grothendieckTopology fppfProperty U.left := by
    rw [smallFppfTopology_eq_restrictedTopology, Functor.mem_restrictedTopology_iff,
      GrothendieckTopology.mem_over_iff] at hT
    exact hT
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (X := U.left)).mp hT₁

  have hmem : ∀ i, (T.functorPushforward (Scheme.Fppf.forget S)).arrows (Over.homMk (𝒰.f i) :
      Over.mk (𝒰.f i ≫ ((Scheme.Fppf.forget S).obj U).hom) ⟶ (Scheme.Fppf.forget S).obj U) :=
    fun i => (Sieve.overEquiv_iff _ _).mp (h𝒰 _ _ (Presieve.ofArrows.mk i))
  let σ := fun i => Presieve.getFunctorPushforwardStructure (hmem i)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ∀ i, 𝒰.X i ⟶ (σ i).preobj.left, ∀ i, ℓ i = (σ i).lift.left :=
    ⟨fun i => (σ i).lift.left, fun _ => rfl⟩
  have hfac : ∀ i, 𝒰.f i = ℓ i ≫ (σ i).premap.left := fun i => by
    rw [hℓ]
    exact congrArg CommaMorphism.left (σ i).fac
  have hw : ∀ i, ℓ i ≫ (σ i).preobj.hom = 𝒰.f i ≫ U.hom := fun i => by
    rw [hℓ]
    exact Over.w (σ i).lift

  have hsheaf : Presieve.IsSheafFor P (Presieve.ofArrows 𝒰.X 𝒰.f) :=
    hP.isSheafFor _ (Scheme.Cover.mem_grothendieckTopology 𝒰)
  have hcompat : Presieve.Arrows.PullbackCompatible (P := P) (π := 𝒰.f)
      (fun i => P.map (ℓ i).op (x (σ i).premap (σ i).cover)) := by
    intro i j
    have hQ : fppfProperty (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ U.hom) :=
      fppfProperty.comp_mem _ _ (fppfProperty.pullback_fst _ _ (𝒰.map_prop j))
        (fppfProperty.comp_mem _ _ (𝒰.map_prop i) U.prop)
    let k₁ : objOf _ hQ ⟶ (σ i).preobj := homOf (σ i).preobj
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ ℓ i) (by rw [Category.assoc, hw i])
    let k₂ : objOf _ hQ ⟶ (σ j).preobj := homOf (σ j).preobj
      (pullback.snd (𝒰.f i) (𝒰.f j) ≫ ℓ j)
      (by rw [Category.assoc, hw j]; exact (pullback.condition_assoc _).symm)
    have comm : k₁ ≫ (σ i).premap = k₂ ≫ (σ j).premap := by
      apply MorphismProperty.Over.Hom.ext
      change (pullback.fst (𝒰.f i) (𝒰.f j) ≫ ℓ i) ≫ (σ i).premap.left =
        (pullback.snd (𝒰.f i) (𝒰.f j) ≫ ℓ j) ≫ (σ j).premap.left
      rw [Category.assoc, Category.assoc, ← hfac i, ← hfac j]
      exact pullback.condition
    calc P.map (pullback.fst (𝒰.f i) (𝒰.f j)).op (P.map (ℓ i).op (x (σ i).premap (σ i).cover))
        = P.map (pullback.fst (𝒰.f i) (𝒰.f j) ≫ ℓ i).op (x (σ i).premap (σ i).cover) :=
          map_map P _ _ _
      _ = P.map (pullback.snd (𝒰.f i) (𝒰.f j) ≫ ℓ j).op (x (σ j).premap (σ j).cover) :=
          hx k₁ k₂ (σ i).cover (σ j).cover comm
      _ = P.map (pullback.snd (𝒰.f i) (𝒰.f j)).op (P.map (ℓ j).op (x (σ j).premap (σ j).cover)) :=
          (map_map P _ _ _).symm
  obtain ⟨t, ht, huniq⟩ :=
    (Presieve.isSheafFor_arrows_iff_pullbacks (P := P) (π := 𝒰.f)).mp hsheaf _ hcompat
  have ht' : ∀ i, P.map (𝒰.f i).op t = P.map (ℓ i).op (x (σ i).premap (σ i).cover) :=
    fun i => ht i
  refine ⟨t, ?_, ?_⟩
  ·

    intro V f hf
    change P.map f.left.op t = x f hf
    have hsep : Presieve.IsSeparatedFor P
        (Presieve.ofArrows (𝒰.pullback₁ f.left).X (𝒰.pullback₁ f.left).f) :=
      (hP.isSheafFor _ (Scheme.Cover.mem_grothendieckTopology (𝒰.pullback₁ f.left))).isSeparatedFor
    refine hsep.ext ?_
    rintro _ _ ⟨i⟩
    have hVi : fppfProperty (pullback.fst f.left (𝒰.f i) ≫ V.hom) :=
      fppfProperty.comp_mem _ _ (fppfProperty.pullback_fst _ _ (𝒰.map_prop i)) V.prop
    let k₁ : objOf _ hVi ⟶ V := homOf V (pullback.fst f.left (𝒰.f i)) rfl
    let k₂ : objOf _ hVi ⟶ (σ i).preobj := homOf (σ i).preobj
      (pullback.snd f.left (𝒰.f i) ≫ ℓ i)
      (by rw [Category.assoc, hw i, ← MorphismProperty.Over.w f]
          exact (pullback.condition_assoc _).symm)
    have comm : k₁ ≫ f = k₂ ≫ (σ i).premap := by
      apply MorphismProperty.Over.Hom.ext
      change pullback.fst f.left (𝒰.f i) ≫ f.left =
        (pullback.snd f.left (𝒰.f i) ≫ ℓ i) ≫ (σ i).premap.left
      rw [Category.assoc, ← hfac i]
      exact pullback.condition
    calc P.map (pullback.fst f.left (𝒰.f i)).op (P.map f.left.op t)
        = P.map (pullback.fst f.left (𝒰.f i) ≫ f.left).op t := map_map P _ _ _
      _ = P.map (pullback.snd f.left (𝒰.f i) ≫ 𝒰.f i).op t :=
          congrArg (fun φ : pullback f.left (𝒰.f i) ⟶ U.left => P.map φ.op t)
            (pullback.condition (f := f.left) (g := 𝒰.f i))
      _ = P.map (pullback.snd f.left (𝒰.f i)).op (P.map (𝒰.f i).op t) := (map_map P _ _ _).symm
      _ = P.map (pullback.snd f.left (𝒰.f i)).op (P.map (ℓ i).op (x (σ i).premap (σ i).cover)) :=
          congrArg (P.map (pullback.snd f.left (𝒰.f i)).op) (ht' i)
      _ = P.map (pullback.snd f.left (𝒰.f i) ≫ ℓ i).op (x (σ i).premap (σ i).cover) :=
          map_map P _ _ _
      _ = P.map (pullback.fst f.left (𝒰.f i)).op (x f hf) := (hx k₁ k₂ hf (σ i).cover comm).symm
  ·
    intro t' ht'
    apply huniq
    intro i
    have h : P.map (σ i).premap.left.op t' = x (σ i).premap (σ i).cover :=
      ht' (σ i).premap (σ i).cover
    calc P.map (𝒰.f i).op t'
        = P.map (ℓ i ≫ (σ i).premap.left).op t' :=
          congrArg (fun φ : 𝒰.X i ⟶ U.left => P.map φ.op t') (hfac i)
      _ = P.map (ℓ i).op (P.map (σ i).premap.left.op t') := (map_map P _ _ t').symm
      _ = P.map (ℓ i).op (x (σ i).premap (σ i).cover) := congrArg (P.map (ℓ i).op) h

end P1R0

universe u

open P1R0 in
theorem solution
    (S : Scheme.{u}) (X : Over S) :
    Presheaf.IsSheaf (smallFppfTopology S) ((Scheme.Fppf.forget S).op ⋙ yoneda.obj X) := by
  rw [isSheaf_iff_isSheaf_of_type]

  let F : (S.Fppf)ᵒᵖ ⥤ Type u := (Scheme.Fppf.forget S ⋙ Over.forget S).op ⋙ yoneda.obj X.left
  let FS : (S.Fppf)ᵒᵖ ⥤ Type u := (Scheme.Fppf.forget S ⋙ Over.forget S).op ⋙ yoneda.obj S
  have hF : Presieve.IsSheaf (smallFppfTopology S) F :=
    isSheaf_comp _ (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have hFS : Presieve.IsSheaf (smallFppfTopology S) FS :=
    isSheaf_comp _ (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

  let G : Subfunctor F :=
    { obj := fun U => {g : (unop U).left ⟶ X.left | g ≫ X.hom = (unop U).hom}
      map := by
        rintro U V i g (hg : g ≫ X.hom = (unop U).hom)
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun t => i.unop.left ≫ t) hg).trans (MorphismProperty.Over.w i.unop)) }

  have hG : Presieve.IsSheaf (smallFppfTopology S) G.toFunctor := by
    refine (Subfunctor.isSheaf_iff G hF).mpr fun U s hs => ?_
    change s ≫ X.hom = (unop U).hom
    refine (hFS _ hs).isSeparatedFor.ext fun V f hf => ?_
    have hf' : (f.left ≫ s) ≫ X.hom = V.hom := hf
    exact (Category.assoc _ _ _).symm.trans (hf'.trans (MorphismProperty.Over.w f).symm)

  let e : G.toFunctor ≅ (Scheme.Fppf.forget S).op ⋙ yoneda.obj X :=
    NatIso.ofComponents
      (fun U => Equiv.toIso
        { toFun := fun g => Over.homMk g.1 g.2
          invFun := fun k => ⟨k.left, Over.w k⟩
          left_inv := fun g => rfl
          right_inv := fun k => Over.OverMorphism.ext rfl })
      (by
        intro U V i
        ext g
        exact Over.OverMorphism.ext rfl)
  exact Presieve.isSheaf_iso (smallFppfTopology S) e hG

end S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj (solution)
