-- Prove2me | solution 1 for AlgebraicGeometry.natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/72d9719a-2380-566e-9145-1dc60040c634

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction

set_option autoImplicit false

p2m_open "CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme"

namespace CECH1DN

universe w u

variable {S : Scheme.{u}}

private theorem _root_.CECH1DN.map_map {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (t : P.obj (op Z)) :
    P.map a.op (P.map b.op t) = P.map (a ≫ b).op t := by
  simp only [op_comp, Functor.map_comp, types_comp_apply]

p2m_export "CECH1DN" "map_map"

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

end CECH1DN

namespace CECH1DN

scoped instance : (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).IsContinuous
    (smallFppfTopology specInt) Scheme.fppfTopology.{0} where
  op_comp_isSheaf_of_types G :=
    isSheaf_comp G.obj ((isSheaf_iff_isSheaf_of_type Scheme.fppfTopology.{0} G.obj).mp G.property)

scoped instance : (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).IsCocontinuous
    (smallFppfTopology specInt) Scheme.fppfTopology.{0} :=
  isCocontinuous_comp (Scheme.Fppf.forget specInt) (Over.forget specInt)
    (smallFppfTopology specInt) (fppfTopology.over specInt)

noncomputable example :=
  (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).sheafAdjunctionCocontinuous Ab.{1}
    (smallFppfTopology specInt) Scheme.fppfTopology.{0}

noncomputable example : Sheaf Scheme.fppfTopology.{0} Ab.{1} ⥤ Sheaf (smallFppfTopology specInt) Ab.{1} :=
  (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).sheafPushforwardContinuous Ab.{1}
    (smallFppfTopology specInt) Scheme.fppfTopology.{0}

example (X : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    (((Scheme.Fppf.forget specInt ⋙ Over.forget specInt).sheafPushforwardContinuous Ab.{1}
        (smallFppfTopology specInt) Scheme.fppfTopology.{0}).obj X).obj
      = (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj := rfl

end CECH1DN
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

namespace CECH1DN

p2m_open "Functor CategoryTheory.Functor CategoryTheory.Limits"

noncomputable abbrev Res :
    Sheaf Scheme.fppfTopology.{0} Ab.{1} ⥤ Sheaf (smallFppfTopology specInt) Ab.{1} :=
  (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).sheafPushforwardContinuous Ab.{1}
    (smallFppfTopology specInt) Scheme.fppfTopology.{0}

noncomputable scoped instance : Res.IsLeftAdjoint :=
  ⟨_, ⟨(Scheme.Fppf.forget specInt ⋙ Over.forget specInt).sheafAdjunctionCocontinuous Ab.{1}
    (smallFppfTopology specInt) Scheme.fppfTopology.{0}⟩⟩

example : PreservesColimitsOfSize.{1, 1} Res := inferInstance

noncomputable scoped instance : PreservesLimitsOfSize.{1, 1} Res :=
  preservesLimits_of_reflects_of_preserves Res
    (sheafToPresheaf (smallFppfTopology specInt) Ab.{1})

example {S : ShortComplex (Sheaf Scheme.fppfTopology.{0} Ab.{1})} (hS : S.ShortExact) :
    (S.map Res).ShortExact :=
  hS.map_of_exact Res

scoped instance : Res.Additive where
  map_add := by intros; exact Sheaf.hom_ext rfl

example : Res.PreservesZeroMorphisms := inferInstance

end CECH1DN
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

namespace CECH1DN

private lemma piEl_ext {ι : Type} {A : ι → Ab.{1}} {x y : ∀ i, A i}
    (h : ∀ i, x i = y i) : x = y := funext h

variable (I : Sheaf Scheme.fppfTopology.{0} Ab.{1})

noncomputable def psiW (W : Scheme.{0}) : Sheaf Scheme.fppfTopology.{0} Ab.{1} :=
  letI := Functor.isContinuous_comp (Over.star W) (Over.forget W)
    Scheme.fppfTopology.{0} (Scheme.fppfTopology.{0}.over W) Scheme.fppfTopology.{0}
  ((Over.star W ⋙ Over.forget W).sheafPushforwardContinuous Ab.{1}
    Scheme.fppfTopology.{0} Scheme.fppfTopology.{0}).obj I

variable (ι : Type) (S : ι → Scheme.{0})

noncomputable def piProdPre : Scheme.{0}ᵒᵖ ⥤ Ab.{1} where
  obj V := AddCommGrpCat.of (∀ i, I.obj.obj (op (S i ⨯ V.unop)))
  map {V W} φ := AddCommGrpCat.ofHom
    { toFun := fun G i => (I.obj.map (prod.map (𝟙 (S i)) φ.unop).op).hom (G i)
      map_zero' := piEl_ext fun i => map_zero _
      map_add' := fun a b => piEl_ext fun i => map_add _ _ _ }
  map_id V := by
    ext G : 2
    exact piEl_ext fun i => by simp
  map_comp {U V W} φ ψ := by
    ext G : 2
    refine piEl_ext fun i => ?_
    have h : prod.map (𝟙 (S i)) (φ ≫ ψ).unop
        = prod.map (𝟙 (S i)) ψ.unop ≫ prod.map (𝟙 (S i)) φ.unop := by
      rw [prod.map_map]
      simp
    show (I.obj.map (prod.map (𝟙 (S i)) (φ ≫ ψ).unop).op).hom (G i)
        = ((I.obj.map (prod.map (𝟙 (S i)) φ.unop).op) ≫
            (I.obj.map (prod.map (𝟙 (S i)) ψ.unop).op)).hom (G i)
    rw [← Functor.map_comp, ← op_comp, h]

noncomputable def piProdCone :
    Cone (Discrete.functor (fun i => psiW I (S i)) ⋙
      sheafToPresheaf Scheme.fppfTopology.{0} Ab.{1}) where
  pt := piProdPre I ι S
  π := Discrete.natTrans fun ⟨i⟩ =>
    { app := fun V => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ i)
      naturality := fun V W φ => by
        ext G : 2
        rfl }

noncomputable def piProdConeIsLimit : IsLimit (piProdCone I ι S) := by
  apply evaluationJointlyReflectsLimits
  intro V
  exact
    { lift := fun c => AddCommGrpCat.ofHom
        { toFun := fun x i => ((c.π.app ⟨i⟩).hom) x
          map_zero' := piEl_ext fun i => map_zero _
          map_add' := fun a b => piEl_ext fun i => map_add _ _ _ }
      fac := fun c => by
        rintro ⟨i⟩
        ext x : 2
        rfl
      uniq := fun c m hm => by
        ext x : 2
        refine piEl_ext fun i => ?_
        exact congrArg (fun ψ => (AddCommGrpCat.Hom.hom ψ) x) (hm ⟨i⟩) }

theorem piProd_isSheaf : Presheaf.IsSheaf Scheme.fppfTopology.{0} (piProdPre I ι S) :=
  Sheaf.isSheaf_of_isLimit (Discrete.functor (fun i => psiW I (S i))) (piProdCone I ι S)
    (piProdConeIsLimit I ι S)

noncomputable def piProdSheaf : Sheaf Scheme.fppfTopology.{0} Ab.{1} :=
  ⟨piProdPre I ι S, piProd_isSheaf I ι S⟩

@[scoped simp] lemma piProdSheaf_map_apply {V W : Scheme.{0}} (φ : W ⟶ V)
    (G : ∀ i, I.obj.obj (op (S i ⨯ V))) (i : ι) :
    ((piProdSheaf I ι S).obj.map φ.op).hom G i
      = (I.obj.map (prod.map (𝟙 (S i)) φ).op).hom (G i) := rfl

noncomputable def toPiProd : I ⟶ piProdSheaf I ι S where
  hom :=
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun s i => (I.obj.map (prod.snd : S i ⨯ V.unop ⟶ V.unop).op).hom s
          map_zero' := piEl_ext fun i => map_zero _
          map_add' := fun a b => piEl_ext fun i => map_add _ _ _ }
      naturality := fun V W φ => by
        ext s : 2
        refine piEl_ext fun i => ?_
        have harr : (φ ≫ (prod.snd : S i ⨯ W.unop ⟶ W.unop).op)
            = (prod.map (𝟙 (S i)) φ.unop ≫ (prod.snd : S i ⨯ V.unop ⟶ V.unop)).op := by
          apply Quiver.Hom.unop_inj
          simp
        change (I.obj.map φ ≫ I.obj.map ((prod.snd : S i ⨯ W.unop ⟶ W.unop).op)).hom s
            = (I.obj.map ((prod.snd : S i ⨯ V.unop ⟶ V.unop).op)
                ≫ I.obj.map (prod.map (𝟙 (S i)) φ.unop).op).hom s
        rw [← I.obj.map_comp, ← I.obj.map_comp, ← op_comp, harr] }

@[scoped simp] lemma toPiProd_app_apply (V : Scheme.{0}ᵒᵖ) (s : I.obj.obj V) (i : ι) :
    (((toPiProd I ι S).hom.app V).hom s) i
      = (I.obj.map (prod.snd : S i ⨯ V.unop ⟶ V.unop).op).hom s := rfl

section Mono

variable (f : ∀ i, S i ⟶ specInt)
  (hS : Sieve.ofArrows S f ∈ Scheme.fppfTopology.{0} specInt)

private noncomputable abbrev elHom {A : Ab.{1}} (a : A) :
    AddCommGrpCat.of (ULift.{1} ℤ) ⟶ A :=
  (homULiftIntAddEquiv A).symm a

private lemma homULiftIntAddEquiv_apply {A : Ab.{1}} (g : AddCommGrpCat.of (ULift.{1} ℤ) ⟶ A) :
    homULiftIntAddEquiv A g = g.hom ⟨1⟩ := rfl

private lemma elHom_apply_one {A : Ab.{1}} (a : A) : (elHom a).hom ⟨1⟩ = a := by
  rw [← homULiftIntAddEquiv_apply]
  exact (homULiftIntAddEquiv A).apply_symm_apply a

private lemma ulift_hom_ext {A : Ab.{1}} {g₁ g₂ : AddCommGrpCat.of (ULift.{1} ℤ) ⟶ A}
    (h : g₁.hom ⟨1⟩ = g₂.hom ⟨1⟩) : g₁ = g₂ :=
  (homULiftIntAddEquiv A).injective
    (by rw [homULiftIntAddEquiv_apply, homULiftIntAddEquiv_apply]; exact h)

private lemma elHom_comp {A B : Ab.{1}} (a : A) (φ : A ⟶ B) :
    elHom a ≫ φ = elHom (φ.hom a) := by
  refine ulift_hom_ext ?_
  show φ.hom ((elHom a).hom ⟨1⟩) = (elHom (φ.hom a)).hom ⟨1⟩
  rw [elHom_apply_one, elHom_apply_one]

include f hS in

theorem mono_toPiProd : Mono (toPiProd I ι S) := by
  have hval : Mono (toPiProd I ι S).1 := by
    rw [NatTrans.mono_iff_mono_app]
    intro V
    rw [AddCommGrpCat.mono_iff_injective]
    intro s t hst
    rw [← sub_eq_zero]
    set d := s - t with hd
    have hcomp : ∀ i, (I.obj.map (prod.snd : S i ⨯ V.unop ⟶ V.unop).op).hom d = 0 := by
      intro i
      have hs' : (((toPiProd I ι S).hom.app V).hom s) i
          = (((toPiProd I ι S).hom.app V).hom t) i := by rw [hst]
      rw [toPiProd_app_apply, toPiProd_app_apply] at hs'
      rw [hd, map_sub]
      exact sub_eq_zero.mpr hs'

    have hR : (Sieve.ofArrows S f).pullback (specZIsTerminal.from V.unop)
        ∈ Scheme.fppfTopology.{0} V.unop :=
      Scheme.fppfTopology.{0}.pullback_stable _ hS

    have hvanish : ∀ ⦃W : Scheme.{0}⦄ ⦃g : W ⟶ V.unop⦄,
        ((Sieve.ofArrows S f).pullback (specZIsTerminal.from V.unop)) g →
        (I.obj ⋙ coyoneda.obj (op (AddCommGrpCat.of (ULift.{1} ℤ)))).map g.op (elHom d)
          = (I.obj ⋙ coyoneda.obj (op (AddCommGrpCat.of (ULift.{1} ℤ)))).map g.op
              (elHom (0 : I.obj.obj V)) := by
      intro W g hg
      obtain ⟨Y, h', g', ⟨i⟩, hfac⟩ := hg
      have hzero : (I.obj.map g.op).hom d = 0 := by
        have hgfac : g = prod.lift h' g ≫ (prod.snd : S i ⨯ V.unop ⟶ V.unop) :=
          (prod.lift_snd _ _).symm
        rw [hgfac, op_comp, Functor.map_comp]
        show (I.obj.map (prod.lift h' g).op).hom
          ((I.obj.map (prod.snd : S i ⨯ V.unop ⟶ V.unop).op).hom d) = 0
        rw [hcomp i, map_zero]
      show elHom d ≫ I.obj.map g.op = elHom (0 : I.obj.obj V) ≫ I.obj.map g.op
      rw [elHom_comp, elHom_comp, hzero, map_zero]

    have hsep := ((I.property (AddCommGrpCat.of (ULift.{1} ℤ))) _ hR).isSeparatedFor
    have helhom : elHom d = elHom (0 : I.obj.obj V) := by
      apply hsep.ext
      intro W g hg
      exact hvanish hg
    rw [← elHom_apply_one (a := d), helhom, elHom_apply_one]
  haveI := hval
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

include f hS in

noncomputable def piProdRetract [Injective I] : piProdSheaf I ι S ⟶ I :=
  haveI := mono_toPiProd I ι S f hS
  Injective.factorThru (𝟙 I) (toPiProd I ι S)

include f hS in
theorem toPiProd_retract [Injective I] :
    toPiProd I ι S ≫ piProdRetract I ι S f hS = 𝟙 I :=
  haveI := mono_toPiProd I ι S f hS
  Injective.comp_factorThru (𝟙 I) (toPiProd I ι S)

end Mono
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

end CECH1DN
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

open CategoryTheory.Abelian

namespace CECH1DN

universe u w

section furniture

variable {S : Scheme.{u}}

theorem map_map_ab {C : Type*} [Category C] (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (t : P.obj (op Z)) :
    P.map a.op (P.map b.op t) = P.map (a ≫ b).op t := by
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

end furniture
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

structure RetractData (I : Sheaf Scheme.fppfTopology.{0} Ab.{1}) (ι : Type) (S : ι → Scheme.{0})
    where

  r (V : Scheme.{0}) : (∀ i, I.obj.obj (op (S i ⨯ V))) →+ I.obj.obj (op V)
  r_natural {V W : Scheme.{0}} (φ : W ⟶ V) (G : ∀ i, I.obj.obj (op (S i ⨯ V))) :
    I.obj.map φ.op (r V G) = r W (fun i => I.obj.map (prod.map (𝟙 (S i)) φ).op (G i))
  r_section (V : Scheme.{0}) (s : I.obj.obj (op V)) :
    r V (fun i => I.obj.map (prod.snd : S i ⨯ V ⟶ V).op s) = s

theorem coboundary_of_cocycle {I : Sheaf Scheme.fppfTopology.{0} Ab.{1}} {ι : Type}
    {S : ι → Scheme.{0}} (D : RetractData I ι S)
    (g : ∀ a b : ι, I.obj.obj (op (S a ⨯ S b)))
    (hg : ∀ a b c : ι,
      I.obj.map (prod.map (𝟙 (S c)) (prod.fst : S a ⨯ S b ⟶ S a)).op (g c a) +
        I.obj.map (prod.snd : S c ⨯ (S a ⨯ S b) ⟶ S a ⨯ S b).op (g a b) =
      I.obj.map (prod.map (𝟙 (S c)) (prod.snd : S a ⨯ S b ⟶ S b)).op (g c b)) :
    ∃ α : ∀ a, I.obj.obj (op (S a)), ∀ a b,
      g a b = I.obj.map (prod.snd : S a ⨯ S b ⟶ S b).op (α b) -
        I.obj.map (prod.fst : S a ⨯ S b ⟶ S a).op (α a) := by
  refine ⟨fun a => D.r (S a) (fun c => g c a), fun a b => ?_⟩
  have key : (fun c => I.obj.map (prod.map (𝟙 (S c)) (prod.snd : S a ⨯ S b ⟶ S b)).op (g c b)) -
      (fun c => I.obj.map (prod.map (𝟙 (S c)) (prod.fst : S a ⨯ S b ⟶ S a)).op (g c a)) =
      fun c => I.obj.map (prod.snd : S c ⨯ (S a ⨯ S b) ⟶ S a ⨯ S b).op (g a b) := by
    funext c
    simp only [Pi.sub_apply]
    rw [← hg a b c]
    abel
  calc g a b
      = D.r (S a ⨯ S b) (fun c => I.obj.map (prod.snd : S c ⨯ (S a ⨯ S b) ⟶ S a ⨯ S b).op
          (g a b)) := (D.r_section (S a ⨯ S b) (g a b)).symm
    _ = D.r (S a ⨯ S b)
          (fun c => I.obj.map (prod.map (𝟙 (S c)) (prod.snd : S a ⨯ S b ⟶ S b)).op (g c b)) -
        D.r (S a ⨯ S b)
          (fun c => I.obj.map (prod.map (𝟙 (S c)) (prod.fst : S a ⨯ S b ⟶ S a)).op (g c a)) := by
          rw [← map_sub, key]
    _ = I.obj.map (prod.snd : S a ⨯ S b ⟶ S b).op (D.r (S b) (fun c => g c b)) -
        I.obj.map (prod.fst : S a ⨯ S b ⟶ S a).op (D.r (S a) (fun c => g c a)) := by
          rw [D.r_natural, D.r_natural]

section lift

variable (I : Sheaf Scheme.fppfTopology.{0} Ab.{1})
  (hret : ∀ (ι : Type) (S : ι → Scheme.{0}) (f : ∀ i, S i ⟶ specInt),
    Sieve.ofArrows S f ∈ Scheme.fppfTopology specInt → RetractData I ι S)
  (L : Sheaf (smallFppfTopology specInt) Ab.{1})
  (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ I.obj)

noncomputable abbrev secAt (U : specInt.Fppf) :
    Sheaf (smallFppfTopology specInt) Ab.{1} ⥤ Ab.{1} :=
  sheafToPresheaf (smallFppfTopology specInt) Ab.{1} ⋙ (CategoryTheory.evaluation _ _).obj (op U)

include hret e in

theorem exists_lift {J Q : Sheaf (smallFppfTopology specInt) Ab.{1}} (ιL : L ⟶ J) (π : J ⟶ Q)
    (w : ιL ≫ π = 0) (hS : (ShortComplex.mk ιL π w).ShortExact)
    (q : Q.obj.obj (op (fppfTerminal specInt))) :
    ∃ t : J.obj.obj (op (fppfTerminal specInt)), π.hom.app (op (fppfTerminal specInt)) t = q := by
  let T : specInt.Fppf := fppfTerminal specInt
  have hmono : Mono ιL := hS.mono_f
  have hepi : Epi π := hS.epi_g

  have hls : Sheaf.IsLocallySurjective π := (Sheaf.isLocallySurjective_iff_epi' _ π).2 hepi
  have hSig : Presheaf.imageSieve π.hom q ∈ smallFppfTopology specInt T :=
    Presheaf.imageSieve_mem _ π.hom q

  have hSig₁ : Sieve.overEquiv ((Scheme.Fppf.forget specInt).obj T)
      ((Presheaf.imageSieve π.hom q).functorPushforward (Scheme.Fppf.forget specInt)) ∈
        Scheme.grothendieckTopology fppfProperty specInt :=
    (Functor.mem_restrictedTopology_iff (G := Scheme.Fppf.forget specInt)
      (K := Scheme.fppfTopology.over specInt)).mp hSig
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (X := specInt)).mp hSig₁
  have hmem : ∀ i, ((Presheaf.imageSieve π.hom q).functorPushforward
      (Scheme.Fppf.forget specInt)).arrows (Over.homMk (𝒰.f i) :
      Over.mk (𝒰.f i ≫ ((Scheme.Fppf.forget specInt).obj T).hom) ⟶
        (Scheme.Fppf.forget specInt).obj T) :=
    fun i => (Sieve.overEquiv_iff _ _).mp (h𝒰 _ _ (Presieve.ofArrows.mk i))
  let σ := fun i => Presieve.getFunctorPushforwardStructure (hmem i)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ∀ i, 𝒰.X i ⟶ (σ i).preobj.left, ∀ i, ℓ i = (σ i).lift.left :=
    ⟨fun i => (σ i).lift.left, fun _ => rfl⟩
  have hfac : ∀ i, 𝒰.f i = ℓ i ≫ (σ i).premap.left := fun i => by
    rw [hℓ]
    exact congrArg CommaMorphism.left (σ i).fac
  have hw : ∀ i, ℓ i ≫ (σ i).preobj.hom = 𝒰.f i ≫ T.hom := fun i => by
    rw [hℓ]
    exact Over.w (σ i).lift

  have hT : IsTerminal T := fppfTerminalIsTerminal specInt
  have hZ : ∀ {Y : Scheme.{0}} (a b : Y ⟶ specInt), a = b := fun a b =>
    specZIsTerminal.hom_ext a b
  have hprodfst : ∀ a b : 𝒰.I₀, fppfProperty (prod.fst : 𝒰.X a ⨯ 𝒰.X b ⟶ 𝒰.X a) :=
    fun a b => by
    have hb : fppfProperty (specZIsTerminal.from (𝒰.X b)) := by
      rw [hZ (specZIsTerminal.from (𝒰.X b)) (𝒰.f b)]; exact 𝒰.map_prop b
    exact fppfProperty.of_isPullback
      (IsPullback.of_is_product' (prodIsProd (𝒰.X a) (𝒰.X b)) specZIsTerminal).flip hb
  have hprodsnd : ∀ (Y : Scheme.{0}) (a : 𝒰.I₀), fppfProperty (prod.snd : 𝒰.X a ⨯ Y ⟶ Y) :=
    fun Y a => by
    have ha : fppfProperty (specZIsTerminal.from (𝒰.X a)) := by
      rw [hZ (specZIsTerminal.from (𝒰.X a)) (𝒰.f a)]; exact 𝒰.map_prop a
    exact fppfProperty.of_isPullback
      (IsPullback.of_is_product' (prodIsProd (𝒰.X a) Y) specZIsTerminal) ha

  let O : 𝒰.I₀ → specInt.Fppf := fun a => objOf (𝒰.f a) (𝒰.map_prop a)
  let fO : ∀ a, O a ⟶ T := fun a => homOf T (𝒰.f a) (Category.comp_id _)

  let O₂ : 𝒰.I₀ → 𝒰.I₀ → specInt.Fppf := fun a b =>
    objOf (prod.fst ≫ 𝒰.f a : 𝒰.X a ⨯ 𝒰.X b ⟶ specInt)
      (fppfProperty.comp_mem _ _ (hprodfst a b) (𝒰.map_prop a))
  let p₁ : ∀ a b, O₂ a b ⟶ O a := fun a b => homOf (O a) prod.fst rfl
  let p₂ : ∀ a b, O₂ a b ⟶ O b := fun a b => homOf (O b) prod.snd (hZ _ _)

  let O₃ : 𝒰.I₀ → 𝒰.I₀ → 𝒰.I₀ → specInt.Fppf := fun c a b =>
    objOf (prod.snd ≫ prod.fst ≫ 𝒰.f a : 𝒰.X c ⨯ (𝒰.X a ⨯ 𝒰.X b) ⟶ specInt)
      (fppfProperty.comp_mem _ _ (hprodsnd _ c)
        (fppfProperty.comp_mem _ _ (hprodfst a b) (𝒰.map_prop a)))
  let q₁ : ∀ c a b, O₃ c a b ⟶ O₂ c a := fun c a b =>
    homOf (O₂ c a) (prod.map (𝟙 _) prod.fst) (hZ _ _)
  let q₂ : ∀ c a b, O₃ c a b ⟶ O₂ c b := fun c a b =>
    homOf (O₂ c b) (prod.map (𝟙 _) prod.snd) (hZ _ _)
  let q₃ : ∀ c a b, O₃ c a b ⟶ O₂ a b := fun c a b =>
    homOf (O₂ a b) prod.snd (hZ _ _)
  have e₁ : ∀ c a b, q₁ c a b ≫ p₁ c a = q₂ c a b ≫ p₁ c b := fun c a b => by
    apply MorphismProperty.Over.Hom.ext
    change prod.map (𝟙 _) prod.fst ≫ prod.fst = prod.map (𝟙 _) prod.snd ≫ prod.fst
    simp only [prod.map_fst]
  have e₂ : ∀ c a b, q₁ c a b ≫ p₂ c a = q₃ c a b ≫ p₁ a b := fun c a b => by
    apply MorphismProperty.Over.Hom.ext
    change prod.map (𝟙 _) prod.fst ≫ prod.snd = prod.snd ≫ prod.fst
    simp only [prod.map_snd]
  have e₃ : ∀ c a b, q₃ c a b ≫ p₂ a b = q₂ c a b ≫ p₂ c b := fun c a b => by
    apply MorphismProperty.Over.Hom.ext
    change prod.snd ≫ prod.snd = prod.map (𝟙 _) prod.snd ≫ prod.snd
    simp only [prod.map_snd]

  have hlift : ∀ a, ∃ t : J.obj.obj (op (O a)), π.hom.app _ t = Q.obj.map (fO a).op q := by
    intro a
    obtain ⟨t', ht'⟩ := (σ a).cover
    let k : O a ⟶ (σ a).preobj := homOf (σ a).preobj (ℓ a) (hw a)
    have hk : k ≫ (σ a).premap = fO a := by
      apply MorphismProperty.Over.Hom.ext
      change ℓ a ≫ (σ a).premap.left = 𝒰.f a
      exact (hfac a).symm
    refine ⟨J.obj.map k.op t', ?_⟩
    calc π.hom.app _ (J.obj.map k.op t')
        = Q.obj.map k.op (π.hom.app _ t') := (NatTrans.naturality_apply π.hom k.op t')
      _ = Q.obj.map k.op (Q.obj.map (σ a).premap.op q) := by rw [ht']
      _ = Q.obj.map (fO a).op q := by rw [map_map_ab, hk]
  choose t ht using hlift

  have hexact : ∀ U : specInt.Fppf, ∀ x : J.obj.obj (op U), π.hom.app _ x = 0 →
      ∃ y : L.obj.obj (op U), ιL.hom.app _ y = x := fun U => by
    have hex := hS.exact.map_of_mono_of_preservesKernel (secAt U) hmono inferInstance
    rw [ShortComplex.ab_exact_iff] at hex
    exact hex
  have hinj : ∀ U : specInt.Fppf, Function.Injective (ιL.hom.app (op U)) := fun U => by
    have : Mono ((secAt U).map ιL) := inferInstance
    exact (AddCommGrpCat.mono_iff_injective _).mp this
  have hιπ : ∀ U : specInt.Fppf, ∀ y : L.obj.obj (op U), π.hom.app _ (ιL.hom.app _ y) = 0 :=
    fun U y => by
    change ((ιL ≫ π).hom.app (op U)) y = 0
    rw [w]
    rfl
  have hd : ∀ a b, ∃ y : L.obj.obj (op (O₂ a b)),
      ιL.hom.app _ y = J.obj.map (p₁ a b).op (t a) - J.obj.map (p₂ a b).op (t b) := by
    intro a b
    apply hexact
    rw [map_sub, NatTrans.naturality_apply π.hom, NatTrans.naturality_apply π.hom, ht, ht,
      map_map_ab, map_map_ab, hT.hom_ext (p₁ a b ≫ fO a) (p₂ a b ≫ fO b), sub_self]
  choose g₀ hg₀ using hd

  let g : ∀ a b, I.obj.obj (op (𝒰.X a ⨯ 𝒰.X b)) := fun a b => e.hom.app (op (O₂ a b)) (g₀ a b)
  have he : ∀ {U V : specInt.Fppf} (k : V ⟶ U) (y : L.obj.obj (op U)),
      I.obj.map k.left.op (e.hom.app (op U) y) = e.hom.app (op V) (L.obj.map k.op y) :=
    fun k y => (NatTrans.naturality_apply e.hom k.op y).symm
  have hcocycle : ∀ a b c,
      I.obj.map (prod.map (𝟙 (𝒰.X c)) (prod.fst : 𝒰.X a ⨯ 𝒰.X b ⟶ 𝒰.X a)).op (g c a) +
        I.obj.map (prod.snd : 𝒰.X c ⨯ (𝒰.X a ⨯ 𝒰.X b) ⟶ 𝒰.X a ⨯ 𝒰.X b).op (g a b) =
      I.obj.map (prod.map (𝟙 (𝒰.X c)) (prod.snd : 𝒰.X a ⨯ 𝒰.X b ⟶ 𝒰.X b)).op (g c b) := by
    intro a b c
    have h₀ : L.obj.map (q₁ c a b).op (g₀ c a) + L.obj.map (q₃ c a b).op (g₀ a b) =
        L.obj.map (q₂ c a b).op (g₀ c b) := by
      apply hinj
      rw [map_add, NatTrans.naturality_apply ιL.hom, NatTrans.naturality_apply ιL.hom,
        NatTrans.naturality_apply ιL.hom, hg₀, hg₀, hg₀, map_sub, map_sub, map_sub,
        map_map_ab, map_map_ab, map_map_ab, map_map_ab, map_map_ab, map_map_ab, e₁, e₂, e₃]
      abel
    have h₁ := congrArg (e.hom.app (op (O₃ c a b))) h₀
    rw [map_add, ← he, ← he, ← he] at h₁
    exact h₁

  obtain ⟨α, hα⟩ := coboundary_of_cocycle
    (hret 𝒰.I₀ 𝒰.X 𝒰.f (Scheme.Cover.mem_grothendieckTopology 𝒰)) g hcocycle
  let t' : ∀ a, J.obj.obj (op (O a)) := fun a =>
    t a + ιL.hom.app _ (e.inv.app (op (O a)) (α a))
  have he' : ∀ {U V : specInt.Fppf} (k : V ⟶ U) (y : I.obj.obj (op U.left)),
      L.obj.map k.op (e.inv.app (op U) y) = e.inv.app (op V) (I.obj.map k.left.op y) :=
    fun k y => (NatTrans.naturality_apply e.inv k.op y).symm
  have hinjE : ∀ V : specInt.Fppf, Function.Injective (e.hom.app (op V)) := fun V =>
    Function.LeftInverse.injective (g := e.inv.app (op V))
      (fun y => Iso.hom_inv_id_app_apply e (op V) y)
  have hcompat₂ : ∀ a b, J.obj.map (p₁ a b).op (t' a) = J.obj.map (p₂ a b).op (t' b) := by
    intro a b
    have hneg : e.inv.app (op (O₂ a b)) (I.obj.map (p₁ a b).left.op (α a)) -
        e.inv.app (op (O₂ a b)) (I.obj.map (p₂ a b).left.op (α b)) = -g₀ a b := by
      apply hinjE (O₂ a b)
      rw [map_sub, map_neg, Iso.inv_hom_id_app_apply, Iso.inv_hom_id_app_apply]
      change I.obj.map (prod.fst : 𝒰.X a ⨯ 𝒰.X b ⟶ 𝒰.X a).op (α a) -
          I.obj.map (prod.snd : 𝒰.X a ⨯ 𝒰.X b ⟶ 𝒰.X b).op (α b) = -g a b
      rw [hα a b, neg_sub]
    show J.obj.map (p₁ a b).op (t a + ιL.hom.app _ (e.inv.app (op (O a)) (α a))) =
      J.obj.map (p₂ a b).op (t b + ιL.hom.app _ (e.inv.app (op (O b)) (α b)))
    rw [map_add, map_add, ← NatTrans.naturality_apply ιL.hom, ← NatTrans.naturality_apply ιL.hom,
      he', he', ← sub_eq_zero, add_sub_add_comm, ← map_sub, hneg, ← hg₀, map_neg, add_neg_cancel]

  have hcov : Sieve.generate (Presieve.ofArrows O fO) ∈ smallFppfTopology specInt T := by
    rw [smallFppfTopology_eq_restrictedTopology, Functor.mem_restrictedTopology_iff,
      GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv ((Scheme.Fppf.forget specInt).obj T)
      ((Sieve.generate (Presieve.ofArrows O fO)).functorPushforward
        (Scheme.Fppf.forget specInt)) ∈ Scheme.grothendieckTopology fppfProperty specInt
    refine GrothendieckTopology.superset_covering _ ?_ (Scheme.Cover.mem_grothendieckTopology 𝒰)
    rintro Y _ ⟨W, i, g', ⟨a⟩, rfl⟩
    refine (Sieve.overEquiv_iff _ _).mpr ⟨O a, fO a, Over.homMk i (hZ _ _),
      Sieve.le_generate _ _ _ (Presieve.ofArrows.mk a), ?_⟩
    ext
    rfl

  have hJ : Presieve.IsSheaf (smallFppfTopology specInt) (J.obj ⋙ forget Ab.{1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (smallFppfTopology specInt) (forget Ab.{1})).obj J).property
  have hQ : Presieve.IsSheaf (smallFppfTopology specInt) (Q.obj ⋙ forget Ab.{1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (smallFppfTopology specInt) (forget Ab.{1})).obj Q).property
  have hcompat : Presieve.Arrows.Compatible (J.obj ⋙ forget Ab.{1}) fO t' := by
    intro a b Z ga gb _
    let m : Z ⟶ O₂ a b := MorphismProperty.Over.homMk (prod.lift ga.left gb.left)
      (by
        change prod.lift ga.left gb.left ≫ prod.fst ≫ 𝒰.f a = Z.hom
        rw [prod.lift_fst_assoc]
        exact MorphismProperty.Over.w ga) trivial
    have ha : ga = m ≫ p₁ a b := by
      apply MorphismProperty.Over.Hom.ext
      change ga.left = prod.lift ga.left gb.left ≫ prod.fst
      rw [prod.lift_fst]
    have hb : gb = m ≫ p₂ a b := by
      apply MorphismProperty.Over.Hom.ext
      change gb.left = prod.lift ga.left gb.left ≫ prod.snd
      rw [prod.lift_snd]
    change J.obj.map ga.op (t' a) = J.obj.map gb.op (t' b)
    rw [ha, hb, ← map_map_ab, ← map_map_ab, hcompat₂]
  obtain ⟨s, hs, -⟩ :=
    (Presieve.isSheafFor_arrows_iff (P := J.obj ⋙ forget Ab.{1}) (π := fO)).mp
      (hJ.isSheafFor _ hcov) t' hcompat
  refine ⟨s, ?_⟩

  have hsep : Presieve.IsSeparatedFor (Q.obj ⋙ forget Ab.{1}) (Presieve.ofArrows O fO) :=
    (hQ.isSheafFor _ hcov).isSeparatedFor
  refine hsep.ext ?_
  rintro _ _ ⟨a⟩
  change Q.obj.map (fO a).op (π.hom.app _ s) = Q.obj.map (fO a).op q
  rw [← NatTrans.naturality_apply π.hom, show J.obj.map (fO a).op s = t' a from hs a]
  show π.hom.app _ (t a + ιL.hom.app _ (e.inv.app (op (O a)) (α a))) = _
  rw [map_add, ht, hιπ, add_zero]

end lift
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

theorem subsingleton_H_one (I : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (hret : ∀ (ι : Type) (S : ι → Scheme.{0}) (f : ∀ i, S i ⟶ specInt),
      Sieve.ofArrows S f ∈ Scheme.fppfTopology specInt → RetractData I ι S)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ I.obj) :
    Subsingleton (fppfCohomology specInt L 1) := by

  let J := Injective.under L
  let ιL : L ⟶ J := Injective.ι L
  let Q := cokernel ιL
  let π : J ⟶ Q := cokernel.π ιL
  let Sx : ShortComplex (Sheaf (smallFppfTopology specInt) Ab.{1}) :=
    ShortComplex.mk ιL π (cokernel.condition ιL)
  have hS : Sx.ShortExact :=
    ShortComplex.ShortExact.mk' (Sx.exact_of_g_is_cokernel (cokernelIsCokernel ιL))
      (inferInstanceAs (Mono (Injective.ι L))) (inferInstanceAs (Epi (cokernel.π ιL)))
  have hT : IsTerminal (fppfTerminal specInt) := fppfTerminalIsTerminal specInt
  refine ⟨fun z₁ z₂ => ?_⟩
  suffices h0 : ∀ z : fppfCohomology specInt L 1, z = 0 by rw [h0 z₁, h0 z₂]
  intro z
  change Ext _ Sx.X₁ 1 at z

  have hz : z.comp (Ext.mk₀ Sx.f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS z hz (zero_add 1)

  obtain ⟨t, ht⟩ := exists_lift I hret L e ιL π (cokernel.condition ιL) hS
    (Sheaf.H.equiv₀ Q hT x₃)
  let x₂ : Sheaf.H J 0 := (Sheaf.H.equiv₀ J hT).symm t
  have hx₂ : Sheaf.H.map π 0 x₂ = x₃ := by
    show Sheaf.H.map π 0 ((Sheaf.H.equiv₀ J hT).symm t) = x₃
    rw [Sheaf.H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  calc z = x₃.comp hS.extClass (zero_add 1) := hx₃.symm
    _ = (Sheaf.H.map π 0 x₂).comp hS.extClass (zero_add 1) := by rw [hx₂]
    _ = (x₂.comp (Ext.mk₀ Sx.g) (add_zero 0)).comp hS.extClass (zero_add 1) := rfl
    _ = x₂.comp ((Ext.mk₀ Sx.g).comp hS.extClass (zero_add 1)) (zero_add 1) :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ _
    _ = 0 := by rw [hS.comp_extClass, Ext.comp_zero]

end CECH1DN
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

namespace CECH1DN

theorem natCard_ext_one_eq.{w', v, u} {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w'} C]
    (A : C)
    {S : ShortComplex C} (hS : S.ShortExact) (h2 : ∀ z : Ext A S.X₂ 1, z = 0) :
    Nat.card (Ext A S.X₁ 1) =
      Nat.card (Ext A S.X₃ 0 ⧸ ((Ext.mk₀ S.g).postcomp A (add_zero 0)).range) := by
  have hδ : Function.Surjective (hS.extClass.postcomp A (zero_add 1)) := fun z => by
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₁ A hS z (h2 _) (zero_add 1)
    exact ⟨x, hx⟩
  have hker : (hS.extClass.postcomp A (zero_add 1)).ker =
      ((Ext.mk₀ S.g).postcomp A (add_zero 0)).range := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ A hS x (zero_add 1) hx
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      show (y.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass (zero_add 1) = 0
      rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  rw [← hker]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hδ).toEquiv.symm

theorem natCard_H_one_eq_card_quotient.{w', w, v, u} {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {T : C} (hT : IsTerminal T) {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (h2 : ∀ z : Sheaf.H S.X₂ 1, z = 0) :
    Nat.card (Sheaf.H S.X₁ 1) =
      Nat.card (S.X₃.obj.obj (op T) ⧸ (S.g.hom.app (op T)).hom.range) := by
  refine (natCard_ext_one_eq _ hS h2).trans (Nat.card_congr
    (QuotientAddGroup.congr _ _ (Sheaf.H.equiv₀ S.X₃ hT) ?_).toEquiv)
  ext y
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, ⟨x₂, rfl⟩, rfl⟩
    refine ⟨Sheaf.H.equiv₀ S.X₂ hT x₂, ?_⟩
    rw [Sheaf.H.equiv₀_naturality hT S.g x₂]
    rfl
  · rintro ⟨t, rfl⟩
    refine ⟨(Ext.mk₀ S.g).postcomp _ (add_zero 0) ((Sheaf.H.equiv₀ S.X₂ hT).symm t),
      ⟨_, rfl⟩, ?_⟩
    show Sheaf.H.equiv₀ S.X₃ hT (Sheaf.H.map S.g 0 ((Sheaf.H.equiv₀ S.X₂ hT).symm t)) = _
    rw [← Sheaf.H.equiv₀_naturality hT S.g, AddEquiv.apply_symm_apply]

theorem natCard_H_congr.{w', w, v, u} {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (i : F ≅ G) (n : ℕ) :
    Nat.card (Sheaf.H F n) = Nat.card (Sheaf.H G n) :=
  Nat.card_congr
    { toFun := Sheaf.H.map i.hom n
      invFun := Sheaf.H.map i.inv n
      left_inv := fun x => by
        rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
      right_inv := fun x => by
        rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply] }

end CECH1DN
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

namespace CECH1DN

noncomputable def retractData_of_injective (I : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    [Injective I] (ι : Type) (S : ι → Scheme.{0}) (f : ∀ i, S i ⟶ specInt)
    (hS : Sieve.ofArrows S f ∈ Scheme.fppfTopology.{0} specInt) : RetractData I ι S where
  r V := (show (∀ i, I.obj.obj (op (S i ⨯ V))) →+ I.obj.obj (op V) from
    ((piProdRetract I ι S f hS).hom.app (op V)).hom)
  r_natural φ G := (NatTrans.naturality_apply (piProdRetract I ι S f hS).hom φ.op G).symm
  r_section V s :=
    congrArg (fun ψ : I ⟶ I => (ψ.hom.app (op V)).hom s) (toPiProd_retract I ι S f hS)

noncomputable abbrev resolution {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
    (X : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι X) (cokernel.π (Injective.ι X)) (cokernel.condition (Injective.ι X))

theorem shortExact_resolution {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
    (X : C) : (resolution X).ShortExact :=
  ShortComplex.ShortExact.mk' ((resolution X).exact_of_g_is_cokernel (cokernelIsCokernel _))
    (inferInstanceAs (Mono (Injective.ι X))) (inferInstanceAs (Epi (cokernel.π (Injective.ι X))))

theorem natCard_fppfH_one_eq (X : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    Nat.card (FppfCohomologyLES.FppfH X 1) =
      Nat.card ((resolution X).X₃.obj.obj (op specInt) ⧸
        ((resolution X).g.hom.app (op specInt)).hom.range) := by

  have h := natCard_H_one_eq_card_quotient.{1, 1, 0, 1} specZIsTerminal (shortExact_resolution X)
    (fun z => Ext.eq_zero_of_injective z)
  exact h

theorem natCard_fppfCohomology_res_one_eq (X : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    Nat.card (fppfCohomology specInt (Res.obj X) 1) =
      Nat.card ((resolution X).X₃.obj.obj (op specInt) ⧸
        ((resolution X).g.hom.app (op specInt)).hom.range) := by
  have hsub : Subsingleton (fppfCohomology specInt (Res.obj (Injective.under X)) 1) :=
    subsingleton_H_one (Injective.under X)
      (fun ι S f hS => retractData_of_injective (Injective.under X) ι S f hS)
      (Res.obj (Injective.under X)) (Iso.refl _)
  have h := natCard_H_one_eq_card_quotient.{1, 1, 0, 1} (fppfTerminalIsTerminal specInt)
    ((shortExact_resolution X).map_of_exact Res) (fun z => @Subsingleton.elim _ hsub z 0)
  exact h

theorem natCard_H_one_eq (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :
    Nat.card (fppfCohomology specInt L 1) = Nat.card (FppfCohomologyLES.FppfH X 1) :=
  have i : L ≅ Res.obj X :=
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := Sheaf.hom_ext e.hom_inv_id
      inv_hom_id := Sheaf.hom_ext e.inv_hom_id }
  (natCard_H_congr.{1, 1, 0, 1} i 1).trans
    ((natCard_fppfCohomology_res_one_eq X).trans (natCard_fppfH_one_eq X).symm)

end CECH1DN
p2m_reactivate "P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.CECH1DN"

theorem solution
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :
    Nat.card (fppfCohomology specInt L 1) = Nat.card (FppfCohomologyLES.FppfH X 1) := by
  exact CECH1DN.natCard_H_one_eq X L e

end S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
end P2MW
export P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction (solution)
