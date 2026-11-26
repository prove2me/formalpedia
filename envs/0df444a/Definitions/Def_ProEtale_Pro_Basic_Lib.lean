-- Prove2me | Definitions.Def_ProEtale_Pro_Basic_Lib
-- name    : ProEtale_Pro_Basic_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:59.267927+00:00
-- url     : https://prove2.me/theorems/5ec591b0-380e-4551-8b12-a10cdb91cf3b
-- title:
--   Relative limit presentations, the pro-category, and a sheaf criterion for finite relatively presentable 1-hypercovers
-- statement:
--   This file continues the published file *Pro/Basic* and develops conditions under which a presheaf on a category $D$ (think of a pro-category) is a sheaf, using presentations of objects of $D$ as limits of objects coming from $C$ via a functor $F : C \to D$.
--
--   **Definitions.**
--   - A *relative colimit presentation* of $X \in D$ over a category $J$ is a diagram $d : J \to C$ with a colimit cocone $F \circ d \Rightarrow X$. Dually, a *relative limit presentation* is a diagram $d : J \to C$ with a limit cone $X \Rightarrow F \circ d$. A morphism of presentations is a natural transformation of the diagrams. It induces a morphism between the presented objects, compatible with the (co)cone maps, and these morphisms compose. When $J$ is connected, every object $F(Y)$ and every morphism $F(f)$ has the constant ("self") presentation.
--   - $F$ is *ind* (`Functor.IsInd`) if every morphism $f : X \to Y$ of $D$ is induced by a morphism between relative colimit presentations of $X$ and $Y$ indexed by a small filtered category. The Yoneda embedding $C \to \mathrm{Ind}(C)$ is ind.
--   - The pro-category is $\mathrm{Pro}(C) := \mathrm{Ind}(C^{\mathrm{op}})^{\mathrm{op}}$.
--   - A *relative limit presentation of a pre-1-hypercover* $E$ of $X \in D$ consists of relative limit presentations, over the same $J$, of $X$, of every $X_i$ and of every $Y_k$. It also includes morphisms of presentations inducing the structure maps of $E$ and satisfying the cocycle condition. At each level $j \in J$ this gives a pre-1-hypercover of $d(j)$ in $C$.
--   - A pre-0- or pre-1-hypercover is *finite* if its index types are finite. $E$ is *relatively presentable* for a topology $J_C$ on $C$ if it has such a presentation over a small cofiltered category in which every level is a 1-hypercover for $J_C$: the level-0 sieve covers and all level-1 sieves cover. A presheaf $P$ *satisfies the sheaf condition for* $E$ if the multifork of $P$ along $E$ is a limit.
--
--   **Results.**
--   1. A general lemma (`IsLimit.ofPreservesLimitColim`) recognising a cone as a limit when a limit commutes with a colimit functor.
--   2. The (co)limit description of the multicospan of a presented hypercover: the levelwise multicospans form a colimit cocone, and the multifork of $P$ along $E$ is a limit provided each level satisfies the sheaf condition, $P$ sends the relevant cofiltered limits to colimits, and the colimit functor preserves the finite multicospan limit.
--   3. Finiteness instances: the walking multicospan of a finite hypercover is a finite category, and a finite pre-0-hypercover with pullbacks gives a finite pre-1-hypercover.
--   4. **Main criterion.** Let $P : D^{\mathrm{op}} \to \mathcal A$ be a presheaf such that $F^{\mathrm{op}} \circ P$ is a $J_C$-sheaf. Assume $P$ sends cofiltered limits of diagrams factoring through $F$ to colimits, which holds in particular if $P$ preserves filtered colimits. Assume $\mathcal A$ has filtered colimits and satisfies AB5. Then $P$ satisfies the sheaf condition for every finite, relatively presentable pre-1-hypercover.
--
--   These tools are used to show that presheaves on the affine pro-étale site defined by colimits from the affine étale site are sheaves.
--
--   **Formalization Note** Main declarations: `CategoryTheory.Limits.RelativeColimitPresentation`, `CategoryTheory.Limits.RelativeLimitPresentation` (with `.Hom`, `.Hom.map`, `.Hom.comp`, `.self`), `CategoryTheory.Functor.IsInd`, `CategoryTheory.Pro`, `PreOneHypercover.RelativeLimitPresentation` (with `preOneHypercover`, `oneHypercover`, `multicospan`, `cocone`, `isColimit`, `multifork`, `isLimit`), `PreZeroHypercover.Finite`, `PreOneHypercover.Finite`, `PreOneHypercover.IsRelativelyPresentable`, `PreOneHypercover.IsSheafFor` and `PreOneHypercover.IsSheafFor.of_preservesFilteredColimitsOfSize`. The hypothesis on $P$ is the class `Functor.PreservesRelativeFilteredColimits.{w} F P` from *Pro/Basic*. An instance derives it from `PreservesFilteredColimitsOfSize.{w, w} P`. The index categories of presentations are `w`-small and AB5 is `AB5OfSize.{w}`. Relative presentability is a `Prop`-valued existential.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Pro/Basic.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Pro_Basic of the same module.

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Definitions.Def_ProEtale_Pro_Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Sheafs in the pro category

In this file we develop conditions for when a presheaf on the pro-category
is a sheaf.
-/

universe s t w v₁ v₂ u₁ u₂

namespace CategoryTheory
open Limits

noncomputable
def Limits.IsLimit.ofPreservesLimitColim {J K C : Type*} [Category J] [Category K] [Category C]
    [HasColimitsOfShape J C]
    {D : J ⥤ K ⥤ C} [PreservesLimit D.flip colim]
    (c : Cone D.flip) (hc : IsLimit c)
    (d : Cocone D) (hd : IsColimit d)
    (f : Cocone c.pt) (hf : IsColimit f)
    (e : Cone d.pt)
    (iso : f.pt ≅ e.pt)
    (w : ∀ j k, (c.π.app k).app j ≫ (d.ι.app j).app k = f.ι.app j ≫ iso.hom ≫ e.π.app k) :
    IsLimit e :=
  let natiso : D.flip ⋙ colim ≅ d.pt :=
    (Limits.colimitIsoFlipCompColim _).symm ≪≫ (colimit.isColimit _).coconePointUniqueUpToIso hd
  let hc' : IsLimit (colim.mapCone c) := isLimitOfPreserves _ hc
  let t : (Cone.postcompose natiso.hom).obj (colim.mapCone c) ≅ e := by
    refine Cone.ext (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hf ≪≫ iso) ?_
    intro k
    apply colimit.hom_ext
    intro j
    simp only [Iso.trans_hom, Iso.symm_hom, Cone.postcompose_obj_pt, Functor.mapCone_pt,
      colim_obj, Cone.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj,
      Functor.comp_obj, Functor.mapCone_π_app, colim_map, colimitIsoFlipCompColim_inv_app,
      ι_colimMap_assoc, Functor.flip_obj_obj, Category.assoc,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc, natiso]
    erw [colimitObjIsoColimitCompEvaluation_ι_inv_assoc]
    simp [← NatTrans.comp_app, w]
  IsLimit.equivOfNatIsoOfIso natiso _ e t hc'

end CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

namespace Limits

structure RelativeColimitPresentation (J : Type w) [Category.{t} J] (F : C ⥤ D) (X : D) where
  diag : J ⥤ C
  ι : diag ⋙ F ⟶ (Functor.const J).obj X
  isColimit : IsColimit (Cocone.mk _ ι)

variable {J : Type w} [Category.{t} J] {F : C ⥤ D} {X : D}

namespace RelativeColimitPresentation

initialize_simps_projections RelativeColimitPresentation (-isColimit)

abbrev cocone (pres : RelativeColimitPresentation J F X) : Cocone (pres.diag ⋙ F) :=
  Cocone.mk _ pres.ι


/-- A morphism between relative colimit presentations is a natural transformation between
the diagrams. -/
@[ext]
structure Hom {X Y : D} (pres₁ : RelativeColimitPresentation J F X)
    (pres₂ : RelativeColimitPresentation J F Y) where
  natTrans : pres₁.diag ⟶ pres₂.diag

namespace Hom

variable {X Y Z : D} {pres₁ : RelativeColimitPresentation J F X}
    {pres₂ : RelativeColimitPresentation J F Y} {pres₃ : RelativeColimitPresentation J F Z}


def map (f : pres₁.Hom pres₂) : X ⟶ Y :=
  pres₁.isColimit.map pres₂.cocone (Functor.whiskerRight f.natTrans F)

variable (f : pres₁.Hom pres₂)

@[reassoc (attr := simp)]
lemma ι_map (j : J) : pres₁.ι.app j ≫ f.map = F.map (f.natTrans.app j) ≫ pres₂.ι.app j :=
  pres₁.isColimit.ι_map _ _ j

end Hom

end RelativeColimitPresentation

structure RelativeLimitPresentation (J : Type w) [Category.{t} J] (F : C ⥤ D) (X : D) where
  diag : J ⥤ C
  π : (Functor.const J).obj X ⟶ diag ⋙ F
  isLimit : IsLimit (Cone.mk _ π)

variable {J : Type w} [Category.{t} J] {F : C ⥤ D} {X : D}

namespace RelativeLimitPresentation

initialize_simps_projections RelativeLimitPresentation (-isLimit)

abbrev cone (pres : RelativeLimitPresentation J F X) : Cone (pres.diag ⋙ F) :=
  Cone.mk _ pres.π

@[reassoc (attr := simp)]
lemma isLimit_lift_π (pres : RelativeLimitPresentation J F X) (s : Cone (pres.diag ⋙ F)) (j : J) :
    pres.isLimit.lift s ≫ pres.π.app j = s.π.app j :=
  pres.isLimit.fac s j


@[simps]
noncomputable def self [IsConnected J] (X : C) : RelativeLimitPresentation J F (F.obj X) where
  diag := (Functor.const _).obj X
  π := (F.constComp _ X).inv
  isLimit := .equivOfNatIsoOfIso (F.constComp _ X).symm _
    (Cone.mk _ (F.constComp _ X).inv) (Cone.ext (Iso.refl _))
    (isLimitConstCone J (F.obj X))


/-- A morphism between relative colimit presentations is a natural transformation between
the diagrams. -/
@[ext]
structure Hom {X Y : D} (pres₁ : RelativeLimitPresentation J F X)
    (pres₂ : RelativeLimitPresentation J F Y) where
  natTrans : pres₁.diag ⟶ pres₂.diag

namespace Hom

variable {X Y Z : D} {pres₁ : RelativeLimitPresentation J F X}
    {pres₂ : RelativeLimitPresentation J F Y} {pres₃ : RelativeLimitPresentation J F Z}


@[simps]
def comp (f : pres₁.Hom pres₂) (g : pres₂.Hom pres₃) : pres₁.Hom pres₃ where
  natTrans := f.natTrans ≫ g.natTrans

def map (f : pres₁.Hom pres₂) : X ⟶ Y :=
  pres₂.isLimit.map pres₁.cone (Functor.whiskerRight f.natTrans F)

variable (f : pres₁.Hom pres₂)

@[reassoc (attr := simp)]
lemma map_π (j : J) : f.map ≫ pres₂.π.app j = pres₁.π.app j ≫ F.map (f.natTrans.app j) :=
  pres₂.isLimit.map_π _ _ j

@[simps]
def self [IsConnected J] {X Y : C} (f : X ⟶ Y) :
    (self (F := F) (J := J) X).Hom (self (J := J) Y) where
  natTrans.app j := f

@[simp]
lemma self_map [IsConnected J] {X Y : C} (f : X ⟶ Y) :
    (self (J := J) (F := F) f).map = F.map f := by
  refine (RelativeLimitPresentation.self (J := J) Y).isLimit.hom_ext fun j ↦ ?_
  rw [map_π]
  simp

end Hom

end RelativeLimitPresentation

end Limits

open Limits Opposite

class Functor.IsInd (F : C ⥤ D) : Prop where
  hom_exists {X Y : D} (f : X ⟶ Y) : ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres₁ : RelativeColimitPresentation J F X) (pres₂ : RelativeColimitPresentation J F Y)
    (t : pres₁.Hom pres₂), f = t.map


instance inst_ProBasic_L233 : Functor.IsInd.{v₁} (Ind.yoneda (C := C)) where
  hom_exists {X Y} f := by
    obtain ⟨J, _, _, D₁, D₂, φ, ⟨e⟩⟩ := Ind.exists_nonempty_arrow_mk_iso_ind_lim (f := f)
    use J, inferInstance, inferInstance
    let pres₁ : RelativeColimitPresentation J Ind.yoneda X :=
    { diag := D₁
      ι := (colimit.cocone (D₁ ⋙ Ind.yoneda)).ι ≫
        (Functor.const J).map (Arrow.leftFunc.mapIso e).inv
      isColimit := (colimit.isColimit _).extendIso _ }
    let pres₂ : RelativeColimitPresentation J Ind.yoneda Y :=
    { diag := D₂
      ι := (colimit.cocone (D₂ ⋙ Ind.yoneda)).ι ≫
        (Functor.const J).map (Arrow.rightFunc.mapIso e).inv
      isColimit := (colimit.isColimit _).extendIso _ }
    refine ⟨pres₁, pres₂, ⟨φ⟩, ?_⟩
    apply pres₁.isColimit.hom_ext
    intro j
    simp only [Functor.comp_obj, Functor.const_obj_obj, RelativeColimitPresentation.Hom.ι_map]
    simp [pres₁, pres₂, Ind.lim]


/-- The pro-category of `C` is `(Ind Cᵒᵖ)ᵒᵖ`. -/
def Pro (C : Type*) [Category C] := (Ind Cᵒᵖ)ᵒᵖ

noncomputable instance inst_ProBasic_L261 : Category (Pro C) :=
  inferInstanceAs <| Category (Ind Cᵒᵖ)ᵒᵖ


structure PreOneHypercover.RelativeLimitPresentation (J : Type*) [Category J]
    {X : D} (F : C ⥤ D) (E : PreOneHypercover.{w} X) where
  pres : Limits.RelativeLimitPresentation J F X
  pres₀ : ∀ i : E.I₀, Limits.RelativeLimitPresentation J F (E.X i)
  pres₁ : ∀ {i j} (k : E.I₁ i j), Limits.RelativeLimitPresentation J F (E.Y k)
  f : ∀ i, (pres₀ i).Hom pres
  p₁ : ∀ {i j} (k : E.I₁ i j), (pres₁ k).Hom (pres₀ i)
  p₂ : ∀ {i j} (k : E.I₁ i j), (pres₁ k).Hom (pres₀ j)
  hf : ∀ i, (f i).map = E.f i
  hp₁ : ∀ {i j} (k : E.I₁ i j), (p₁ k).map = E.p₁ k
  hp₂ : ∀ {i j} (k : E.I₁ i j), (p₂ k).map = E.p₂ k
  w : ∀ {i j} (k : E.I₁ i j), (p₁ k).comp (f i) = (p₂ k).comp (f j)

@[simps]
def PreOneHypercover.RelativeLimitPresentation.preOneHypercover {J : Type*} [Category J]
    {X : D} {F : C ⥤ D} {E : PreOneHypercover.{w} X}
    (pres : E.RelativeLimitPresentation J F) (j : J) :
    PreOneHypercover (pres.pres.diag.obj j) where
  I₀ := E.I₀
  X i := (pres.pres₀ i).diag.obj j
  f i := (pres.f i).natTrans.app j
  I₁ := E.I₁
  Y _ _ k := (pres.pres₁ k).diag.obj j
  p₁ _ _ k := (pres.p₁ k).natTrans.app j
  p₂ _ _ k := (pres.p₂ k).natTrans.app j
  w _ _ k := by simpa using congr($(pres.w k).natTrans.app j)

variable {J : Type*} [Category J] {X : D} {F : C ⥤ D} {E : PreOneHypercover.{w} X}
  {K : GrothendieckTopology C}

def PreOneHypercover.RelativeLimitPresentation.oneHypercover
    (pres : E.RelativeLimitPresentation J F) (j : J)
    (mem₀ : (pres.preOneHypercover j).sieve₀ ∈ K _)
    (mem₁ : ∀ {a b : E.I₀} {W : C} (p₁ : W ⟶ (pres.preOneHypercover j).X a)
        (p₂ : W ⟶ (pres.preOneHypercover j).X b),
        p₁ ≫ (pres.preOneHypercover j).f a = p₂ ≫ (pres.preOneHypercover j).f b →
        (pres.preOneHypercover j).sieve₁ p₁ p₂ ∈ K W) :
    K.OneHypercover (pres.pres.diag.obj j) where
  __ := pres.preOneHypercover j
  mem₀ := mem₀
  mem₁ _ _ _ := mem₁

variable {A : Type*} [Category A]

@[simps]
def PreOneHypercover.RelativeLimitPresentation.multicospan (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A) :
    Jᵒᵖ ⥤ (WalkingMulticospan E.multicospanShape ⥤ A) where
  obj j := ((pres.preOneHypercover j.unop).multicospanIndex (F.op ⋙ P)).multicospan
  map {i j} f :=
    { app
        | .left k => P.map (F.map <| (pres.pres₀ k).diag.map f.unop).op
        | .right k => P.map (F.map <| (pres.pres₁ k.2).diag.map f.unop).op
      naturality k l f := by
        rcases f
        · simp
        · simp [← Functor.map_comp, ← op_comp]
        · simp [← Functor.map_comp, ← op_comp] }

@[simps]
def PreOneHypercover.RelativeLimitPresentation.cocone (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A) :
    Cocone (pres.multicospan P) where
  pt := (E.multicospanIndex P).multicospan
  ι.app j :=
    { app
        | .left k => P.map ((pres.pres₀ k).π.app j.unop).op
        | .right k => P.map ((pres.pres₁ k.2).π.app j.unop).op
      naturality k l f := by
        match f with
        | .id _ => simp
        | .fst k =>
          suffices h : P.map (F.map ((pres.p₁ k.snd).natTrans.app (unop j))).op ≫
              P.map ((pres.pres₁ k.snd).π.app (unop j)).op =
                P.map ((pres.pres₀ k.fst.1).π.app (unop j)).op ≫ P.map (E.p₁ k.snd).op by
            simpa
          simp_rw [← Functor.map_comp, ← op_comp]
          rw [← pres.hp₁ k.2]
          simp
        | .snd k =>
          suffices h : P.map (F.map ((pres.p₂ k.snd).natTrans.app (unop j))).op ≫
              P.map ((pres.pres₁ k.snd).π.app (unop j)).op =
                P.map ((pres.pres₀ k.fst.2).π.app (unop j)).op ≫ P.map (E.p₂ k.snd).op by
            simpa
          simp_rw [← Functor.map_comp, ← op_comp]
          rw [← pres.hp₂ k.2]
          simp
    }
  ι.naturality i j f := by
    ext k
    match k with
    | .left k =>
        simp only [multicospan_obj, MulticospanIndex.multicospan_obj_left, MulticospanIndex.multicospan_obj_right, multicospanShape_L,
          preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, Functor.comp_obj,
          Functor.op_obj, multicospanShape_R, multicospanIndex_right, preOneHypercover_I₁,
          preOneHypercover_Y, Functor.const_obj_obj, NatTrans.comp_app, multicospan_map_app,
          ← Functor.map_comp, ← op_comp, Functor.const_obj_map, Category.comp_id]
        congr 2
        simpa using ((pres.pres₀ k).π.naturality f.unop).symm
    | .right k =>
        simp only [multicospan_obj, MulticospanIndex.multicospan_obj_left, MulticospanIndex.multicospan_obj_right, multicospanShape_L,
          preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, Functor.comp_obj,
          Functor.op_obj, multicospanShape_R, multicospanIndex_right, preOneHypercover_I₁,
          preOneHypercover_Y, Functor.const_obj_obj, NatTrans.comp_app, multicospan_map_app,
          ← Functor.map_comp, ← op_comp, Functor.const_obj_map, Category.comp_id]
        congr 2
        simpa using ((pres.pres₁ k.2).π.naturality f.unop).symm

noncomputable
def PreOneHypercover.RelativeLimitPresentation.isColimit (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A)
    (h₀ : ∀ i, IsColimit (P.mapCocone (pres.pres₀ i).cone.op))
    (h₁ : ∀ {i j : E.I₀} (k : E.I₁ i j), IsColimit (P.mapCocone (pres.pres₁ k).cone.op)) :
    IsColimit (pres.cocone P) :=
  evaluationJointlyReflectsColimits _ fun k ↦ match k with
    | .left k => h₀ k
    | .right k => h₁ k.2

@[simps]
def PreOneHypercover.RelativeLimitPresentation.multifork (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A) :
    Cone (pres.multicospan P).flip where
  pt := pres.pres.diag.op ⋙ F.op ⋙ P
  π.app
    | .left k =>
      Functor.whiskerRight (NatTrans.op (pres.f k).natTrans) _
    | .right k =>
      Functor.whiskerRight (NatTrans.op <| (pres.p₁ k.2).natTrans ≫ (pres.f k.1.1).natTrans) _
  π.naturality k l f := by
    rcases f
    · simp
    · ext; simp
    · ext
      simp only [multicospanShape_snd, Functor.const_obj_obj, Functor.comp_obj, Functor.op_obj,
        Functor.flip_obj_obj, multicospan_obj, MulticospanIndex.multicospan_obj_left, MulticospanIndex.multicospan_obj_right, multicospanShape_L,
        preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, multicospanShape_R,
        multicospanIndex_right, preOneHypercover_I₁, preOneHypercover_Y, Functor.const_obj_map,
        NatTrans.op_comp, Functor.whiskerRight_comp, Category.id_comp, NatTrans.comp_app,
        Functor.whiskerRight_app, NatTrans.op_app, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op, Functor.flip_map_app, MulticospanIndex.multicospan_map_fst, MulticospanIndex.multicospan_map_snd,
        multicospanIndex_snd, preOneHypercover_p₂, ← Functor.map_comp, ← op_comp]
      congr 3
      simpa using congr($(pres.w _).natTrans.app _)

noncomputable
def PreOneHypercover.RelativeLimitPresentation.isLimit (P : Dᵒᵖ ⥤ A)
    [HasColimitsOfShape Jᵒᵖ A]
    [PreservesLimitsOfShape (WalkingMulticospan E.multicospanShape) (colim : (Jᵒᵖ ⥤ A) ⥤ _)]
    (pres : E.RelativeLimitPresentation J F)
    (hX : IsColimit (P.mapCocone pres.pres.cone.op))
    (h₀ : ∀ i, IsColimit (P.mapCocone (pres.pres₀ i).cone.op))
    (h₁ : ∀ {i j : E.I₀} (k : E.I₁ i j), IsColimit (P.mapCocone (pres.pres₁ k).cone.op))
    (h : ∀ j, IsLimit <| (pres.preOneHypercover j).multifork (F.op ⋙ P)) :
    IsLimit (E.multifork P) := by
  refine IsLimit.ofPreservesLimitColim (pres.multifork P) ?_ (pres.cocone P)
      (pres.isColimit P h₀ h₁)
      (P.mapCocone pres.pres.cone.op) hX _ (.refl _) ?_
  · refine evaluationJointlyReflectsLimits _ fun j ↦ ?_
    refine IsLimit.ofIsoLimit (h j.1) (Cone.ext (Iso.refl _) ?_)
    intro l
    simp only [Functor.const_obj_obj, MulticospanIndex.multicospan_obj_left, MulticospanIndex.multicospan_obj_right, multicospanShape_L,
      preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, Functor.comp_obj,
      Functor.op_obj, multicospanShape_R, multicospanIndex_right, preOneHypercover_I₁,
      preOneHypercover_Y, Functor.mapCone_pt, multifork_pt, evaluation_obj_obj, Iso.refl_hom,
      Functor.mapCone_π_app, multifork_π_app, NatTrans.op_comp, Functor.whiskerRight_comp,
      evaluation_obj_map, Category.id_comp]
    cases l <;> rfl
  · intro j k
    match k with
    | .left k =>
      suffices h : (pres.pres₀ k).π.app (unop j) ≫ F.map ((pres.f k).natTrans.app (unop j)) =
          E.f k ≫ pres.pres.π.app (unop j) by
        simp [h, ← Functor.map_comp, ← op_comp, PreOneHypercover.multifork]
      rw [← pres.hf]
      simp
    | .right k =>
      suffices h : (pres.pres₁ k.snd).π.app (unop j) ≫
          F.map ((pres.p₁ k.snd).natTrans.app (unop j) ≫ (pres.f k.fst.1).natTrans.app (unop j)) =
          E.p₁ k.snd ≫ E.f k.fst.1 ≫ pres.pres.π.app (unop j) by
        simp [h, ← Functor.map_comp, ← op_comp, PreOneHypercover.multifork]
      rw [← pres.hf, ← pres.hp₁]
      simp

section

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

protected class PreZeroHypercover.Finite {X : C} (E : PreZeroHypercover.{w} X) : Prop where
  finite₀ : _root_.Finite E.I₀ := by infer_instance

protected class PreOneHypercover.Finite {X : C} (E : PreOneHypercover.{w} X) : Prop extends
    E.toPreZeroHypercover.Finite where
  finite₁ : ∀ i j, _root_.Finite (E.I₁ i j) := by infer_instance

attribute [instance] PreZeroHypercover.Finite.finite₀ PreOneHypercover.Finite.finite₁

instance inst_ProBasic_L475 {X : C} (E : PreZeroHypercover.{w} X) [E.HasPullbacks] [E.Finite] :
    E.toPreOneHypercover.Finite where
  finite₀ := by dsimp; infer_instance
  finite₁ i j := by dsimp; infer_instance

instance inst_ProBasic_L480 {X : C} (E : PreOneHypercover.{w} X) [E.Finite] : Finite E.I₁' := by
  dsimp [PreOneHypercover.I₁']
  infer_instance

instance inst_ProBasic_L484 (s : MulticospanShape) [Finite s.L] [Finite s.R] : Finite (WalkingMulticospan s) := by
  cases nonempty_fintype s.L
  cases nonempty_fintype s.R
  infer_instance

instance inst_ProBasic_L489 {J : MulticospanShape} [Finite J.L] [Finite J.R] (a b : WalkingMulticospan J) :
    Finite (a ⟶ b) := by
  let S := Σ (a : WalkingMulticospan J) (b : WalkingMulticospan J), a ⟶ b
  let proj : (J.L ⊕ J.R) ⊕ J.R ⊕ J.R → S
    | .inl (.inl l) => ⟨_, _, .id (.left l)⟩
    | .inl (.inr r) => ⟨_, _, .id (.right r)⟩
    | .inr (.inl r) => ⟨_, _, .fst r⟩
    | .inr (.inr r) => ⟨_, _, .snd r⟩
  have : proj.Surjective := by
    intro ⟨a, b, f⟩
    rcases f
    · cases a
      · exact ⟨.inl (.inl _), rfl⟩
      · exact ⟨.inl (.inr _), rfl⟩
    · exact ⟨.inr (.inl _), rfl⟩
    · exact ⟨.inr (.inr _), rfl⟩
  have := Finite.of_surjective _ this
  let emb : (a ⟶ b) → S := fun f ↦ ⟨_, _, f⟩
  refine .of_injective emb fun f g hfg ↦ by cases hfg; rfl

noncomputable
instance inst_ProBasic_L509 {X : C} (E : PreOneHypercover.{w} X) [E.Finite] :
    FinCategory (WalkingMulticospan E.multicospanShape) := by
  haveI : Finite E.multicospanShape.L := by dsimp; infer_instance
  haveI : Finite E.multicospanShape.R := by dsimp; infer_instance
  letI := Fintype.ofFinite E.multicospanShape.L
  letI := Fintype.ofFinite E.multicospanShape.R
  classical
  infer_instance

variable (F A) in
def PreOneHypercover.IsRelativelyPresentable
    {X : D} (E : PreOneHypercover X) : Prop :=
  ∃ (I : Type w) (_ : SmallCategory I) (_ : IsCofiltered I)
    (pres : E.RelativeLimitPresentation I F),
      ∀ j, (pres.preOneHypercover j).sieve₀ ∈ J _ ∧
      ∀ {a b : E.I₀} {W : C} (p₁ : W ⟶ (pres.preOneHypercover j).X a)
        (p₂ : W ⟶ (pres.preOneHypercover j).X b),
        p₁ ≫ (pres.preOneHypercover j).f a = p₂ ≫ (pres.preOneHypercover j).f b →
        (pres.preOneHypercover j).sieve₁ p₁ p₂ ∈ J W


/-- A presheaf `P : Dᵒᵖ ⥤ A` satisfies the sheaf condition for a pre-`1`-hypercover `E` if the
associated multifork is limiting. -/
abbrev PreOneHypercover.IsSheafFor {X : D} (E : PreOneHypercover.{w} X) (P : Dᵒᵖ ⥤ A) :
    Prop :=
  Nonempty (IsLimit <| E.multifork P)


instance (priority := 100) Functor.preservesRelativeFilteredColimits_of_preservesFilteredColimits
    (P : Dᵒᵖ ⥤ A) [PreservesFilteredColimitsOfSize.{w, w} P] :
    Functor.PreservesRelativeFilteredColimits.{w} F P where
  nonempty_isColimit _ hc := ⟨isColimitOfPreserves P hc.op⟩

lemma PreOneHypercover.IsSheafFor.of_preservesFilteredColimitsOfSize (P : Dᵒᵖ ⥤ A)
    (h : Presheaf.IsSheaf J (F.op ⋙ P))
    [Functor.PreservesRelativeFilteredColimits.{w} F P] [HasFilteredColimitsOfSize.{w, w} A]
    [AB5OfSize.{w} A]
    {X : D} (E : PreOneHypercover.{t} X) (h : IsRelativelyPresentable.{w} F J E) [E.Finite] :
    E.IsSheafFor P := by
  obtain ⟨I, _, _, pres, mem⟩ := h
  constructor
  apply pres.isLimit (P := P)
    (Functor.PreservesRelativeFilteredColimits.nonempty_isColimit
      pres.pres.cone pres.pres.isLimit).some
    (fun i ↦ (Functor.PreservesRelativeFilteredColimits.nonempty_isColimit
      (pres.pres₀ i).cone (pres.pres₀ i).isLimit).some)
    (fun {i j} k ↦ (Functor.PreservesRelativeFilteredColimits.nonempty_isColimit
      (pres.pres₁ k).cone (pres.pres₁ k).isLimit).some)
  intro j
  let E' : J.OneHypercover (pres.pres.diag.obj j) := pres.oneHypercover j (mem j).1 (mem j).2
  exact E'.isLimitMultifork ⟨_, h⟩


end

end CategoryTheory


