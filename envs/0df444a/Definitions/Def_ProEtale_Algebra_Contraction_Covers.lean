-- Prove2me | Definitions.Def_ProEtale_Algebra_Contraction_Covers
-- name    : ProEtale_Algebra_Contraction_Covers
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:35.030792+00:00
-- url     : https://prove2.me/theorems/0d9cc351-e4ba-45c7-acc3-b4e1266181fd
-- title:
--   Pro-contractions: iterated limits of finite fibre products of covers, and splitting of covers of the contraction
-- statement:
--   Let $\mathcal C$ be a category and let $P$, $Q$ be classes of morphisms of $\mathcal C$. The file is meant to be used with $\mathcal C = \mathsf{CRing}^{\mathrm{op}}$, to construct pro-étale "contractions" in the style of the Stacks project, with some differences.
--
--   **Precontraction.** Fix an object $X$ such that the category of $P$-morphisms $Y \to X$ is essentially small. Consider the directed set of finite families of (representatives of) such $P$-morphisms $Y_i \to X$, ordered by inclusion. To each finite family associate the wide fibre product $Y_1 \times_X \cdots \times_X Y_n \to X$, which gives a cofiltered diagram in $\mathcal C/X$. The **precontraction** of $X$ is the limit of this diagram in $\mathcal C/X$. By construction, every $P$-morphism $f\colon Y \to X$ receives a map over $X$ from the precontraction.
--
--   **Contraction.** Define a sequence of objects $X_0 = X$, with $X_{n+1}$ the precontraction of $X_n$ with respect to $P \cap Q$. This gives a tower $\cdots \to X_2 \to X_1 \to X_0 = X$ indexed by $\mathbb N^{\mathrm{op}}$. The **contraction** of $X$ is its limit
--   $$\operatorname{Contr}(X) = \lim_n X_n,$$
--   with projections $\pi_n\colon \operatorname{Contr}(X) \to X_n$ and base map $\pi_0\colon \operatorname{Contr}(X) \to X$.
--
--   The file also introduces auxiliary bookkeeping for a precoverage $K$: the preorder of $K$-covering presieves of $X$ (directed when $K$ is stable under unions) and the category of $0$-hypercovers of $X$ with isomorphism-indexed morphisms.
--
--   Principal results:
--
--   1. If $P$ contains identities and is stable under base change and composition, then the base map of any finite wide fibre product of $P$-morphisms into $X$ is in $P$.
--   2. If $P$ is multiplicative and stable under base change, the structure map of the precontraction is pro-$P$, i.e. a cofiltered limit of $P$-morphisms.
--   3. Assume $P$ and $Q$ are multiplicative and stable under base change, $P$ "pre-pro-spreads", $\mathcal C$ has pullbacks and is locally small, and the opposites of $P$-morphisms are finitely presentable in $\mathcal C^{\mathrm{op}}$. Then each projection $\pi_n$ is pro-(pro-$P$), and the base map $\operatorname{Contr}(X) \to X$ is pro-$P$.
--   4. If moreover $\operatorname{pro}(Q) = Q$, every projection $\pi_n$ lies in $Q$.
--   5. **Splitting.** Assume $\operatorname{pro}(Q) = Q$, and that $Q(g\circ f)$, $Q(f)$ and $P(g)$ together imply $Q(g)$. Assume also that $P$ and $Q$ are multiplicative and stable under base change, $P$ pre-pro-spreads, and $\mathcal C$ has pullbacks. Then every morphism $f\colon Y \to \operatorname{Contr}(X)$ lying in both $P$ and $Q$ has a section: there is $g\colon \operatorname{Contr}(X) \to Y$ with $f \circ g = \mathrm{id}$.
--
--   The contraction is used to produce, for a ring, a pro-étale extension over which every cover of a prescribed kind splits. This is the mechanism behind w-contractible covers in Bhatt–Scholze.
--
--   **Formalization Note** $\mathcal C$ has objects in `Type u` and morphisms in `Type v`, and the smallness of the categories of $P$-arrows is measured in universe `w` via `SmallModel`. The main declarations are `CategoryTheory.FiniteFamilies` and `FiniteFamilies.diag`, `MorphismProperty.precontraction`, `Precontraction.π`, `Contraction.Construction.obj`, `Contraction.Construction.diag`, `MorphismProperty.contraction`, `contraction.π` and `Contraction.base`. The auxiliary declarations are `SCov` and `Cov`, and the results are `MorphismProperty.of_isLimit_widePullbackCone`, `widePullbackBase`, `pro_precontraction_hom`, `pro_pro_contractionπ`, `pro_pro_contractionBase`, `prop_contractionπ`, `exists_comp_eq_id_contraction` and `pro_contractionBase`. The precontraction and the contraction use $P \cap Q$ (written `P ⊓ Q`) at every step. In `pro_pro_contractionπ` the outer `pro` uses universe-$0$ index categories (the tower is indexed by $\mathbb N^{\mathrm{op}}$). The section statement is written `g ≫ f = 𝟙 _` in diagrammatic order. Its finiteness and smallness hypotheses are the typeclass assumptions in force at that point of the file (essential smallness of `(P ⊓ Q).Over ⊤ X`, existence of the relevant limits, finite wide pullbacks).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/Contraction/Covers.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.Order.BooleanAlgebra.Set
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_FiniteLimits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_WidePullbacks
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Composition
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Another attempt at pro-contractions.

In this file we work in `CommRingCatᵒᵖ`, to be able to use the `0`-hypercover API.
The construction is very similar to the stacks project construction, but
has some subtle differences.
-/

universe s t w' w v u

namespace CategoryTheory

open Limits

namespace MorphismProperty

instance inst_AlgebraContractionCovers_L23 {C : Type*} [Category C] (P Q : MorphismProperty C) [P.ContainsIdentities] (X : C) :
    Nonempty (P.Over Q X) :=
  ⟨Over.mk _ _ (P.id_mem X)⟩

lemma of_isLimit_widePullbackCone {C : Type*} [Category C]
    [HasFiniteWidePullbacks C] {ι : Type*} [Finite ι] {X : C}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X}
    (P : MorphismProperty C)
    (s : WidePullbackCone f) (hs : IsLimit s) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] (hf : ∀ i, P (f i)) :
    P s.base := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e h =>
    let s' := s.reindex e
    have hs' : IsLimit s' := (WidePullbackCone.reindexIsLimitEquiv _ _).symm hs
    change P s'.base
    apply h _ hs'
    intro
    apply hf
  | h_empty =>
    have : IsIso s.base := by
      use WidePullbackCone.IsLimit.lift hs (𝟙 X) (fun i ↦ i.elim) (by simp)
      simp only [WidePullbackCone.IsLimit.lift_base, and_true]
      apply WidePullbackCone.IsLimit.hom_ext hs <;> simp
    exact P.of_isIso _
  | h_option ih =>
    let s' : WidePullbackCone (fun i ↦ f (some i)) :=
      limit.cone _
    let hs' : IsLimit s' := limit.isLimit _
    have H : P s'.base := by
      apply ih _ hs'
      intro
      apply hf
    have H' : P (s.π none) := by
      apply P.of_isPullback _ H
      · exact f none
      · exact WidePullbackCone.IsLimit.lift hs' s.base (fun i ↦ s.π (some i)) (by simp)
      · apply IsPullback.flip
        apply CategoryTheory.Limits.WidePullbackCone.isPullback_of_isCompl'
        · exact Option.some_injective _
        · rw [← Set.compl_range_some]
          exact IsCompl.symm isCompl_compl
        · exact hs
    rw [← s.condition none]
    exact P.comp_mem _ _ H' (hf none)

lemma widePullbackBase {C : Type*} [Category C] [HasFiniteWidePullbacks C]
    {ι : Type*} [Finite ι] {X : C}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X}
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) := by
  apply of_isLimit_widePullbackCone
  · exact limit.isLimit _
  · exact hf

end MorphismProperty

variable {C : Type u} [Category.{v} C] (K : Precoverage C)

instance inst_AlgebraContractionCovers_L83 [EssentiallySmall.{w} C] [Nonempty C] : Nonempty (SmallModel C) :=
  Nonempty.map (equivSmallModel C).functor.obj ‹_›

@[ext]
structure FiniteFamilies (C : Type*) [Category C] where
  set : Set C
  finite : set.Finite

instance inst_AlgebraContractionCovers_L91 : Preorder (FiniteFamilies C) where
  le U V := U.set ⊆ V.set
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

instance inst_AlgebraContractionCovers_L96 [Nonempty C] : Nonempty (FiniteFamilies C) :=
  ⟨⟨{Nonempty.some ‹_›}, by simp⟩⟩

instance inst_AlgebraContractionCovers_L99 : IsDirected (FiniteFamilies C) (· ≤ ·) where
  directed U V :=
    ⟨⟨U.set ∪ V.set, U.finite.union V.finite⟩, Set.subset_union_left, Set.subset_union_right⟩


namespace FiniteFamilies

variable {P : MorphismProperty C} {X : C} [EssentiallySmall.{w, v, max u v} (P.Over ⊤ X)]

def Index (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X))) : Type w := A.set

instance inst_AlgebraContractionCovers_L119 (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X))) : Finite A.Index :=
  A.finite

@[simps]
def indexHom {A B : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X))}
    (h : A ≤ B) (i : A.Index) : B.Index :=
  ⟨i.1, h i.2⟩

noncomputable def family (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))
    (i : A.Index) : C :=
  ((equivSmallModel _).inverse.obj i.1).left

noncomputable def hom (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))
    (i : A.Index) : A.family i ⟶ X :=
  ((equivSmallModel _).inverse.obj i.1).hom

lemma property_hom (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))
    (i : A.Index) : P (A.hom i) :=
  ((equivSmallModel _).inverse.obj i.1).prop

variable (P) in
noncomputable
def diag (X : C) [EssentiallySmall.{w} (P.Over ⊤ X)]
    [HasFiniteWidePullbacks C] :
    (FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))ᵒᵖ ⥤ Over X where
  obj U :=
    Over.mk (WidePullback.base <| U.unop.hom)
  map {U V} f :=
    Over.homMk <| WidePullback.lift (WidePullback.base _)
    (fun j ↦ WidePullback.π _ (indexHom (leOfHom f.unop) j))
    (by intro; exact WidePullback.π_arrow _ _)

end FiniteFamilies

structure SCov (K : Precoverage C) (X : C) where
  presieve : Presieve X
  mem : presieve ∈ K X

structure Cov (K : Precoverage C) (X : C) where
  toZeroHypercover : Precoverage.ZeroHypercover.{w} K X

variable {K : Precoverage C} {X : C}

instance inst_AlgebraContractionCovers_L162 : Preorder (SCov K X) where
  le U V := U.presieve ≤ V.presieve
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans


namespace Cov

@[ext]
structure Hom (U V : Cov K X) where
  σ : V.1.I₀ → U.1.I₀
  iso (i : V.1.I₀) : U.1.X (σ i) ⟶ V.1.X i
  [isIso (i : V.1.I₀) : IsIso (iso i)]
  w (i : V.1.I₀) : iso i ≫ V.1.f _ = U.1.f _ := by cat_disch

attribute [reassoc (attr := simp)] Hom.w
attribute [instance] Hom.isIso

@[simps]
def Hom.id (U : Cov K X) : U.Hom U where
  σ := _root_.id
  iso _ := 𝟙 _

@[simps]
def Hom.comp {U V W : Cov K X} (f : U.Hom V) (g : V.Hom W) : U.Hom W where
  σ i := f.σ (g.σ i)
  iso _ := f.iso _ ≫ g.iso _

open Limits

variable [∀ (X : C), ∀ (U : Cov K X), HasWidePullback _ U.1.X U.1.f]

variable (X P) in
@[simps! id_σ id_iso comp_σ comp_iso]
instance inst_AlgebraContractionCovers_L206 : Category (Cov K X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intros; ext <;> simp only [Hom.comp_σ, Hom.id_σ, id_eq, heq_eq_eq]; ext; simp
  comp_id := by
    intros; ext <;> simp only [Hom.comp_σ, Hom.id_σ, id_eq, heq_eq_eq]; ext; simp
  assoc := by
    intros; ext <;> simp only [Hom.comp_σ, heq_eq_eq]; ext; simp

instance inst_AlgebraContractionCovers_L219 [K.HasIsos] : Nonempty (Cov K X) :=
  ⟨⟨Precoverage.ZeroHypercover.singleton (𝟙 X) (K.mem_coverings_of_isIso _)⟩⟩


end Cov

namespace SCov


instance inst_AlgebraContractionCovers_L256 [K.HasIsos] : Nonempty (SCov K X) :=
  ⟨⟨.singleton (𝟙 X), K.mem_coverings_of_isIso _⟩⟩

instance inst_AlgebraContractionCovers_L259 [K.IsStableUnderSup] : IsDirected (SCov K X) (· ≤ ·) where
  directed U V :=
    ⟨⟨U.presieve ⊔ V.presieve, K.sup_mem_coverings U.2 V.2⟩,
      le_sup_left (a := U.1), le_sup_right (a := U.1)⟩


end SCov


namespace MorphismProperty

variable (P Q : MorphismProperty C)

variable (X : C)

section

variable [EssentiallySmall.{w} (P.Over ⊤ X)]

noncomputable
def precontraction (X : C) [EssentiallySmall.{w} (P.Over ⊤ X)]
    [HasFiniteWidePullbacks C] [HasLimit (FiniteFamilies.diag.{w} P X)] : Over X :=
  limit (FiniteFamilies.diag.{w} P X)

variable [HasFiniteWidePullbacks C] [HasLimit (FiniteFamilies.diag.{w} P X)]

noncomputable
def Precontraction.π {Y : C} (f : Y ⟶ X) (hf : P f) :
    P.precontraction X ⟶ CategoryTheory.Over.mk f :=
  letI U : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)) :=
    { set := { (equivSmallModel _).functor.obj (.mk _ _ hf) }
      finite := by simp }
  limit.π (FiniteFamilies.diag.{w} P X) ⟨U⟩ ≫
    CategoryTheory.Over.homMk (WidePullback.π U.hom ⟨_, rfl⟩)
      (WidePullback.π_arrow _ _) ≫
    (Functor.mapIso (Over.forget P ⊤ _)
      ((equivSmallModel <| P.Over ⊤ X).unitIso.app _)).inv

@[reassoc (attr := simp)]
lemma Precontraction.π_arrow {Y : C} (f : Y ⟶ X) (hf : P f) :
    (Precontraction.π P X f hf).left ≫ f = (P.precontraction X).hom := by
  simpa using (Precontraction.π P X f hf).w

lemma pro_precontraction_hom [P.IsMultiplicative] [P.IsStableUnderBaseChange] :
    pro.{w} P (precontraction.{w} P X).hom := by
  refine ⟨(FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))ᵒᵖ, inferInstance, inferInstance,
    FiniteFamilies.diag _ _ ⋙ CategoryTheory.Over.forget _, ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
  · exact { app _ := ((FiniteFamilies.diag _ _).obj _).hom }
  · exact Functor.whiskerRight
      (limit.cone <| FiniteFamilies.diag P X).π
      (CategoryTheory.Over.forget X)
  · exact isLimitOfPreserves (CategoryTheory.Over.forget X) (limit.isLimit _)
  · simp only [Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj]
    apply widePullbackBase
    intro i
    apply FiniteFamilies.property_hom
  · simp only [Functor.const_obj_obj, Functor.comp_obj, Over.forget_obj,
      limit.cone_x, Functor.whiskerRight_app, limit.cone_π, Over.forget_map, CategoryTheory.Over.w]
    rfl

end

variable [HasFiniteWidePullbacks C]
  [∀ X, EssentiallySmall.{w} ((P ⊓ Q).Over ⊤ X)]
  [∀ X : C, HasLimitsOfShape (FiniteFamilies (SmallModel.{w} ((P ⊓ Q).Over ⊤ X)))ᵒᵖ (Over X)]

namespace Contraction
namespace Construction

noncomputable
def obj : ℕ → C
  | 0 => X
  | n + 1 => (precontraction.{w} (P ⊓ Q) (obj n)).left

variable (K) in
noncomputable
def diag : ℕᵒᵖ ⥤ C := Functor.ofOpSequence (X := obj P Q X)
  fun _ ↦ ((P ⊓ Q).precontraction _).hom


end Construction
end Contraction

open Contraction

variable [HasLimitsOfShape ℕᵒᵖ C]

variable (K) in
noncomputable
def contraction : C :=
  limit (Contraction.Construction.diag P Q X)

variable (K) in
noncomputable
abbrev contraction.π (n : ℕ) : contraction P Q X ⟶ Construction.obj P Q X n :=
  limit.π _ _

variable (K) in
noncomputable def Contraction.base : contraction P Q X ⟶ X :=
  contraction.π _ _ _ 0


lemma pro_pro_contractionπ [PreProSpreads.{w} P] [Limits.HasPullbacks C] [LocallySmall.{w} C]
    (H : P.op ≤ isFinitelyPresentable.{w} Cᵒᵖ)
    [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    [Q.IsStableUnderBaseChange] [Q.IsMultiplicative] (X : C) (n : ℕ) :
    pro.{0} (pro.{w} P) (contraction.π P Q X n) := by
  haveI := IsMultiplicative.pro_of_le_isFinitelyPresentable H
  apply pro_coneπ
  · exact limit.isLimit _
  · intro k f
    apply ofOpSequence_map_of_isMultiplicative
    intro m
    apply pro_mono inf_le_left
    exact pro_precontraction_hom.{w} (P ⊓ Q) (Construction.obj P Q X m)

lemma pro_pro_contractionBase [PreProSpreads.{w} P] [Limits.HasPullbacks C] [LocallySmall.{w} C]
    (H : P.op ≤ isFinitelyPresentable.{w} Cᵒᵖ)
    [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    [Q.IsStableUnderBaseChange] [Q.IsMultiplicative] (X : C) :
    pro.{0} (pro.{w} P) (Contraction.base P Q X) :=
  pro_pro_contractionπ _ _ H _ 0

lemma prop_contractionπ
    (h : pro.{w} Q = Q)
    [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    [Q.IsStableUnderBaseChange] [Q.IsMultiplicative]
    (X : C) (n : ℕ) :
    Q (contraction.π P Q X n) := by
  have h' : pro.{0} Q = Q := by
    refine le_antisymm (le_trans ?_ h.le) ?_
    · apply pro_of_univLE
    · exact Q.le_pro
  nth_rw 1 [← h']
  apply pro_coneπ
  · exact limit.isLimit _
  · intro k f
    apply ofOpSequence_map_of_isMultiplicative
    intro m
    nth_rw 1 [← h]
    apply pro_mono inf_le_right
    exact pro_precontraction_hom.{w} (P ⊓ Q) (Construction.obj P Q X m)

lemma exists_comp_eq_id_contraction
    (h : pro.{w} Q = Q)
    (H : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      Q (f ≫ g) → Q f → P g → Q g)
    [PreProSpreads.{0} P] [Limits.HasPullbacks C]
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {Y : C} (f : Y ⟶ contraction.{w} P Q X) (hf : P f) (hf' : Q f) :
    ∃ (g : contraction.{w} P Q X ⟶ Y), g ≫ f = 𝟙 (contraction.{w} P Q X) := by
  obtain ⟨n, D', u, v, hv, hu⟩ :
      ∃ (n : ℕ) (D' : C) (u : D' ⟶ Construction.obj P Q X n) (v : Y ⟶ D'),
        IsPullback f v (contraction.π P Q X n) u ∧ P u := by
    obtain ⟨⟨n⟩, D', f', g, h, hf'⟩ := P.exists_isPullback_of_isCofiltered
      (J := ℕᵒᵖ) (D := Construction.diag P Q X)
      (limit.cone _) (limit.isLimit _) f hf
    use n, D', f', g, h
  have hu' : Q u := by
    apply H v
    · rw [← hv.w]
      apply Q.comp_mem _ _ hf'
      apply prop_contractionπ
      exact h
    · apply Q.of_isPullback hv
      apply prop_contractionπ
      apply h
    · exact hu
  let l : P.contraction Q X ⟶ Y := by
    refine hv.lift (𝟙 _) (contraction.π P Q X (n + 1) ≫
      (Precontraction.π (P ⊓ Q) _ u ⟨hu, hu'⟩).left) ?_
    have := limit.w (Construction.diag P Q X) ⟨homOfLE (Nat.le_succ n)⟩
    dsimp only [Nat.succ_eq_add_one, homOfLE_leOfHom] at this
    simp only [contraction.π, Category.id_comp, Category.assoc, Precontraction.π_arrow, ← this]
    simp [Construction.diag, Functor.ofOpSequence]
  use l
  simp [l]

lemma pro_contractionBase [LocallySmall.{w} C]
    (H : P.op ≤ isFinitelyPresentable.{w} Cᵒᵖ)
    [PreProSpreads.{w} P] [Limits.HasPullbacks C]
    [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    [Q.IsStableUnderBaseChange] [Q.IsMultiplicative] (X : C) :
    pro.{w} P (Contraction.base P Q X) := by
  rw [← pro_pro (P := P) H]
  apply pro_of_univLE.{0, w}
  exact P.pro_pro_contractionBase _ H _

end MorphismProperty

end CategoryTheory


