-- Prove2me | Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_AffineTransitionLimit
-- name    : ProEtale_Mathlib_AlgebraicGeometry_AffineTransitionLimit
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:00.927931+00:00
-- url     : https://prove2.me/theorems/ac3fc90b-71e6-4c54-88a9-02b502f221a3
-- title:
--   Morphisms between cofiltered limits as limits of levelwise maps, and images of deep transition maps
-- statement:
--   **Category theory.** Let $I, I'$ be cofiltered categories, $D : I \to \mathcal C$ and $D' : I' \to \mathcal C$ diagrams with limit cones $c, c'$, and $f : \lim D \to \lim D'$. Assume that for every $i' \in I'$ the functor $\operatorname{Hom}(-, D'(i'))$ preserves the colimit of $D^{\mathrm{op}}$, i.e. $\operatorname{Hom}(\lim D, D'(i')) = \operatorname{colim}_i \operatorname{Hom}(D(i), D'(i'))$. The auxiliary category has objects $(i, i', h : D(i) \to D'(i'))$ with $c_i \circ h = f \circ c'_{i'}$ (diagrammatic order); it is shown to be cofiltered and both projections to $I$ and $I'$ are initial. Consequently:
--
--   1. There exist a cofiltered category $\mathcal J$, initial functors $G : \mathcal J \to I$ and $G' : \mathcal J \to I'$, and a natural transformation $g : D\circ G \to D'\circ G'$ such that $f$ is the morphism of limits induced by $g$.
--
--   **Schemes.** Let $I$ be cofiltered and $D, D' : I \to \mathrm{Sch}$ with limit cones $c, c'$.
--
--   2. Suppose $D'$ has affine transition maps and quasi-compact, quasi-separated terms, $f : D \to D'$ is a natural transformation, $i \in I$, the image of $f_i$ is open (e.g. $f_i$ étale), and the induced map $\lim D \to \lim D'$ is surjective. Then there is $k \to i$ such that
--   $$\operatorname{im}\big(D'(k) \to D'(i)\big) \subseteq \operatorname{im}(f_i).$$
--   A docstring explains why the naive statement "$f_k$ is surjective for $k$ deep enough" fails in general.
--   3. Suppose $D$ has affine transition maps and qcqs terms, with structure maps $t_i : D(i) \to S$ locally of finite presentation; $D' : I' \to \mathrm{Sch}$ ($I'$ small cofiltered) has structure maps $t'_{i'} : D'(i') \to S$ locally of finite presentation; and $f : \lim D \to \lim D'$ is a morphism over $S$. Then there are a small cofiltered $\mathcal J$, initial $G : \mathcal J \to I$, $G' : \mathcal J \to I'$ and $g : D\circ G \to D'\circ G'$ over $S$ such that $f$ is induced by $g$.
--
--   The file also records that over and under categories are nonempty. These results let one present morphisms of affine pro-étale objects as limits of morphisms of étale objects.
--
--   **Formalization Note** Main declarations: `CategoryTheory.ConstructLimitMap.Aux` (with `isCofiltered`, `initial_projLeft`, `initial_projRight`, `map`), `CategoryTheory.Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda`, `AlgebraicGeometry.exists_range_map_subset_range_app_of_surjective_isLimitMap`, `AlgebraicGeometry.exists_eq_isLimitMap_whisker`. In item 1 the index category $\mathcal J$ lies in `Type (max u₂ u₃ v₁)`; in item 3 it is a `SmallCategory` in `Type u`. The induced map is expressed with `IsLimit.map` after whiskering the cones along the initial functors. In item 2 the surjectivity hypothesis is `Surjective` for scheme morphisms, and the cone on $D$ need not be a limit.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: EGA4.3, Thm. 8.10.5 (vi). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.CategoryTheory.Presentable.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe t u
universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory


variable {C : Type u₁} [Category.{v₁} C]
  {I : Type u₂} {I' : Type u₃} [Category.{v₂} I]
  [Category.{v₃} I']
  {D : I ⥤ C} {D' : I' ⥤ C}
  {c : Cone D} {c' : Cone D'}
  (hc : IsLimit c) (hc' : IsLimit c')
  (f : c.pt ⟶ c'.pt)

namespace ConstructLimitMap

def Aux : ObjectProperty (Comma D D') :=
  fun A ↦ c.π.app A.left ≫ A.hom = f ≫ c'.π.app A.right

@[reassoc]
lemma Aux.w (A : (Aux f).FullSubcategory) :
    c.π.app A.obj.left ≫ A.obj.hom = f ≫ c'.π.app A.obj.right :=
  A.property

@[simps!]
def Aux.projLeft : (Aux f).FullSubcategory ⥤ I :=
  (Aux f).ι ⋙ Comma.fst _ _

@[simps!]
def Aux.projRight : (Aux f).FullSubcategory ⥤ I' :=
  (Aux f).ι ⋙ Comma.snd _ _

variable
  [IsCofiltered I] [IsCofiltered I']
  [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))]

/-! TODO: The following three proofs are very similar, unify them. -/

include hc in
lemma isCofiltered : IsCofiltered (Aux f).FullSubcategory := by
  obtain ⟨i'⟩ := IsCofiltered.nonempty (C := I')
  obtain ⟨a, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
  have : Nonempty (Aux f).FullSubcategory := ⟨⟨a, i', p⟩, hp⟩
  have : IsCofilteredOrEmpty (Aux f).FullSubcategory := by
    refine ⟨?_, ?_⟩
    · intro j₁ j₂
      let l' := IsCofiltered.min j₁.obj.right j₂.obj.right
      let lp₁ := IsCofiltered.minToLeft j₁.obj.right j₂.obj.right
      let lp₂ := IsCofiltered.minToRight j₁.obj.right j₂.obj.right
      obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc
        (f ≫ c'.π.app (IsCofiltered.min j₁.obj.right j₂.obj.right))
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
        (q ≫ D'.map lp₁) j₁.obj.hom (by simp [reassoc_of% hq, Aux.w])
      obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_preservesColimit_yoneda hc
        (q ≫ D'.map lp₂) j₂.obj.hom (by simp [reassoc_of% hq, Aux.w])
      obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
      refine ⟨⟨⟨i₀, l', D.map il₀ ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq, l']⟩, ?_, ?_, trivial⟩
      · exact ObjectProperty.homMk ⟨il₀ ≫ va₂, lp₁, by simp [heqa]⟩
      · exact ObjectProperty.homMk ⟨ir₀ ≫ vb₂, lp₂, by
          dsimp
          rw [← Functor.map_comp_assoc, heq]
          simp [heqb]⟩
    · intro j₁ j₂ u v
      obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc
        (f ≫ c'.π.app (IsCofiltered.eq u.hom.right v.hom.right))
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
        (q ≫ D'.map (IsCofiltered.eqHom _ _)) j₁.obj.hom (by simp [reassoc_of% hq, Aux.w])
      obtain ⟨i₀, α, β, hα, hβ⟩ := IsCofiltered.bowtie u.hom.left (va₂ ≫ v.hom.left) (𝟙 _) va₂
      refine ⟨⟨⟨i₀, IsCofiltered.eq u.hom.right v.hom.right,
          D.map β ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq]⟩, ?_, ?_⟩
      · refine ObjectProperty.homMk
          ⟨β ≫ va₂, IsCofiltered.eqHom _ _, ?_⟩
        simp [heqa]
      · ext
        · simp only [Category.comp_id] at hβ
          subst hβ
          simpa using hα
        · simp [← IsCofiltered.eq_condition]
  constructor

include hc in
lemma initial_projLeft : (Aux.projLeft f).Initial := by
  constructor
  intro i
  have : Nonempty (CostructuredArrow (Aux.projLeft f) i) := by
    obtain ⟨i'⟩ := IsCofiltered.nonempty (C := I')
    obtain ⟨a, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
    exact ⟨CostructuredArrow.mk
      (Y := ⟨⟨IsCofiltered.min i a, i', D.map (IsCofiltered.minToRight _ _) ≫ p⟩, by
        simp [Aux, hp]⟩)
      (IsCofiltered.minToLeft _ _)⟩
  refine zigzag_isConnected fun j₁ j₂ ↦ ?_
  obtain ⟨i₁, l, r, hlr⟩ := IsCofiltered.cospan j₁.hom j₂.hom
  obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc
    (f ≫ c'.π.app (IsCofiltered.min j₁.left.obj.right j₂.left.obj.right))
  let l' := IsCofiltered.min j₁.left.obj.right j₂.left.obj.right
  let lp₁ := IsCofiltered.minToLeft j₁.left.obj.right j₂.left.obj.right
  let lp₂ := IsCofiltered.minToRight j₁.left.obj.right j₂.left.obj.right
  obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₁) j₁.left.obj.hom (by simp [reassoc_of% hq, Aux.w])
  obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₂) j₂.left.obj.hom (by simp [reassoc_of% hq, Aux.w])
  obtain ⟨i₀, il₀, ir₀, heq₁, heq₂⟩ := IsCofiltered.bowtie va₁ vb₁ (va₂ ≫ j₁.hom) (vb₂ ≫ j₂.hom)
  let middle : CostructuredArrow (Aux.projLeft f) i :=
    CostructuredArrow.mk (Y := ⟨⟨i₀, l', D.map il₀ ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq, l']⟩)
      (il₀ ≫ va₂ ≫ j₁.hom)
  trans middle
  · refine .of_inv ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (il₀ ≫ va₂) lp₁ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc]
        simp only [Functor.map_comp, Category.assoc]
        rw [heqa]
    · simp [middle]
  · refine .of_hom ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (ir₀ ≫ vb₂) lp₂ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc, heq₁]
        simp [heqb]
    · simp [middle, heq₂]

include hc in
lemma initial_projRight : (Aux.projRight f).Initial := by
  refine ⟨fun i' ↦ ?_⟩
  have : Nonempty (CostructuredArrow (Aux.projRight f) i') := by
    obtain ⟨i, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
    exact ⟨CostructuredArrow.mk (Y := ⟨Comma.mk i i' p, hp⟩) <| 𝟙 _⟩
  refine zigzag_isConnected fun j₁ j₂ ↦ ?_
  obtain ⟨l', lp₁, lp₂, hlp⟩ := IsCofiltered.cospan j₁.hom j₂.hom
  obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app l')
  obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₁) j₁.left.obj.hom (by simp [reassoc_of% hq, Aux.w] <;> rfl)
  obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₂) j₂.left.obj.hom (by simp [reassoc_of% hq, Aux.w] <;> rfl)
  obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
  let middle : CostructuredArrow (Aux.projRight f) i' :=
    CostructuredArrow.mk (Y := ⟨⟨i₀, l', D.map il₀ ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq]⟩)
      (lp₁ ≫ j₁.hom)
  trans middle
  · refine .of_inv ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (il₀ ≫ va₂) lp₁ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc]
        simp only [Functor.map_comp, Category.assoc]
        rw [heqa]
    · simp [middle]
  · refine .of_hom ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (ir₀ ≫ vb₂) lp₂ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc, heq]
        simp [heqb]
    · simp [middle, hlp]

@[simps]
def map : Aux.projLeft f ⋙ D ⟶ Aux.projRight f ⋙ D' where
  app A := A.obj.hom

end ConstructLimitMap

variable
  [IsCofiltered I] [IsCofiltered I']
  [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))]

set_option linter.unusedSectionVars false in
open ConstructLimitMap in
include hc hc' in
lemma Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda :
    ∃ (J : Type (max u₂ u₃ v₁))
      (_ : Category.{max v₂ v₃} J) (_ : IsCofiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Initial) (_ : G'.Initial) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsLimit.map (c.whisker _) ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc') g := by
  have := initial_projRight hc f
  have := initial_projLeft hc f
  use (Aux f).FullSubcategory, inferInstance, isCofiltered hc f,
    Aux.projLeft f, Aux.projRight f, inferInstance, inferInstance, map f
  apply ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc').hom_ext
  intro i'
  rw [IsLimit.map_π]
  dsimp
  apply i'.property.symm

end CategoryTheory

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

variable {I : Type u} [Category.{u} I] {S X : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)

variable [IsCofiltered I]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ (i : I), CompactSpace (D.obj i)] [∀ (i : I), QuasiSeparatedSpace (D.obj i)]

open TopologicalSpace

section

variable (D' : I ⥤ Scheme.{u}) (t' : D' ⟶ (Functor.const I).obj S) (c' : Cone D')
  (hc' : IsLimit c')

variable [∀ {i j} (f : i ⟶ j), IsAffineHom (D'.map f)]
  [∀ (i : I), CompactSpace (D'.obj i)] [∀ (i : I), QuasiSeparatedSpace (D'.obj i)]

omit [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ (i : I), CompactSpace ↥(D.obj i)]
  [∀ (i : I), QuasiSeparatedSpace ↥(D.obj i)] [∀ (i : I), QuasiSeparatedSpace ↥(D'.obj i)] in
include hc' in
/-- If `lim fᵢ` is surjective and `fᵢ` has open image (e.g. if `fᵢ` is étale), then the image of
a deep enough transition map `D'ₖ ⟶ D'ᵢ` is contained in the image of `fᵢ`. In particular, the
base change of `fᵢ` along `D'ₖ ⟶ D'ᵢ` is surjective. Compare [EGA4.3, Thm. 8.10.5 (vi)].

Note that the naive statement "`fₖ` is surjective for all `k ⟶ i` for `i` deep enough" is false
for a general natural transformation `f`: EGA 8.10.5 considers systems induced from a single
morphism by base change. (Counterexample: `I = ℕᵒᵖ`, `D k = 𝔸¹ ∖ {0, …, k}`,
`D' k = 𝔸¹ ∖ {0, …, k - 1}` with `f.app k` the open immersion; no `f.app k` is surjective,
but the limit map is an isomorphism.) -/
lemma exists_range_map_subset_range_app_of_surjective_isLimitMap (f : D ⟶ D') (i : I)
    (hopen : IsOpen (Set.range (f.app i).base))
    (hf : Surjective (IsLimit.map c hc' f)) :
    ∃ (k : I) (fki : k ⟶ i), Set.range (D'.map fki).base ⊆ Set.range (f.app i).base := by
  let U : (D'.obj i).Opens := ⟨Set.range (f.app i).base, hopen⟩
  obtain ⟨k, fki, hk⟩ := exists_map_eq_top D' c' hc' (i := i) U <| by
    rw [TopologicalSpace.Opens.ext_iff]
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hf.surj y
    refine ⟨c.π.app i x, ?_⟩
    calc f.app i (c.π.app i x)
        = (c.π.app i ≫ f.app i) x := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (IsLimit.map c hc' f ≫ c'.π.app i) x :=
        (congrArg (fun g : c.pt ⟶ D'.obj i ↦ g x) (IsLimit.map_π c hc' f i)).symm
      _ = c'.π.app i (IsLimit.map c hc' f x) := Scheme.Hom.comp_apply _ _ _
  refine ⟨k, fki, ?_⟩
  rintro _ ⟨z, rfl⟩
  have : z ∈ (D'.map fki ⁻¹ᵁ U : Set (D'.obj k)) := by
    rw [hk]
    trivial
  exact this

end

variable {I' : Type u} [SmallCategory I'] (D' : I' ⥤ Scheme.{u})
  (t' : D' ⟶ (Functor.const I').obj S)
  (c' : Cone D') (hc' : IsLimit c')

variable [IsCofiltered I']

instance inst_MathlibAlgebraicGeometryAffineTransitionLimit_L273 {C : Type*} [Category* C] (X : C) : Nonempty (Over X) :=
  ⟨Over.mk (𝟙 X)⟩

instance inst_MathlibAlgebraicGeometryAffineTransitionLimit_L276 {C : Type*} [Category* C] (X : C) : Nonempty (Under X) :=
  ⟨Under.mk (𝟙 X)⟩

include hc hc' in
lemma exists_eq_isLimitMap_whisker (f : c.pt ⟶ c'.pt)
    (hf : ∀ (i : I) (i' : I'), c.π.app i ≫ t.app i = f ≫ c'.π.app i' ≫ t'.app i')
    [∀ i, LocallyOfFinitePresentation (t.app i)] [∀ i, LocallyOfFinitePresentation (t'.app i)] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Initial) (_ : G'.Initial) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsLimit.map (c.whisker _) ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc') g ∧
      (∀ j, g.app j ≫ t'.app _ = t.app _) := by
  obtain ⟨i'⟩ := IsCofiltered.nonempty (C := I')
  obtain ⟨i, g, hi, hg⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation _ t
    (t'.app i') _ hc (f ≫ c'.π.app i') (by ext; simp [hf _ i'])
  let p' : c'.pt ⟶ S :=
    c'.π.app i' ≫ t'.app i'
  have hp' (j' : Over i') : c'.π.app j'.left ≫ t'.app j'.left = p' := by
    simp only [p']
    have h1 := t'.naturality j'.hom
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h1
    have h2 := c'.π.naturality j'.hom
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h2
    rw [h2, Category.assoc, h1]
  let p : c.pt ⟶ S :=
    f ≫ p'
  have hp (j : Over i) : c.π.app j.left ≫ t.app j.left = p := by
    simp only [p, p', hf _ i']
  have hc₀ : IsLimit (Cone.whisker (Over.forget i) c) :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc
  have hc'₀ : IsLimit (Cone.whisker (Over.forget i') c') :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc'
  have : IsCofiltered (Over i) := inferInstance
  have (j' : Over i') :
      PreservesColimit (Over.lift (Over.forget i ⋙ D) ((Over.forget i).whiskerLeft t)).op
        (yoneda.obj ((Over.lift (Over.forget i' ⋙ D')
        ((Over.forget i').whiskerLeft t')).obj j')) := by
    apply +allowSynthFailures @Scheme.preservesColimit_yoneda
    · intro _ _ g; exact inferInstanceAs (IsAffineHom (D.map g.left))
    · intro j; exact inferInstanceAs (CompactSpace (D.obj j.left))
    · intro j; exact inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
    · exact inferInstanceAs (LocallyOfFinitePresentation (t'.app j'.left))
  obtain ⟨J, _, _, G, G', _, _, g, hg⟩ := Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda
    (D := Over.lift (Over.forget i ⋙ D) (Functor.whiskerLeft _ t))
    (D' := Over.lift (Over.forget i' ⋙ D') (Functor.whiskerLeft _ t'))
    (c := Over.liftCone _ _ (c.whisker _) p hp)
    (c' := Over.liftCone _ _ (c'.whisker _) p' hp')
    (hc := Over.isLimitLiftCone _ _ _ _ _ hc₀)
    (hc' := Over.isLimitLiftCone _ _ _ _ _ hc'₀)
    (Over.homMk f rfl)
  use J, inferInstance, inferInstance, G ⋙ Over.forget _, G' ⋙ Over.forget _, inferInstance,
    inferInstance
  refine ⟨Functor.whiskerRight g (Over.forget S), ?_, ?_⟩
  · apply ((Functor.Initial.isLimitWhiskerEquiv (G' ⋙ Over.forget i') c').symm hc').hom_ext
    intro j
    rw [IsLimit.map_π]
    have := hg =≫ (Cone.whisker G'
      (Over.liftCone _ ((Over.forget i').whiskerLeft t') (Cone.whisker _ _) _ hp')).π.app j
    rw [IsLimit.map_π] at this
    simpa using congr($(this).left)
  · simp only [Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj, Functor.whiskerRight_app,
      Over.lift_obj, Functor.whiskerLeft_app, Over.forget_map]
    intro j
    exact Over.w (g.app j)

end AlgebraicGeometry


