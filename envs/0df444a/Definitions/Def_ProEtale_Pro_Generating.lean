-- Prove2me | Definitions.Def_ProEtale_Pro_Generating
-- name    : ProEtale_Pro_Generating
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:38:19.154876+00:00
-- url     : https://prove2.me/theorems/a2c0bc39-faaf-45a8-aad7-456c8fc75d75
-- title:
--   Sheaf criterion on a pro-category via relatively presentable presieves when pullbacks exist
-- statement:
--   Let $F : C \to D$ be a functor (think $D = \mathrm{Pro}(C)$), where $C$ and $D$ have pullbacks and $F$ preserves them. This file reduces the sheaf criterion of *Pro/Basic* from 1-hypercovers to presieves (0-hypercovers).
--
--   **Definitions.**
--   - A *relative limit presentation* of a pre-0-hypercover $E = \{f_i : X_i \to X\}$ of $X \in D$ over $J$ is a relative limit presentation of $X$ and of each $X_i$ (diagrams $J \to C$ with limit cones after applying $F$), with morphisms of presentations inducing the $f_i$. At each level $j$ it gives a pre-0-hypercover of $d(j)$ in $C$.
--   - $E$ is *relatively presentable* for a topology $J_C$ on $C$ if it has such a presentation over a small cofiltered category with every level a $J_C$-covering.
--   - The precoverage `relativelyPresentable` on $D$ consists of the presieves whose associated pre-0-hypercover is relatively presentable.
--
--   **Results.**
--   1. Constructions on relative limit presentations: the pullback of presented objects along presented morphisms is presented, using that $F$ preserves pullbacks; a presentation can be reindexed along an initial functor; and, for $J$ cofiltered, a presentation can be restricted to an object of $C$ mapping to a level, with a comparison morphism of presentations.
--   2. A presentation of a pre-0-hypercover gives one of its pre-1-hypercover of pairwise pullbacks, whose level-1 sieves cover. So a finite, relatively presentable pre-0-hypercover gives a relatively presentable pre-1-hypercover.
--   3. Sheaf conditions for hypercovers can be tested after composing with all coyoneda functors $\mathrm{Hom}(M, -)$. If a precoverage $B$ generates the topology $K$ on $D$, then $P$ is a $K$-sheaf iff it satisfies the sheaf condition for the saturated pre-0-hypercover of every presieve in $B$.
--   4. **Main theorem.** Let $P : D^{\mathrm{op}} \to \mathcal A$ be a presheaf such that $F^{\mathrm{op}} \circ P$ is a $J_C$-sheaf and $P$ sends cofiltered limits of diagrams factoring through $F$ to colimits. Assume $\mathcal A$ has filtered colimits and satisfies AB5. Let $B$ be a precoverage on $D$ that generates the topology $K$, all of whose presieves are relatively presentable and finite. Then $P$ is a $K$-sheaf:
--   $$B \le \mathrm{relPres}_{F,J_C},\quad B \le \mathrm{finite},\quad B \text{ generates } K \;\Longrightarrow\; P \text{ is a } K\text{-sheaf}.$$
--
--   According to its docstring, this is applied to the affine pro-étale site with $B$ consisting of finite Zariski coverings and single faithfully flat pro-étale maps of affine schemes, both relatively presentable with respect to the inclusion of the affine étale site.
--
--   **Formalization Note** Main declarations: `CategoryTheory.PreZeroHypercover.RelativeLimitPresentation`, `Limits.RelativeLimitPresentation.pullback`, `.precomp`, `.restrict`, `.restrictHom`, `PreZeroHypercover.RelativeLimitPresentation.onePullbacks`, `PreZeroHypercover.IsRelativelyPresentable` (with `.toPreOneHypercover`), `Precoverage.relativelyPresentable`, `Precoverage.Generates.isSheaf_iff_preZeroHypercover` and `CategoryTheory.Presheaf.isSheaf_of_generates_of_isRelativelyPresentable`. The hypothesis on $P$ is the class `Functor.PreservesRelativeFilteredColimits.{w} F P`. AB5 is `AB5OfSize.{w}` and filtered colimits are `HasFilteredColimitsOfSize.{w, w}`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Pro/Generating.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.Hypercover.Saturate
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Pro_Basic_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Sheaf condition in pro-category when pullbacks exist

In this file we deduce an important special case of the material developed
in `Proetale/Pro.lean`: If pullbacks exist and the functor `F : C ⥤ D`
(think `D = Pro C`) preserves them, then, to apply the sheaf criterion,
it suffices to show that presieves (i.e. `0`-hypercovers) are relatively
presentable under `F`.
-/

universe t w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (F : C ⥤ D)
variable {X : C} (R : Presieve X)
variable (A : Type*) [Category* A]

variable (B : Precoverage D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

structure PreZeroHypercover.RelativeLimitPresentation (J : Type*) [Category* J] {X : D}
    (E : PreZeroHypercover.{w} X) where
  pres : Limits.RelativeLimitPresentation J F X
  pres₀ : ∀ i : E.I₀, Limits.RelativeLimitPresentation J F (E.X i)
  f : ∀ i, (pres₀ i).Hom pres
  hf : ∀ i, (f i).map = E.f i

variable {F} in
@[simps]
def PreZeroHypercover.RelativeLimitPresentation.preZeroHypercover {J : Type*} [Category* J] {X : D}
    {E : PreZeroHypercover.{w} X} (pres : E.RelativeLimitPresentation F J) (j : J) :
    PreZeroHypercover.{w} (pres.pres.diag.obj j) where
  I₀ := E.I₀
  X i := (pres.pres₀ i).diag.obj j
  f i := (pres.f i).natTrans.app j

section

variable [Limits.HasPullbacks C] [Limits.HasPullbacks D] [PreservesLimitsOfShape WalkingCospan F]

@[simps]
noncomputable
def Limits.RelativeLimitPresentation.pullback {X Y S : D} (f : X ⟶ S) (g : Y ⟶ S)
    (p : PullbackCone f g) (hp : IsLimit p) {J : Type*} [Category* J]
    (pX : RelativeLimitPresentation J F X) (pY : RelativeLimitPresentation J F Y)
    (pS : RelativeLimitPresentation J F S)
    (pf : pX.Hom pS) (pg : pY.Hom pS) (hf : pf.map = f) (hg : pg.map = g) :
    RelativeLimitPresentation J F p.pt where
  diag.obj j := Limits.pullback (pf.natTrans.app j) (pg.natTrans.app j)
  diag.map {i j} f := pullback.map _ _ _ _ (pX.diag.map f) (pY.diag.map f) (pS.diag.map f)
    (by simp) (by simp)
  π.app j := by
    refine (IsPullback.map F (.of_hasPullback (pf.natTrans.app j) (pg.natTrans.app j))).lift
      (p.fst ≫ pX.π.app j) (p.snd ≫ pY.π.app j) ?_
    subst hf hg
    simpa using p.condition =≫ pS.π.app j
  π.naturality {i j} f := by
    subst hf hg
    apply ((IsPullback.map F (.of_hasPullback (pf.natTrans.app j) (pg.natTrans.app j)))).hom_ext
    · have := pX.π.naturality f
      simp at this
      simp [← Functor.map_comp]
      simp [this]
    · have := pY.π.naturality f
      simp at this
      simp [← Functor.map_comp]
      simp [this]
  isLimit := by
    refine .mk ?_ ?_ ?_
    · intro s
      dsimp
      refine PullbackCone.IsLimit.lift hp ?_ ?_ ?_
      · let sX : Cone (pX.diag ⋙ F) :=
          { pt := s.pt
            π.app j := s.π.app j ≫ F.map (pullback.fst _ _)
            π.naturality i j f := by
              have := s.π.naturality f
              simp at this
              simp [this, ← Functor.map_comp] }
        exact pX.isLimit.lift sX
      · let sY : Cone (pY.diag ⋙ F) :=
          { pt := s.pt
            π.app j := s.π.app j ≫ F.map (pullback.snd _ _)
            π.naturality i j f := by
              have := s.π.naturality f
              simp at this
              simp [this, ← Functor.map_comp] }
        exact pY.isLimit.lift sY
      · subst hf hg
        apply pS.isLimit.hom_ext
        intro j
        simp [← Functor.map_comp, pullback.condition]
    · intro s j
      apply ((IsPullback.map F (.of_hasPullback (pf.natTrans.app j) (pg.natTrans.app j)))).hom_ext
      · simp
      · simp
    · intro s m hm
      apply PullbackCone.IsLimit.hom_ext hp
      · apply pX.isLimit.hom_ext
        intro j
        simpa using hm j =≫ F.map (pullback.fst _ _)
      · apply pY.isLimit.hom_ext
        intro j
        simpa using hm j =≫ F.map (pullback.snd _ _)

@[simps]
noncomputable
def Limits.RelativeLimitPresentation.precomp
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {J K : Type*} [Category* J] [Category* K]
    {X : D} (pres : RelativeLimitPresentation J F X)
    (G : K ⥤ J) [G.Initial] :
    RelativeLimitPresentation K F X where
  diag := G ⋙ pres.diag
  π := (Functor.constCompWhiskeringLeftIso _ _).inv.app _ ≫
    Functor.whiskerLeft _ pres.π ≫ (Functor.associator _ _ _).inv
  isLimit := by
    refine IsLimit.postcomposeHomEquiv (Functor.associator _ _ _).symm _ ?_
    refine (Functor.Initial.isLimitExtendConeEquiv (G := pres.diag ⋙ F) G _) ?_
    refine IsLimit.equivOfNatIsoOfIso (Iso.refl _) _ _ ?_ pres.isLimit
    refine Cone.ext (.refl _) fun j ↦ ?_
    simpa using pres.π.naturality _

@[simps!]
noncomputable
def Limits.RelativeLimitPresentation.restrict
    {C D : Type*} [Category* C] [HasPullbacks C] [Category* D] {F : C ⥤ D} {J : Type*} [Category* J]
    {X : D} (pres : RelativeLimitPresentation J F X)
    [IsCofiltered J]
    [PreservesLimitsOfShape WalkingCospan F]
    {j : J} {U : C} (f : U ⟶ pres.diag.obj j)
    (V : D) (fst : V ⟶ F.obj U) (snd : V ⟶ X)
    (hg : IsPullback fst snd (F.map f) (pres.π.app j)) :
    RelativeLimitPresentation (Over j) F V :=
  haveI : CategoryTheory.IsConnected (Over j) := IsCofiltered.isConnected _
  RelativeLimitPresentation.pullback _ _ (F.map f) hg.flip.cone hg.flip.isLimit
    (pres.precomp (Over.forget j))
    (.self _)
    (.self _)
    { natTrans.app j := pres.diag.map j.hom
      natTrans.naturality := by simp [← Functor.map_comp] }
    (.self f)
    (by
      apply ((RelativeLimitPresentation.self (F := F) (J := Over j) _)).isLimit.hom_ext
      intro k
      rw [RelativeLimitPresentation.Hom.map_π]
      simpa using (pres.π.naturality k.hom).symm)
    (by simp)

@[simps]
noncomputable
def Limits.RelativeLimitPresentation.restrictHom
    {C D : Type*} [Category* C] [HasPullbacks C] [Category* D] {F : C ⥤ D} {J : Type*} [Category* J]
    {X : D} (pres : RelativeLimitPresentation J F X)
    [PreservesLimitsOfShape WalkingCospan F]
    [IsCofiltered J]
    {j : J} {U : C} (f : U ⟶ pres.diag.obj j)
    (V : D) (fst : V ⟶ F.obj U) (snd : V ⟶ X)
    (hg : IsPullback fst snd (F.map f) (pres.π.app j)) :
    (pres.restrict _ _ _ _ hg).Hom (pres.precomp (Over.forget _)) where
  natTrans.app j := pullback.fst _ _

@[simp]
lemma Limits.RelativeLimitPresentation.restrictHom_map
    {C D : Type*} [Category* C] [HasPullbacks C] [Category* D] {F : C ⥤ D} {J : Type*} [Category* J]
    {X : D} (pres : RelativeLimitPresentation J F X)
    [PreservesLimitsOfShape WalkingCospan F]
    [IsCofiltered J]
    {j : J} {U : C} (f : U ⟶ pres.diag.obj j)
    (V : D) (fst : V ⟶ F.obj U) (snd : V ⟶ X)
    (hg : IsPullback fst snd (F.map f) (pres.π.app j)) :
    (pres.restrictHom _ _ _ _ hg).map = snd := by
  refine (pres.precomp (Over.forget j)).isLimit.hom_ext ?_
  intro i
  simp only [RelativeLimitPresentation.precomp_diag, Functor.comp_obj, Over.forget_obj,
    RelativeLimitPresentation.Hom.map_π, Functor.const_obj_obj,
    RelativeLimitPresentation.restrict_diag_obj, RelativeLimitPresentation.restrict_π_app,
    RelativeLimitPresentation.restrictHom_natTrans_app]
  simp

@[simps]
noncomputable
def PreZeroHypercover.RelativeLimitPresentation.onePullbacks {J : Type*} [Category* J] {X : D}
    {E : PreZeroHypercover.{w} X} (pres : E.RelativeLimitPresentation F J) :
    E.toPreOneHypercover.RelativeLimitPresentation J F where
  __ := pres
  pres₁ {i j} k := .pullback _ _ _ _ (limit.isLimit _) (pres.pres₀ i) (pres.pres₀ j) pres.pres
    (pres.f i) (pres.f j) (pres.hf i) (pres.hf j)
  p₁ k :=
    { natTrans.app j := pullback.fst _ _
      natTrans.naturality i j f := by simp }
  p₂ k :=
    { natTrans.app j := pullback.snd _ _
      natTrans.naturality i j f := by simp }
  hp₁ {i j} k := (pres.pres₀ i).isLimit.hom_ext (by simp)
  hp₂ {i j} k := (pres.pres₀ j).isLimit.hom_ext (by simp)
  w k := by ext; simp [pullback.condition]


def PreZeroHypercover.RelativeLimitPresentation.sieve₁_mem
    {I : Type*} [Category* I] {X : D}
    {E : PreZeroHypercover.{w} X} (pres : E.RelativeLimitPresentation F I)
    (h : ∀ j, (pres.preZeroHypercover j).sieve₀ ∈ J (pres.pres.diag.obj j))
    {i j : E.I₀} (a : I)
    (W : C) (p₁ : W ⟶ (pres.pres₀ i).diag.obj a)
    (p₂ : W ⟶ (pres.pres₀ j).diag.obj a) (w : p₁ ≫ (pres.f i).natTrans.app a =
      p₂ ≫ (pres.f j).natTrans.app a) :
    (pres.onePullbacks.preOneHypercover a).sieve₁ p₁ p₂ ∈ J W := by
  let E' : Precoverage.ZeroHypercover J.toPrecoverage _ :=
    ⟨pres.preZeroHypercover a, h _⟩
  exact J.toGrothendieck_toPrecoverage_le _ ((E'.toOneHypercover).mem₁ _ _ p₁ p₂ w)

def PreZeroHypercover.IsRelativelyPresentable {X : D} (E : PreZeroHypercover.{w} X) : Prop :=
  ∃ (I : Type t) (_ : SmallCategory I) (_ : IsCofiltered I)
    (pres : E.RelativeLimitPresentation F I),
    ∀ j, (pres.preZeroHypercover j).sieve₀ ∈ J (pres.pres.diag.obj j)

lemma PreZeroHypercover.IsRelativelyPresentable.toPreOneHypercover {X : D} (E : PreZeroHypercover X)
    (h : PreZeroHypercover.IsRelativelyPresentable.{w} F J E) [E.Finite] :
    PreOneHypercover.IsRelativelyPresentable.{w} F J E.toPreOneHypercover := by
  obtain ⟨I, _, _, pres, hpres⟩ := h
  refine ⟨I, inferInstance, inferInstance, pres.onePullbacks, ?_⟩
  intro a
  refine ⟨hpres _, fun {i j} W p₁ p₂ w ↦ ?_⟩
  exact PreZeroHypercover.RelativeLimitPresentation.sieve₁_mem _ _ _ hpres _ _ _ _ w

end

def Precoverage.relativelyPresentable : Precoverage D where
  coverings _ R := PreZeroHypercover.IsRelativelyPresentable.{w} F J R.preZeroHypercover

lemma Presieve.finite_uncurry_iff {X : C} (R : Presieve X) :
    R.uncurry.Finite ↔ R.preZeroHypercover.Finite :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.finite₀⟩

lemma PreOneHypercover.isSheafFor_iff_isSheafFor_comp_coyoneda {X : C} {P : Cᵒᵖ ⥤ A}
    {E : PreOneHypercover X} :
    E.IsSheafFor P ↔ ∀ (M : A), E.IsSheafFor (P ⋙ coyoneda.obj (.op M)) :=
  ⟨fun h M ↦ ⟨Multifork.isLimitMapOfPreserves _ (coyoneda.obj (.op M)) h.some⟩,
    fun h ↦ ⟨coyonedaJointlyReflectsLimits _ _
      fun _ ↦ (Multifork.isLimitMapEquiv _ _).symm (h _).some⟩⟩

lemma PreZeroHypercover.isSheafFor_saturate_iff {X : C} {E : PreZeroHypercover X} {P : Cᵒᵖ ⥤ A} :
    E.saturate.IsSheafFor P ↔
      ∀ (M : A), Presieve.IsSheafFor (P ⋙ coyoneda.obj (.op M)) E.presieve₀ := by
  rw [PreOneHypercover.isSheafFor_iff_isSheafFor_comp_coyoneda]
  simp_rw [PreZeroHypercover.isLimit_saturate_type_iff]

lemma Precoverage.Generates.isSheaf_iff_preZeroHypercover (H : B.Generates K) (P : Dᵒᵖ ⥤ A) :
    Presheaf.IsSheaf K P ↔
      ∀ ⦃X : D⦄ (R : Presieve X), R ∈ B X → R.preZeroHypercover.saturate.IsSheafFor P := by
  simp [H.isSheaf_iff, PreZeroHypercover.isSheafFor_saturate_iff]

namespace Presheaf

variable [HasPullbacks C] [HasPullbacks D] [PreservesLimitsOfShape WalkingCospan F]

variable {A : Type*} [Category.{t} A]

/--
Suppose `C` and `D` have pullbacks and `F : C ⥤ D` preserves them. If `P` is a presheaf on `D` that

1. is a sheaf when restricted to `C`, and
2. preserves filtered colimits,

then `P` is a sheaf for any topology that is generated by finite, relatively presentable presieves,
i.e., cofiltered limits of covering presieves in `C`.

In our application to the affine pro-étale site, `B` will be the precoverage
given by finite Zariski coverings and single morphism coverings given by faithfully flat, pro-étale
morphisms between affine schemes. Both of these are ind-presentable wrt. to the
inclusion of the affine étale site into the affine pro-étale site.
-/
theorem isSheaf_of_generates_of_isRelativelyPresentable (P : Dᵒᵖ ⥤ A) (h : IsSheaf J (F.op ⋙ P))
    [Functor.PreservesRelativeFilteredColimits.{w} F P] [HasFilteredColimitsOfSize.{w, w} A]
    [AB5OfSize.{w} A] (H : B.Generates K)
    (h₁ : B ≤ Precoverage.relativelyPresentable.{w} F J)
    (h₂ : B ≤ Precoverage.finite _) :
    IsSheaf K P := by
  rw [H.isSheaf_iff_preZeroHypercover (A := A)]
  intro X R hR
  dsimp [PreOneHypercover.IsSheafFor]
  rw [(R.preZeroHypercover.isLimitSaturateEquivOfHasPullbacks _).nonempty_congr]
  have : R.preZeroHypercover.Finite := by
    rw [← Presieve.finite_uncurry_iff]
    exact h₂ _ hR
  apply PreOneHypercover.IsSheafFor.of_preservesFilteredColimitsOfSize.{_, w} J _ (F := F) h
    R.preZeroHypercover.toPreOneHypercover _
  exact (h₁ _ hR).toPreOneHypercover _ _ _

end Presheaf

end CategoryTheory


