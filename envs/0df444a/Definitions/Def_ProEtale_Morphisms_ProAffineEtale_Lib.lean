-- Prove2me | Definitions.Def_ProEtale_Morphisms_ProAffineEtale_Lib
-- name    : ProEtale_Morphisms_ProAffineEtale_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:55:52.167022+00:00
-- url     : https://prove2.me/theorems/03ec401f-97a9-5d83-a3e5-caac208e64b0
-- title:
--   Pro-affine-étale morphisms of schemes: base change along affine maps, right cancellation, composition, closure under pullbacks
-- statement:
--   This file continues the published file on pro-affine-étale morphisms. A morphism of schemes $f\colon X \to S$ is **pro-affine-étale** if $X$ is a cofiltered limit $X = \lim_j X_j$ of schemes over $S$ in which every $X_j$ is affine and every structure map $X_j \to S$ is étale. In particular, the source of a pro-affine-étale morphism is affine.
--
--   Principal results:
--
--   1. In any category, if $P$ is stable under composition, $f$ is pro-$P$ and $g$ is in $P$, then $g\circ f$ is pro-$P$.
--   2. Pro-affine-étale morphisms are stable under base change along any affine morphism $f\colon X \to Y$.
--   3. **Right cancellation.** If $g\colon Y \to Z$ and $g \circ f\colon X \to Z$ are pro-affine-étale, then $f\colon X \to Y$ is pro-affine-étale.
--   4. **Composition.** If $f\colon X \to Y$ and $g\colon Y \to Z$ are pro-affine-étale, so is $g \circ f$.
--   5. For a scheme $S$, the full subcategory of the slice category $\mathrm{Sch}/S$ consisting of objects with pro-affine-étale structure map is closed under fibre products, i.e. limits of cospan shape.
--
--   These stability properties are what is needed to use pro-affine-étale morphisms as the morphisms of a site, the affine pro-étale site of a scheme.
--
--   **Formalization Note** Schemes live in universe `u`, and `proAffineEtale` is `MorphismProperty.pro.{u} (@Etale ⊓ ofObjectProperty (IsAffine ·) ⊤)`. The results are `MorphismProperty.pro_comp_mem_of_mem` and anonymous instances of `proAffineEtale.IsStableUnderBaseChangeAlong f` (for `[IsAffineHom f]`), `proAffineEtale.HasOfPostcompProperty proAffineEtale`, `proAffineEtale.IsStableUnderComposition` and `(proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape WalkingCospan`. Lean writes composition diagrammatically: `f ≫ g` is $g \circ f$. The proofs of cancellation and composition reduce to the corresponding facts for ind-étale ring maps on global sections. A source comment notes that composition is proved directly, not derived from a general stability result for `pro P`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Morphisms/ProAffineEtale.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Morphisms_ProAffineEtale of the same module.

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.Pi
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_Bijective
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_HenselianLocalRing
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_IntegralLocal
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WeakDimension
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_WeaklyEtaleField
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_FromPi1_Etale
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_GroupWithZero_NonZeroDivisors
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Limits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_Logic_Function_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_IntegralClosure_IntegrallyClosed
import Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Mathlib_RingTheory_WeaklyEtale_Localization
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Pro-affine-étale morphisms

In this file we define the class of pro-affine-étale morphisms of schemes:
These are the morphisms of the form `lim Xᵢ ⟶ S` where each `Xᵢ` is absolutely affine
and étale over `X`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory
namespace MorphismProperty

universe w' v' u'

variable {C : Type u'} [Category.{v'} C] {P : MorphismProperty C}

/-- If `P` is stable under composition, then `pro P` morphisms compose with `P`-morphisms. -/
lemma pro_comp_mem_of_mem [P.IsStableUnderComposition] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : pro.{w'} P f) (hg : P g) : pro.{w'} P (f ≫ g) := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hf
  refine ⟨J, ‹_›, ‹_›, D, t ≫ (Functor.const J).map g, s, hs, fun j ↦ ⟨?_, ?_⟩⟩
  · exact P.comp_mem _ _ (hts j).1 hg
  · dsimp
    rw [← Category.assoc, (hts j).2]

end MorphismProperty
end CategoryTheory

namespace AlgebraicGeometry


instance inst_MorphismsProAffineEtale_L72 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    proAffineEtale.IsStableUnderBaseChangeAlong f := by
  rw [proAffineEtale]
  have : (@Etale ⊓ ofObjectProperty (IsAffine ·) ⊤ :
      MorphismProperty Scheme.{u}).IsStableUnderBaseChangeAlong f := by
    constructor
    intro Z W f' g' g h ⟨h₁, h₂⟩
    refine ⟨MorphismProperty.of_isPullback h h₁, ?_⟩
    have : IsAffine Z := h₂.left
    have : IsAffineHom f' := MorphismProperty.of_isPullback h.flip ‹_›
    rw [ofObjectProperty_top_right_iff]
    exact isAffine_of_isAffineHom f'
  infer_instance


/-- Pro-affine-étale morphisms cancel from the right: if `g` and `f ≫ g` are
pro-affine-étale, then so is `f`. -/
instance inst_MorphismsProAffineEtale_L281 : proAffineEtale.HasOfPostcompProperty proAffineEtale where
  of_postcomp {X Y Z} f g hg hfg := by
    haveI : IsAffine X := hfg.isAffine
    haveI hY : IsAffine Y := hg.isAffine
    obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hg
    obtain ⟨j₀⟩ : Nonempty J := IsCofiltered.nonempty
    haveI : IsAffine (D.obj j₀) := ofObjectProperty_top_right_iff.mp (hts j₀).1.2
    have hπ : proAffineEtale (s.app j₀) :=
      proAffineEtale.app_mem hs (fun j ↦ (hts j).1) j₀
    -- The composite `X ⟶ Y ⟶ D.obj j₀` is pro-affine-étale: it descends to a finite
    -- stage of the presentation of `f ≫ g` since `D.obj j₀` is locally of finite
    -- presentation over `Z`.
    have hfπ : proAffineEtale (f ≫ s.app j₀) := by
      obtain ⟨K, _, _, E, u, r, hr, hur⟩ := hfg
      have hAffE (k : K) : IsAffine (E.obj k) := ofObjectProperty_top_right_iff.mp (hur k).1.2
      haveI : ∀ {i j : K} (a : i ⟶ j), IsAffineHom (E.map a) := fun {i j} a ↦ by
        haveI := hAffE i; haveI := hAffE j; infer_instance
      haveI : ∀ k : K, CompactSpace (E.obj k) := fun k ↦ by
        haveI := hAffE k; infer_instance
      haveI : ∀ k : K, QuasiSeparatedSpace (E.obj k) := fun k ↦ by
        haveI := hAffE k; infer_instance
      haveI : Etale (t.app j₀) := (hts j₀).1.1
      have hcomm : (Cone.mk X r).π ≫ u =
          (Functor.const K).map ((f ≫ s.app j₀) ≫ t.app j₀) := by
        ext k
        dsimp
        rw [(hur k).2, Category.assoc, (hts j₀).2]
      obtain ⟨k₀, q, hq1, hq2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
        E u (t.app j₀) (Cone.mk X r) hr (f ≫ s.app j₀) hcomm
      refine ⟨Over k₀, inferInstance, inferInstance, CategoryTheory.Over.forget k₀ ⋙ E,
        { app l := E.map l.hom ≫ q
          naturality {l l'} a := by
            dsimp
            rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp,
              CategoryTheory.Over.w a] },
        ((Cone.mk X r).whisker (CategoryTheory.Over.forget k₀)).π,
        (Functor.Initial.isLimitWhiskerEquiv (CategoryTheory.Over.forget k₀)
          (Cone.mk X r)).symm hr,
        fun l ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
      · -- `E.map l.hom ≫ q` is étale by cancellation along the étale map `t.app j₀`
        have h1 : (E.map l.hom ≫ q) ≫ t.app j₀ = u.app l.left := by
          rw [Category.assoc, hq2]
          simp
        exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ (t.app j₀)
          (hts j₀).1.1 (by rw [h1]; exact (hur l.left).1.1)
      · exact ofObjectProperty_top_right_iff.mpr (hAffE l.left)
      · change r.app l.left ≫ E.map l.hom ≫ q = f ≫ s.app j₀
        rw [← Category.assoc, show r.app l.left ≫ E.map l.hom = r.app k₀ from by
          simpa using (r.naturality l.hom).symm]
        exact hq1
    haveI : IsAffine (((Functor.const J).obj Y).obj j₀) := hY
    rw [proAffineEtale_iff_appTop] at hπ hfπ ⊢
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hfπ
    exact RingHom.IndEtale.of_comp hπ hfπ

/- TODO: this previously followed from a (sorried, mathematically unjustified) global
instance `IsStableUnderComposition (pro P)`. The corrected statement
`MorphismProperty.IsStableUnderComposition.pro_of_le_isFinitelyPresentable` additionally
requires `P.IsStableUnderBaseChange` and `P.op ≤ isFinitelyPresentable Schemeᵒᵖ`,
which are not available for `Etale ⊓ ofObjectProperty (IsAffine ·) ⊤`. -/
instance inst_MorphismsProAffineEtale_L343 : proAffineEtale.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    haveI hX : IsAffine X := hf.isAffine
    haveI hY : IsAffine Y := hg.isAffine
    obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hg
    obtain ⟨j₀⟩ : Nonempty J := IsCofiltered.nonempty
    haveI : IsAffine (D.obj j₀) := ofObjectProperty_top_right_iff.mp (hts j₀).1.2
    have hπ : proAffineEtale (s.app j₀) :=
      proAffineEtale.app_mem hs (fun j ↦ (hts j).1) j₀
    have hfπ : proAffineEtale (f ≫ s.app j₀) := by
      haveI : IsAffine (((Functor.const J).obj Y).obj j₀) := hY
      rw [proAffineEtale_iff_appTop] at hπ hf ⊢
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
      exact RingHom.IndEtale.comp hf hπ
    have hcomp := MorphismProperty.pro_comp_mem_of_mem hfπ (hts j₀).1
    rwa [Category.assoc, (hts j₀).2] at hcomp

/-- `proAffineEtale.overObj S` is closed under cospan limits in `Over S`: a pullback of a
cospan whose three legs have `proAffineEtale` structural maps again has
`proAffineEtale` structural map. -/
instance inst_MorphismsProAffineEtale_L360 {S : Scheme.{u}} :
    (proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape WalkingCospan :=
  Over.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong (P := proAffineEtale)
    fun h₁ h₂ _ ↦ by
      have : IsAffine _ := h₁.isAffine
      have : IsAffine _ := h₂.isAffine
      infer_instance


end AlgebraicGeometry


