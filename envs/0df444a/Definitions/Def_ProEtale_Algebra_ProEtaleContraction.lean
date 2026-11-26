-- Prove2me | Definitions.Def_ProEtale_Algebra_ProEtaleContraction
-- name    : ProEtale_Algebra_ProEtaleContraction
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:48:25.407289+00:00
-- url     : https://prove2.me/theorems/69b038bf-e820-4bab-96ca-eeaa9174ba24
-- title:
--   An ind-étale faithfully flat algebra over which every faithfully flat étale algebra has a retraction
-- statement:
--   For any commutative ring $R$ this file constructs an $R$-algebra $\widetilde R$, the **étale ind-contraction** of $R$, such that:
--
--   1. $R \to \widetilde R$ is ind-étale;
--   2. $R \to \widetilde R$ is faithfully flat;
--   3. every étale ring homomorphism $f : \widetilde R \to S$ that is surjective on spectra ($\operatorname{Spec} S \to \operatorname{Spec}\widetilde R$ surjective, so $f$ is faithfully flat) has a retraction: there is a ring homomorphism $g : S \to \widetilde R$ with
--   $$g \circ f = \mathrm{id}_{\widetilde R}.$$
--
--   $\widetilde R$ is the general *contraction* construction applied in $\mathrm{CommRing}^{\mathrm{op}}$ to the morphism properties "étale" and "faithfully flat" at $R$. That construction is a sequential limit in $\mathrm{CommRing}^{\mathrm{op}}$, i.e. a colimit of rings, of successive covers that adjoin sections to all faithfully flat étale algebras.
--
--   The file is a step toward rings with no nontrivial pro-étale covers, i.e. w-contractible rings: every faithfully flat étale cover of $\widetilde R$ splits.
--
--   **Formalization Note** All rings are in `Type u`. Main declarations: `IndEtaleContraction R` (the underlying type of `MorphismProperty.contraction.{u} CommRingCat.etale.op CommRingCat.faithfullyFlat.op (op (CommRingCat.of R))`), its `CommRing` and `Algebra R` instances, the instances `indEtale_indEtaleContraction` and `faithfullyFlat_indEtaleContraction`, and `RingHom.Etale.exists_comp_eq_id_indContraction`. Faithful flatness of $f$ is stated as étaleness plus `Function.Surjective (PrimeSpectrum.comap f)`. An auxiliary instance provides the limits of shape `FiniteFamilies(...)ᵒᵖ` in `Over R` needed by the construction.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/ProEtaleContraction.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Ring.Fin
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Ideal
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Inseparable
import Definitions.Def_ProEtale_Algebra_Contraction_Covers
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_FromPi1_Etale
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_FiniteLimits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_WidePullbacks
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Composition
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Constructing ind-étale algebras

In this file we construct for any ring `R` an ind-étale, faithfully flat `R`-algebra
`IndEtaleContraction R` such that any faithfully flat, étale ring homomorphism
`IndEtaleContraction R →+* S` has a retraction.
-/

universe u

open CategoryTheory Opposite

variable {R : Type u} [CommRing R]

-- local instance to speed up instance search
instance inst_AlgebraProEtaleContraction_L25 (R : CommRingCat.{u}ᵒᵖ) :
    Limits.HasLimitsOfShape
      (FiniteFamilies (SmallModel.{u}
      ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R)))ᵒᵖ (Over R) :=
  inferInstance

/-- The étale ind-contraction of a ring. This is defined
to be the contraction wrt. to the morphism property of étale ring homomorphisms. -/
def IndEtaleContraction (R : Type u) [CommRing R] : Type u :=
  (MorphismProperty.contraction.{u}
    CommRingCat.etale.op
    CommRingCat.faithfullyFlat.op
    (op <| CommRingCat.of R) : CommRingCat.{u}ᵒᵖ).unop

noncomputable instance inst_AlgebraProEtaleContraction_L39 : CommRing (IndEtaleContraction R) :=
  inferInstanceAs <| CommRing (_ : CommRingCat.{u})

noncomputable instance inst_AlgebraProEtaleContraction_L42 : Algebra R (IndEtaleContraction R) :=
  letI f : R →+* IndEtaleContraction R :=
    (MorphismProperty.Contraction.base _ _ (op <| CommRingCat.of R)).unop.hom
  f.toAlgebra

/-- The ind-contraction of `R` is ind-étale over `R`. -/
instance indEtale_indEtaleContraction : Algebra.IndEtale R (IndEtaleContraction R) := by
  rw [← RingHom.IndEtale.algebraMap_iff, RingHom.algebraMap_toAlgebra,
    RingHom.IndEtale.iff_ind_etale]
  dsimp only [CommRingCat.ofHom_hom]
  rw [MorphismProperty.ind_eq_unop_pro_op]
  dsimp only [MorphismProperty.unop.eq_1, Quiver.Hom.op_unop]
  apply MorphismProperty.pro_contractionBase
  exact MorphismProperty.le_isFinitelyPresentable_op_op
    CommRingCat.etale_le_isFinitelyPresentable.{u}

instance faithfullyFlat_indEtaleContraction : Module.FaithfullyFlat R (IndEtaleContraction R) := by
  rw [← RingHom.faithfullyFlat_algebraMap_iff, RingHom.algebraMap_toAlgebra]
  have heq : MorphismProperty.pro.{u} CommRingCat.faithfullyFlat.{u}.op =
      CommRingCat.faithfullyFlat.{u}.op := by
    conv_rhs => rw [← CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat]
    rw [MorphismProperty.ind_eq_unop_pro_op, MorphismProperty.op_unop]
  exact MorphismProperty.prop_contractionπ
    CommRingCat.etale.op CommRingCat.faithfullyFlat.op heq (op <| .of R) 0

/-- Any étale ring homomorphism `IndEtaleContraction R →+* S` has a retraction. -/
lemma RingHom.Etale.exists_comp_eq_id_indContraction {S : Type u} [CommRing S]
    (f : IndEtaleContraction R →+* S) (hf : f.Etale)
    (hf' : Function.Surjective (PrimeSpectrum.comap f)) :
    ∃ (g : S →+* IndEtaleContraction R), g.comp f = .id (IndEtaleContraction R) := by
  have : MorphismProperty.PreProSpreads.{0} CommRingCat.etale.op := by
    rw [MorphismProperty.PreProSpreads.op_iff]
    exact MorphismProperty.PreIndSpreads.of_univLE.{u} _
  have hf' : f.FaithfullyFlat := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨hf.smooth.flat, hf'⟩
  have heq : MorphismProperty.pro.{u} CommRingCat.faithfullyFlat.{u}.op =
      CommRingCat.faithfullyFlat.{u}.op := by
    conv_rhs => rw [← CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat]
    rw [MorphismProperty.ind_eq_unop_pro_op, MorphismProperty.op_unop]
  obtain ⟨g, hg⟩ := MorphismProperty.exists_comp_eq_id_contraction
    CommRingCat.etale.op _ _ heq
    (fun {R S T} f g hfg hf hg ↦ by
      rw [CommRingCat.faithfullyFlat_eq] at ⊢ hfg
      refine ⟨?_, ?_⟩
      · exact hg.smooth.flat
      · apply Function.Surjective.of_comp (g := PrimeSpectrum.comap f.1.hom)
        exact hfg.2)
    (CommRingCat.ofHom f).op hf hf'
  use g.unop.hom
  exact congr($(hg).unop.hom)


