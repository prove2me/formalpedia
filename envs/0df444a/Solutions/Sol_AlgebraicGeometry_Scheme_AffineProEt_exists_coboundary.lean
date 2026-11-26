-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.AffineProEt.exists_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:37:41.50961+00:00
-- url     : https://prove2.me/submissions/e0391877-dbe5-4d2b-a950-031ce4a4ac34

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.Pi
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Hypercover.Saturate
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.MorphismProperty
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Logic.Function.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
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
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Stonean.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sets.CompactOpenCovered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Comparator_Definitions
import Definitions.Def_ProEtale_Comparator_Lib
import Definitions.Def_ProEtale_Algebra_Bijective
import Definitions.Def_ProEtale_Algebra_Contraction_Covers
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_HenselianLocalRing
import Definitions.Def_ProEtale_Algebra_IdentifiesLocalRings
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndBijectiveOnStalks
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale
import Definitions.Def_ProEtale_Algebra_IndWeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_IntegralLocal
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_ProEtaleContraction
import Definitions.Def_ProEtale_Algebra_PullbackProfinite
import Definitions.Def_ProEtale_Algebra_RetractionsStrictlyHenselian
import Definitions.Def_ProEtale_Algebra_StalkAlgebraic
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WContractible
import Definitions.Def_ProEtale_Algebra_WContractible_Lib
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WLocal_Lib
import Definitions.Def_ProEtale_Algebra_WLocalization_Basic
import Definitions.Def_ProEtale_Algebra_WLocalization_Ideal
import Definitions.Def_ProEtale_Algebra_WStrictLocalization
import Definitions.Def_ProEtale_Algebra_WeakDimension
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Algebra_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Algebra_WeaklyEtaleField
import Definitions.Def_ProEtale_Algebra_WeaklyEtaleIndEtale
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
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_AffineTransitionLimit
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Extensive
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineEtale
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineRefinement
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_Small
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Comma_ArrowRefinement
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Comma_StructuredArrow_Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_FiniteLimits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_WidePullbacks
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Composition
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Limits
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_DenseSubsite_Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Finite
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Grothendieck
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Pullback
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_CechResolution
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_LocallyVanish
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sheafification
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_Sieves
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_Logic_Function_Basic
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Prod
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_GoingDown
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_IntegralClosure_IntegrallyClosed
import Definitions.Def_ProEtale_Mathlib_RingTheory_LocalRing_RingHom_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_Localization
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_Topology
import Definitions.Def_ProEtale_Mathlib_RingTheory_TensorProduct_Maps
import Definitions.Def_ProEtale_Mathlib_RingTheory_WeaklyEtale_Localization
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
import Definitions.Def_ProEtale_Mathlib_Topology_Constructions
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_JacobsonSpace
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_ConstructibleTopology
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale
import Definitions.Def_ProEtale_Morphisms_ProAffineEtale_Lib
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale_Lib
import Definitions.Def_ProEtale_Pro_Basic
import Definitions.Def_ProEtale_Pro_Basic_Lib
import Definitions.Def_ProEtale_Pro_Generating
import Definitions.Def_ProEtale_Pro_PresheafColimit
import Definitions.Def_ProEtale_Topology_Coherent_Affine
import Definitions.Def_ProEtale_Topology_Coherent_Etale
import Definitions.Def_ProEtale_Topology_Comparison_Affine
import Definitions.Def_ProEtale_Topology_Comparison_Affine_Lib
import Definitions.Def_ProEtale_Topology_Comparison_FreeSheaf
import Definitions.Def_ProEtale_Topology_Comparison_SectionsColimit
import Definitions.Def_ProEtale_Topology_Flat_QuasiCompactCover
import Definitions.Def_ProEtale_Topology_LocalProperties
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_Proetale_Basic
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification
import Definitions.Def_ProEtale_Topology_Proetale_Sheafification_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ConnectedComponents
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Pullback
import Definitions.Def_ProEtale_Topology_Comparison_CechColimit
import Theorems.Thm_CategoryTheory_cechFreeEval_exact_succ
import Theorems.Thm_CategoryTheory_shortComplex_exact_of_evaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Čech cocycles of pullbacks of injective sheaves are coboundaries

For a surjection `q : W ⟶ U₀` of affine pro-étale objects and an injective abelian sheaf
`I` on the small étale site, every positive-degree Čech cocycle of `ν^*I` along `q` is a
coboundary: the Čech complex of `ν^*I` along `q` is a filtered colimit of Čech complexes
of `I` along surjective étale covers at the finite stages of a relative limit presentation
of `q`, and these are exact since `I` is injective.
-/

universe w₂ w₁ u

open CategoryTheory Limits Opposite Abelian AlgebraicTopology

open scoped Simplicial

namespace AddCommGrpCat


lemma hom_sum_apply {M N : AddCommGrpCat.{u + 1}} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (x : M) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact hom_add_apply _ _ _

end AddCommGrpCat

namespace CategoryTheory

/-! ### Translation between morphisms out of free abelian sheaves and sections

We record that `freeAbelianSheafHomEquiv` is additive (via the "generator" trick: every
morphism out of the free abelian sheaf is determined by its value on the canonical
generating section), and compute the image of a composition with the Čech differential. -/

section SectionsTranslation

variable {C : Type (u + 1)} [Category.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]

/-- Every morphism out of a free abelian sheaf corresponds, under
`freeAbelianSheafHomEquiv`, to the value of its component at `U` on the canonical
generating section. -/
lemma freeAbelianSheafHomEquiv_eq_app {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}}
    (φ : (freeAbelianSheafFunctor J).obj U ⟶ F) :
    freeAbelianSheafHomEquiv φ =
      φ.hom.app (op U)
        (freeAbelianSheafHomEquiv (𝟙 ((freeAbelianSheafFunctor J).obj U))) := by
  conv_lhs => rw [← Category.id_comp φ]
  exact freeAbelianSheafHomEquiv_naturality_right _ _

lemma freeAbelianSheafHomEquiv_zero {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}} :
    freeAbelianSheafHomEquiv (0 : (freeAbelianSheafFunctor J).obj U ⟶ F) =
      (0 : F.obj.obj (op U)) := by
  rw [freeAbelianSheafHomEquiv_eq_app]
  have h0 : (0 : (freeAbelianSheafFunctor J).obj U ⟶ F).hom = 0 := rfl
  rw [h0, NatTrans.app_zero]
  rfl

lemma freeAbelianSheafHomEquiv_sum {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}}
    {ι : Type*} (s : Finset ι) (φ : ι → ((freeAbelianSheafFunctor J).obj U ⟶ F)) :
    freeAbelianSheafHomEquiv (∑ i ∈ s, φ i) =
      ∑ i ∈ s, freeAbelianSheafHomEquiv (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using freeAbelianSheafHomEquiv_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rw [freeAbelianSheafHomEquiv_eq_app, freeAbelianSheafHomEquiv_eq_app (φ i),
      freeAbelianSheafHomEquiv_eq_app (∑ j ∈ s, φ j), Sheaf.Hom.add_app]
    exact AddCommGrpCat.hom_add_apply _ _ _

lemma freeAbelianSheafHomEquiv_zsmul {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}}
    (z : ℤ) (φ : (freeAbelianSheafFunctor J).obj U ⟶ F) :
    freeAbelianSheafHomEquiv (z • φ) = z • freeAbelianSheafHomEquiv φ := by
  rw [freeAbelianSheafHomEquiv_eq_app, freeAbelianSheafHomEquiv_eq_app φ]
  have h : (z • φ).hom = z • φ.hom := rfl
  rw [h, NatTrans.app_zsmul]
  exact AddCommGrpCat.hom_zsmul_apply _ _ _

variable [HasFiniteWidePullbacks C]

/-- The Čech differential of free abelian sheaves is the alternating sum of the images of
the face maps of the Čech nerve. -/
lemma cechFreeD_eq {U V : C} (f : V ⟶ U) (n : ℕ) :
    cechFreeD J f n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i) := by
  have h1 : cechFreeD J f n =
      (presheafToSheaf J AddCommGrpCat.{u + 1}).map
        ((cechFreePresheafComplex f).d (n + 1) n) := rfl
  have h2 : (cechFreePresheafComplex f).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        freeAbelianPresheafFunctor.map ((Arrow.mk f).cechNerve.δ i) := by
    refine (AlternatingFaceMapComplex.obj_d_eq _ n).trans ?_
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [SimplicialObject.whiskering_obj_obj_δ]
  rw [h1, h2, Functor.map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [Functor.map_zsmul]; rfl

end SectionsTranslation


section SectionsTranslation

variable {C : Type (u + 1)} [Category.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
variable [HasFiniteWidePullbacks C]

/-- Under `freeAbelianSheafHomEquiv`, precomposition with the Čech differential of free
abelian sheaves corresponds to the Čech differential on sections. -/
lemma freeAbelianSheafHomEquiv_cechFreeD_comp {U V : C} (f : V ⟶ U)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (n : ℕ) (ψ : cechFree J f n ⟶ F) :
    freeAbelianSheafHomEquiv (cechFreeD J f n ≫ ψ) =
      cechPresheafD f F.obj n (freeAbelianSheafHomEquiv ψ) := by
  rw [cechFreeD_eq, Preadditive.sum_comp]
  have h1 : ∀ i : Fin (n + 2),
      ((-1 : ℤ) ^ (i : ℕ) • (freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i)) ≫ ψ =
        (-1 : ℤ) ^ (i : ℕ) •
          ((freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i) ≫ ψ) :=
    fun i ↦ Preadditive.zsmul_comp _ _ _
  rw [Finset.sum_congr rfl fun i _ ↦ h1 i, freeAbelianSheafHomEquiv_sum]
  have h2 : ∀ i : Fin (n + 2),
      freeAbelianSheafHomEquiv ((-1 : ℤ) ^ (i : ℕ) •
          ((freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i) ≫ ψ)) =
        (-1 : ℤ) ^ (i : ℕ) •
          (F.obj.map ((Arrow.mk f).cechNerve.δ i).op (freeAbelianSheafHomEquiv ψ)) := by
    intro i
    rw [freeAbelianSheafHomEquiv_zsmul, freeAbelianSheafHomEquiv_naturality_left]
    rfl
  rw [Finset.sum_congr rfl fun i _ ↦ h2 i]
  have h3 : cechPresheafD f F.obj n (freeAbelianSheafHomEquiv ψ) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) • F.obj.map ((Arrow.mk f).cechNerve.δ i).op)
        (freeAbelianSheafHomEquiv ψ) := by
    rw [cechPresheafD]
    exact AddCommGrpCat.hom_sum_apply _ _ _
  rw [h3]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (AddCommGrpCat.hom_zsmul_apply _ _ _).symm

/-- The Čech complex of free abelian sheaves is exact in positive degrees; this holds
without any covering assumption on `f`. -/
lemma cechFree_exact_succ' {U V : C} (f : V ⟶ U) (n : ℕ) :
    (ShortComplex.mk (cechFreeD J f (n + 1)) (cechFreeD J f n)
      (cechFreeD_comp_d J f n)).Exact := by
  have hpsh : (ShortComplex.mk ((cechFreePresheafComplex f).d (n + 2) (n + 1))
      ((cechFreePresheafComplex f).d (n + 1) n)
      ((cechFreePresheafComplex f).d_comp_d _ _ _)).Exact := by
    apply shortComplex_exact_of_evaluation
    intro X
    obtain ⟨W⟩ := X
    exact cechFreeEval_exact_succ f W n
  exact hpsh.map (presheafToSheaf J AddCommGrpCat.{u + 1})

/-- A positive-degree Čech cocycle of an injective abelian sheaf on any site is a
coboundary. -/
lemma exists_cechPresheafD_eq {U V : C} (f : V ⟶ U)
    (I : Sheaf J AddCommGrpCat.{u + 1}) (hI : Injective I) (m : ℕ)
    (x : I.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋m + 1⦌))))
    (hx : cechPresheafD f I.obj (m + 1) x = 0) :
    ∃ y, cechPresheafD f I.obj m y = x := by
  haveI := hI
  have hφ : cechFreeD J f (m + 1) ≫ freeAbelianSheafHomEquiv.symm x = 0 := by
    apply freeAbelianSheafHomEquiv.injective
    rw [freeAbelianSheafHomEquiv_cechFreeD_comp, Equiv.apply_symm_apply, hx,
      freeAbelianSheafHomEquiv_zero]
  have hexact := cechFree_exact_succ' (J := J) f m
  refine ⟨freeAbelianSheafHomEquiv
    (hexact.descToInjective (freeAbelianSheafHomEquiv.symm x) hφ), ?_⟩
  rw [← freeAbelianSheafHomEquiv_cechFreeD_comp]
  have hψ : cechFreeD J f m ≫
      hexact.descToInjective (freeAbelianSheafHomEquiv.symm x) hφ =
        freeAbelianSheafHomEquiv.symm x :=
    hexact.comp_descToInjective (freeAbelianSheafHomEquiv.symm x) hφ
  rw [hψ, Equiv.apply_symm_apply]

end SectionsTranslation

/-! ### Objects carrying Čech nerve data

`IsCechNerveAt g n P` is data exhibiting `P` as the `n`-th object of the Čech nerve of
`g`, by means of `n + 1` projections and a base map together with a compatible
isomorphism to the wide pullback. Such data is stable under binary pullbacks
(`IsCechNerveAt.succ`), which is how the Čech nerve objects on the pro-étale site are
matched with cofiltered limits of Čech nerve objects on the étale site. -/

section CechIter

variable {D : Type w₂} [Category.{w₁} D] {V U : D}

variable (g : V ⟶ U) [∀ k : ℕ, HasWidePullback (Arrow.mk g).right
    (fun _ : Fin (k + 1) ↦ (Arrow.mk g).left) fun _ ↦ (Arrow.mk g).hom]


namespace IsCechNerveAt

variable {g} {n : ℕ} {P : D}


/-- A morphism satisfying the simplicial identities of the `i`-th face map is the `i`-th
face map. -/
lemma eq_face {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) {t : P' ⟶ P}
    (htπ : ∀ j, t ≫ h.π j = h'.π ((SimplexCategory.δ i).toOrderHom j))
    (htbase : t ≫ h.base = h'.base) :
    t = h'.face h i :=
  h.hom_ext (fun j ↦ by rw [htπ, face_π]) (by rw [htbase, face_base])


/-- The alternating sum of the face maps is conjugate to the Čech differential on
sections. -/
lemma faceD_eq {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    h'.faceD h F =
      F.map (h.iso.inv.op) ≫ cechPresheafD g F n ≫ F.map (h'.iso.hom.op) := by
  rw [faceD, cechPresheafD, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  rw [face, op_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc]

end IsCechNerveAt

/-- Restriction along an isomorphism followed by restriction along its inverse is the
identity, elementwise. -/
lemma map_op_hom_inv_apply {F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {X Y : D} (e : X ≅ Y)
    (t : F.obj (op Y)) :
    F.map (e.inv.op) (F.map (e.hom.op) t) = t := by
  have h : F.map (e.hom.op) ≫ F.map (e.inv.op) = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id]
  have := ConcreteCategory.congr_hom h t
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at this

/-- Restriction along the inverse of an isomorphism followed by restriction along the
isomorphism is the identity, elementwise. -/
lemma map_op_inv_hom_apply {F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {X Y : D} (e : X ≅ Y)
    (t : F.obj (op X)) :
    F.map (e.hom.op) (F.map (e.inv.op) t) = t := by
  have h : F.map (e.inv.op) ≫ F.map (e.hom.op) = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id]
  have := ConcreteCategory.congr_hom h t
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at this

end CechIter

end CategoryTheory

namespace AlgebraicGeometry
namespace Scheme
namespace AffineProEt

/-! ### The tower of iterated fibre products

We construct, for a morphism `q : W ⟶ U₀` of affine pro-étale objects presented as a
morphism of relative limit presentations, the tower of iterated fibre products of `W`
over `U₀`, simultaneously with relative limit presentations whose stages carry étale
Čech nerve data and with pro-étale Čech nerve data on the total spaces. -/

variable {S : Scheme.{u}}

section Tower

variable {W U₀ : S.AffineProEt} (q : W ⟶ U₀)
variable {A : Type u} [SmallCategory A]
variable (presU : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) U₀)
variable (presW : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) W)
variable (fW : presW.Hom presU)


namespace CechTower

variable {q presU presW fW} {n : ℕ}
variable (T' : CechTower q presU presW fW (n + 1)) (T : CechTower q presU presW fW n)


@[simp]
lemma faceHom_app (i : Fin (n + 2)) (a : A) :
    (AffineEtale.Spec S).map ((T'.faceHom T i).natTrans.app a) =
      (T'.ét a).face (T.ét a) i :=
  Functor.map_preimage _ _

lemma faceHom_app_comp_πSt (i : Fin (n + 2)) (a : A) (j : Fin (n + 1)) :
    (T'.faceHom T i).natTrans.app a ≫ T.πSt a j =
      T'.πSt a ((SimplexCategory.δ i).toOrderHom j) := by
  apply (AffineEtale.Spec S).map_injective
  rw [CategoryTheory.Functor.map_comp, faceHom_app, ← T.ét_π, IsCechNerveAt.face_π,
    T'.ét_π]

lemma faceHom_app_comp_bM (i : Fin (n + 2)) (a : A) :
    (T'.faceHom T i).natTrans.app a ≫ T.bM.natTrans.app a = T'.bM.natTrans.app a := by
  apply (AffineEtale.Spec S).map_injective
  rw [CategoryTheory.Functor.map_comp, faceHom_app, ← T.ét_base, IsCechNerveAt.face_base,
    T'.ét_base]

lemma faceHom_map_comp_πM (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (T'.faceHom T i).map ≫ T.πM j = T'.πM ((SimplexCategory.δ i).toOrderHom j) := by
  apply presW.isLimit.hom_ext
  intro a
  rw [Category.assoc, T.πM_π j a, T'.πM_π ((SimplexCategory.δ i).toOrderHom j) a,
    ← Category.assoc, (T'.faceHom T i).map_π a, Category.assoc,
    ← CategoryTheory.Functor.map_comp, faceHom_app_comp_πSt]

lemma faceHom_map_comp_bM (i : Fin (n + 2)) :
    (T'.faceHom T i).map ≫ T.bM.map = T'.bM.map := by
  apply presU.isLimit.hom_ext
  intro a
  rw [Category.assoc, T.bM.map_π a, ← Category.assoc, (T'.faceHom T i).map_π a,
    Category.assoc, ← CategoryTheory.Functor.map_comp, faceHom_app_comp_bM,
    T'.bM.map_π a]

lemma map_faceHom_map (i : Fin (n + 2)) :
    (AffineProEt.toProEt S).map ((T'.faceHom T i).map) = T'.pro.face T.pro i := by
  apply IsCechNerveAt.eq_face
  · intro j
    rw [T.pro_π, T'.pro_π, ← CategoryTheory.Functor.map_comp, faceHom_map_comp_πM]
  · rw [T.pro_base, T'.pro_base, ← CategoryTheory.Functor.map_comp, faceHom_map_comp_bM]

section Differentials

variable (I : Sheaf S.smallEtaleTopology Ab.{u + 1})


/-- The stage-wise Čech differentials intertwine the legs of the sections cocones. -/
lemma stageD_comp_ι (a : A) :
    T'.stageD T I a ≫ ProEt.sheafPullbackSectionsι I T'.presM a =
      ProEt.sheafPullbackSectionsι I T.presM a ≫ T'.proD T I := by
  rw [stageD, proD, IsCechNerveAt.faceD, IsCechNerveAt.faceD, Preadditive.sum_comp,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  rw [← faceHom_app, ← map_faceHom_map]
  exact ProEt.sheafPullbackSectionsι_naturality I (T'.faceHom T i) a

/-- The stage-wise Čech differentials commute with the transition maps of the
presentations. -/
lemma map_comp_stageD {a a' : A} (u : a ⟶ a') :
    I.obj.map ((AffineEtale.Spec S).map (T.presM.diag.map u)).op ≫ T'.stageD T I a =
      T'.stageD T I a' ≫
        I.obj.map ((AffineEtale.Spec S).map (T'.presM.diag.map u)).op := by
  rw [stageD, stageD, IsCechNerveAt.faceD, IsCechNerveAt.faceD, Preadditive.comp_sum,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  rw [← faceHom_app T' T i a, ← faceHom_app T' T i a', ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun t ↦ I.obj.map ((AffineEtale.Spec S).map t).op)
    ((T'.faceHom T i).natTrans.naturality u).symm

lemma stageD_eq (a : A) :
    T'.stageD T I a = I.obj.map ((T.ét a).iso.inv.op) ≫
      cechPresheafD ((AffineEtale.Spec S).map (fW.natTrans.app a)) I.obj n ≫
        I.obj.map ((T'.ét a).iso.hom.op) :=
  IsCechNerveAt.faceD_eq _ _ _

lemma proD_eq :
    T'.proD T I =
      ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map (T.pro.iso.inv.op) ≫
        cechPresheafD ((AffineProEt.toProEt S).map q)
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj n ≫
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map (T'.pro.iso.hom.op) :=
  IsCechNerveAt.faceD_eq _ _ _

end Differentials

end CechTower


end Tower

/-- Positive-degree Čech cocycles of the pullback of an injective abelian sheaf
along a surjection of affine pro-étale objects are coboundaries. -/
lemma exists_coboundary {W U₀ : S.AffineProEt} (q : W ⟶ U₀) (hq : Surjective q.left)
    (I : Sheaf S.smallEtaleTopology Ab.{u + 1}) (hI : Injective I) (m : ℕ)
    (φ : cechFree (ProEt.topology S) ((AffineProEt.toProEt S).map q) (m + 1) ⟶
      (ProEt.sheafPullback S Ab.{u + 1}).obj I)
    (hφ : cechFreeD (ProEt.topology S) ((AffineProEt.toProEt S).map q) (m + 1) ≫ φ = 0) :
    ∃ ψ : cechFree (ProEt.topology S) ((AffineProEt.toProEt S).map q) m ⟶
        (ProEt.sheafPullback S Ab.{u + 1}).obj I,
      φ = cechFreeD (ProEt.topology S) ((AffineProEt.toProEt S).map q) m ≫ ψ := by
  classical
  -- Step 1: a relative limit presentation of the singleton cover of `q`.
  have hsing : Presieve.singleton q ∈ (Precoverage.singleton S.AffineProEt ⊓
      MorphismProperty.precoverage fun _ _ f ↦ Surjective f.left) U₀ :=
    ⟨⟨W, q, rfl⟩, by rwa [MorphismProperty.singleton_mem_precoverage_iff]⟩
  obtain ⟨A, instA, instAcof, pack, -⟩ :=
    AffineProEt.singleton_inf_le_relativelyPresentable S U₀ hsing
  let i₀ : (Presieve.singleton q).preZeroHypercover.I₀ := ⟨⟨W, q⟩, Presieve.singleton.mk⟩
  let presU := pack.pres
  let presW := pack.pres₀ i₀
  let fW : presW.Hom presU := pack.f i₀
  have hfW : fW.map = q := pack.hf i₀
  -- The tower of iterated fibre products.
  let T : ∀ n, CechTower q presU presW fW n := cechTower hfW
  -- Step 2: the cocycle as a section of the pullback sheaf.
  set x := freeAbelianSheafHomEquiv φ with hx
  have hcoc : cechPresheafD ((AffineProEt.toProEt S).map q)
      ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj (m + 1) x = 0 := by
    rw [hx, ← freeAbelianSheafHomEquiv_cechFreeD_comp, hφ, freeAbelianSheafHomEquiv_zero]
  -- Step 3: descend the cocycle to an étale stage.
  haveI : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  set x' := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
    ((T (m + 1)).pro.iso.hom.op) x with hx'
  obtain ⟨aop, xa, hxa⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (CategoryTheory.forget Ab.{u + 1})
      (ProEt.isColimitSheafPullbackSectionsCocone I (T (m + 1)).presM)) x'
  set a₀ := aop.unop with ha₀
  have hxa' : ProEt.sheafPullbackSectionsι I (T (m + 1)).presM a₀ xa = x' := hxa
  -- The stage-level cocycle dies in the colimit.
  have hdie : ProEt.sheafPullbackSectionsι I (T (m + 2)).presM a₀
      ((T (m + 2)).stageD (T (m + 1)) I a₀ xa) = 0 := by
    have h1 := ConcreteCategory.congr_hom
      ((T (m + 2)).stageD_comp_ι (T (m + 1)) I a₀) xa
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    have h2 := ConcreteCategory.congr_hom ((T (m + 2)).proD_eq (T (m + 1)) I)
      (ProEt.sheafPullbackSectionsι I (T (m + 1)).presM a₀ xa)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
    rw [h1, h2, hxa', hx']
    have hcancel := map_op_hom_inv_apply (F := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj)
      ((T (m + 1)).pro.iso) x
    refine (congrArg (fun t ↦ ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
        ((T (m + 2)).pro.iso.hom.op) (cechPresheafD ((AffineProEt.toProEt S).map q)
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj (m + 1) t)) hcancel).trans
      ((congrArg (fun t ↦ ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
        ((T (m + 2)).pro.iso.hom.op) t) hcoc).trans (map_zero _))
  -- Step 4: the cocycle condition holds at a later stage.
  obtain ⟨kop, w, hw⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (CategoryTheory.forget Ab.{u + 1})
      (ProEt.isColimitSheafPullbackSectionsCocone I (T (m + 2)).presM))
    ((T (m + 2)).stageD (T (m + 1)) I a₀ xa)
    (0 : I.obj.obj
      (op ((AffineEtale.Spec S).obj ((T (m + 2)).presM.diag.obj a₀))))).mp
    (by
      have h0 : ProEt.sheafPullbackSectionsι I (T (m + 2)).presM a₀ (0 : I.obj.obj
          (op ((AffineEtale.Spec S).obj ((T (m + 2)).presM.diag.obj a₀)))) = 0 :=
        map_zero _
      exact hdie.trans h0.symm)
  set a₁ := kop.unop with ha₁
  set u : a₁ ⟶ a₀ := w.unop with hu
  set xa₁ := I.obj.map
    ((AffineEtale.Spec S).map ((T (m + 1)).presM.diag.map u)).op xa with hxa₁def
  have hxa₁ : ProEt.sheafPullbackSectionsι I (T (m + 1)).presM a₁ xa₁ = x' := by
    have h3 := ConcreteCategory.congr_hom
      (ProEt.map_sheafPullbackSectionsι I (T (m + 1)).presM u) xa
    rw [ConcreteCategory.comp_apply] at h3
    exact h3.trans hxa'
  have hw' : I.obj.map ((AffineEtale.Spec S).map ((T (m + 2)).presM.diag.map u)).op
      ((T (m + 2)).stageD (T (m + 1)) I a₀ xa) = 0 := by
    have h5 : I.obj.map ((AffineEtale.Spec S).map ((T (m + 2)).presM.diag.map u)).op
        ((T (m + 2)).stageD (T (m + 1)) I a₀ xa) =
          I.obj.map ((AffineEtale.Spec S).map ((T (m + 2)).presM.diag.map u)).op 0 := hw
    rw [map_zero] at h5
    exact h5
  have hcoc₁ : (T (m + 2)).stageD (T (m + 1)) I a₁ xa₁ = 0 := by
    have h4 := ConcreteCategory.congr_hom
      ((T (m + 2)).map_comp_stageD (T (m + 1)) I u) xa
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h4
    exact h4.trans hw'
  -- Step 5: solve the cocycle at the étale stage, using injectivity of `I`.
  set xé := I.obj.map (((T (m + 1)).ét a₁).iso.inv.op) xa₁ with hxé
  have hcocé : cechPresheafD ((AffineEtale.Spec S).map (fW.natTrans.app a₁)) I.obj
      (m + 1) xé = 0 := by
    have h6 := ConcreteCategory.congr_hom
      ((T (m + 2)).stageD_eq (T (m + 1)) I a₁) xa₁
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hcoc₁] at h6
    have h7 := congrArg (I.obj.map (((T (m + 2)).ét a₁).iso.inv.op)) h6
    rw [map_zero, map_op_hom_inv_apply] at h7
    exact h7.symm
  obtain ⟨yé, hyé⟩ := exists_cechPresheafD_eq
    ((AffineEtale.Spec S).map (fW.natTrans.app a₁)) I hI m xé hcocé
  set ya := I.obj.map (((T m).ét a₁).iso.hom.op) yé with hya
  have hstep : (T (m + 1)).stageD (T m) I a₁ ya = xa₁ := by
    have h8 := ConcreteCategory.congr_hom ((T (m + 1)).stageD_eq (T m) I a₁) ya
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hya,
      map_op_hom_inv_apply, hyé, hxé, map_op_inv_hom_apply] at h8
    exact h8
  -- Step 6: go back up to the pro-étale site.
  set y' := ProEt.sheafPullbackSectionsι I (T m).presM a₁ ya with hy'
  have hxy : x' = (T (m + 1)).proD (T m) I y' := by
    have h9 := ConcreteCategory.congr_hom ((T (m + 1)).stageD_comp_ι (T m) I a₁) ya
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hstep, hxa₁] at h9
    rw [hy']
    exact h9
  set y := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
    ((T m).pro.iso.inv.op) y' with hy
  refine ⟨freeAbelianSheafHomEquiv.symm y, ?_⟩
  apply freeAbelianSheafHomEquiv.injective
  rw [freeAbelianSheafHomEquiv_cechFreeD_comp, Equiv.apply_symm_apply, ← hx]
  have h10 : x = ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
      ((T (m + 1)).pro.iso.inv.op) x' := by
    rw [hx', map_op_hom_inv_apply]
  have h11 := ConcreteCategory.congr_hom ((T (m + 1)).proD_eq (T m) I) y'
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h11
  rw [h10, hxy, h11]
  refine (map_op_hom_inv_apply (F := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj)
      ((T (m + 1)).pro.iso) _).trans ?_
  exact congrArg (fun t ↦ cechPresheafD ((AffineProEt.toProEt S).map q)
    ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj m t) hy.symm

end AffineProEt
end Scheme
end AlgebraicGeometry


theorem solution.{sol_u1} : type_of% @AlgebraicGeometry.Scheme.AffineProEt.exists_coboundary.{sol_u1} := @AlgebraicGeometry.Scheme.AffineProEt.exists_coboundary.{sol_u1}
