-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.ProEt.bijective_extLimitToLimit_of_isMittagLeffler
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:39:53.208372+00:00
-- url     : https://prove2.me/submissions/1f59c022-c866-4bbc-945b-e024326b61e6

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
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
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
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.CofilteredSystem
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
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
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
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
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
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
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
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_SequentialLimit
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_AffineTransitionLimit
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Extensive
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineEtale
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineRefinement
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_EtaleCohomology_Lib
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_Small
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib
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
import Definitions.Def_ProEtale_Topology_Comparison_Acyclicity
import Definitions.Def_ProEtale_Topology_Comparison_Affine
import Definitions.Def_ProEtale_Topology_Comparison_Affine_Lib
import Definitions.Def_ProEtale_Topology_Comparison_CechColimit
import Definitions.Def_ProEtale_Topology_Comparison_CohomologyComparison
import Definitions.Def_ProEtale_Topology_Comparison_CohomologyComparison_Lib
import Definitions.Def_ProEtale_Topology_Comparison_ContinuousComparison
import Definitions.Def_ProEtale_Topology_Comparison_ContinuousComparison_Lib
import Definitions.Def_ProEtale_Topology_Comparison_FreeSheaf
import Definitions.Def_ProEtale_Topology_Comparison_RepleteExact
import Definitions.Def_ProEtale_Topology_Comparison_RepleteExact_Lib
import Definitions.Def_ProEtale_Topology_Comparison_SectionsColimit
import Definitions.Def_ProEtale_Topology_Comparison_WeaklyContractible
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
import Definitions.Def_ProEtale_Topology_Comparison_LimitComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_shortExact_limMap
import Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_subsingleton_H_limit_of_isSplitEpi
import Theorems.Thm_AlgebraicGeometry_Scheme_ProEt_subsingleton_H_sheafPullback_injective
import Theorems.Thm_CategoryTheory_Abelian_Ext_bijective_extLimitToLimit_zero
import Theorems.Thm_CategoryTheory_Abelian_Ext_exists_of_levelDelta_app_eq_zero
import Theorems.Thm_CategoryTheory_Abelian_Ext_exists_transition_preimage_ker
import Theorems.Thm_CategoryTheory_Abelian_Ext_injective_levelDelta_app
import Theorems.Thm_CategoryTheory_Abelian_Ext_isMittagLeffler_forget_of_app_bijective
import Theorems.Thm_CategoryTheory_Abelian_Ext_isMittagLeffler_of_exact
import Theorems.Thm_CategoryTheory_Abelian_Ext_levelDelta_comp_app_zero
import Theorems.Thm_CategoryTheory_Abelian_Ext_surjective_levelDelta_app
import Theorems.Thm_CategoryTheory_Abelian_Ext_surjective_limMap_and_exact
import Theorems.Thm_CategoryTheory_SequentialSystem_epi_transition_of_epi_app
import Theorems.Thm_CategoryTheory_SequentialSystem_epi_transition_whisker
import Theorems.Thm_CategoryTheory_SequentialSystem_injective_obj_of_injective
import Theorems.Thm_CategoryTheory_SequentialSystem_isSplitEpi_transition_of_injective

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# The canonical map from cohomology of a limit to the limit of cohomologies

For `Z : A` and an inverse system `G : ℕᵒᵖ ⥤ A` in an abelian category with `Ext`-groups,
the limit projections induce a canonical map

`extLimitToLimit : Ext Z (limit G) m ⟶ limit (n ↦ Ext Z (Gₙ) m)`.

In degree `0` this map is bijective by the universal property of the limit
(`bijective_extLimitToLimit_zero`). In positive degrees it is in general neither
injective nor surjective (the failure is a `lim¹`-term, Jannsen); we prove that it *is*
bijective for the systems relevant to the `ℓ`-adic comparison: for
`G = F ⋙ ν^*` the pullback of a system `F` of abelian sheaves on the small étale site
of a scheme `S` with epimorphic transition maps, and `Z` the constant pro-étale sheaf
`ℤ`, the map is bijective in degree `i + 1` under the Mittag-Leffler condition for the
degree-`i` level system
(`AlgebraicGeometry.Scheme.ProEt.bijective_extLimitToLimit_of_isMittagLeffler`).

This is the canonical-map refinement of
`AlgebraicGeometry.Scheme.nonempty_continuousH_addEquiv_H_limit`
(`Proetale/Topology/Comparison/ContinuousComparison.lean`) combined with
`CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem`
(`Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean`): instead
of comparing both sides abstractly with continuous étale cohomology `Ext (Δℤ) F`, we
compare them directly by a fused dimension-shifting argument, keeping track of the
canonical map. The connecting-map ladders on the source side are provided by
`ShortComplex.ShortExact.extClass_naturality` applied to the limit projections, which
constitute a morphism of short complexes from the limit sequence to each level sequence
(`extLimitToLimit_levelDelta`).
-/

universe w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory
namespace Abelian
namespace Ext

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

section Def

variable (Z : A) (G : ℕᵒᵖ ⥤ A) [HasLimit G]


variable {Z G} in
/-- The components of the canonical comparison map are postcomposition with the limit
projections. -/
lemma π_extLimitToLimit_apply (m : ℕ) (k : ℕᵒᵖ) (x : Ext Z (limit G) m) :
    ConcreteCategory.hom (limit.π (levelSystem Z G m) k)
      (ConcreteCategory.hom (extLimitToLimit Z G m) x) =
      x.comp (Ext.mk₀ (limit.π G k)) (add_zero m) :=
  (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (extLimitToLimit_π Z G m k) x)

variable {G} in
/-- Naturality of the canonical comparison map: postcomposition with `limMap τ`
corresponds to the limit of the levelwise postcompositions. -/
lemma extLimitToLimit_limMap {G' : ℕᵒᵖ ⥤ A} [HasLimit G'] (τ : G ⟶ G')
    (m : ℕ) (x : Ext Z (limit G) m) :
    ConcreteCategory.hom (limMap (Functor.whiskerRight τ (extFunctorObj Z m)))
        (ConcreteCategory.hom (extLimitToLimit Z G m) x) =
      ConcreteCategory.hom (extLimitToLimit Z G' m)
        (x.comp (Ext.mk₀ (limMap τ)) (add_zero m)) := by
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  have h1 : ConcreteCategory.hom (limit.π (G' ⋙ extFunctorObj Z m) k)
      (ConcreteCategory.hom (limMap (Functor.whiskerRight τ (extFunctorObj Z m)))
        (ConcreteCategory.hom (extLimitToLimit Z G m) x)) =
      ConcreteCategory.hom ((Functor.whiskerRight τ (extFunctorObj Z m)).app k)
        (ConcreteCategory.hom (limit.π (levelSystem Z G m) k)
          (ConcreteCategory.hom (extLimitToLimit Z G m) x)) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom
        (limMap_π (Functor.whiskerRight τ (extFunctorObj Z m)) k) _).trans
        (ConcreteCategory.comp_apply _ _ _))
  have h2 : ConcreteCategory.hom (limit.π (G' ⋙ extFunctorObj Z m) k)
      (ConcreteCategory.hom (extLimitToLimit Z G' m)
        (x.comp (Ext.mk₀ (limMap τ)) (add_zero m))) =
      (x.comp (Ext.mk₀ (limMap τ)) (add_zero m)).comp
        (Ext.mk₀ (limit.π G' k)) (add_zero m) :=
    π_extLimitToLimit_apply m k _
  rw [h1, h2, π_extLimitToLimit_apply]
  calc ConcreteCategory.hom ((Functor.whiskerRight τ (extFunctorObj Z m)).app k)
        (x.comp (Ext.mk₀ (limit.π G k)) (add_zero m))
      = (x.comp (Ext.mk₀ (limit.π G k)) (add_zero m)).comp
          (Ext.mk₀ (τ.app k)) (add_zero m) := rfl
    _ = x.comp ((Ext.mk₀ (limit.π G k)).comp (Ext.mk₀ (τ.app k)) (add_zero 0))
          (add_zero m) := Ext.comp_assoc_of_third_deg_zero _ _ _ _
    _ = x.comp (Ext.mk₀ (limMap τ ≫ limit.π G' k)) (add_zero m) := by
        rw [Ext.mk₀_comp_mk₀, ← limMap_π]
    _ = x.comp ((Ext.mk₀ (limMap τ)).comp (Ext.mk₀ (limit.π G' k)) (add_zero 0))
          (add_zero m) := by rw [Ext.mk₀_comp_mk₀]
    _ = (x.comp (Ext.mk₀ (limMap τ)) (add_zero m)).comp
          (Ext.mk₀ (limit.π G' k)) (add_zero m) :=
        (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

/-- The transition maps of the degree-zero level system of a system with split
epimorphic transition maps are surjective, by composing with the splittings. -/
lemma surjective_transition_levelSystem_of_isSplitEpi (G : ℕᵒᵖ ⥤ A)
    (hG : ∀ n, IsSplitEpi (SequentialSystem.transition G n)) (n : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      (SequentialSystem.transition (levelSystem Z G 0) n)) := by
  obtain ⟨σ⟩ := (hG n).exists_splitEpi
  intro y
  refine ⟨y.comp (Ext.mk₀ σ.section_) (add_zero 0), ?_⟩
  have h1 : ConcreteCategory.hom (SequentialSystem.transition (levelSystem Z G 0) n)
      (y.comp (Ext.mk₀ σ.section_) (add_zero 0)) =
      (y.comp (Ext.mk₀ σ.section_) (add_zero 0)).comp
        (Ext.mk₀ (SequentialSystem.transition G n)) (add_zero 0) := rfl
  rw [h1, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, σ.id, Ext.comp_mk₀_id]

end Def


section Delta

variable [HasLimitsOfShape ℕᵒᵖ A]

variable (Z : A) {T : ShortComplex (ℕᵒᵖ ⥤ A)}


/-- **The canonical comparison map intertwines the connecting maps**: for a short exact
sequence `T` of inverse systems which is levelwise short exact and whose limit sequence
is short exact, postcomposition with the extension class of the limit sequence followed
by the canonical comparison map agrees with the canonical comparison map followed by
the limit of the levelwise connecting maps. -/
lemma extLimitToLimit_levelDelta
    (hTk : ∀ k : ℕᵒᵖ, (T.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact)
    (hTL : (T.map lim).ShortExact) (m : ℕ) (x : Ext Z (limit T.X₃) m) :
    ConcreteCategory.hom (limMap (levelDelta Z hTk m))
        (ConcreteCategory.hom (extLimitToLimit Z T.X₃ m) x) =
      ConcreteCategory.hom (extLimitToLimit Z T.X₁ (m + 1))
        (x.comp hTL.extClass rfl) := by
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  have h1 : ConcreteCategory.hom (limit.π (levelSystem Z T.X₁ (m + 1)) k)
      (ConcreteCategory.hom (limMap (levelDelta Z hTk m))
        (ConcreteCategory.hom (extLimitToLimit Z T.X₃ m) x)) =
      ConcreteCategory.hom ((levelDelta Z hTk m).app k)
        (ConcreteCategory.hom (limit.π (levelSystem Z T.X₃ m) k)
          (ConcreteCategory.hom (extLimitToLimit Z T.X₃ m) x)) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (limMap_π (levelDelta Z hTk m) k) _).trans
        (ConcreteCategory.comp_apply _ _ _))
  have hnat : hTL.extClass.comp (Ext.mk₀ (limit.π T.X₁ k)) (add_zero 1) =
      (Ext.mk₀ (limit.π T.X₃ k)).comp (hTk k).extClass (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality hTL (hTk k) (limitπShortComplexHom T k)
  rw [h1, π_extLimitToLimit_apply, π_extLimitToLimit_apply]
  calc ConcreteCategory.hom ((levelDelta Z hTk m).app k)
        (x.comp (Ext.mk₀ (limit.π T.X₃ k)) (add_zero m))
      = (x.comp (Ext.mk₀ (limit.π T.X₃ k)) (add_zero m)).comp (hTk k).extClass rfl := rfl
    _ = x.comp ((Ext.mk₀ (limit.π T.X₃ k)).comp (hTk k).extClass (zero_add 1)) rfl :=
        Ext.comp_assoc_of_second_deg_zero _ _ _ _
    _ = x.comp (hTL.extClass.comp (Ext.mk₀ (limit.π T.X₁ k)) (add_zero 1)) rfl := by
        rw [hnat]
    _ = (x.comp hTL.extClass rfl).comp (Ext.mk₀ (limit.π T.X₁ k)) (add_zero (m + 1)) :=
        (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

end Delta

end Ext
end Abelian
end CategoryTheory

namespace AlgebraicGeometry
namespace Scheme
namespace ProEt

open CategoryTheory.Abelian

variable {S : Scheme.{u}}

/-- **`Ext` into the limit of a pulled-back system is the limit of the levelwise
`Ext`-groups, under a Mittag-Leffler hypothesis** (the `lim¹`-free case of Jannsen's
exact sequence, in its canonical-map form): for an inverse system `F` of abelian
sheaves on the small étale site of `S` with epimorphic transition maps, the canonical
map from the pro-étale cohomology of `lim ν^*Fₙ` in degree `i + 1` to the inverse limit
of the pro-étale cohomology groups of the `ν^*Fₙ` is bijective, provided the degree-`i`
level system satisfies the Mittag-Leffler condition. -/
theorem bijective_extLimitToLimit_of_isMittagLeffler
    (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1})
    (hF : ∀ n, Epi (SequentialSystem.transition F n)) (i : ℕ)
    (hML : (((F ⋙ ProEt.sheafPullback S Ab.{u + 1}) ⋙
      extFunctorObj (proetaleConstantUnit S) i) ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler) :
    Function.Bijective (ConcreteCategory.hom (Ext.extLimitToLimit
      (proetaleConstantUnit S) (F ⋙ ProEt.sheafPullback S Ab.{u + 1}) (i + 1))) := by
  -- Fused dimension shift: canonical-map refinement of
  -- `nonempty_continuousH_addEquiv_H_limit` composed with
  -- `Ext.nonempty_addEquiv_limit_levelSystem`. Dimension shifting along
  -- `0 → F → I → Q → 0`, with the connecting ladders on the source side provided by
  -- `Ext.extLimitToLimit_levelDelta` and on the target side by `Ext.levelDelta`.
  induction i generalizing F with
  | zero =>
    -- Setup: the short exact sequence `0 → F → I → Q → 0` and its pullback `T`.
    let SC : ShortComplex (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
      ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    haveI hinj : Injective SC.X₂ := inferInstanceAs (Injective (Injective.under F))
    let T : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}) :=
      SC.map ((Functor.whiskeringRight ℕᵒᵖ (Sheaf S.smallEtaleTopology Ab.{u + 1})
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj (ProEt.sheafPullback S Ab.{u + 1}))
    have hTk : ∀ k : ℕᵒᵖ, (T.map ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj k)).ShortExact := by
      intro k
      haveI : PreservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI : PreservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI := comp_preservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      haveI := comp_preservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      exact hSC.map_of_exact ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k ⋙ ProEt.sheafPullback S Ab.{u + 1})
    have hX₁ : ∀ n, Epi (SequentialSystem.transition T.X₁ n) := by
      intro n
      haveI : (ProEt.sheafPullback S Ab.{u + 1}).PreservesEpimorphisms :=
        Functor.preservesEpimorphisms_of_adjunction (ProEt.sheafAdjunction S Ab.{u + 1})
      exact SequentialSystem.epi_transition_whisker (ProEt.sheafPullback S Ab.{u + 1}) hF n
    have hTL : (T.map lim).ShortExact := shortExact_limMap hTk hX₁
    have hsplit : ∀ n, IsSplitEpi (SequentialSystem.transition T.X₂ n) := fun n ↦ by
      haveI := SequentialSystem.isSplitEpi_transition_of_injective SC.X₂ n
      exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
        (SequentialSystem.transition SC.X₂ n)))
    have hsubk : ∀ (k : ℕᵒᵖ) (q : ℕ), Subsingleton
        (Ext (proetaleConstantUnit S) (T.X₂.obj k) (q + 1)) := by
      intro k q
      haveI : Injective (SC.X₂.obj k) :=
        SequentialSystem.injective_obj_of_injective SC.X₂ k.unop
      exact subsingleton_H_sheafPullback_injective (SC.X₂.obj k) (q + 1) q.succ_pos
    have h₂lim : ∀ q, 0 < q → Subsingleton
        (Sheaf.H (limit (Injective.under F ⋙ ProEt.sheafPullback S Ab.{u + 1})) q) := by
      refine subsingleton_H_limit_of_isSplitEpi _ (fun n ↦ ?_) (fun k q hq ↦ ?_)
      · haveI := SequentialSystem.isSplitEpi_transition_of_injective (Injective.under F) n
        exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
          (SequentialSystem.transition (Injective.under F) n)))
      · haveI : Injective ((Injective.under F).obj k) :=
          SequentialSystem.injective_obj_of_injective (Injective.under F) k.unop
        exact subsingleton_H_sheafPullback_injective ((Injective.under F).obj k) q hq
    -- The Mittag-Leffler exchange of limit and cokernel on the level systems.
    obtain ⟨hsurjL, hexactL⟩ := Ext.surjective_limMap_and_exact
      (Functor.whiskerRight T.g (extFunctorObj (proetaleConstantUnit S) 0))
      (Ext.levelDelta (proetaleConstantUnit S) hTk 0)
      (Ext.levelDelta_comp_app_zero (proetaleConstantUnit S) hTk 0)
      (Ext.exists_of_levelDelta_app_eq_zero (proetaleConstantUnit S) hTk 0)
      (fun k ↦ Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk 0 k (hsubk k 0))
      (Ext.surjective_transition_levelSystem_of_isSplitEpi
        (proetaleConstantUnit S) T.X₂ hsplit)
      (Ext.exists_transition_preimage_ker (proetaleConstantUnit S) hTk hML)
    constructor
    · -- Injectivity: a class killed by the canonical map is `δ` of a section which
      -- lifts to the middle object, hence vanishes.
      rw [injective_iff_map_eq_zero]
      intro ξ hξ
      obtain ⟨s, rfl⟩ := Ext.deltaZero_surjective hTL (proetaleConstantUnit S)
        (h₂lim 1 one_pos) ξ
      rw [Ext.deltaZero_apply] at hξ
      have h0 : ConcreteCategory.hom (limMap (Ext.levelDelta (proetaleConstantUnit S)
          hTk 0)) (ConcreteCategory.hom (Ext.extLimitToLimit (proetaleConstantUnit S)
            T.X₃ 0) (Ext.mk₀ s)) = 0 := by
        rw [Ext.extLimitToLimit_levelDelta (proetaleConstantUnit S) hTk hTL 0 (Ext.mk₀ s)]
        exact hξ
      obtain ⟨b, hb⟩ := hexactL _ h0
      obtain ⟨w', hw'⟩ := (Ext.bijective_extLimitToLimit_zero
        (proetaleConstantUnit S) T.X₂).2 b
      obtain ⟨w, rfl⟩ := (Ext.mk₀_bijective (proetaleConstantUnit S) (limit T.X₂)).2 w'
      rw [← hw', Ext.extLimitToLimit_limMap (proetaleConstantUnit S) T.g 0 (Ext.mk₀ w),
        Ext.mk₀_comp_mk₀] at hb
      have hs : w ≫ limMap T.g = s :=
        (Ext.mk₀_bijective _ _).1
          ((Ext.bijective_extLimitToLimit_zero (proetaleConstantUnit S) T.X₃).1 hb)
      exact (Ext.deltaZero_apply_eq_zero_iff hTL _ s).2 ⟨w, hs⟩
    · -- Surjectivity: lift through the surjection of limits and the degree-zero
      -- bijectivity, then apply the connecting ladder.
      intro t
      obtain ⟨c, hc⟩ := hsurjL t
      obtain ⟨x, hx⟩ := (Ext.bijective_extLimitToLimit_zero
        (proetaleConstantUnit S) T.X₃).2 c
      refine ⟨x.comp hTL.extClass rfl, ?_⟩
      exact Eq.trans
        (Ext.extLimitToLimit_levelDelta (proetaleConstantUnit S) hTk hTL 0 x).symm
        (Eq.trans (congrArg (ConcreteCategory.hom
          (limMap (Ext.levelDelta (proetaleConstantUnit S) hTk 0))) hx) hc)
  | succ i IH =>
    -- Setup as in the base case.
    let SC : ShortComplex (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
      ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    haveI hinj : Injective SC.X₂ := inferInstanceAs (Injective (Injective.under F))
    let T : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}) :=
      SC.map ((Functor.whiskeringRight ℕᵒᵖ (Sheaf S.smallEtaleTopology Ab.{u + 1})
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj (ProEt.sheafPullback S Ab.{u + 1}))
    have hTk : ∀ k : ℕᵒᵖ, (T.map ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj k)).ShortExact := by
      intro k
      haveI : PreservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI : PreservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI := comp_preservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      haveI := comp_preservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      exact hSC.map_of_exact ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k ⋙ ProEt.sheafPullback S Ab.{u + 1})
    have hX₁ : ∀ n, Epi (SequentialSystem.transition T.X₁ n) := by
      intro n
      haveI : (ProEt.sheafPullback S Ab.{u + 1}).PreservesEpimorphisms :=
        Functor.preservesEpimorphisms_of_adjunction (ProEt.sheafAdjunction S Ab.{u + 1})
      exact SequentialSystem.epi_transition_whisker (ProEt.sheafPullback S Ab.{u + 1}) hF n
    have hTL : (T.map lim).ShortExact := shortExact_limMap hTk hX₁
    have hsplit : ∀ n, IsSplitEpi (SequentialSystem.transition T.X₂ n) := fun n ↦ by
      haveI := SequentialSystem.isSplitEpi_transition_of_injective SC.X₂ n
      exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
        (SequentialSystem.transition SC.X₂ n)))
    have hsubk : ∀ (k : ℕᵒᵖ) (q : ℕ), Subsingleton
        (Ext (proetaleConstantUnit S) (T.X₂.obj k) (q + 1)) := by
      intro k q
      haveI : Injective (SC.X₂.obj k) :=
        SequentialSystem.injective_obj_of_injective SC.X₂ k.unop
      exact subsingleton_H_sheafPullback_injective (SC.X₂.obj k) (q + 1) q.succ_pos
    have h₂lim : ∀ q, 0 < q → Subsingleton
        (Sheaf.H (limit (Injective.under F ⋙ ProEt.sheafPullback S Ab.{u + 1})) q) := by
      refine subsingleton_H_limit_of_isSplitEpi _ (fun n ↦ ?_) (fun k q hq ↦ ?_)
      · haveI := SequentialSystem.isSplitEpi_transition_of_injective (Injective.under F) n
        exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
          (SequentialSystem.transition (Injective.under F) n)))
      · haveI : Injective ((Injective.under F).obj k) :=
          SequentialSystem.injective_obj_of_injective (Injective.under F) k.unop
        exact subsingleton_H_sheafPullback_injective ((Injective.under F).obj k) q hq
    -- Transport the Mittag-Leffler hypothesis to the cokernel system at degree `i`.
    have hMLQ : (Ext.levelSystem (proetaleConstantUnit S) T.X₃ i ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler := by
      obtain _ | j := i
      · exact Ext.isMittagLeffler_of_exact
          (Functor.whiskerRight T.g (extFunctorObj (proetaleConstantUnit S) 0))
          (Ext.levelDelta (proetaleConstantUnit S) hTk 0)
          (Ext.exists_of_levelDelta_app_eq_zero (proetaleConstantUnit S) hTk 0)
          (fun k ↦ Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk 0 k
            (hsubk k 0))
          (Ext.surjective_transition_levelSystem_of_isSplitEpi
            (proetaleConstantUnit S) T.X₂ hsplit)
          hML
      · exact Ext.isMittagLeffler_forget_of_app_bijective
          (Ext.levelDelta (proetaleConstantUnit S) hTk (j + 1))
          (fun k ↦ ⟨Ext.injective_levelDelta_app (proetaleConstantUnit S) hTk j k
              (hsubk k j),
            Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk (j + 1) k
              (hsubk k (j + 1))⟩)
          hML
    -- The cokernel system has epimorphic transition maps.
    have hQepi : ∀ n, Epi (SequentialSystem.transition SC.X₃ n) := by
      have hIepi : ∀ n, Epi (SequentialSystem.transition SC.X₂ n) := fun n ↦
        haveI := SequentialSystem.isSplitEpi_transition_of_injective
          (Injective.under F) n
        inferInstanceAs (Epi (SequentialSystem.transition (Injective.under F) n))
      haveI : Epi SC.g := inferInstanceAs (Epi (cokernel.π (Injective.ι F)))
      exact SequentialSystem.epi_transition_of_epi_app SC.g (fun k ↦ inferInstance) hIepi
    have hbij3 := IH SC.X₃ hQepi hMLQ
    -- The connecting maps are bijective on both sides.
    have hconn : Function.Bijective (fun x : Ext (proetaleConstantUnit S)
        (limit T.X₃) (i + 1) ↦ x.comp hTL.extClass rfl) :=
      (Ext.connectingEquiv hTL (proetaleConstantUnit S) i
        (h₂lim (i + 1) i.succ_pos) (h₂lim (i + 2) (by omega))).bijective
    haveI : ∀ k, IsIso ((Ext.levelDelta (proetaleConstantUnit S) hTk (i + 1)).app k) := by
      intro k
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ⟨Ext.injective_levelDelta_app (proetaleConstantUnit S) hTk i k (hsubk k i),
        Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk (i + 1) k
          (hsubk k (i + 1))⟩
    haveI : IsIso (Ext.levelDelta (proetaleConstantUnit S) hTk (i + 1)) :=
      NatIso.isIso_of_isIso_app _
    have hlimδ : Function.Bijective (ConcreteCategory.hom
        (limMap (Ext.levelDelta (proetaleConstantUnit S) hTk (i + 1)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    -- Conclude via the commuting square `Ext.extLimitToLimit_levelDelta`.
    have hsq : (ConcreteCategory.hom (Ext.extLimitToLimit (proetaleConstantUnit S)
        T.X₁ (i + 2))) ∘ (fun x : Ext (proetaleConstantUnit S) (limit T.X₃) (i + 1) ↦
          x.comp hTL.extClass rfl) =
        (ConcreteCategory.hom (limMap (Ext.levelDelta (proetaleConstantUnit S)
          hTk (i + 1)))) ∘ (ConcreteCategory.hom (Ext.extLimitToLimit
            (proetaleConstantUnit S) T.X₃ (i + 1))) :=
      funext fun x ↦
        (Ext.extLimitToLimit_levelDelta (proetaleConstantUnit S) hTk hTL (i + 1) x).symm
    have hcomp : Function.Bijective ((ConcreteCategory.hom
        (Ext.extLimitToLimit (proetaleConstantUnit S) T.X₁ (i + 2))) ∘
        (fun x : Ext (proetaleConstantUnit S) (limit T.X₃) (i + 1) ↦
          x.comp hTL.extClass rfl)) := by
      rw [hsq]
      exact hlimδ.comp hbij3
    exact (Function.Bijective.of_comp_iff _ hconn).mp hcomp

end ProEt
end Scheme
end AlgebraicGeometry


theorem solution.{sol_u1} : type_of% @AlgebraicGeometry.Scheme.ProEt.bijective_extLimitToLimit_of_isMittagLeffler.{sol_u1} := @AlgebraicGeometry.Scheme.ProEt.bijective_extLimitToLimit_of_isMittagLeffler.{sol_u1}
