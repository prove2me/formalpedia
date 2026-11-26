-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.AffineProEt.isIso_sigmaDesc_freeAbelianSheafFunctor_map
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:38:11.126131+00:00
-- url     : https://prove2.me/submissions/bf8f0569-1481-4b50-8599-4f4dd596b465

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
import Definitions.Def_ProEtale_Topology_Comparison_CechColimit
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
import Definitions.Def_ProEtale_Topology_Comparison_Acyclicity
import Theorems.Thm_CategoryTheory_GrothendieckTopology_W_whiskerRight_free

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

/-!
# Acyclicity of pullbacks of injective sheaves on affine pro-étale objects

For an injective abelian sheaf `I` on the small étale site of a scheme `S`, the pullback
`ν^*I` to the pro-étale site has vanishing higher cohomology on every affine pro-étale
object. This is the key analytic input in the comparison of étale and pro-étale cohomology
([BS15, proof of Corollary 5.1.6]).

The proof is via Cartan's criterion (`CategoryTheory.Sheaf.ext_free_eq_zero_of_cech`):
every covering sieve of an affine pro-étale object refines through a single surjection
`q : W ⟶ U` between affine pro-étale objects which admits a relative limit presentation by
surjective étale covers at finite levels; the Čech complex of `ν^*I` along `q` is the
filtered colimit of the Čech complexes of `I` along the finite-level covers, each of which
is exact because `I` is injective.
-/

universe u

open CategoryTheory Limits Opposite Abelian

open scoped Simplicial

namespace AlgebraicGeometry
namespace Scheme

variable {S : Scheme.{u}}

namespace AffineProEt


/-- Points of pullbacks in the pro-étale site surject onto compatible pairs of points. -/
lemma _root_.AlgebraicGeometry.Scheme.ProEt.exists_left_base_preimage
    {P X Y Z : S.ProEt} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X.left) (y : Y.left)
    (hxy : f.left.base x = g.left.base y) :
    ∃ p : P.left, fst.left.base p = x ∧ snd.left.base p = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  have hL : IsPullback fst.left snd.left f.left g.left :=
    h.map (ProEt.forget S ⋙ Over.forget S)
  refine ⟨hL.isoPullback.inv.base z, ?_, ?_⟩
  · calc fst.left.base (hL.isoPullback.inv.base z)
        = (hL.isoPullback.inv ≫ fst.left).base z := rfl
      _ = (pullback.fst f.left g.left).base z := by rw [hL.isoPullback_inv_fst]
      _ = x := hz₁
  · calc snd.left.base (hL.isoPullback.inv.base z)
        = (hL.isoPullback.inv ≫ snd.left).base z := rfl
      _ = (pullback.snd f.left g.left).base z := by rw [hL.isoPullback_inv_snd]
      _ = y := hz₂


/-- The canonical map from the coproduct of the free abelian sheaves on finitely many
disjoint open pieces covering `W` to the free abelian sheaf on `W` is an isomorphism:
the corresponding map of presheaves of types is locally bijective. -/
lemma isIso_sigmaDesc_freeAbelianSheafFunctor_map {W : S.AffineProEt}
    {ι : Type u} (V : ι → S.AffineProEt) (j : ∀ k, V k ⟶ W)
    (hoi : ∀ k, IsOpenImmersion (j k).left)
    (hcov : ∀ x : W.left, ∃ k, x ∈ Set.range ((j k).left.base))
    (hdisj : Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
      (Set.range ((j l).left.base))) :
    IsIso (Sigma.desc fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).map
      ((AffineProEt.toProEt S).map (j k))) := by
  classical
  -- The comparison map of presheaves of types from the coproduct of the pieces to `W`.
  let y : ι → ((S.ProEt)ᵒᵖ ⥤ Type (u + 1)) :=
    fun k ↦ uliftYoneda.{u + 1}.obj ((AffineProEt.toProEt S).obj (V k))
  let φ : (∐ y) ⟶ uliftYoneda.{u + 1}.obj ((AffineProEt.toProEt S).obj W) :=
    Sigma.desc fun k ↦ uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))
  -- Sections of the coproduct come from the components.
  have jointly_surj : ∀ (T : (S.ProEt)ᵒᵖ) (x : ToType ((∐ y).obj T)),
      ∃ (k : ι) (z : ToType ((y k).obj T)), (Sigma.ι y k).app T z = x := by
    intro T x
    obtain ⟨⟨k⟩, z, hz⟩ := Types.jointly_surjective
      (Discrete.functor y ⋙ (CategoryTheory.evaluation (S.ProEt)ᵒᵖ (Type (u + 1))).obj T)
      (isColimitOfPreserves ((CategoryTheory.evaluation (S.ProEt)ᵒᵖ (Type (u + 1))).obj T)
        (colimit.isColimit (Discrete.functor y))) x
    exact ⟨k, z, hz⟩
  -- The comparison map evaluated on a component.
  have happ : ∀ (k : ι) (T : (S.ProEt)ᵒᵖ) (z : ToType ((y k).obj T)),
      φ.app T ((Sigma.ι y k).app T z) =
        (uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))).app T z := by
    intro k T z
    have h := NatTrans.congr_app (Sigma.ι_desc
      (f := y) (fun k ↦ uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))) k) T
    calc φ.app T ((Sigma.ι y k).app T z)
        = ((Sigma.ι y k).app T ≫ φ.app T) z := (ConcreteCategory.comp_apply _ _ _).symm
      _ = ((Sigma.ι y k ≫ φ).app T) z := by rw [NatTrans.comp_app]
      _ = (uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))).app T z :=
          ConcreteCategory.congr_hom h z
  -- The comparison map is locally surjective: the pieces pull back to a Zariski cover.
  haveI : Presheaf.IsLocallySurjective (ProEt.topology S) φ := by
    constructor
    intro T s
    have hpboi : ∀ k, IsOpenImmersion
        (pullback.fst s.down ((AffineProEt.toProEt S).map (j k))).left := by
      intro k
      exact MorphismProperty.of_isPullback
        (((IsPullback.of_hasPullback s.down ((AffineProEt.toProEt S).map (j k))).flip).map
          (ProEt.forget S ⋙ Over.forget S)) (hoi k)
    have hpbsurj : ∀ x : T.left, ∃ k, x ∈ Set.range
        ((pullback.fst s.down ((AffineProEt.toProEt S).map (j k))).left.base) := by
      intro x
      obtain ⟨k, v, hv⟩ := hcov (s.down.left.base x)
      obtain ⟨pt, hp₁, -⟩ := ProEt.exists_left_base_preimage
        (IsPullback.of_hasPullback s.down ((AffineProEt.toProEt S).map (j k))) x v hv.symm
      exact ⟨k, pt, hp₁⟩
    refine (ProEt.topology S).superset_covering ?_
      (ProEt.generate_ofArrows_mem_topology
        (fun k ↦ pullback.fst s.down ((AffineProEt.toProEt S).map (j k))) hpboi hpbsurj)
    rintro T' h ⟨Z, h', l, ⟨k⟩, rfl⟩
    refine ⟨(Sigma.ι y k).app (op T')
      (ULift.up (h' ≫ pullback.snd s.down ((AffineProEt.toProEt S).map (j k)))), ?_⟩
    rw [happ]
    change ULift.up ((h' ≫ pullback.snd s.down ((AffineProEt.toProEt S).map (j k))) ≫
        (AffineProEt.toProEt S).map (j k)) =
      ULift.up ((h' ≫ pullback.fst s.down ((AffineProEt.toProEt S).map (j k))) ≫ s.down)
    refine congrArg ULift.up ?_
    rw [Category.assoc, Category.assoc, ← pullback.condition]
  -- The comparison map is locally injective, by disjointness of the pieces.
  haveI : Presheaf.IsLocallyInjective (ProEt.topology S) φ := by
    constructor
    intro T x₁ x₂ hx
    obtain ⟨k₁, z₁, hz₁⟩ := jointly_surj T x₁
    obtain ⟨k₂, z₂, hz₂⟩ := jointly_surj T x₂
    have heq : z₁.down ≫ (AffineProEt.toProEt S).map (j k₁) =
        z₂.down ≫ (AffineProEt.toProEt S).map (j k₂) := by
      have e₁ : φ.app T x₁ =
          ULift.up (z₁.down ≫ (AffineProEt.toProEt S).map (j k₁)) := by
        rw [← hz₁, happ]; rfl
      have e₂ : φ.app T x₂ =
          ULift.up (z₂.down ≫ (AffineProEt.toProEt S).map (j k₂)) := by
        rw [← hz₂, happ]; rfl
      exact congrArg ULift.down (e₁.symm.trans (hx.trans e₂))
    by_cases hk : k₁ = k₂
    · -- equal indices: the two sections agree since the piece is a monomorphism
      subst hk
      haveI hm : Mono ((j k₁).left) := inferInstance
      haveI : Mono ((AffineProEt.toProEt S).map (j k₁)) :=
        Functor.mono_of_mono_map (F := ProEt.forget S ⋙ Over.forget S)
          (f := (AffineProEt.toProEt S).map (j k₁)) hm
      have hzz : z₁ = z₂ := ULift.ext _ _ ((cancel_mono _).mp heq)
      rw [← hz₁, ← hz₂, hzz, Presheaf.equalizerSieve_self_eq_top]
      exact (ProEt.topology S).top_mem _
    · -- distinct indices: the object is empty by disjointness of the pieces
      haveI : IsEmpty T.unop.left := by
        constructor
        intro t
        have h1 : (j k₁).left.base (z₁.down.left.base t) =
            (j k₂).left.base (z₂.down.left.base t) := by
          have h2 := congrArg
            (fun (m : T.unop ⟶ (AffineProEt.toProEt S).obj W) ↦ m.left.base t) heq
          exact h2
        exact Set.disjoint_left.mp (hdisj hk) ⟨_, rfl⟩ ⟨_, h1.symm⟩
      exact (ProEt.topology S).superset_covering bot_le (ProEt.bot_mem_topology T.unop)
  -- Hence the comparison map of free abelian sheaves is an isomorphism.
  have hWφ : (ProEt.topology S).W φ :=
    (ProEt.topology S).W_of_isLocallyBijective φ
  have hW2 : (ProEt.topology S).W (Functor.whiskerRight φ AddCommGrpCat.free.{u + 1}) :=
    hWφ.whiskerRight_free
  haveI hiso : IsIso ((presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map
      (Functor.whiskerRight φ AddCommGrpCat.free.{u + 1})) := by
    rw [← GrothendieckTopology.W_iff]
    exact hW2
  -- The sheaf-level comparison map from the coproduct of the free sheaves on the pieces.
  let L₁ := (Functor.whiskeringRight (S.ProEt)ᵒᵖ (Type (u + 1)) Ab.{u + 1}).obj
    AddCommGrpCat.free.{u + 1}
  haveI : L₁.IsLeftAdjoint :=
    (Adjunction.whiskerRight (S.ProEt)ᵒᵖ AddCommGrpCat.adj.{u + 1}).isLeftAdjoint
  haveI : IsIso ((presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map
      (L₁.map φ)) := hiso
  have hceq : (Sigma.desc fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).map
        ((AffineProEt.toProEt S).map (j k))) =
      sigmaComparison (presheafToSheaf (ProEt.topology S) Ab.{u + 1})
        (fun k ↦ L₁.obj (y k)) ≫
      (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (sigmaComparison L₁ y) ≫
      (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (L₁.map φ) := by
    refine colimit.hom_ext fun ⟨k⟩ ↦ ?_
    change Sigma.ι _ k ≫ _ = Sigma.ι _ k ≫ _
    rw [Sigma.ι_desc]
    have hk : Sigma.ι (fun k ↦ (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).obj
          (L₁.obj (y k))) k ≫
        sigmaComparison (presheafToSheaf (ProEt.topology S) Ab.{u + 1})
          (fun k ↦ L₁.obj (y k)) ≫
        (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (sigmaComparison L₁ y) ≫
        (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (L₁.map φ) =
        (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map
          (L₁.map (Sigma.ι y k ≫ φ)) := by
      rw [ι_comp_sigmaComparison_assoc, ← Functor.map_comp_assoc, ι_comp_sigmaComparison,
        ← Functor.map_comp, ← Functor.map_comp]
    have hφk : Sigma.ι y k ≫ φ =
        uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k)) :=
      Sigma.ι_desc _ k
    exact (hk.trans (congrArg (fun t ↦ (presheafToSheaf (ProEt.topology S)
      Ab.{u + 1}).map (L₁.map t)) hφk)).symm
  rw [hceq]
  infer_instance


end AffineProEt

variable (S)


end Scheme
end AlgebraicGeometry


theorem solution.{sol_u1} : type_of% @AlgebraicGeometry.Scheme.AffineProEt.isIso_sigmaDesc_freeAbelianSheafFunctor_map.{sol_u1} := @AlgebraicGeometry.Scheme.AffineProEt.isIso_sigmaDesc_freeAbelianSheafFunctor_map.{sol_u1}
