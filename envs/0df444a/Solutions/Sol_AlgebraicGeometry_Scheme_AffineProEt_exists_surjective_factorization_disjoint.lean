-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_factorization_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-26T19:37:51.211628+00:00
-- url     : https://prove2.me/submissions/551fcea8-78b0-43e7-9292-a56b6ffdb1f5

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


/-- A variant of `AffineProEt.exists_surjective_factorization` which additionally records
that the open pieces `j i : V i ⟶ W` have pairwise disjoint ranges: `W` is the disjoint
union `Spec (∏ᵢ Γ(Vᵢ))` of the `V i`. -/
lemma exists_surjective_factorization_disjoint {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ X) (j : ∀ i, V i ⟶ W),
      Surjective q.left ∧ (∀ i, j i ≫ q = f i) ∧ (∀ i, IsOpenImmersion (j i).left) ∧
      (∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base)) ∧
      (Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
        (Set.range ((j l).left.base))) := by
  -- The product of the rings of global sections; `Spec` of it is the disjoint union.
  let R : CommRingCat.{u} := .of (Π i, Γ((V i).left, ⊤))
  let φ : Γ(X.left, ⊤) ⟶ R := CommRingCat.ofHom (Pi.ringHom fun i ↦ ((f i).left.appTop).hom)
  have hφ : φ.hom.IndEtale :=
    RingHom.IndEtale.pi _ fun i ↦ indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (f i))
  let q₀ : Spec R ⟶ X.left := Spec.map φ ≫ X.left.isoSpec.inv
  have hq₀ : proAffineEtale q₀ :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr (proAffineEtale_Spec_iff.mpr hφ)
  let W : S.AffineProEt := mk (q₀ ≫ X.hom) (proAffineEtale.comp_mem _ _ hq₀ X.prop)
  let q : W ⟶ X := MorphismProperty.Over.homMk q₀ rfl trivial
  let e : ∀ i, (V i).left ⟶ Spec R := fun i ↦
    (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
  have he : ∀ i, e i ≫ q₀ = (f i).left := by
    intro i
    have h1 : φ ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) = (f i).left.appTop := by
      ext x
      rfl
    change ((V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))) ≫
      Spec.map φ ≫ X.left.isoSpec.inv = (f i).left
    rw [Category.assoc, ← Spec.map_comp_assoc, h1, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hw : ∀ i, e i ≫ W.hom = (V i).hom := fun i ↦ by
    change e i ≫ q₀ ≫ X.hom = (V i).hom
    rw [← Category.assoc, he i, MorphismProperty.Over.w (f i)]
  let j : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (e i) (hw i) trivial
  have hcomp : ∀ i, j i ≫ q = f i := by
    intro i
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left]
    exact he i
  have hoiSpec (i : ι) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i))) := by
    rw [← ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i]
    infer_instance
  have hoi : ∀ i, IsOpenImmersion (j i).left := fun i ↦ by
    have hj : (j i).left = (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := rfl
    rw [hj]
    haveI := hoiSpec i
    infer_instance
  -- The pieces `j i` factor through `sigmaSpec` via the coproduct inclusions.
  have key : ∀ (i : ι) (c : (V i).left),
      (j i).left c =
        (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
          ((Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i) ((V i).left.isoSpec.hom c)) := by
    intro i c
    have hj : (j i).left = (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := rfl
    calc (j i).left c
        = (Spec.map (CommRingCat.ofHom
            (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)))
            ((V i).left.isoSpec.hom c) := by
          rw [hj]; exact Scheme.Hom.comp_apply _ _ _
      _ = (Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i ≫ sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((V i).left.isoSpec.hom c) :=
          congrArg (fun g ↦ g ((V i).left.isoSpec.hom c))
            (ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i).symm
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i) ((V i).left.isoSpec.hom c)) :=
          Scheme.Hom.comp_apply _ _ _
  have hcov : ∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base) := by
    intro w
    obtain ⟨p, hp⟩ := (sigmaSpec fun i ↦ Γ((V i).left, ⊤)).surjective w
    obtain ⟨i, y, hy⟩ : ∃ (i : ι) (y : Spec (Γ((V i).left, ⊤))),
        ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i) y = p :=
      ⟨_, (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).covers p⟩
    have h2 : (V i).left.isoSpec.inv ≫ e i =
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := by
      change (V i).left.isoSpec.inv ≫ (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) = _
      rw [Iso.inv_hom_id_assoc]
    have hmor : (V i).left.isoSpec.inv ≫ (j i).left =
        (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
          sigmaSpec fun k ↦ Γ((V k).left, ⊤) := by
      have hj : (j i).left = e i := rfl
      rw [hj, h2, show (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i =
        Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i from rfl, ι_sigmaSpec]
    refine ⟨i, (V i).left.isoSpec.inv y, ?_⟩
    calc (j i).left ((V i).left.isoSpec.inv y)
        = ((V i).left.isoSpec.inv ≫ (j i).left) y := (Scheme.Hom.comp_apply _ _ _).symm
      _ = ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
            sigmaSpec fun k ↦ Γ((V k).left, ⊤)) y := congrArg (fun g ↦ g y) hmor
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i y) :=
          Scheme.Hom.comp_apply _ _ _
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤)) p := by rw [hy]
      _ = w := hp
  have hq₀surj : Function.Surjective q₀.base := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨(e i).base y, ?_⟩
    calc q₀.base ((e i).base y) = (e i ≫ q₀).base y := rfl
      _ = (f i).left.base y := by rw [he i]
      _ = x := hy
  -- Disjointness of the ranges of the pieces, via disjointness of the coproduct components.
  have hdisj : Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
      (Set.range ((j l).left.base)) := by
    intro k l hkl
    rw [Set.disjoint_left]
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have hinj : Function.Injective (sigmaSpec fun m ↦ Γ((V m).left, ⊤)).base :=
      (sigmaSpec fun m ↦ Γ((V m).left, ⊤)).isOpenEmbedding.injective
    have heq : (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k) ((V k).left.isoSpec.hom a) =
        (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) l) ((V l).left.isoSpec.hom b) := by
      apply hinj
      rw [← key k a, ← key l b]
      exact ha.trans hb.symm
    have hd := disjoint_opensRange_sigmaι (fun m ↦ Spec (Γ((V m).left, ⊤))) k l hkl
    have hmem : (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k) ((V k).left.isoSpec.hom a) ∈
        (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k).opensRange ⊓
          (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) l).opensRange :=
      ⟨⟨_, rfl⟩, ⟨_, heq.symm⟩⟩
    simpa using hd.le_bot hmem
  exact ⟨W, q, j, ⟨hq₀surj⟩, hcomp, hoi, hcov, hdisj⟩


end AffineProEt

variable (S)


end Scheme
end AlgebraicGeometry


theorem solution.{sol_u1} : type_of% @AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_factorization_disjoint.{sol_u1} := @AlgebraicGeometry.Scheme.AffineProEt.exists_surjective_factorization_disjoint.{sol_u1}
