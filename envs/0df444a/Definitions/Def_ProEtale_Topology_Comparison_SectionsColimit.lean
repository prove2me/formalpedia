-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_SectionsColimit
-- name    : ProEtale_Topology_Comparison_SectionsColimit
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T18:27:25.532639+00:00
-- url     : https://prove2.me/theorems/aa62b004-e9c5-5aa7-b8dc-9ea3fc55afbb
-- title:
--   Sections of the pro-étale pullback of an étale abelian sheaf over an affine pro-étale object are the colimit of sections over the stages
-- statement:
--   Let $S$ be a scheme, $\nu : S_{\text{ét}} \to S_{\text{proét}}$ the inclusion of the small étale site into the small pro-étale site, and $F$ a sheaf of abelian groups on the small étale site of $S$. Write $\nu^*F$ for its pullback to the small pro-étale site. Let $U$ be an object of the small affine pro-étale site of $S$ together with a **relative limit presentation** $U = \lim_{j \in J} U_j$, i.e. a small diagram $j \mapsto U_j$ of affine étale $S$-schemes and a limit cone from $U$ to it.
--
--   The file defines:
--   - an isomorphism identifying the restriction to the affine étale site of the left Kan extension $\nu_! F$ (along $\nu^{\mathrm{op}}$, of an étale presheaf $F$) with $F$ itself, via the unit of the Kan extension;
--   - an isomorphism, for each affine pro-étale $U$, between $(\nu_!F)(U)$ and the sections $(\nu^*F)(U)$ of the sheaf pullback (the left Kan extension is already a sheaf on the affine pro-étale site);
--   - the canonical maps $\iota_j : F(U_j) \to (\nu^*F)(U)$, obtained by restriction along the projections $U \to U_j$ followed by these identifications, and the cocone formed by them over the diagram $j \mapsto F(U_j)$ (indexed by $J^{\mathrm{op}}$).
--
--   Principal results:
--   1. The maps $\iota_j$ are compatible with the transition maps of the presentation, and are natural with respect to morphisms of relative limit presentations; an explicit formula for $\iota_j$ is given.
--   2. (Bhatt–Scholze, Lemma 5.1.1.) If $J$ is cofiltered, the cocone is a colimit cocone:
--   $$(\nu^*F)(U) \;=\; \operatorname*{colim}_{j \in J^{\mathrm{op}}} F(U_j).$$
--
--   This is the underived form of the comparison lemma between étale and pro-étale sections; it is the input to the description of classical pro-étale sheaves (Lemma 5.1.2).
--
--   **Formalization Note** Coefficients are `Ab.{u + 1}` for `S : Scheme.{u}` and the index category `J : Type u` is small. The main declarations, in namespace `AlgebraicGeometry.Scheme.ProEt`, are `lanToProEtaleRestrictIso`, `sheafPullbackSectionsIso`, `sheafPullbackSectionsι`, `sheafPullbackSectionsCocone`, `map_sheafPullbackSectionsι`, `sheafPullbackSectionsι_naturality` and `isColimitSheafPullbackSectionsCocone` (stated as data: an `IsColimit` structure, under `[IsCofiltered J]`). The presentation is a `RelativeLimitPresentation J (AffineEtale.toAffineProEt S) U`; only sections (not derived functors) are treated.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Bhatt–Scholze, Lemma 5.1.1. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/SectionsColimit.lean (declarations needed by the transplanted proofs, unused ones removed).

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
import Mathlib.Algebra.Category.Ring.Basic
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
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Hypercover.Saturate
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.MorphismProperty
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.CategoryTheory.Sites.Pullback
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Sections of the pullback of an étale sheaf over affine pro-étale objects

Let `S` be a scheme and `F` an abelian sheaf on the small étale site of `S`. If `U` is an
object of the small affine pro-étale site of `S`, presented as a cofiltered limit
`U = limⱼ Uⱼ` of affine étale `S`-schemes (a `RelativeLimitPresentation`), then the sections
of the pullback of `F` to the small pro-étale site over `U` are the filtered colimit of the
sections `F(Uⱼ)` at the stages of the presentation. This is the underived form of
Bhatt–Scholze, Lemma 5.1.1.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackSectionsι`: the canonical map
  `F(Uⱼ) ⟶ (ν^*F)(U)`, given by restriction along the projection `U ⟶ Uⱼ` combined with the
  identification of the pullback with the left Kan extension on the affine pro-étale site.
- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackSectionsCocone`: the cocone over the diagram
  `j ↦ F(Uⱼ)` (indexed by `Jᵒᵖ`) with point `(ν^*F)(U)` and legs `sheafPullbackSectionsι`.
- `AlgebraicGeometry.Scheme.ProEt.isColimitSheafPullbackSectionsCocone`: this cocone is a
  colimit cocone, i.e. `(ν^*F)(U) = colimⱼ F(Uⱼ)`.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry
namespace Scheme

variable (S : Scheme.{u})

namespace ProEt

/-- The restriction of the presheaf pullback of an étale presheaf `F` (i.e., the left Kan
extension along the inclusion of the small étale site into the small pro-étale site) to the
small affine étale site is canonically isomorphic to `F` itself, via the unit of the left
Kan extension. -/
noncomputable def lanToProEtaleRestrictIso (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) :
    (AffineEtale.toAffineProEt S).op ⋙ (AffineProEt.toProEt S).op ⋙
      (toProEtale S).op.lan.obj F ≅ (AffineEtale.Spec S).op ⋙ F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
    Functor.isoWhiskerRight (NatIso.op (AffineEtale.toAffineProEtCompToProEtIso S).symm) _ ≪≫
    Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso <| (toProEtale S).op.lanUnit.app F).symm

variable {S}
variable (F : Sheaf S.smallEtaleTopology Ab.{u + 1})

/-- Evaluated at an affine pro-étale object `U`, the sections of the sheaf pullback of an
étale sheaf `F` agree with the sections of the presheaf pullback (left Kan extension),
since the latter is already a sheaf on the small affine pro-étale site. -/
noncomputable def sheafPullbackSectionsIso (U : S.AffineProEt) :
    ((toProEtale S).op.lan.obj F.obj).obj (op ((AffineProEt.toProEt S).obj U)) ≅
      ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).obj
        (op ((AffineProEt.toProEt S).obj U)) :=
  ((sheafPullbackCompIso S).app F).symm.app (op U)

@[simp]
lemma sheafPullbackSectionsIso_hom (U : S.AffineProEt) :
    (sheafPullbackSectionsIso F U).hom = ((sheafPullbackCompIso S).inv.app F).app (op U) :=
  rfl

variable {J : Type u} [SmallCategory J] {U : S.AffineProEt}
  (pres : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) U)

/-- Given a presentation of an affine pro-étale object `U` as a cofiltered limit
`U = limⱼ Uⱼ` of affine étale `S`-schemes, the sections of `F` at the stages `Uⱼ` form a
cocone over the sections of the pullback of `F` at `U`: the legs are restriction along the
projections `U ⟶ Uⱼ`, combined with the identification of the pullback sheaf with the left
Kan extension on the small affine pro-étale site. -/
noncomputable def sheafPullbackSectionsCocone :
    Cocone ((pres.diag ⋙ AffineEtale.Spec S).op ⋙ (sheafToPresheaf _ _).obj F) :=
  Cocone.extend
    ((Cocone.precompose
        (Functor.isoWhiskerLeft pres.diag.op (lanToProEtaleRestrictIso S F.obj)).inv).obj
      (((AffineProEt.toProEt S).op ⋙ (toProEtale S).op.lan.obj F.obj).mapCocone pres.cone.op))
    (sheafPullbackSectionsIso F U).hom

@[simp]
lemma sheafPullbackSectionsCocone_pt :
    (sheafPullbackSectionsCocone F pres).pt =
      ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).obj
        (op ((AffineProEt.toProEt S).obj U)) :=
  rfl

/-- The canonical map from the sections of an étale sheaf `F` at a stage `Uⱼ` of a
presentation `U = limⱼ Uⱼ` of an affine pro-étale object `U` to the sections of the
pullback of `F` at `U`. -/
noncomputable def sheafPullbackSectionsι (j : J) :
    F.obj.obj (op ((AffineEtale.Spec S).obj (pres.diag.obj j))) ⟶
      ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).obj
        (op ((AffineProEt.toProEt S).obj U)) :=
  (sheafPullbackSectionsCocone F pres).ι.app (op j)

@[simp]
lemma sheafPullbackSectionsCocone_ι_app (j : Jᵒᵖ) :
    (sheafPullbackSectionsCocone F pres).ι.app j = sheafPullbackSectionsι F pres j.unop :=
  rfl

/-- The legs of `sheafPullbackSectionsCocone`, explicitly: restrict from the stage to the
left Kan extension at `U` along the projection, then identify with the sections of the
sheaf pullback. -/
lemma sheafPullbackSectionsι_eq (j : J) :
    sheafPullbackSectionsι F pres j =
      (lanToProEtaleRestrictIso S F.obj).inv.app (op (pres.diag.obj j)) ≫
        ((toProEtale S).op.lan.obj F.obj).map
          ((AffineProEt.toProEt S).map (pres.π.app j)).op ≫
        ((sheafPullbackCompIso S).inv.app F).app (op U) := by
  simp [sheafPullbackSectionsι, sheafPullbackSectionsCocone]

/-- The legs of `sheafPullbackSectionsCocone` are compatible with the transition maps of the
presentation. -/
@[reassoc (attr := simp)]
lemma map_sheafPullbackSectionsι {j j' : J} (f : j ⟶ j') :
    F.obj.map ((AffineEtale.Spec S).map (pres.diag.map f)).op ≫
        sheafPullbackSectionsι F pres j =
      sheafPullbackSectionsι F pres j' :=
  (sheafPullbackSectionsCocone F pres).w f.op

/-- **Bhatt–Scholze, Lemma 5.1.1.** The sections of the pullback of an étale sheaf `F` over
an affine pro-étale object `U` are the filtered colimit of the sections of `F` at the stages
of a relative limit presentation `U = limⱼ Uⱼ` by affine étale `S`-schemes. -/
noncomputable def isColimitSheafPullbackSectionsCocone [IsCofiltered J] :
    IsColimit (sheafPullbackSectionsCocone F pres) :=
  ((IsColimit.precomposeInvEquiv
      (Functor.isoWhiskerLeft pres.diag.op (lanToProEtaleRestrictIso S F.obj))
      (((AffineProEt.toProEt S).op ⋙ (toProEtale S).op.lan.obj F.obj).mapCocone
        pres.cone.op)).symm
    (Functor.PreservesRelativeFilteredColimits.nonempty_isColimit pres.cone
      pres.isLimit).some).ofIsoColimit
    (Cocone.ext (sheafPullbackSectionsIso F U) fun _ ↦ rfl)

/-- The legs of `sheafPullbackSectionsCocone` are compatible with morphisms of relative
limit presentations. -/
@[reassoc]
lemma sheafPullbackSectionsι_naturality {X Y : S.AffineProEt}
    {pres₁ : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) X}
    {pres₂ : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) Y}
    (φ : pres₁.Hom pres₂) (j : J) :
    F.obj.map ((AffineEtale.Spec S).map (φ.natTrans.app j)).op ≫
        sheafPullbackSectionsι F pres₁ j =
      sheafPullbackSectionsι F pres₂ j ≫
        ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).map
          ((AffineProEt.toProEt S).map φ.map).op := by
  have h1 : F.obj.map ((AffineEtale.Spec S).map (φ.natTrans.app j)).op ≫
      (lanToProEtaleRestrictIso S F.obj).inv.app (op (pres₁.diag.obj j)) =
      (lanToProEtaleRestrictIso S F.obj).inv.app (op (pres₂.diag.obj j)) ≫
        ((toProEtale S).op.lan.obj F.obj).map
          ((AffineProEt.toProEt S).map
            ((AffineEtale.toAffineProEt S).map (φ.natTrans.app j))).op :=
    (lanToProEtaleRestrictIso S F.obj).inv.naturality (φ.natTrans.app j).op
  have h2 : ((toProEtale S).op.lan.obj F.obj).map
        ((AffineProEt.toProEt S).map φ.map).op ≫
        ((sheafPullbackCompIso S).inv.app F).app (op X) =
      ((sheafPullbackCompIso S).inv.app F).app (op Y) ≫
        ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).map
          ((AffineProEt.toProEt S).map φ.map).op :=
    ((sheafPullbackCompIso S).inv.app F).naturality (φ.map).op
  rw [sheafPullbackSectionsι_eq, sheafPullbackSectionsι_eq, reassoc_of% h1,
    ← Functor.map_comp_assoc, ← op_comp, ← Functor.map_comp,
    ← RelativeLimitPresentation.Hom.map_π φ j, Functor.map_comp, op_comp,
    Functor.map_comp_assoc, h2, Category.assoc, Category.assoc]

end ProEt

end Scheme
end AlgebraicGeometry


