-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_CechColimit
-- name    : ProEtale_Topology_Comparison_CechColimit
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T18:30:03.67881+00:00
-- url     : https://prove2.me/theorems/a0eedd10-da1d-5f37-8bb5-f2658b6c8e09
-- title:
--   Čech nerve data and the tower of iterated fibre products of a map of affine pro-étale objects, with stagewise Čech differentials
-- statement:
--   This file sets up the combinatorial machinery for comparing Čech complexes on the pro-étale site with filtered colimits of Čech complexes on the étale site. It contains constructions and their basic compatibilities; the statement announced in the module docstring (positive-degree Čech cocycles of $\nu^*I$ along a surjection of affine pro-étale objects are coboundaries, for $I$ an injective abelian sheaf on the small étale site) is proved later, not in this file.
--
--   **Čech differential on sections.** For a morphism $g : V \to U$ in a category $\mathcal D$ having all finite wide pullbacks of copies of $g$, write $\check C_n(g) = V \times_U \cdots \times_U V$ ($n+1$ factors) for the $n$-th object of the Čech nerve. For a presheaf of abelian groups $F$ on $\mathcal D$ the Čech differential is
--   $$d = \sum_{i=0}^{n+1} (-1)^i\, F(\delta_i) : F(\check C_n(g)) \longrightarrow F(\check C_{n+1}(g)),$$
--   where $\delta_i$ are the face maps of the Čech nerve.
--
--   **Čech nerve data.** For $n \in \mathbb N$ and an object $P$, a structure `IsCechNerveAt g n P` consists of projections $\pi_0,\dots,\pi_n : P \to V$, a base map $b : P \to U$ with $\pi_j \circ g = b$ (composition written diagrammatically), and an isomorphism $P \cong \check C_n(g)$ compatible with the projections and the base. The file provides:
--
--   1. the canonical datum exhibiting $V$ (with identity projection and base $g$) as $\check C_0(g)$;
--   2. the map $\check C_{k+1}(g) \to \check C_k(g)$ forgetting the last projection, with its projection and base identities;
--   3. a successor construction: if $P$ carries data in degree $n$ and $P'$ is a pullback of $b : P \to U$ and $g : V \to U$, then $P'$ carries data in degree $n+1$, with prescribed projections and base;
--   4. the $i$-th face map $P' \to P$ between objects carrying data in degrees $n+1$ and $n$, its compatibility with projections ($\mathrm{face}_i \circ \pi_j = \pi'_{\delta_i(j)}$) and with base maps, and the corresponding alternating sum of face maps on sections of an abelian presheaf; plus an extensionality lemma for maps into $P$.
--
--   **The tower of iterated fibre products.** Let $S$ be a scheme, $q : W \to U_0$ a morphism of affine pro-étale objects over $S$, and suppose $U_0$ and $W$ are given relative limit presentations indexed by the same small category $A$, with stages affine étale objects over $S$, together with a morphism of presentations $f_W$ lying over $q$. A level-$n$ tower datum consists of an affine pro-étale object $M$ (the $(n+1)$-fold fibre product of $W$ over $U_0$) with its own relative limit presentation, a morphism of presentations to that of $U_0$, projections $M \to W$ and stagewise projections, Čech nerve data for the étale level maps $f_{W,a}$ at every stage $a \in A$, and Čech nerve data for $q$ on the pro-étale site, all compatible. The file constructs level $0$ ($M = W$), the passage from level $n$ to level $n+1$ by stagewise pullbacks, the resulting tower indexed by $\mathbb N$, the morphisms of presentations between consecutive levels induced by the stagewise face maps, and the two Čech differentials: on sections of an abelian étale sheaf $I$ at each stage, and on sections of the pro-étale pullback $\nu^*I$ over the levels of the tower.
--
--   These constructions are used to identify the Čech complex of $\nu^*I$ along $q$ with a filtered colimit of étale Čech complexes, a step in the comparison between étale and pro-étale cohomology.
--
--   **Formalization Note** The Čech differential is `CategoryTheory.cechPresheafD`, the Čech nerve data structure is `CategoryTheory.IsCechNerveAt` (with `IsCechNerveAt.zero`, `IsCechNerveAt.succ`, `IsCechNerveAt.face`, `IsCechNerveAt.faceD`) and `CategoryTheory.cechNerveForgetLast`. The tower is the structure `AlgebraicGeometry.Scheme.AffineProEt.CechTower` with `CechTower.zero`, `CechTower.succ`, `CechTower.faceHom`, `CechTower.stageD`, `CechTower.proD`, and the whole tower `AlgebraicGeometry.Scheme.AffineProEt.cechTower`. Abelian presheaves take values in `AddCommGrpCat.{u+1}`; the scheme $S$ lives in universe `u` and the index category $A$ is a `SmallCategory` in `Type u`. The pullback $\nu^*$ is `ProEt.sheafPullback S Ab`. Most constructions are data (`noncomputable def`/`structure`), with equalities recorded as fields rather than proved by unfolding. The file also contains a trivial lemma `AddCommGrpCat.hom_zsmul_apply` ($(z\cdot f)(x) = z\cdot f(x)$).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/CechColimit.lean (declarations needed by the transplanted proofs, unused ones removed).

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

lemma hom_zsmul_apply {M N : AddCommGrpCat.{u + 1}} (z : ℤ) (f : M ⟶ N) (x : M) :
    (z • f) x = z • f x :=
  rfl


end AddCommGrpCat

namespace CategoryTheory

/-! ### Translation between morphisms out of free abelian sheaves and sections

We record that `freeAbelianSheafHomEquiv` is additive (via the "generator" trick: every
morphism out of the free abelian sheaf is determined by its value on the canonical
generating section), and compute the image of a composition with the Čech differential. -/


/-- The Čech differential on sections: the alternating sum of the restrictions along the
face maps of the Čech nerve. -/
noncomputable def cechPresheafD {D : Type w₂} [Category.{w₁} D] {V U : D} (g : V ⟶ U)
    [∀ k : ℕ, HasWidePullback (Arrow.mk g).right
      (fun _ : Fin (k + 1) ↦ (Arrow.mk g).left) fun _ ↦ (Arrow.mk g).hom]
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    F.obj (op ((Arrow.mk g).cechNerve.obj (op ⦋n⦌))) ⟶
      F.obj (op ((Arrow.mk g).cechNerve.obj (op ⦋n + 1⦌))) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((Arrow.mk g).cechNerve.δ i).op


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

/-- Data exhibiting `P` as the `n`-th object of the Čech nerve of `g`. -/
structure IsCechNerveAt (n : ℕ) (P : D) where
  /-- The projections to `V`. -/
  π : Fin (n + 1) → (P ⟶ V)
  /-- The structure map to `U`. -/
  base : P ⟶ U
  wπ : ∀ j, π j ≫ g = base
  /-- The comparison isomorphism with the wide pullback. -/
  iso : P ≅ (Arrow.mk g).cechNerve.obj (op ⦋n⦌)
  iso_π : ∀ j, iso.hom ≫ WidePullback.π (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) j = π j
  iso_base : iso.hom ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) = base

/-- Forgetting the last projection of a Čech nerve object. -/
noncomputable def cechNerveForgetLast (k : ℕ) :
    (Arrow.mk g).cechNerve.obj (op ⦋k + 1⦌) ⟶ (Arrow.mk g).cechNerve.obj (op ⦋k⦌) :=
  WidePullback.lift (WidePullback.base _)
    (fun j : Fin (k + 1) ↦ WidePullback.π (fun _ : Fin (k + 2) ↦ (Arrow.mk g).hom) j.castSucc)
    (fun _ ↦ WidePullback.π_arrow _ _)

@[reassoc (attr := simp)]
lemma cechNerveForgetLast_π (k : ℕ) (j : Fin (k + 1)) :
    cechNerveForgetLast g k ≫ WidePullback.π (fun _ : Fin (k + 1) ↦ (Arrow.mk g).hom) j =
      WidePullback.π (fun _ : Fin (k + 2) ↦ (Arrow.mk g).hom) j.castSucc :=
  WidePullback.lift_π _ _ _ _ j

@[reassoc (attr := simp)]
lemma cechNerveForgetLast_base (k : ℕ) :
    cechNerveForgetLast g k ≫ WidePullback.base (fun _ : Fin (k + 1) ↦ (Arrow.mk g).hom) =
      WidePullback.base (fun _ : Fin (k + 2) ↦ (Arrow.mk g).hom) :=
  WidePullback.lift_base _ _ _ _

namespace IsCechNerveAt

variable {g} {n : ℕ} {P : D}

@[reassoc]
lemma inv_π (h : IsCechNerveAt g n P) (j : Fin (n + 1)) :
    h.iso.inv ≫ h.π j = WidePullback.π (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) j := by
  rw [← h.iso_π, Iso.inv_hom_id_assoc]

@[reassoc]
lemma inv_base (h : IsCechNerveAt g n P) :
    h.iso.inv ≫ h.base = WidePullback.base (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) := by
  rw [← h.iso_base, Iso.inv_hom_id_assoc]

lemma hom_ext (h : IsCechNerveAt g n P) {Z : D} {t₁ t₂ : Z ⟶ P}
    (hπ : ∀ j, t₁ ≫ h.π j = t₂ ≫ h.π j) (hbase : t₁ ≫ h.base = t₂ ≫ h.base) :
    t₁ = t₂ := by
  rw [← cancel_mono h.iso.hom]
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, h.iso_π, hπ]
  · rw [Category.assoc, Category.assoc, h.iso_base, hbase]

variable (g) in
/-- `V` itself is the `0`-th object of the Čech nerve of `g`. -/
noncomputable def zero : IsCechNerveAt g 0 V where
  π _ := 𝟙 V
  base := g
  wπ _ := Category.id_comp g
  iso :=
    { hom := WidePullback.lift g (fun _ : Fin 1 ↦ 𝟙 V) (fun _ ↦ Category.id_comp g)
      inv := WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk g).hom) 0
      hom_inv_id := WidePullback.lift_π _ _ _ _ 0
      inv_hom_id := by
        apply WidePullback.hom_ext
        · intro j
          rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
          exact congrArg (WidePullback.π fun _ : Fin 1 ↦ (Arrow.mk g).hom)
            (Subsingleton.elim (0 : Fin 1) j)
        · rw [Category.assoc, WidePullback.lift_base, Category.id_comp]
          exact WidePullback.π_arrow _ 0 }
  iso_π j := WidePullback.lift_π _ _ _ _ j
  iso_base := WidePullback.lift_base _ _ _ _

@[simp]
lemma zero_π (j : Fin 1) : (zero g).π j = 𝟙 V := rfl

@[simp]
lemma zero_base : (zero g).base = g := rfl

/-- Extend Čech nerve data one degree up along a binary pullback. The new projections,
base map and the comparison equations are supplied as data to avoid definitional
unfolding issues at use sites. -/
noncomputable def succ (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) :
    IsCechNerveAt g (n + 1) P' := by
  have wπ' : ∀ j : Fin (n + 2), π' j ≫ g = base' := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hlast, hbase]
    | cast j => rw [hπ, hbase, Category.assoc, h.wπ, sq.w]
  have hcomm : (cechNerveForgetLast g n ≫ h.iso.inv) ≫ h.base =
      WidePullback.π (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom) (Fin.last (n + 1)) ≫ g := by
    rw [Category.assoc, h.inv_base, cechNerveForgetLast_base]
    exact (WidePullback.π_arrow _ _).symm
  have hfst : WidePullback.lift (arrows := fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom)
      base' π' wπ' ≫ cechNerveForgetLast g n = fst ≫ h.iso.hom := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.assoc, cechNerveForgetLast_π, WidePullback.lift_π,
        h.iso_π, hπ]
    · rw [Category.assoc, Category.assoc, cechNerveForgetLast_base, WidePullback.lift_base,
        h.iso_base, hbase, sq.w]
  refine
    { π := π'
      base := base'
      wπ := wπ'
      iso :=
        { hom := WidePullback.lift (arrows := fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom)
            base' π' wπ'
          inv := sq.lift (cechNerveForgetLast g n ≫ h.iso.inv)
            (WidePullback.π (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom) (Fin.last (n + 1)))
            hcomm
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      iso_π := fun j ↦ WidePullback.lift_π _ _ _ _ j
      iso_base := WidePullback.lift_base _ _ _ _ }
  · apply sq.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, hfst, Category.assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, IsPullback.lift_snd, WidePullback.lift_π, hlast, Category.id_comp]
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      induction j using Fin.lastCases with
      | last => rw [WidePullback.lift_π, hlast, IsPullback.lift_snd]
      | cast j =>
        rw [WidePullback.lift_π, hπ, ← Category.assoc, IsPullback.lift_fst,
          Category.assoc, h.inv_π, cechNerveForgetLast_π]
    · rw [Category.assoc, Category.id_comp, WidePullback.lift_base, hbase,
        ← Category.assoc, IsPullback.lift_snd]
      exact WidePullback.π_arrow _ _

@[simp]
lemma succ_π (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) (j : Fin (n + 2)) :
    (h.succ sq π' base' hπ hlast hbase).π j = π' j := rfl

@[simp]
lemma succ_base (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) :
    (h.succ sq π' base' hπ hlast hbase).base = base' := rfl

/-- The `i`-th face map between objects carrying Čech nerve data. -/
noncomputable def face {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) : P' ⟶ P :=
  h'.iso.hom ≫ (Arrow.mk g).cechNerve.δ i ≫ h.iso.inv

@[reassoc]
lemma face_π {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    h'.face h i ≫ h.π j = h'.π ((SimplexCategory.δ i).toOrderHom j) := by
  have hδ : (Arrow.mk g).cechNerve.δ i ≫
      WidePullback.π (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) j =
        WidePullback.π (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom)
          ((SimplexCategory.δ i).toOrderHom j) :=
    cechNerve_map_comp_π g ((SimplexCategory.δ i).op) j
  rw [face, Category.assoc, Category.assoc, h.inv_π, hδ, h'.iso_π]

@[reassoc]
lemma face_base {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) :
    h'.face h i ≫ h.base = h'.base := by
  have hδ : (Arrow.mk g).cechNerve.δ i ≫
      WidePullback.base (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) =
        WidePullback.base (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom) :=
    cechNerve_map_comp_base g ((SimplexCategory.δ i).op)
  rw [face, Category.assoc, Category.assoc, h.inv_base, hδ, h'.iso_base]


/-- The alternating sum of the face maps, on sections of an abelian presheaf. -/
noncomputable def faceD {P' P : D} (h' : IsCechNerveAt g (n + 1) P')
    (h : IsCechNerveAt g n P) (F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.obj (op P) ⟶ F.obj (op P') :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((h'.face h i).op)


end IsCechNerveAt


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

/-- The `n`-th level of the tower of iterated fibre products of `q : W ⟶ U₀`: an affine
pro-étale object `M` with a relative limit presentation whose stages carry Čech nerve
data for the étale level maps, and which itself carries Čech nerve data for `q` on the
pro-étale site. -/
structure CechTower (n : ℕ) where
  /-- The `n`-th iterated fibre product of `W` over `U₀`. -/
  M : S.AffineProEt
  /-- The relative limit presentation of `M`. -/
  presM : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) M
  /-- The base morphism of presentations. -/
  bM : presM.Hom presU
  /-- The projections of `M` to `W`. -/
  πM : Fin (n + 1) → (M ⟶ W)
  /-- The stage-wise projections to the stages of `W`. -/
  πSt : ∀ a : A, Fin (n + 1) → (presM.diag.obj a ⟶ presW.diag.obj a)
  πM_π : ∀ (j : Fin (n + 1)) (a : A), πM j ≫ presW.π.app a =
    presM.π.app a ≫ (AffineEtale.toAffineProEt S).map (πSt a j)
  πSt_nat : ∀ {a a' : A} (u : a ⟶ a') (j : Fin (n + 1)),
    presM.diag.map u ≫ πSt a' j = πSt a j ≫ presW.diag.map u
  /-- The Čech nerve data at the étale stages. -/
  ét : ∀ a : A, IsCechNerveAt ((AffineEtale.Spec S).map (fW.natTrans.app a)) n
    ((AffineEtale.Spec S).obj (presM.diag.obj a))
  ét_π : ∀ (a : A) (j : Fin (n + 1)), (ét a).π j = (AffineEtale.Spec S).map (πSt a j)
  ét_base : ∀ a : A, (ét a).base = (AffineEtale.Spec S).map (bM.natTrans.app a)
  /-- The Čech nerve data on the pro-étale site. -/
  pro : IsCechNerveAt ((AffineProEt.toProEt S).map q) n ((AffineProEt.toProEt S).obj M)
  pro_π : ∀ j : Fin (n + 1), pro.π j = (AffineProEt.toProEt S).map (πM j)
  pro_base : pro.base = (AffineProEt.toProEt S).map bM.map

namespace CechTower

variable {q presU presW fW}

/-- The zeroth level of the tower: `W` itself. -/
noncomputable def zero (hfW : fW.map = q) : CechTower q presU presW fW 0 where
  M := W
  presM := presW
  bM := fW
  πM _ := 𝟙 W
  πSt _ _ := 𝟙 _
  πM_π _ _ := by simp
  πSt_nat _ _ := by simp
  ét _ := .zero _
  ét_π _ _ := by rw [IsCechNerveAt.zero_π, CategoryTheory.Functor.map_id]
  ét_base _ := rfl
  pro := .zero _
  pro_π _ := by rw [IsCechNerveAt.zero_π, CategoryTheory.Functor.map_id]
  pro_base := by rw [IsCechNerveAt.zero_base, hfW]

variable {n : ℕ}

/-- The presentation of the next level of the tower, by stage-wise pullbacks. -/
noncomputable def presNext (T : CechTower q presU presW fW n) (hfW : fW.map = q) :
    RelativeLimitPresentation A (AffineEtale.toAffineProEt S) (pullback T.bM.map q) :=
  RelativeLimitPresentation.pullback (F := AffineEtale.toAffineProEt S) T.bM.map q
    (IsPullback.of_hasPullback T.bM.map q).cone (IsPullback.of_hasPullback T.bM.map q).isLimit
    T.presM presW presU T.bM fW rfl hfW

variable (T : CechTower q presU presW fW n) (hfW : fW.map = q)

lemma presNext_π_app_fst (a : A) :
    (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map
        (pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a)) =
      pullback.fst T.bM.map q ≫ T.presM.π.app a :=
  IsPullback.lift_fst _ _ _ _

lemma presNext_π_app_snd (a : A) :
    (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map
        (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a)) =
      pullback.snd T.bM.map q ≫ presW.π.app a :=
  IsPullback.lift_snd _ _ _ _

lemma presNext_diag_map {a a' : A} (u : a ⟶ a') :
    (T.presNext hfW).diag.map u =
      pullback.map (T.bM.natTrans.app a) (fW.natTrans.app a) (T.bM.natTrans.app a')
        (fW.natTrans.app a') (T.presM.diag.map u) (presW.diag.map u) (presU.diag.map u)
        (by simp) (by simp) :=
  rfl

/-- The base morphism of presentations of the next level. -/
noncomputable def bMNext : (T.presNext hfW).Hom presU where
  natTrans :=
    { app a := pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ fW.natTrans.app a
      naturality a a' u := by
        rw [presNext_diag_map]
        rw [pullback.lift_snd_assoc, Category.assoc, fW.natTrans.naturality,
          Category.assoc] }

@[simp]
lemma bMNext_app (a : A) :
    (T.bMNext hfW).natTrans.app a =
      pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ fW.natTrans.app a :=
  rfl

lemma bMNext_map : (T.bMNext hfW).map = pullback.snd T.bM.map q ≫ q := by
  apply presU.isLimit.hom_ext
  intro a
  rw [RelativeLimitPresentation.Hom.map_π, bMNext_app, Functor.map_comp, ← Category.assoc,
    presNext_π_app_snd, Category.assoc, ← RelativeLimitPresentation.Hom.map_π fW a, hfW,
    Category.assoc]

/-- The projections of the next level of the tower. -/
noncomputable def πMNext : Fin (n + 2) → (pullback T.bM.map q ⟶ W) :=
  Fin.snoc (fun j ↦ pullback.fst T.bM.map q ≫ T.πM j) (pullback.snd T.bM.map q)

/-- The stage-wise projections of the next level of the tower. -/
noncomputable def πStNext (a : A) :
    Fin (n + 2) → ((T.presNext hfW).diag.obj a ⟶ presW.diag.obj a) :=
  Fin.snoc (fun j ↦ pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ T.πSt a j)
    (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a))

lemma πMNext_π (j : Fin (n + 2)) (a : A) :
    T.πMNext j ≫ presW.π.app a =
      (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map (T.πStNext hfW a j) := by
  induction j using Fin.lastCases with
  | last =>
    rw [πMNext, πStNext, Fin.snoc_last, Fin.snoc_last]
    exact (T.presNext_π_app_snd hfW a).symm
  | cast j =>
    rw [πMNext, πStNext, Fin.snoc_castSucc, Fin.snoc_castSucc, Category.assoc, T.πM_π,
      CategoryTheory.Functor.map_comp, ← Category.assoc, ← presNext_π_app_fst,
      Category.assoc]

lemma πStNext_nat {a a' : A} (u : a ⟶ a') (j : Fin (n + 2)) :
    (T.presNext hfW).diag.map u ≫ T.πStNext hfW a' j =
      T.πStNext hfW a j ≫ presW.diag.map u := by
  induction j using Fin.lastCases with
  | last =>
    rw [πStNext, πStNext, Fin.snoc_last, Fin.snoc_last, presNext_diag_map,
      pullback.lift_snd]
  | cast j =>
    rw [πStNext, πStNext, Fin.snoc_castSucc, Fin.snoc_castSucc, presNext_diag_map,
      pullback.lift_fst_assoc, Category.assoc, T.πSt_nat, Category.assoc]

/-- The étale Čech nerve data of the next level of the tower. -/
noncomputable def étNext (a : A) :
    IsCechNerveAt ((AffineEtale.Spec S).map (fW.natTrans.app a)) (n + 1)
      ((AffineEtale.Spec S).obj ((T.presNext hfW).diag.obj a)) := by
  have sq : IsPullback
      ((AffineEtale.Spec S).map (pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a)))
      ((AffineEtale.Spec S).map (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a)))
      ((T.ét a).base) ((AffineEtale.Spec S).map (fW.natTrans.app a)) := by
    rw [T.ét_base a]
    exact (IsPullback.of_hasPullback (T.bM.natTrans.app a) (fW.natTrans.app a)).map
      (AffineEtale.Spec S)
  refine (T.ét a).succ sq (fun j ↦ (AffineEtale.Spec S).map (T.πStNext hfW a j))
    ((AffineEtale.Spec S).map ((T.bMNext hfW).natTrans.app a)) ?_ ?_ ?_
  · intro j
    simp only [πStNext, Fin.snoc_castSucc, CategoryTheory.Functor.map_comp, T.ét_π a j]
  · simp only [πStNext, Fin.snoc_last]
  · rw [bMNext_app, CategoryTheory.Functor.map_comp]

/-- The pro-étale Čech nerve data of the next level of the tower. -/
noncomputable def proNext :
    IsCechNerveAt ((AffineProEt.toProEt S).map q) (n + 1)
      ((AffineProEt.toProEt S).obj (pullback T.bM.map q)) := by
  have sq : IsPullback
      ((AffineProEt.toProEt S).map (pullback.fst T.bM.map q))
      ((AffineProEt.toProEt S).map (pullback.snd T.bM.map q))
      (T.pro.base) ((AffineProEt.toProEt S).map q) := by
    rw [T.pro_base]
    exact (IsPullback.of_hasPullback T.bM.map q).map (AffineProEt.toProEt S)
  refine T.pro.succ sq (fun j ↦ (AffineProEt.toProEt S).map (T.πMNext j))
    ((AffineProEt.toProEt S).map ((T.bMNext hfW).map)) ?_ ?_ ?_
  · intro j
    simp only [πMNext, Fin.snoc_castSucc, CategoryTheory.Functor.map_comp, T.pro_π j]
  · simp only [πMNext, Fin.snoc_last]
  · rw [bMNext_map, CategoryTheory.Functor.map_comp]

/-- The next level of the tower. -/
noncomputable def succ : CechTower q presU presW fW (n + 1) where
  M := pullback T.bM.map q
  presM := T.presNext hfW
  bM := T.bMNext hfW
  πM := T.πMNext
  πSt := T.πStNext hfW
  πM_π := T.πMNext_π hfW
  πSt_nat := T.πStNext_nat hfW
  ét := T.étNext hfW
  ét_π _ _ := rfl
  ét_base _ := rfl
  pro := T.proNext hfW
  pro_π _ := rfl
  pro_base := rfl

end CechTower

namespace CechTower

variable {q presU presW fW} {n : ℕ}
variable (T' : CechTower q presU presW fW (n + 1)) (T : CechTower q presU presW fW n)

lemma ét_π_nat {a a' : A} (u : a ⟶ a') (j : Fin (n + 1)) :
    (AffineEtale.Spec S).map (T.presM.diag.map u) ≫ (T.ét a').π j =
      (T.ét a).π j ≫ (AffineEtale.Spec S).map (presW.diag.map u) := by
  rw [T.ét_π a', T.ét_π a, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, T.πSt_nat u]

lemma ét_base_nat {a a' : A} (u : a ⟶ a') :
    (AffineEtale.Spec S).map (T.presM.diag.map u) ≫ (T.ét a').base =
      (T.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
  rw [T.ét_base a', T.ét_base a, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, T.bM.natTrans.naturality u]

/-- The stage-wise face maps of consecutive levels of the tower assemble into a morphism
of presentations. -/
noncomputable def faceHom (i : Fin (n + 2)) : T'.presM.Hom T.presM where
  natTrans :=
    { app a := (AffineEtale.Spec S).preimage ((T'.ét a).face (T.ét a) i)
      naturality a a' u := by
        apply (AffineEtale.Spec S).map_injective
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
          Functor.map_preimage, Functor.map_preimage]
        apply (T.ét a').hom_ext
        · intro j
          have hL : ((AffineEtale.Spec S).map (T'.presM.diag.map u) ≫
              (T'.ét a').face (T.ét a') i) ≫ (T.ét a').π j =
                (T'.ét a).π ((SimplexCategory.δ i).toOrderHom j) ≫
                  (AffineEtale.Spec S).map (presW.diag.map u) := by
            rw [Category.assoc, IsCechNerveAt.face_π, T'.ét_π_nat u]
          have hR : ((T'.ét a).face (T.ét a) i ≫
              (AffineEtale.Spec S).map (T.presM.diag.map u)) ≫ (T.ét a').π j =
                (T'.ét a).π ((SimplexCategory.δ i).toOrderHom j) ≫
                  (AffineEtale.Spec S).map (presW.diag.map u) := by
            rw [Category.assoc, T.ét_π_nat u, ← Category.assoc, IsCechNerveAt.face_π]
          rw [hL, hR]
        · have hL : ((AffineEtale.Spec S).map (T'.presM.diag.map u) ≫
              (T'.ét a').face (T.ét a') i) ≫ (T.ét a').base =
                (T'.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
            rw [Category.assoc, IsCechNerveAt.face_base, T'.ét_base_nat u]
          have hR : ((T'.ét a).face (T.ét a) i ≫
              (AffineEtale.Spec S).map (T.presM.diag.map u)) ≫ (T.ét a').base =
                (T'.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
            rw [Category.assoc, T.ét_base_nat u, ← Category.assoc, IsCechNerveAt.face_base]
          rw [hL, hR] }


section Differentials

variable (I : Sheaf S.smallEtaleTopology Ab.{u + 1})

/-- The Čech differential at the étale stages of the tower. -/
noncomputable def stageD (a : A) :
    I.obj.obj (op ((AffineEtale.Spec S).obj (T.presM.diag.obj a))) ⟶
      I.obj.obj (op ((AffineEtale.Spec S).obj (T'.presM.diag.obj a))) :=
  (T'.ét a).faceD (T.ét a) I.obj

/-- The Čech differential on the sections of the pullback sheaf over the tower. -/
noncomputable def proD :
    ((sheafToPresheaf (ProEt.topology S) Ab.{u + 1}).obj
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I)).obj
        (op ((AffineProEt.toProEt S).obj T.M)) ⟶
      ((sheafToPresheaf (ProEt.topology S) Ab.{u + 1}).obj
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I)).obj
        (op ((AffineProEt.toProEt S).obj T'.M)) :=
  T'.pro.faceD T.pro ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj


end Differentials

end CechTower

variable {q presU presW fW} in
/-- The tower of iterated fibre products of `q`. -/
noncomputable def cechTower (hfW : fW.map = q) : ∀ n, CechTower q presU presW fW n :=
  fun n ↦ Nat.rec (CechTower.zero hfW) (fun _ T ↦ T.succ hfW) n

end Tower


end AffineProEt
end Scheme
end AlgebraicGeometry


