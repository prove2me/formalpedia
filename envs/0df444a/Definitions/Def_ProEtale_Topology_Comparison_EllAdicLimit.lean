-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_EllAdicLimit
-- name    : ProEtale_Topology_Comparison_EllAdicLimit
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T19:01:38.331336+00:00
-- url     : https://prove2.me/theorems/9fbb3c6c-9ca5-5ffa-8a12-4600994ab147
-- title:
--   The $\ell$-adic sheaf on the pro-étale site is the inverse limit of the pulled-back constant étale sheaves $\mathbb{Z}/\ell^n$
-- statement:
--   Fix a scheme $X$ and a prime $\ell$. On the pro-étale site $X_{\mathrm{pro\acute et}}$ let $\widehat{\mathbb{Z}}_\ell$ denote the $\ell$-adic sheaf $U \mapsto C(U, \mathbb{Z}_\ell)$ of continuous maps from the underlying space of $U$ to the $\ell$-adic integers, and let $\nu^*$ denote pullback of abelian sheaves from the small étale site $X_{\mathrm{\acute et}}$ to $X_{\mathrm{pro\acute et}}$.
--
--   The file first proves three topological facts about $\mathbb{Z}_\ell$, where $\pi_n : \mathbb{Z}_\ell \to \mathbb{Z}/\ell^n$ is the reduction map:
--
--   1. each $\pi_n$ is continuous ($\mathbb{Z}/\ell^n$ discrete);
--   2. a map $f : U \to \mathbb{Z}_\ell$ from a topological space is continuous as soon as every $\pi_n \circ f$ is continuous;
--   3. given continuous maps $g_n : U \to \mathbb{Z}/\ell^n$ compatible with the reductions $\mathbb{Z}/\ell^{n+1} \to \mathbb{Z}/\ell^n$, there is a **unique** continuous $f : U \to \mathbb{Z}_\ell$ with $\pi_n(f(x)) = g_n(x)$ for all $n$ and $x$.
--
--   It then defines the inverse system $n \mapsto \mathbb{Z}/\ell^n$ of abelian groups indexed by $\mathbb{N}^{\mathrm{op}}$, with the reduction maps as transitions, and its composite with the constant-sheaf functor, an inverse system $n \mapsto \underline{\mathbb{Z}/\ell^n}$ of constant sheaves on $X_{\mathrm{\acute et}}$. The main construction is an isomorphism of abelian sheaves on $X_{\mathrm{pro\acute et}}$
--   $$\widehat{\mathbb{Z}}_\ell \;\cong\; \lim_{n} \nu^*\big(\underline{\mathbb{Z}/\ell^n}\big),$$
--   and a lemma identifying its components: composing it with the $n$-th limit projection gives the map $C(-,\mathbb{Z}_\ell) \to C(-,\mathbb{Z}/\ell^n)$ induced by $\pi_n$, followed by the inverse of the comparison isomorphism $\nu^*\underline{\mathbb{Z}/\ell^n} \cong C(-,\mathbb{Z}/\ell^n)$. The limit property is checked sectionwise, where it is fact 3.
--
--   This identification lets $\ell$-adic pro-étale cohomology be computed from the torsion coefficients $\mathbb{Z}/\ell^n$, which come from the étale site.
--
--   **Formalization Note** $X$ is a `Scheme.{u}`. Mathlib's `X.ellAdicSheaf ℓ` takes values in `Ab.{u}`; here it is lifted to `Ab.{u+1}` with `sheafCompose _ AddCommGrpCat.uliftFunctor`, and the groups $\mathbb{Z}/\ell^n$ are also `ULift`ed, because the pullback `ProEt.sheafPullback X Ab.{u+1}` lives in `Ab.{u+1}`. Primality of $\ell$ is the instance `[Fact ℓ.Prime]`. Main declarations: `continuous_toZModPow`, `continuous_of_forall_continuous_toZModPow`, `existsUnique_continuousMap_padicInt`, `zmodAbSystem` (with `zmodAbSystem_transition`), `zmodSystem`, `ellAdicSheafLimitIso` and `ellAdicSheafLimitIso_hom_π`, all in `AlgebraicGeometry.Scheme.ProEt`. The limit cone and its limit property are private. The module docstring also says that the transition maps of `zmodSystem` are epimorphisms, but this file has no lemma stating that.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/EllAdicLimit.lean (declarations needed by the transplanted proofs, unused ones removed).

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
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Basic
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
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_AffineTransitionLimit
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Cover_MorphismProperty
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Extensive
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Morphisms_UnderlyingMap
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineEtale
import Definitions.Def_ProEtale_Mathlib_AlgebraicGeometry_Sites_AffineRefinement
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
import Definitions.Def_ProEtale_Topology_Comparison_FreeSheaf
import Definitions.Def_ProEtale_Topology_Comparison_ProetConstantSheaf
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# The `ℓ`-adic sheaf as a limit of `ℤ/ℓⁿ`-sheaves

We identify the (`ULift`ed) `ℓ`-adic sheaf `X.ellAdicSheaf ℓ` on the pro-étale site of a
scheme `X` with the inverse limit of the pullbacks of the constant étale sheaves
`ℤ/ℓⁿℤ`:

- `AlgebraicGeometry.Scheme.ProEt.zmodSystem`: the inverse system
  `n ↦ (constant étale sheaf at ℤ/ℓⁿℤ)` with the reduction maps as transitions; its
  transition maps are epimorphisms.
- `AlgebraicGeometry.Scheme.ProEt.ellAdicSheafLimitIso`:
  `ULift (ellAdicSheaf) ≅ lim_n ν^*(ℤ/ℓⁿℤ)`.

Sectionwise this is the topological statement that `ℤ_[ℓ]` is the inverse limit of the
finite discrete groups `ℤ/ℓⁿℤ`: a continuous map `U → ℤ_[ℓ]` is the same as a compatible
family of continuous maps `U → ℤ/ℓⁿℤ` (`PadicInt.lift` and the fact that the topology of
`ℤ_[ℓ]` is detected by the quotients `toZModPow`).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry
namespace Scheme

namespace ProEt

section Padic

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The projections `ℤ_[ℓ] → ℤ/ℓⁿℤ` are continuous (they are "locally constant": their
fibers are unions of balls of radius `ℓ⁻ⁿ`). -/
lemma continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) := by
  -- The fibers are open: if `toZModPow n x = a` and `‖y - x‖ ≤ ℓ⁻ⁿ`, then
  -- `y - x ∈ Ideal.span {(ℓ : ℤ_[ℓ])^n} = RingHom.ker (toZModPow n)`
  -- (`PadicInt.norm_le_pow_iff_mem_span_pow`, `PadicInt.ker_toZModPow`), so
  -- `toZModPow n y = a`. Hence the map is locally constant
  -- (`IsLocallyConstant.continuous`, or directly `continuous_discrete_rng`-style:
  -- preimages of singletons are open).
  have hℓ : (0 : ℝ) < (ℓ : ℝ) := by
    exact_mod_cast (Fact.out (p := ℓ.Prime)).pos
  refine continuous_def.mpr fun s _ ↦ Metric.isOpen_iff.mpr fun x hx ↦ ?_
  refine ⟨(ℓ : ℝ) ^ (-(n : ℤ) + 1), zpow_pos hℓ _, fun y hy ↦ ?_⟩
  have h1 : ‖y - x‖ < (ℓ : ℝ) ^ (-(n : ℤ) + 1) := by
    rw [← dist_eq_norm]
    exact hy
  have h2 : ‖y - x‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) :=
    (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (y - x) (-(n : ℤ))).mpr h1
  have h3 : PadicInt.toZModPow (p := ℓ) n (y - x) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) n).mp h2
  have h4 : PadicInt.toZModPow (p := ℓ) n y = PadicInt.toZModPow (p := ℓ) n x := by
    rw [map_sub, sub_eq_zero] at h3
    exact h3
  change PadicInt.toZModPow (p := ℓ) n y ∈ s
  rw [h4]
  exact hx

/-- A map into `ℤ_[ℓ]` is continuous as soon as its compositions with all the
projections `toZModPow n` are continuous: the topology of `ℤ_[ℓ]` is the inverse limit
topology. -/
lemma continuous_of_forall_continuous_toZModPow {U : Type*} [TopologicalSpace U]
    (f : U → ℤ_[ℓ]) (hf : ∀ n, Continuous fun x ↦ PadicInt.toZModPow n (f x)) :
    Continuous f := by
  -- Use the metric characterization: for `x₀` and `ε > 0` pick `n` with
  -- `(ℓ : ℝ)⁻¹ ^ n < ε`; on the open set
  -- `{x | toZModPow n (f x) = toZModPow n (f x₀)}` (open by `hf n`, discrete target)
  -- one has `f x - f x₀ ∈ ker (toZModPow n) = span {ℓ^n}`, hence
  -- `‖f x - f x₀‖ ≤ ℓ⁻ⁿ < ε` (`PadicInt.norm_le_pow_iff_mem_span_pow`,
  -- `PadicInt.ker_toZModPow`). Conclude with `Metric.continuous_iff`
  -- (mind `zpow` vs `pow` normalization for the radius).
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt ℓ hε
  have hopen : IsOpen {x : U | PadicInt.toZModPow n (f x) = PadicInt.toZModPow n (f x₀)} :=
    (isOpen_discrete {PadicInt.toZModPow n (f x₀)}).preimage (hf n)
  have hmem : {x : U | PadicInt.toZModPow n (f x) = PadicInt.toZModPow n (f x₀)} ∈
      nhds x₀ := hopen.mem_nhds rfl
  refine Filter.eventually_of_mem hmem fun x hx ↦ ?_
  have h1 : PadicInt.toZModPow (p := ℓ) n (f x - f x₀) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hx
  have h2 : ‖f x - f x₀‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow (p := ℓ) n,
      RingHom.mem_ker]
    exact h1
  calc dist (f x) (f x₀) = ‖f x - f x₀‖ := dist_eq_norm _ _
    _ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := h2
    _ < ε := hn

/-- A compatible family of continuous maps `U → ℤ/ℓⁿℤ` arises from a unique continuous
map `U → ℤ_[ℓ]`. -/
theorem existsUnique_continuousMap_padicInt {U : Type*} [TopologicalSpace U]
    (g : ∀ n, C(U, ZMod (ℓ ^ n)))
    (hg : ∀ n, (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))) ∘
      (g (n + 1)) = g n) :
    ∃! f : C(U, ℤ_[ℓ]), ∀ n x, PadicInt.toZModPow n (f x) = g n x := by
  -- Existence: upgrade `hg` from successive indices to all pairs `m ≤ n` (induction);
  -- form the subring `R ≤ ∀ n, ZMod (ℓ ^ n)` of compatible families
  -- (`Subring` with carrier `{s | ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) _
  -- (s n) = s m}`; closure under the ring operations is componentwise), with the
  -- projections `R →+* ZMod (ℓ ^ n)`; `PadicInt.lift` (with
  -- `PadicInt.lift_spec`) produces `R →+* ℤ_[ℓ]`. The map
  -- `f := fun x ↦ lift ⟨fun n ↦ g n x, _⟩` satisfies `toZModPow n ∘ f = g n`
  -- (`lift_spec` applied pointwise), and is continuous by
  -- `continuous_of_forall_continuous_toZModPow` since
  -- `toZModPow n ∘ f = g n` is continuous.
  -- Uniqueness: two such `f f'` agree pointwise since `toZModPow n (f x) = toZModPow n
  -- (f' x)` for all `n` implies `f x = f' x` (`PadicInt.ext_of_toZModPow` or
  -- `PadicInt.eq_of_forall_toZModPow_eq` — grep for the exact name; it follows from
  -- `PadicInt.dense_range_intCast`-style arguments or directly from
  -- `norm_le_pow_iff_mem_span_pow`: `‖f x - f' x‖ ≤ ℓ⁻ⁿ` for all `n` forces equality).
  -- Upgrade the compatibility from successive indices to all pairs `m ≤ n`.
  have hg' : ∀ (x : U) (m n : ℕ) (h : m ≤ n),
      ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (g n x) = g m x := by
    intro x m n h
    induction n, h using Nat.le_induction with
    | base =>
      rw [ZMod.castHom_apply, ZMod.cast_id]
    | succ n hmn ih =>
      have h1 : ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (g (n + 1) x) =
          g n x := congrFun (hg n) x
      have h2 : ZMod.castHom (pow_dvd_pow ℓ hmn) (ZMod (ℓ ^ m))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (g (n + 1) x)) =
          ZMod.castHom (pow_dvd_pow ℓ (hmn.trans (Nat.le_succ n))) (ZMod (ℓ ^ m))
            (g (n + 1) x) :=
        RingHom.congr_fun
          (ZMod.castHom_comp (pow_dvd_pow ℓ hmn) (pow_dvd_pow ℓ (Nat.le_succ n)))
          (g (n + 1) x)
      calc ZMod.castHom (pow_dvd_pow ℓ (hmn.trans (Nat.le_succ n))) (ZMod (ℓ ^ m))
            (g (n + 1) x)
          = ZMod.castHom (pow_dvd_pow ℓ hmn) (ZMod (ℓ ^ m))
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (g (n + 1) x)) :=
            h2.symm
        _ = ZMod.castHom (pow_dvd_pow ℓ hmn) (ZMod (ℓ ^ m)) (g n x) := by rw [h1]
        _ = g m x := ih
  -- The subring of compatible families in the product of the `ℤ/ℓⁿℤ`.
  let R : Subring (∀ n, ZMod (ℓ ^ n)) :=
    { carrier := {s | ∀ (m n : ℕ) (h : m ≤ n),
        ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (s n) = s m}
      one_mem' := fun m n h ↦ by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) 1 = 1
        rw [map_one]
      mul_mem' := fun {a b} ha hb m n h ↦ by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (a n * b n) = a m * b m
        rw [map_mul, ha m n h, hb m n h]
      zero_mem' := fun m n h ↦ by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) 0 = 0
        rw [map_zero]
      add_mem' := fun {a b} ha hb m n h ↦ by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (a n + b n) = a m + b m
        rw [map_add, ha m n h, hb m n h]
      neg_mem' := fun {a} ha m n h ↦ by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (-(a n)) = -(a m)
        rw [map_neg, ha m n h] }
  -- The compatible projections out of `R`, in the shape required by `PadicInt.lift`.
  have compat : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
      (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k1))).comp
        ((Pi.evalRingHom (fun k ↦ ZMod (ℓ ^ k)) k2).comp R.subtype) =
      (Pi.evalRingHom (fun k ↦ ZMod (ℓ ^ k)) k1).comp R.subtype := by
    intro k1 k2 hk
    refine RingHom.ext fun s ↦ ?_
    exact s.2 k1 k2 hk
  have hmem : ∀ x : U, (fun n ↦ g n x) ∈ R := fun x m n h ↦ hg' x m n h
  -- The candidate map, via the universal property of `ℤ_[ℓ]`.
  have hφ : ∀ (n : ℕ) (x : U),
      PadicInt.toZModPow n (PadicInt.lift compat ⟨fun k ↦ g k x, hmem x⟩) = g n x :=
    fun n x ↦ RingHom.congr_fun (PadicInt.lift_spec compat n) ⟨fun k ↦ g k x, hmem x⟩
  have hcont : Continuous fun x ↦ PadicInt.lift compat ⟨fun k ↦ g k x, hmem x⟩ :=
    continuous_of_forall_continuous_toZModPow ℓ _ fun n ↦
      (g n).continuous.congr fun x ↦ (hφ n x).symm
  refine ⟨⟨fun x ↦ PadicInt.lift compat ⟨fun k ↦ g k x, hmem x⟩, hcont⟩, hφ, ?_⟩
  intro f' hf'
  ext x
  exact PadicInt.ext_of_toZModPow.mp fun n ↦ (hf' n x).trans (hφ n x).symm

end Padic

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian groups, with the reduction maps as
transition maps. -/
noncomputable def zmodAbSystem : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.ofSequence
    (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)).leftOp

set_option linter.unusedSectionVars false in
lemma zmodAbSystem_obj (n : ℕ) :
    (zmodAbSystem ℓ).obj (op n) = AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))) :=
  rfl

set_option linter.unusedSectionVars false in
/-- The transition maps of `zmodAbSystem` are the (`ULift`ed) reduction maps. -/
lemma zmodAbSystem_transition (n : ℕ) :
    SequentialSystem.transition (zmodAbSystem ℓ) n =
      AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom) := by
  -- `Functor.ofSequence_map_homOfLE_succ` (or the corresponding simp lemma) plus
  -- `leftOp`/`op` unfolding; morphisms in `ℕ` are subsingletons.
  exact congrArg Quiver.Hom.unop
    (Functor.ofSequence_map_homOfLE_succ
      (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
      (f := fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)
      n)


/-- The inverse system of constant étale sheaves `ℤ/ℓⁿℤ` on the small étale site. -/
noncomputable def zmodSystem : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}


section LimitCone

/-- Functoriality of `topologicalSheafLiftedMap` in the coefficient map. -/
private lemma topologicalSheafLiftedMap_comp
    (M₁ M₂ M₃ : Type) [TopologicalSpace M₁] [AddCommGroup M₁] [IsTopologicalAddGroup M₁]
    [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M₁ →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafLiftedMap X M₁ f hf ≫ topologicalSheafLiftedMap X M₂ g hg =
      topologicalSheafLiftedMap X M₁ (g.comp f) (hg.comp hf) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro t
  rfl

/-- `topologicalSheafLiftedMap` only depends on the coefficient map. -/
private lemma topologicalSheafLiftedMap_congr (M₁ M₂ : Type)
    [TopologicalSpace M₁] [AddCommGroup M₁] [IsTopologicalAddGroup M₁]
    [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    {f f' : M₁ →+ M₂} {hf : Continuous f} {hf' : Continuous f'} (h : f = f') :
    topologicalSheafLiftedMap X M₁ f hf = topologicalSheafLiftedMap X M₁ f' hf' := by
  subst h
  rfl

/-- The comparison isomorphism between the value of the pulled-back system at `n` and
the sheaf of continuous `ℤ/ℓⁿℤ`-valued maps. -/
private noncomputable def ellAdicIso (n : ℕ) :
    (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj (op n) ≅
      topologicalSheafLifted X (ZMod (ℓ ^ n)) :=
  sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ n))

set_option linter.unusedSectionVars false in
/-- The comparison isomorphisms intertwine the transition maps of the pulled-back system
with postcomposition by the reduction maps. -/
private lemma ellAdicIso_inv_naturality (n : ℕ) :
    (ellAdicIso X ℓ (n + 1)).inv ≫
        SequentialSystem.transition (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n =
      topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology ≫
        (ellAdicIso X ℓ n).inv := by
  -- Identify the transition map of the composed system.
  have h0 : SequentialSystem.transition
        (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n =
      (ProEt.sheafPullback X Ab.{u + 1}).map
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) :=
    congrArg (fun f ↦ (ProEt.sheafPullback X Ab.{u + 1}).map
      ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map f)) (zmodAbSystem_transition ℓ n)
  -- Naturality of the pullback-constant comparison in the coefficient group.
  have hnat1 : (ProEt.sheafPullback X Ab.{u + 1}).map
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
        (sheafPullbackConstantIso X
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))).hom =
      (sheafPullbackConstantIso X
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
        (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)) :=
    (sheafPullbackCompConstantIso X).hom.naturality
      (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))
  -- Naturality of the constant-to-continuous comparison in the coefficient group.
  have hnat2 : constantToTopologicalSheafLifted X (ZMod (ℓ ^ (n + 1))) ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology =
      (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)) ≫
        constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
    constantToTopologicalSheafLifted_naturality X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
  -- The combined naturality square for the `hom` direction.
  have hsq : (ProEt.sheafPullback X Ab.{u + 1}).map
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
        (ellAdicIso X ℓ n).hom =
      (ellAdicIso X ℓ (n + 1)).hom ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology := by
    calc (ProEt.sheafPullback X Ab.{u + 1}).map
          ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
            (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
          (ellAdicIso X ℓ n).hom
        = ((ProEt.sheafPullback X Ab.{u + 1}).map
            ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
              (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
                (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
                  (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
            (sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))).hom) ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
          (Category.assoc _ _ _).symm
      _ = ((sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
            (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
              (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
                (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
                  (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
          congrArg (fun h ↦ h ≫ constantToTopologicalSheafLifted X (ZMod (ℓ ^ n))) hnat1
      _ = (sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
            (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
              (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
                (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
                  (ZMod (ℓ ^ n))).toAddMonoidHom)) ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
          Category.assoc _ _ _
      _ = (sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ (n + 1))) ≫
            topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
              continuous_of_discreteTopology :=
          congrArg (fun h ↦ (sheafPullbackConstantIso X
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫ h) hnat2.symm
      _ = (ellAdicIso X ℓ (n + 1)).hom ≫
            topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
              continuous_of_discreteTopology :=
          (Category.assoc _ _ _).symm
  rw [h0, Iso.inv_comp_eq, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The legs of the limit cone with apex the lifted `ℓ`-adic sheaf. -/
private noncomputable def ellAdicLeg (n : ℕ) :
    topologicalSheafLifted X ℤ_[ℓ] ⟶
      (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj (op n) :=
  topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
      (continuous_toZModPow ℓ n) ≫ (ellAdicIso X ℓ n).inv

/-- The legs are compatible with the transition maps. -/
private lemma ellAdicLeg_succ (n : ℕ) :
    ellAdicLeg X ℓ (n + 1) ≫
        SequentialSystem.transition (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n =
      ellAdicLeg X ℓ n := by
  have hcomp : topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
        (continuous_toZModPow ℓ (n + 1)) ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology =
      topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
        (continuous_toZModPow ℓ n) := by
    refine (topologicalSheafLiftedMap_comp X _ _ _ _ _ _ _).trans
      (topologicalSheafLiftedMap_congr X _ _ ?_)
    refine AddMonoidHom.ext fun z ↦ ?_
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) z
  calc ellAdicLeg X ℓ (n + 1) ≫
        SequentialSystem.transition (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n
      = topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
          (continuous_toZModPow ℓ (n + 1)) ≫
        ((ellAdicIso X ℓ (n + 1)).inv ≫
          SequentialSystem.transition
            (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n) :=
        Category.assoc _ _ _
    _ = topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
          (continuous_toZModPow ℓ (n + 1)) ≫
        (topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology ≫ (ellAdicIso X ℓ n).inv) :=
        congrArg (fun h ↦ topologicalSheafLiftedMap X ℤ_[ℓ]
          (PadicInt.toZModPow (n + 1)).toAddMonoidHom (continuous_toZModPow ℓ (n + 1)) ≫ h)
          (ellAdicIso_inv_naturality X ℓ n)
    _ = (topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
          (continuous_toZModPow ℓ (n + 1)) ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology) ≫ (ellAdicIso X ℓ n).inv :=
        (Category.assoc _ _ _).symm
    _ = topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
          (continuous_toZModPow ℓ n) ≫ (ellAdicIso X ℓ n).inv :=
        congrArg (fun h ↦ h ≫ (ellAdicIso X ℓ n).inv) hcomp
    _ = ellAdicLeg X ℓ n := rfl

/-- The cone over the pulled-back system with apex the lifted `ℓ`-adic sheaf. -/
private noncomputable def ellAdicCone :
    Cone (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) where
  pt := topologicalSheafLifted X ℤ_[ℓ]
  π := SequentialSystem.natTransOfSucc (fun n ↦ ellAdicLeg X ℓ n) (ellAdicLeg_succ X ℓ)

/-- The cone `ellAdicCone` is a limit cone: sectionwise this is the statement that a
continuous map to `ℤ_[ℓ]` is the same as a compatible family of continuous maps to the
`ℤ/ℓⁿℤ`. -/
private noncomputable def isLimitEllAdicCone : IsLimit (ellAdicCone X ℓ) := by
  apply isLimitOfReflects (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
  refine evaluationJointlyReflectsLimits _ fun U ↦ ?_
  apply isLimitOfReflects (CategoryTheory.forget Ab.{u + 1})
  refine ((Types.isLimit_iff _).mpr ?_).some
  intro s hs
  -- The comparison isomorphisms are bijective on sections over `U`.
  have cancel1 : ∀ (n : ℕ)
      (t : ToType (((zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj
        (op n)).obj.obj U)),
      ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) t) = t := by
    intro n t
    have h1 : (ellAdicIso X ℓ n).hom.hom.app U ≫ (ellAdicIso X ℓ n).inv.hom.app U =
        𝟙 (((zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj (op n)).obj.obj U) :=
      congrArg (fun f ↦ f.hom.app U) (ellAdicIso X ℓ n).hom_inv_id
    exact ((ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom h1 t)).trans (ConcreteCategory.id_apply t)
  have cancel2 : ∀ (n : ℕ) (t : ULift.{u + 1} C((unop U).left, ZMod (ℓ ^ n))),
      ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U) t) = t := by
    intro n t
    have h1 : (ellAdicIso X ℓ n).inv.hom.app U ≫ (ellAdicIso X ℓ n).hom.hom.app U =
        𝟙 ((topologicalSheafLifted X (ZMod (ℓ ^ n))).obj.obj U) :=
      congrArg (fun f ↦ f.hom.app U) (ellAdicIso X ℓ n).inv_hom_id
    have h2 := ConcreteCategory.congr_hom h1 t
    have h3 := (ConcreteCategory.comp_apply ((ellAdicIso X ℓ n).inv.hom.app U)
      ((ellAdicIso X ℓ n).hom.hom.app U) t).symm
    have h4 := ConcreteCategory.id_apply
      (X := (topologicalSheafLifted X (ZMod (ℓ ^ n))).obj.obj U) t
    exact (h3.trans h2).trans h4
  -- The transition square on sections over `U`.
  have hBsq : ∀ (n : ℕ) (a : ULift.{u + 1} C((unop U).left, ZMod (ℓ ^ (n + 1)))),
      ConcreteCategory.hom
          ((SequentialSystem.transition
            (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U)
          (ConcreteCategory.hom ((ellAdicIso X ℓ (n + 1)).inv.hom.app U) a) =
        ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
          (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology).hom.app U) a) := by
    intro n a
    have h1 : (ellAdicIso X ℓ (n + 1)).inv.hom.app U ≫
          (SequentialSystem.transition
            (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U =
        (topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology).hom.app U ≫
          (ellAdicIso X ℓ n).inv.hom.app U :=
      congrArg (fun f ↦ f.hom.app U) (ellAdicIso_inv_naturality X ℓ n)
    have h2 := ConcreteCategory.congr_hom h1 a
    have h3 := (ConcreteCategory.comp_apply ((ellAdicIso X ℓ (n + 1)).inv.hom.app U)
      ((SequentialSystem.transition
        (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U) a).symm
    have h4 := ConcreteCategory.comp_apply ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
      continuous_of_discreteTopology).hom.app U) ((ellAdicIso X ℓ n).inv.hom.app U) a
    exact (h3.trans h2).trans h4
  -- The compatible family of continuous maps obtained from the section `s`.
  let g' : ∀ n : ℕ, ULift.{u + 1} C((unop U).left, ZMod (ℓ ^ n)) := fun n ↦
    ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) (s (op n))
  let g : ∀ n : ℕ, C((unop U).left, ZMod (ℓ ^ n)) := fun n ↦ (g' n).down
  have htrans : ∀ n : ℕ,
      ConcreteCategory.hom
        ((SequentialSystem.transition
          (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U)
        (s (op (n + 1))) = s (op n) := fun n ↦ hs ((homOfLE (Nat.le_succ n)).op)
  have hgc : ∀ n : ℕ, ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
      continuous_of_discreteTopology).hom.app U) (g' (n + 1)) = g' n := by
    intro n
    have e1 : ConcreteCategory.hom ((ellAdicIso X ℓ (n + 1)).inv.hom.app U) (g' (n + 1)) =
        s (op (n + 1)) := cancel1 (n + 1) (s (op (n + 1)))
    have e2 : ConcreteCategory.hom
        ((SequentialSystem.transition
          (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ (n + 1)).inv.hom.app U) (g' (n + 1))) =
        s (op n) :=
      (congrArg (fun z ↦ ConcreteCategory.hom
        ((SequentialSystem.transition
          (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U) z) e1).trans
        (htrans n)
    have e3 : ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
        (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology).hom.app U) (g' (n + 1))) = s (op n) :=
      (hBsq n (g' (n + 1))).symm.trans e2
    have e4 : ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
          (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology).hom.app U) (g' (n + 1)))) =
        ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) (s (op n)) :=
      congrArg (fun z ↦ ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) z) e3
    have e6 := cancel2 n (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
      continuous_of_discreteTopology).hom.app U) (g' (n + 1)))
    exact e6.symm.trans e4
  have hgfun : ∀ n : ℕ, (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))) ∘
      (g (n + 1)) = g n := by
    intro n
    have e5 : ULift.up.{u + 1} ((ContinuousMap.mk
        ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)
        continuous_of_discreteTopology).comp (g (n + 1))) = g' n := hgc n
    funext x
    exact ContinuousMap.congr_fun (congrArg ULift.down e5) x
  obtain ⟨f, hf, huniq⟩ := existsUnique_continuousMap_padicInt ℓ g hgfun
  refine ⟨ULift.up f, fun k ↦ ?_, fun y hy ↦ ?_⟩
  · -- The element `ULift.up f` maps to the given section.
    obtain ⟨n⟩ := k
    have p2 : ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U)
        (ULift.up f) = g' n := by
      have p2a : (ContinuousMap.mk ((PadicInt.toZModPow (p := ℓ) n)).toAddMonoidHom
          (continuous_toZModPow ℓ n)).comp f = g n := ContinuousMap.ext fun x ↦ hf n x
      exact congrArg ULift.up.{u + 1} p2a
    have p1 := ConcreteCategory.comp_apply ((topologicalSheafLiftedMap X ℤ_[ℓ]
      (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U)
      ((ellAdicIso X ℓ n).inv.hom.app U) (ULift.up f)
    have p3 := congrArg
      (fun z ↦ ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U) z) p2
    have p4 := cancel1 n (s (op n))
    exact p1.trans (p3.trans p4)
  · -- Uniqueness.
    let y' : ULift.{u + 1} C((unop U).left, ℤ_[ℓ]) := y
    have q1 : ∀ n : ℕ, ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
        (ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
          (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U) y') =
        s (op n) := by
      intro n
      have qa := (ConcreteCategory.comp_apply ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U)
        ((ellAdicIso X ℓ n).inv.hom.app U) y').symm
      exact qa.trans (hy (op n))
    have q2 : ∀ n : ℕ, ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U) y' =
        g' n := by
      intro n
      have qb := congrArg
        (fun z ↦ ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) z) (q1 n)
      have qc := cancel2 n (ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U) y')
      exact qc.symm.trans qb
    have q3 : ∀ (n : ℕ) (x : (unop U).left), PadicInt.toZModPow n (y'.down x) = g n x := by
      intro n x
      have q3a : (ContinuousMap.mk ((PadicInt.toZModPow (p := ℓ) n)).toAddMonoidHom
          (continuous_toZModPow ℓ n)).comp y'.down = g n := congrArg ULift.down (q2 n)
      exact ContinuousMap.congr_fun q3a x
    exact ULift.ext y' (ULift.up f) (huniq y'.down q3)

end LimitCone

/-- **The `ℓ`-adic sheaf is the limit of the `ℤ/ℓⁿℤ`-sheaves**: the `ULift`ed
`X.ellAdicSheaf ℓ` is the inverse limit over `n` of the pullbacks to the pro-étale site
of the constant étale sheaves `ℤ/ℓⁿℤ`. -/
noncomputable def ellAdicSheafLimitIso :
    (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ) ≅
      limit (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) := by
  -- Step 1: identify the diagram. Construct a natural isomorphism
  -- `zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u+1} ≅ D` where
  -- `D : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u+1}` has `D.obj (op n) =
  -- topologicalSheafLifted X (ZMod (ℓ ^ n))` and transition maps
  -- `topologicalSheafLiftedMap` of the reductions: componentwise the isomorphism is
  -- `sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ n))`
  -- (`Proetale/Topology/Comparison/ProetConstantSheaf.lean`), and naturality is
  -- `constantToTopologicalSheafLifted_naturality` combined with the naturality of
  -- `sheafPullbackConstantIso` in the coefficient group (it is `.app` of the functor
  -- isomorphism `sheafPullbackCompConstantIso`, see
  -- `Proetale/Topology/Comparison/FreeSheaf.lean`). Define `D` itself with
  -- `Functor.ofSequence`/`leftOp` as for `zmodAbSystem`, or avoid naming `D` by
  -- building the limit cone for the original diagram directly with components passing
  -- through the isomorphisms.
  -- Step 2: build a cone on the diagram with apex the lifted `ellAdicSheaf`:
  -- the leg at `n` is `topologicalSheafLiftedMap X ℤ_[ℓ] ((PadicInt.toZModPow n).toAddMonoidHom)
  -- (continuous_toZModPow ℓ n)` composed with the step-1 isomorphism (inverted);
  -- cone compatibility from `PadicInt.zmod_cast_comp_toZModPow` and functoriality of
  -- `topologicalSheafLiftedMap` in the coefficient map (prove a small composition
  -- lemma `topologicalSheafLiftedMap_comp` first).
  -- Step 3: the cone is limiting; conclude with
  -- `(limit.isLimit _).conePointUniqueUpToIso` or `IsLimit.conePointUniqueUpToIso`.
  -- For the limiting property: `sheafToPresheaf` creates limits, presheaf limits are
  -- detected by evaluation (`evaluationJointlyReflectsLimits`), and limits in `Ab` are
  -- detected by `forget` (`isLimitOfReflects`); at each `U : X.ProEt` the underlying
  -- cone of types is `C(U.left, ℤ_[ℓ]) → (compatible families of C(U.left, ℤ/ℓⁿ))`
  -- (after `ULift`), which is a bijection onto the sections by
  -- `existsUnique_continuousMap_padicInt`; use `Types.isLimit_iff` or build the
  -- comparison with `Types.limitEquivSections` as in the `IsLimit` arguments of
  -- `Proetale/Topology/Comparison/RepleteExact.lean` (read `shortExact_telescope` and
  -- the helpers there for the established pattern).
  exact (isLimitEllAdicCone X ℓ).conePointUniqueUpToIso
    (limit.isLimit (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}))

/-- The legs of `ellAdicSheafLimitIso`: composing with the limit projections recovers
the reduction maps `ℤ_[ℓ] → ℤ/ℓⁿℤ` on the sheaves of continuous functions, up to the
comparison isomorphism with the pullback of the constant sheaf. -/
lemma ellAdicSheafLimitIso_hom_π (n : ℕ) :
    (ellAdicSheafLimitIso X ℓ).hom ≫
        limit.π (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) (op n) =
      topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
          (continuous_toZModPow ℓ n) ≫
        (sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ n))).inv :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitEllAdicCone X ℓ)
    (limit.isLimit _) (op n)


end ProEt

end Scheme
end AlgebraicGeometry


