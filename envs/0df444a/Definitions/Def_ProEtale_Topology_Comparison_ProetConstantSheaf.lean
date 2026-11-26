-- Prove2me | Definitions.Def_ProEtale_Topology_Comparison_ProetConstantSheaf
-- name    : ProEtale_Topology_Comparison_ProetConstantSheaf
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T18:41:24.789808+00:00
-- url     : https://prove2.me/theorems/d9179469-58af-5d92-9ac0-181debbb9659
-- title:
--   Sheaves of continuous maps on the pro-étale site, and the constant sheaf of a discrete group as a sheaf of continuous maps
-- statement:
--   Let $X$ be a scheme and let $X_{\mathrm{pro\acute et}}$ be its small pro-étale site, whose objects are schemes $U$ with a weakly étale morphism $U \to X$. For a topological abelian group $M$, the presheaf $U \mapsto C(|U|, M)$ of continuous maps from the underlying topological space of a scheme into $M$ is a sheaf for the fpqc topology on schemes; since the pro-étale topology is coarser than the fpqc topology, it restricts to a sheaf of abelian groups on $X_{\mathrm{pro\acute et}}$, which we denote $\mathcal{C}(-,M)$:
--   $$\mathcal{C}(-,M)(U) = C(|U|, M), \qquad U \in X_{\mathrm{pro\acute et}}.$$
--   For $M = \mathbb{Z}_\ell$ this is (definitionally) the $\ell$-adic sheaf of $X$. The file also defines the version of $\mathcal{C}(-,M)$ with values in abelian groups of the next universe, and, for a continuous homomorphism $f \colon M \to M'$, the morphism $\mathcal{C}(-,M) \to \mathcal{C}(-,M')$ given by postcomposition with $f$.
--
--   Now let $M$ be **discrete**. The canonical morphism
--   $$\underline{M} \longrightarrow \mathcal{C}(-,M)$$
--   from the constant pro-étale sheaf $\underline{M}$ is defined as the adjoint (under the constant sheaf / global sections adjunction, using that $X$ is terminal in $X_{\mathrm{pro\acute et}}$) of the map sending $m \in M$ to the constant function with value $m$ on $X$.
--
--   Principal results:
--   1. Sections of $\mathcal{C}(-,M)$ over $U$ are exactly $C(|U|,M)$, and the $\ell$-adic sheaf equals $\mathcal{C}(-,\mathbb{Z}_\ell)$ (both by definition).
--   2. **(Bhatt–Scholze, Lemma 4.2.12.)** For a discrete abelian group $M$, the canonical morphism $\underline{M} \to \mathcal{C}(-,M)$ is an isomorphism of sheaves on $X_{\mathrm{pro\acute et}}$. (A continuous map to a discrete group is locally constant: its fibres form a clopen cover, which is a pro-étale cover; over the empty scheme the empty sieve is covering.)
--   3. Composing with the isomorphism $\nu^{*}\underline{M}_{\mathrm{\acute et}} \cong \underline{M}_{\mathrm{pro\acute et}}$ (from a previously published file), where $\nu^*$ is pullback from the étale to the pro-étale site, one obtains an isomorphism $\nu^{*}\underline{M}_{\mathrm{\acute et}} \cong \mathcal{C}(-,M)$.
--   4. Naturality of $\underline{M} \to \mathcal{C}(-,M)$ in $M$: for an additive map $f\colon M \to M'$ of discrete groups, the square formed with $\underline{f}$ and postcomposition with $f$ commutes.
--
--   These identifications are used to compare the pullbacks of the étale constant sheaves $\mathbb{Z}/\ell^n$ with the sheaves of continuous $\mathbb{Z}/\ell^n$-valued functions, which is the input for the comparison between $\ell$-adic and pro-étale cohomology.
--
--   **Formalization Note** The scheme is `X : Scheme.{u}` and the coefficient group `M : Type` lives in universe $0$, with `[TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]` (and `[DiscreteTopology M]` for the comparison). The sheaf `AlgebraicGeometry.Scheme.ProEt.topologicalSheaf X M` takes values in `Ab.{u}`; `ProEt.topologicalSheafLifted X M` is its `ULift` to `Ab.{u + 1}`, the universe in which the constant sheaf and sheafification are used, and the constant sheaf is applied to `ULift.{u+1} M`. The comparison map is `ProEt.constantToTopologicalSheafLifted`, its invertibility is the instance `ProEt.isIso_constantToTopologicalSheafLifted`, the combined isomorphism is `ProEt.sheafPullbackConstantTopologicalIso`, and naturality is `ProEt.constantToTopologicalSheafLifted_naturality`; postcomposition is `ProEt.topologicalSheafLiftedMap`. The pro-étale site uses weakly étale (not pro-étale) morphisms, as in Mathlib's `Scheme.ProEt`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Bhatt–Scholze, Lemma 4.2.12. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Comparison/ProetConstantSheaf.lean (declarations needed by the transplanted proofs, unused ones removed).

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
import Definitions.Def_ProEtale_Topology_Comparison_Acyclicity
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Sheaves of continuous maps on the pro-étale site and constant sheaves

For a topological abelian group `M`, the presheaf `U ↦ C(U, M)` is a sheaf for the fpqc
topology (`AlgebraicGeometry.continuousMapPresheafAb`), hence restricts to a sheaf on the
pro-étale site of a scheme `X`; for `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ`. We define
this restriction in general (`AlgebraicGeometry.Scheme.ProEt.topologicalSheaf`) together
with its `ULift` to `Ab.{u + 1}` (`ProEt.topologicalSheafLifted`), and prove the key
comparison (BS, Lemma 4.2.12): for a *discrete* abelian group `M`, the canonical map
from the constant sheaf is an isomorphism

- `AlgebraicGeometry.Scheme.ProEt.constantToTopologicalSheafLifted`
- `AlgebraicGeometry.Scheme.ProEt.isIso_constantToTopologicalSheafLifted`
- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackConstantTopologicalIso` (combination with
  the pullback of the constant sheaf from the étale site).

The point is that a continuous map `U → M` to a discrete group is locally constant: its
fibers form a clopen cover of `U`, which is a pro-étale cover, and on each piece the
section is constant. Injectivity is local as well (over the empty scheme the empty sieve
is a cover).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry
namespace Scheme

variable (X : Scheme.{u})

namespace ProEt

section Topological

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, for a topological abelian
group `M`. For `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ` (definitionally, see
`ellAdicSheaf_eq_topologicalSheaf`). -/
noncomputable def topologicalSheaf : Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb M, .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

lemma ellAdicSheaf_eq_topologicalSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    X.ellAdicSheaf ℓ = topologicalSheaf X ℤ_[ℓ] :=
  rfl

/-- The sections of `topologicalSheaf X M` over `U` are the continuous maps
`U.left → M`. -/
lemma topologicalSheaf_obj (U : X.ProEt) :
    (topologicalSheaf X M).obj.obj (op U) = AddCommGrpCat.of C(U.left, M) :=
  rfl

/-- The `ULift` of `topologicalSheaf X M` to `Ab.{u + 1}`. -/
noncomputable def topologicalSheafLifted : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (topologicalSheaf X M)

/-- Postcomposition with a continuous additive map, as a morphism of the lifted
sheaves of continuous maps. -/
noncomputable def topologicalSheafLiftedMap {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    topologicalSheafLifted X M ⟶ topologicalSheafLifted X M' where
  hom :=
    { app := fun U ↦ AddCommGrpCat.uliftFunctor.{u + 1}.map
        (AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (fun g ↦ (ContinuousMap.mk f hf).comp g)
            (fun g₁ g₂ ↦ by ext x; exact map_add f _ _)))
      naturality := by
        -- Componentwise both composites send a continuous map `g : U.left → M` to
        -- `f ∘ g ∘ (restriction)`; this is associativity of composition.
        intro U V h
        apply ConcreteCategory.hom_ext
        intro g
        rfl }

end Topological

section Discrete

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  [DiscreteTopology M]

/-- The canonical morphism from the constant sheaf with values `M` to the sheaf of
continuous `M`-valued maps, for a discrete abelian group `M`: it is the adjoint of the
map sending `m` to the constant function with value `m` on the terminal object. -/
noncomputable def constantToTopologicalSheafLifted :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} M)) ⟶
      topologicalSheafLifted X M :=
  ((constantSheafAdj (ProEt.topology X) Ab.{u + 1}
    (isTerminalMkIdProEt X)).homEquiv _ _).symm
    (AddCommGrpCat.ofHom
      { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })

/-- The presheaf-level constant-functions morphism: the transpose under the
constant-presheaf adjunction of the map sending `m` to the constant function with
value `m` on the terminal object. Its sheafification-transpose is
`constantToTopologicalSheafLifted`. -/
private noncomputable def constantToTopologicalPresheaf :
    (Functor.const (X.ProEt)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} M)) ⟶
      (topologicalSheafLifted X M).obj :=
  ((constantPresheafAdj Ab.{u + 1} (isTerminalMkIdProEt X)).homEquiv _ _).symm
    (AddCommGrpCat.ofHom
      { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })

omit [DiscreteTopology M] in
/-- The component of `constantToTopologicalPresheaf` at `V` sends `m` to the constant
function with value `m` on `V.left`: restricting a constant function along the unique
map to the terminal object yields a constant function, definitionally. -/
private lemma constantToTopologicalPresheaf_app (V : (X.ProEt)ᵒᵖ) (m : ULift.{u + 1} M) :
    (constantToTopologicalPresheaf X M).app V m =
      ULift.up (⟨fun _ ↦ m.down, continuous_const⟩ : C(V.unop.left, M)) :=
  rfl

omit [DiscreteTopology M] in
/-- `constantToTopologicalSheafLifted` is the sheafification-transpose of
`constantToTopologicalPresheaf`. -/
private lemma constantToTopologicalSheafLifted_eq :
    constantToTopologicalSheafLifted X M =
      (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
          (constantToTopologicalPresheaf X M) ≫
        (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).counit.app
          (topologicalSheafLifted X M) := by
  -- The right-hand side is, by definition of `Adjunction.homEquiv`, the transpose of
  -- `constantToTopologicalPresheaf` under the sheafification adjunction; the claim is
  -- then the compatibility of the hom-equivalence of a composite adjunction with the
  -- hom-equivalences of the factors (`Adjunction.comp_homEquiv`).
  have h1 : constantToTopologicalSheafLifted X M =
      ((sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).homEquiv
          ((Functor.const (X.ProEt)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} M)))
          (topologicalSheafLifted X M)).symm
        (constantToTopologicalPresheaf X M) := by
    unfold constantToTopologicalSheafLifted constantSheafAdj
    rw [Adjunction.comp_homEquiv]
    rfl
  exact h1

omit [DiscreteTopology M] in
/-- `constantToTopologicalPresheaf` is locally injective: two constants agreeing as
functions on a nonempty scheme are equal, and over the empty scheme the empty sieve
is covering. -/
private lemma isLocallyInjective_constantToTopologicalPresheaf :
    Presheaf.IsLocallyInjective (ProEt.topology X) (constantToTopologicalPresheaf X M) := by
  constructor
  intro V m₁ m₂ h
  by_cases hV : Nonempty V.unop.left
  · obtain ⟨v⟩ := hV
    have h1 := (constantToTopologicalPresheaf_app X M V m₁).symm.trans
      (h.trans (constantToTopologicalPresheaf_app X M V m₂))
    have h2 : m₁ = m₂ :=
      ULift.ext _ _ (ContinuousMap.congr_fun (congrArg ULift.down h1) v)
    rw [h2, Presheaf.equalizerSieve_self_eq_top]
    exact (ProEt.topology X).top_mem _
  · haveI : IsEmpty V.unop.left := not_nonempty_iff.mp hV
    exact (ProEt.topology X).superset_covering bot_le (ProEt.bot_mem_topology V.unop)

/-- `constantToTopologicalPresheaf` is locally surjective: a continuous map to the
discrete group `M` is locally constant; its clopen fibers form a pro-étale cover by
open immersions, on each piece of which the section is the image of a constant. -/
private lemma isLocallySurjective_constantToTopologicalPresheaf :
    Presheaf.IsLocallySurjective (ProEt.topology X) (constantToTopologicalPresheaf X M) := by
  constructor
  intro V s
  let g : C(V.left, M) := s.down
  -- The fibers of `g` are open (even clopen) since `M` is discrete.
  let O : M → V.left.Opens := fun m ↦
    ⟨g ⁻¹' {m}, (isOpen_discrete _).preimage g.continuous⟩
  -- The fibers as pro-étale objects over `X`: open immersions are étale, hence weakly
  -- étale, and weakly étale morphisms are stable under composition.
  let W : M → X.ProEt := fun m ↦ ProEt.mk ((O m).ι ≫ V.hom)
  let j : ∀ m : M, W m ⟶ V := fun m ↦
    MorphismProperty.Over.homMk (O m).ι rfl trivial
  have hoi : ∀ i : ULift.{u} M, IsOpenImmersion (j i.down).left := fun i ↦
    inferInstanceAs (IsOpenImmersion (O i.down).ι)
  have hsurj : ∀ x : V.left, ∃ i : ULift.{u} M,
      x ∈ Set.range ((j i.down).left.base) := fun x ↦
    ⟨ULift.up (g x), ⟨x, rfl⟩, rfl⟩
  have hcov : Sieve.generate (Presieve.ofArrows (fun i : ULift.{u} M ↦ W i.down)
      (fun i ↦ j i.down)) ∈ ProEt.topology X V :=
    ProEt.generate_ofArrows_mem_topology _ hoi hsurj
  refine (ProEt.topology X).superset_covering ?_ hcov
  rintro T f ⟨Z, h', l, ⟨k⟩, rfl⟩
  refine ⟨ULift.up k.down, ?_⟩
  -- On the fiber over `k.down`, the section `g` restricts to the constant `k.down`.
  have key : ∀ z : T.left, g ((h' ≫ j k.down).left.base z) = k.down := fun z ↦
    ((h'.left.base z).property : g (h'.left.base z).val ∈ ({k.down} : Set M))
  have e1 : (constantToTopologicalPresheaf X M).app (op T) (ULift.up k.down) =
      ULift.up (⟨fun _ ↦ k.down, continuous_const⟩ : C(T.left, M)) :=
    constantToTopologicalPresheaf_app X M (op T) (ULift.up k.down)
  have e2 : (ULift.up (⟨fun _ ↦ k.down, continuous_const⟩ : C(T.left, M)) :
        ULift.{u + 1} C(T.left, M)) =
      ULift.up (g.comp ((h' ≫ j k.down).left.base.hom)) :=
    congrArg ULift.up (ContinuousMap.ext fun z ↦ (key z).symm)
  have e3 : (topologicalSheafLifted X M).obj.map (h' ≫ j k.down).op s =
      ULift.up (g.comp ((h' ≫ j k.down).left.base.hom)) := rfl
  exact e1.trans (e2.trans e3.symm)

/-- **The constant sheaf on the pro-étale site is the sheaf of continuous maps**
(BS, Lemma 4.2.12) for a discrete abelian group `M`. -/
instance isIso_constantToTopologicalSheafLifted :
    IsIso (constantToTopologicalSheafLifted X M) := by
  -- The sheaf category is abelian, hence balanced; it suffices to prove that the map
  -- is a monomorphism and an epimorphism.
  --
  -- **Epi** (via `Sheaf.isLocallySurjective_iff_epi'`): let `U : X.ProEt` and let
  -- `g : C(U.left, M)` be a section of the target (after `ULift`). The fibers
  -- `g ⁻¹' {m}` are clopen (`IsOpen` since `M` is discrete and `g` continuous; closed
  -- as complement of the union of the others), so the open subschemes
  -- `V m := U.left ∣_ᵤ ⟨g ⁻¹' {m}, _⟩` (`Scheme.restrict`/`Scheme.Opens` API), as
  -- pro-étale objects over `X` via the composites with `U.hom` (open immersions are
  -- weakly étale: étale implies weakly étale, plus composition stability — see how the
  -- disjoint-union pieces are built in `exists_surjective_factorization_disjoint`,
  -- `Proetale/Topology/Comparison/Acyclicity.lean`), give a jointly surjective family
  -- of open immersions `V m ⟶ U`, hence a covering sieve by
  -- `ProEt.generate_ofArrows_mem_topology` (same file; index the family by
  -- `ULift.{u} M` if a `Type u` index is required). On each piece, `g` restricts to
  -- the constant function with value `m`, which is in the image of the map (factor
  -- the adjoint through `Presheaf.imageSieve` membership: the constant section over
  -- `V m` is the image of the global section `m` of the constant sheaf restricted to
  -- `V m`; relate the adjoint to the presheaf-level constant-functions map via
  -- `Adjunction.homEquiv` unfolding and `toSheafify`).
  --
  -- **Mono**: via local injectivity. The morphism is, up to the canonical isomorphism
  -- `presheafToSheaf`-image, the sheafification of the presheaf morphism
  -- `ψ : (constant presheaf) ⟶ (continuous maps presheaf)` given by constant
  -- functions. `ψ` is locally injective: if two constants `m₁, m₂` agree as functions
  -- on `U.left`, then either `U.left` is nonempty and `m₁ = m₂` (so the top sieve
  -- works), or `U.left` is empty and the empty sieve is covering
  -- (`ProEt.bot_mem_topology`, cf. its use in
  -- `Proetale/Topology/Comparison/Acyclicity.lean`). Local injectivity passes to the
  -- sheafification (`Presheaf.isLocallyInjective` API: `toSheafify` is locally
  -- bijective and local injectivity is stable under composition with locally
  -- injective maps — see `Mathlib.CategoryTheory.Sites.LocallyInjective`), and a
  -- locally injective morphism of sheaves is a monomorphism
  -- (`Sheaf.mono_of_isLocallyInjective` or the corresponding `iff`).
  --
  -- (Implementation note: instead of mono + epi + balanced, we directly observe that
  -- the presheaf morphism `constantToTopologicalPresheaf` is locally bijective by the
  -- two arguments above, hence a `J.W`-equivalence, so its sheafification is an
  -- isomorphism; the map in question is the sheafification composed with the counit
  -- of the sheafification adjunction at a sheaf, which is an isomorphism.)
  haveI := isLocallyInjective_constantToTopologicalPresheaf X M
  haveI := isLocallySurjective_constantToTopologicalPresheaf X M
  haveI : IsIso ((presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
      (constantToTopologicalPresheaf X M)) := by
    rw [← GrothendieckTopology.W_iff]
    exact (ProEt.topology X).W_of_isLocallyBijective _
  rw [constantToTopologicalSheafLifted_eq]
  infer_instance

/-- The pullback to the pro-étale site of the constant étale sheaf with values `M` is
the sheaf of continuous `M`-valued maps, for `M` discrete. -/
noncomputable def sheafPullbackConstantTopologicalIso :
    (ProEt.sheafPullback X Ab.{u + 1}).obj
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} M))) ≅
      topologicalSheafLifted X M :=
  sheafPullbackConstantIso X (AddCommGrpCat.of (ULift.{u + 1} M)) ≪≫
    asIso (constantToTopologicalSheafLifted X M)

/-- Naturality of `constantToTopologicalSheafLifted` in the coefficient group: for an
additive map `f : M →+ M'` of discrete groups, the square with the constant-sheaf
functor on the left and postcomposition on the right commutes. -/
lemma constantToTopologicalSheafLifted_naturality {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] [DiscreteTopology M'] (f : M →+ M') :
    constantToTopologicalSheafLifted X M ≫
        topologicalSheafLiftedMap X M (f := f) (continuous_of_discreteTopology) =
      (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom f)) ≫
        constantToTopologicalSheafLifted X M' := by
  -- Both sides are adjoints (under `constantSheafAdj ... |>.homEquiv`) of the same map
  -- `ULift M ⟶ (sections of topologicalSheafLifted X M' over the terminal object)`,
  -- by naturality of the adjunction hom-equivalence
  -- (`Adjunction.homEquiv_naturality_left_symm` / `_right_symm`); compute both
  -- transposes on elements (`m ↦` constant function with value `f m`).
  unfold constantToTopologicalSheafLifted
  refine (((constantSheafAdj (ProEt.topology X) Ab.{u + 1}
      (isTerminalMkIdProEt X)).homEquiv_naturality_right_symm _
        (topologicalSheafLiftedMap X M (f := f)
          continuous_of_discreteTopology)).symm.trans ?_).trans
    ((constantSheafAdj (ProEt.topology X) Ab.{u + 1}
      (isTerminalMkIdProEt X)).homEquiv_naturality_left_symm
        (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom f)) _)
  refine congrArg _ ?_
  apply ConcreteCategory.hom_ext
  intro m
  rfl

end Discrete

end ProEt

end Scheme
end AlgebraicGeometry


