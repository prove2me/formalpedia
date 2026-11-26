-- Prove2me | Definitions.Def_ProEtale_Algebra_WContractible_Lib
-- name    : ProEtale_Algebra_WContractible_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:59:31.883808+00:00
-- url     : https://prove2.me/theorems/6ae5e4a1-5315-428b-ba28-3b09399bb8c0
-- title:
--   Restrictions to closed sets of connected components, and modifying $\pi_0(\operatorname{Spec} R)$ along a profinite map (Stacks 097D)
-- statement:
--   This file continues the published file on w-contractible rings (same module) with the ring-theoretic constructions used to build w-contractible covers.
--
--   Let $A$ be a commutative ring and $X = \operatorname{Spec} A$. Clopen subsets $W \subseteq X$ correspond to idempotents $e_W \in A$.
--
--   - **Restriction to a clopen.** $A_W := A[e_W^{-1}]$, the localization of $A$ at the idempotent $e_W$. It is a standard open immersion over $A$, for $W_1 \le W_2$ there is a canonical $A$-algebra map $A_{W_2} \to A_{W_1}$, and the image of $\operatorname{Spec} A_W \to X$ is exactly $W$.
--   - **Restriction to a set of components.** For a subset $T \subseteq \pi_0(X)$ of the space of connected components, let $\mathrm{Res}(T)$ be the colimit, in commutative $A$-algebras, of the rings $A_W$ over the cofiltered poset of clopens $W$ containing the preimage of $T$ in $X$.
--   - **Pullback along a discrete quotient.** For a compact space $T$, a discrete quotient $S$ of $T$ and a continuous map $f : T \to \pi_0(X)$, a ring $\mathrm{Pullback}(S,f)$, defined as the restriction of the finite product $A^S$ to a certain set of components determined by $S$ and $f$.
--   - **Modifying $\pi_0$ along a profinite map (Stacks 097D).** Let $T$ be a compact Hausdorff space and $i : T \to \pi_0(\operatorname{Spec} R)$ continuous. Using $\operatorname{Spec} \mathrm{LC}(T,R) \cong T \times \operatorname{Spec} R$, where $\mathrm{LC}(T,R)$ is the ring of locally constant functions $T \to R$, the ring $D = \mathrm{PullbackProfinite}(R,T,i)$ is the restriction of $\mathrm{LC}(T,R)$ to the closed set of components lying on the graph $\{(t,\mathfrak p) : i(t) = [\mathfrak p]\}$ of $i$.
--
--   Principal results:
--   1. $\mathrm{Res}(T)$ is ind-Zariski over $A$ and $A \to \mathrm{Res}(T)$ is surjective. For each admissible clopen $W$, $\ker(A \to A_W) \subseteq \ker(A \to \mathrm{Res}(T))$, and $V(\ker(A \to A_W)) = W$.
--   2. If $T \subseteq \pi_0(X)$ is closed, the image of $\operatorname{Spec} \mathrm{Res}(T) \to X$ is the preimage of $T$. In general $\operatorname{Spec} \mathrm{Res}(T) \to X$ is a closed embedding.
--   3. $\mathrm{Pullback}(S,f)$ is ind-Zariski over $A^S$ and over $A$.
--   4. The graph of $i$ and the corresponding subsets of $\operatorname{Spec}\mathrm{LC}(T,R)$ and of its $\pi_0$ are closed, and the subset of $\operatorname{Spec}\mathrm{LC}(T,R)$ is a union of connected components.
--   5. $D$ is ind-Zariski over $\mathrm{LC}(T,R)$ and over $R$. The image of $\operatorname{Spec} D$ in $\operatorname{Spec}\mathrm{LC}(T,R)$ is the graph. There is a homeomorphism
--   $$\operatorname{Spec} D \;\cong\; \{(t,\mathfrak p) \in T \times \operatorname{Spec} R : i(t) = [\mathfrak p]\},$$
--   compatible with the projections $\operatorname{Spec} D \to T$ and $\operatorname{Spec} D \to \operatorname{Spec} R$.
--   6. (Stacks 097D) The square with vertices $\operatorname{Spec} D$, $T$, $\operatorname{Spec} R$, $\pi_0(\operatorname{Spec} R)$ and maps $\operatorname{Spec} D \to T$, $\operatorname{Spec} D \to \operatorname{Spec} R$, $i$, and the quotient map $\operatorname{Spec} R \to \pi_0(\operatorname{Spec} R)$ is a pullback square in the category of topological spaces.
--
--   These constructions are used to show that every ring has a faithfully flat ind-étale w-contractible cover: they change the space of connected components of a w-strictly-local ring into an extremally disconnected one.
--
--   **Formalization Note** Everything lives in the namespace `WContractification`, with rings in a single universe `u`. The main declarations are `RestrictClopen`, `Restriction` (defined as a `colimit` in `CommAlgCat A` of `Restriction.diag T`), `Pullback`, `PullbackProfinite`, `PullbackProfinite.fiberHomeo`, `PullbackProfinite.isPullback`, `Restriction.range_algebraMap_specComap` and `Restriction.isClosedEmbedding_algebraMap_specComap`. The fiber product is modelled as the subtype $\{q : T \times \operatorname{Spec} R \mid i(q_1) = \mathrm{mk}(q_2)\}$. Ind-Zariski is the project's notion `Algebra.IndZariski`: a filtered colimit of local isomorphisms. The profinite space $T$ only needs to be compact and Hausdorff here, and the space for `Pullback` only needs to be compact.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 097D; Stacks Project, Tag 04PL. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WContractible.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Algebra_WContractible of the same module.

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
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
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Cones
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
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Algebra_Bijective
import Definitions.Def_ProEtale_Algebra_Contraction_Covers
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
import Definitions.Def_ProEtale_Algebra_ProEtaleContraction
import Definitions.Def_ProEtale_Algebra_PullbackProfinite
import Definitions.Def_ProEtale_Algebra_RetractionsStrictlyHenselian
import Definitions.Def_ProEtale_Algebra_StalkAlgebraic
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WLocal_Lib
import Definitions.Def_ProEtale_Algebra_WLocalization_Basic
import Definitions.Def_ProEtale_Algebra_WLocalization_Ideal
import Definitions.Def_ProEtale_Algebra_WStrictLocalization
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
import Definitions.Def_ProEtale_Mathlib_RingTheory_Localization_Pi
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
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
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ConnectedComponents
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Pullback
import Definitions.Def_ProEtale_Algebra_WContractible

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# w-contractible rings

A ring is w-contractible if it is w-strictly-local and the space of connected components of
its prime spectrum is extremally disconnected.

Every w-contractible ring is indeed contractible in the ind-étale topology in the following
sense: If `R` is w-contractible, then every ind-étale faithfully flat map `R →+* S`
has a retraction.

The ind-étale site has enough contractible objects, in the sense that every ring admits a
faithfully flat, ind-étale algebra that is w-contractible.
-/

universe u


open PrimeSpectrum TopologicalSpace

noncomputable section

namespace WContractification

variable {A : Type u} [CommRing A]

/-!
## The W-Contractification

In this section, we construct w-contractification of w-strictly local rings.
-/

def RestrictClopen (W : Clopens (PrimeSpectrum A)) : Type u :=
  Localization.Away (isIdempotentElemEquivClopens.symm W).val

namespace RestrictClopen

variable {W W₁ W₂ : Clopens (PrimeSpectrum A)}

instance commRing : CommRing (RestrictClopen W) := fast_instance%
  inferInstanceAs <| CommRing <| Localization.Away _

instance algebra : Algebra A (RestrictClopen W) := fast_instance%
  inferInstanceAs <| Algebra A <| Localization.Away _

instance away : IsLocalization.Away (isIdempotentElemEquivClopens.symm W).val
    (RestrictClopen W) :=
  inferInstanceAs <| IsLocalization.Away (isIdempotentElemEquivClopens.symm W).val <|
    Localization.Away (isIdempotentElemEquivClopens.symm W).val

instance isStandardOpenImmersion : Algebra.IsStandardOpenImmersion A (RestrictClopen W) :=
  ⟨(isIdempotentElemEquivClopens.symm W).val, RestrictClopen.away⟩

lemma val_dvd {W₁ W₂ : Clopens (PrimeSpectrum A)} (h : W₁ ≤ W₂) :
    (isIdempotentElemEquivClopens.symm W₂).val ∣
    (isIdempotentElemEquivClopens.symm W₁).val := by
  use (isIdempotentElemEquivClopens.symm W₁).val
  nth_rw 1 [(isIdempotentElemEquivClopens.symm.monotone h).symm, mul_comm]

open IsLocalization Away in
def map {W₁ W₂ : Clopens (PrimeSpectrum A)} (h : W₁ ≤ W₂) :
    RestrictClopen W₂ →ₐ[A] RestrictClopen W₁ where
  toRingHom := lift (isIdempotentElemEquivClopens.symm W₂).val (isUnit_of_dvd _ (val_dvd h))
  commutes' r := by simp

/-- The range of `Spec`-side comap of the algebra map `A → RestrictClopen W` is `W`. -/
lemma range_comap (W : Clopens (PrimeSpectrum A)) :
    Set.range (PrimeSpectrum.comap (algebraMap A (RestrictClopen W))) =
      (W : Set (PrimeSpectrum A)) := by
  rw [localization_away_comap_range (RestrictClopen W) (isIdempotentElemEquivClopens.symm W).val]
  exact congr_arg Opens.carrier (basicOpen_isIdempotentElemEquivClopens_symm W)

end RestrictClopen

open scoped CategoryTheory
open CategoryTheory.Limits Topology PrimeSpectrum ConnectedComponents Continuous

section Restriction
variable (T : Set (ConnectedComponents (PrimeSpectrum A)))

def Restriction.diag :
    {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W}ᵒᵖ ⥤ CommAlgCat A where
  obj W := .of A (RestrictClopen W.unop.val)
  map {X Y} f := CommAlgCat.ofHom (RestrictClopen.map f.unop.le)
  map_id X := by
    apply CommAlgCat.hom_ext
    exact Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton
        (Submonoid.powers (isIdempotentElemEquivClopens.symm X.unop.val).val)) _ _
  map_comp {X _ _} _ _ := by
    apply CommAlgCat.hom_ext
    exact Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton
        (Submonoid.powers (isIdempotentElemEquivClopens.symm X.unop.val).val)) _ _

def Restriction : Type u :=
  colimit (C := CommAlgCat A) (Restriction.diag T)

namespace Restriction

instance commRing : CommRing (Restriction T) :=
  inferInstanceAs <| CommRing <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance algebra : Algebra A (Restriction T) :=
  inferInstanceAs <| Algebra A <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance nonempty_index :
    Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
  ⟨⟨⊤, le_top⟩⟩

instance isCofiltered_index : CategoryTheory.IsCofiltered
    {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} where
  cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ =>
    ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE (Subtype.mk_le_mk.mpr inf_le_left),
      CategoryTheory.homOfLE (Subtype.mk_le_mk.mpr inf_le_right), trivial⟩
  cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩

instance indZariski : Algebra.IndZariski A (Restriction T) := by
  rw [Algebra.IndZariski.iff_ind_isLocalIso]
  exact ⟨_, inferInstance, inferInstance, .colimit (Restriction.diag T),
    fun W => show Algebra.IsLocalIso A (RestrictClopen W.unop.val) from inferInstance⟩

lemma algebraMap_surjective : Function.Surjective (algebraMap A (Restriction T)) := by
  intro x
  -- The forgetful functor preserves filtered colimits, giving joint surjectivity.
  have hc := CategoryTheory.Limits.colimit.isColimit (Restriction.diag T)
  have hc' := CategoryTheory.Limits.isColimitOfPreserves
    (CategoryTheory.forget (CommAlgCat A)) hc
  obtain ⟨⟨j⟩, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hc' x
  -- `algebraMap A (RestrictClopen j.val)` is surjective (localization at an idempotent).
  have hpiece : Function.Surjective (algebraMap A (RestrictClopen j.val)) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (isIdempotentElemEquivClopens.symm j.val).val
      (isIdempotentElemEquivClopens.symm j.val).prop
  obtain ⟨a, ha⟩ := hpiece y
  refine ⟨a, ?_⟩
  simp only [CategoryTheory.Functor.mapCocone_ι_app, colimit.cocone_ι] at hy
  rw [← hy, ← ha]
  exact ((colimit.ι (Restriction.diag T) (Opposite.op j)).hom.commutes a).symm

variable {T}

/-- The zero locus of the kernel of `A → RestrictClopen W` equals `W`. -/
lemma zeroLocus_ker_restrictClopen_eq (W : Clopens (PrimeSpectrum A)) :
    zeroLocus (RingHom.ker (algebraMap A (RestrictClopen W)) : Set A) =
      (W : Set (PrimeSpectrum A)) := by
  rw [← range_comap_of_surjective (RestrictClopen W) (algebraMap A (RestrictClopen W))
        (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _
          (isIdempotentElemEquivClopens.symm W).prop),
      RestrictClopen.range_comap]

/-- For `W` a clopen containing the preimage of `T`, the kernel of `A → RestrictClopen W`
is contained in the kernel of the algebra map into the colimit `Restriction T`. -/
lemma ker_algebraMap_restrictClopen_le
    {W : Clopens (PrimeSpectrum A)} (hW : ConnectedComponents.mk ⁻¹' T ≤ W) :
    RingHom.ker (algebraMap A (RestrictClopen W)) ≤
      RingHom.ker (algebraMap A (Restriction T)) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  let ι : RestrictClopen W →ₐ[A] Restriction T :=
    (colimit.ι (Restriction.diag T) (Opposite.op ⟨W, hW⟩)).hom
  calc algebraMap A (Restriction T) a
      = ι (algebraMap A (RestrictClopen W) a) := (ι.commutes a).symm
    _ = ι 0 := by rw [ha]
    _ = 0 := map_zero _

/-- The image of `Spec(Restriction T) → Spec A` is the preimage of `T` under the projection
`Spec A → π₀(Spec A)`, whenever `T` is closed. -/
lemma range_algebraMap_specComap (h : IsClosed T) :
    Set.range (PrimeSpectrum.comap <| algebraMap A (Restriction T)) =
      ConnectedComponents.mk ⁻¹' T := by
  rw [range_comap_of_surjective _ _ (algebraMap_surjective T)]
  refine Set.Subset.antisymm ?_ ?_
  · -- ⊆: any prime in `V(ker)` lies in every clopen containing the preimage of `T`,
    -- hence in the intersection of all such clopens, which is the preimage of `T`
    -- by Stacks 04PL.
    intro p hp
    have hp_mem_W : ∀ (W : Clopens (PrimeSpectrum A)),
        ConnectedComponents.mk ⁻¹' T ≤ W → p ∈ (W : Set (PrimeSpectrum A)) := fun W hW ↦ by
      rw [← zeroLocus_ker_restrictClopen_eq W]
      exact zeroLocus_anti_mono (ker_algebraMap_restrictClopen_le (T := T) hW) hp
    obtain ⟨J, hJ⟩ := isClosed_and_iUnion_connectedComponent_eq_iff.mp
      ⟨h.preimage ConnectedComponents.continuous_coe,
        _, ConnectedComponents.iUnion_connectedComponent_preimage_mk T⟩
    rw [← hJ]
    simp only [Set.iInter_coe_set, Set.mem_iInter, Subtype.forall]
    intro V hV hVJ
    refine hp_mem_W ⟨V, hV⟩ ?_
    rw [← hJ]
    exact Set.iInter_subset_of_subset ⟨⟨V, hV⟩, hVJ⟩ le_rfl
  · -- ⊇: given `a ∈ ker(A → Restriction T)`, the equality criterion for filtered colimits
    -- yields a clopen `W ⊇ T` at which `a` already vanishes. Then `p ∈ W` forces `a ∈ p`.
    intro p hp
    rw [mem_zeroLocus]
    intro a ha
    rw [SetLike.mem_coe, RingHom.mem_ker] at ha
    let ι_top := colimit.ι (Restriction.diag T) (Opposite.op ⟨(⊤ : Clopens _), le_top⟩)
    have heq_in_colim : ι_top.hom (algebraMap A (RestrictClopen ⊤) a) =
        ι_top.hom (0 : RestrictClopen ⊤) :=
      (ι_top.hom.commutes a).trans (ha.trans (map_zero ι_top.hom).symm)
    obtain ⟨k, f, g, hfg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff
        (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A))
        (isColimitOfPreserves (CategoryTheory.forget (CommAlgCat A))
          (colimit.isColimit (Restriction.diag T)))).mp heq_in_colim
    let W := k.unop.val
    have hW : ConnectedComponents.mk ⁻¹' T ≤ W := k.unop.property
    have hf_alg : (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)).map f
        (algebraMap A (RestrictClopen ⊤) a) = algebraMap A (RestrictClopen W) a :=
      ((Restriction.diag T).map f).hom.commutes a
    have ha_zero : algebraMap A (RestrictClopen W) a = 0 := by
      rw [← hf_alg, hfg]
      exact map_zero ((Restriction.diag T).map g).hom
    have hker_le : RingHom.ker (algebraMap A (RestrictClopen W)) ≤ p.asIdeal := by
      rw [← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus]
      exact zeroLocus_ker_restrictClopen_eq W ▸ hW hp
    exact hker_le (RingHom.mem_ker.mpr ha_zero)

/-- The map `Spec(Restriction T) → Spec A` is a closed embedding. -/
lemma isClosedEmbedding_algebraMap_specComap :
    IsClosedEmbedding (PrimeSpectrum.comap <| algebraMap A (Restriction T)) :=
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective (Restriction T)
    (algebraMap A (Restriction T)) (algebraMap_surjective T)

end Restriction

end Restriction

section Pullback

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] (S : DiscreteQuotient T)
  (f : C(T, ConnectedComponents (PrimeSpectrum A)))

def Z := Set.range fun t ↦ connectedComponentsMap (PrimeSpectrum.continuous_sigmaToPi fun _ ↦ A) <|
  connectedComponentsMap Prod.continuous_toSigma (prodMap.symm (mkHomeomorph _ (S.proj t), f t))

def Pullback := Restriction (Z S f)

namespace Pullback

instance commRing : CommRing (Pullback S f) :=
  inferInstanceAs <| CommRing <| Restriction (Z S f)

instance algebra' : Algebra (S → A) (Pullback S f) :=
  inferInstanceAs <| Algebra (S → A) <| Restriction (Z S f)

instance algebra : Algebra A (Pullback S f) :=
  Algebra.compHom _ (Pi.ringHom fun _ : S ↦ RingHom.id A)

instance isScalarTower : IsScalarTower A (S → A) (Pullback S f) :=
  .of_algebraMap_eq' rfl

variable {T : Type u} [TopologicalSpace T] [CompactSpace T] (S : DiscreteQuotient T)
  (f : C(T, ConnectedComponents (PrimeSpectrum A)))

instance indZariski' : Algebra.IndZariski (S → A) (Pullback S f) :=
  inferInstanceAs <| Algebra.IndZariski (S → A) <| Restriction (Z S f)

instance indZariski : Algebra.IndZariski A (Pullback S f) :=
  .trans A (S → A) (Pullback S f)


-- Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting for 1.123

end Pullback

end Pullback

section PullbackProfinite

/-!
## Modifying the connected components along a profinite map (Stacks 097D)

Given a ring `R` and a continuous map `i : T → π₀(Spec R)` from a profinite space, we
construct an ind-Zariski `R`-algebra `PullbackProfinite R T i` realizing the cartesian
square
```
Spec D --→ T
  |        |
  ↓        ↓
Spec R --→ π₀(Spec R)
```
of topological spaces. Following the identification
`Spec (LocallyConstant T R) ≃ₜ T × Spec R` (see `Proetale.Algebra.PullbackProfinite`),
the ring is obtained as the `Restriction` of `LocallyConstant T R` to the closed subset
of connected components lying on the graph of `i`. This computes the Stacks 097D
colimit `A^f_{π₀} = colim_q A^f_q` in a single step.
-/

open LocallyConstant TopCat

variable (R : Type u) [CommRing R]
variable (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T]
variable (i : C(T, ConnectedComponents (PrimeSpectrum R)))

namespace PullbackProfinite

/-- The graph of `i` inside `T × Spec R`. -/
def graph : Set (T × PrimeSpectrum R) :=
  {q | i q.1 = ConnectedComponents.mk q.2}

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
lemma isClosed_graph : IsClosed (graph R T i) :=
  isClosed_eq (i.continuous.comp continuous_fst)
    (ConnectedComponents.continuous_coe.comp continuous_snd)

/-- The set of primes of `LocallyConstant T R` lying on the graph of `i`. -/
def specGraph : Set (PrimeSpectrum (LocallyConstant T R)) :=
  toPrimeSpectrum '' graph R T i

lemma isClosed_specGraph : IsClosed (specGraph R T i) :=
  (homeomorphPrimeSpectrum (T := T) (R := R)).isClosedMap _ (isClosed_graph R T i)

/-- `specGraph` is a union of connected components: connected components of
`T × Spec R` are of the form `{t} × C` and both `i ∘ fst` and `π₀ ∘ snd` are constant
on them. -/
lemma connectedComponent_subset_specGraph {P : PrimeSpectrum (LocallyConstant T R)}
    (hP : P ∈ specGraph R T i) :
    connectedComponent P ⊆ specGraph R T i := by
  obtain ⟨⟨t, x⟩, hq, rfl⟩ := hP
  intro P' hP'
  set e := homeomorphPrimeSpectrum (T := T) (R := R) with he
  have h1 : e.symm P' ∈ connectedComponent (e.symm (toPrimeSpectrum (t, x))) :=
    e.symm.continuous.image_connectedComponent_subset _ ⟨P', hP', rfl⟩
  have h2 : e.symm (toPrimeSpectrum (t, x)) = (t, x) := e.symm_apply_apply (t, x)
  rw [h2, connectedComponent.prod, connectedComponent_eq_singleton] at h1
  have hfst : (e.symm P').1 = t := Set.mem_singleton_iff.mp h1.1
  have hmk : ConnectedComponents.mk (e.symm P').2 = ConnectedComponents.mk x :=
    ConnectedComponents.coe_eq_coe'.mpr h1.2
  refine ⟨e.symm P', ?_, e.apply_symm_apply P'⟩
  change i (e.symm P').1 = ConnectedComponents.mk (e.symm P').2
  rw [hfst, hmk]
  exact hq

/-- The closed subset of `π₀(Spec (LocallyConstant T R))` of components lying on the
graph of `i`. -/
def Z : Set (ConnectedComponents (PrimeSpectrum (LocallyConstant T R))) :=
  ConnectedComponents.mk '' specGraph R T i

lemma preimage_mk_Z : ConnectedComponents.mk ⁻¹' Z R T i = specGraph R T i := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro P ⟨P', hP', hmk⟩
  exact connectedComponent_subset_specGraph R T i hP'
    (ConnectedComponents.coe_eq_coe'.mp hmk.symm)

lemma isClosed_Z : IsClosed (Z R T i) :=
  ConnectedComponents.continuous_coe.isClosedMap _ (isClosed_specGraph R T i)

end PullbackProfinite

/-- The modification of the connected components of `Spec R` along the continuous map
`i : T → π₀(Spec R)` from a profinite space: an ind-Zariski `R`-algebra `D` with
`Spec D = Spec R ×_{π₀(Spec R)} T`, see `PullbackProfinite.isPullback`. This is the
ring `A^f_{π₀}` of Stacks 097D, realized as the restriction of `LocallyConstant T R`
to the components on the graph of `i`. -/
@[stacks 097D]
def PullbackProfinite : Type u :=
  Restriction (PullbackProfinite.Z R T i)

namespace PullbackProfinite

instance commRing : CommRing (PullbackProfinite R T i) :=
  inferInstanceAs <| CommRing <| Restriction _

instance algebra' : Algebra (LocallyConstant T R) (PullbackProfinite R T i) :=
  inferInstanceAs <| Algebra _ <| Restriction _

instance algebra : Algebra R (PullbackProfinite R T i) :=
  Algebra.compHom _ (algebraMap R (LocallyConstant T R))

instance isScalarTower :
    IsScalarTower R (LocallyConstant T R) (PullbackProfinite R T i) :=
  .of_algebraMap_eq' rfl

instance indZariski' :
    Algebra.IndZariski (LocallyConstant T R) (PullbackProfinite R T i) :=
  inferInstanceAs <| Algebra.IndZariski _ <| Restriction _

instance indZariski : Algebra.IndZariski R (PullbackProfinite R T i) :=
  Algebra.IndZariski.trans R (LocallyConstant T R) (PullbackProfinite R T i)

lemma range_comap_algebraMap :
    Set.range (PrimeSpectrum.comap
      (algebraMap (LocallyConstant T R) (PullbackProfinite R T i))) = specGraph R T i :=
  (Restriction.range_algebraMap_specComap (isClosed_Z R T i)).trans
    (preimage_mk_Z R T i)

/-- The projection `Spec D → T`. -/
noncomputable def projT : C(PrimeSpectrum (PullbackProfinite R T i), T) :=
  ⟨fun y ↦ ((homeomorphPrimeSpectrum (T := T) (R := R)).symm
      (PrimeSpectrum.comap (algebraMap (LocallyConstant T R) (PullbackProfinite R T i)) y)).1,
    continuous_fst.comp ((homeomorphPrimeSpectrum (T := T) (R := R)).symm.continuous.comp
      (PrimeSpectrum.continuous_comap _))⟩

/-- The structure map `Spec D → Spec R`. -/
def projSpec : C(PrimeSpectrum (PullbackProfinite R T i), PrimeSpectrum R) :=
  ⟨PrimeSpectrum.comap (algebraMap R (PullbackProfinite R T i)),
    PrimeSpectrum.continuous_comap _⟩

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
lemma comap_algebraMap_comap (y : PrimeSpectrum (PullbackProfinite R T i)) :
    PrimeSpectrum.comap (algebraMap R (LocallyConstant T R))
      (PrimeSpectrum.comap
        (algebraMap (LocallyConstant T R) (PullbackProfinite R T i)) y) =
      PrimeSpectrum.comap (algebraMap R (PullbackProfinite R T i)) y := by
  rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]

/-- `Spec D` is homeomorphic to the fiber product of `i : T → π₀(Spec R)` and
`Spec R → π₀(Spec R)`, realized as a subspace of `T × Spec R`. -/
noncomputable def fiberHomeo :
    PrimeSpectrum (PullbackProfinite R T i) ≃ₜ
      {q : T × PrimeSpectrum R // i q.1 = ConnectedComponents.mk q.2} :=
  (((Restriction.isClosedEmbedding_algebraMap_specComap
      (T := Z R T i)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_comap_algebraMap R T i))).trans
    ((homeomorphPrimeSpectrum (T := T) (R := R)).image (graph R T i)).symm)

lemma coe_fiberHomeo (y : PrimeSpectrum (PullbackProfinite R T i)) :
    (fiberHomeo R T i y : T × PrimeSpectrum R) =
      (homeomorphPrimeSpectrum (T := T) (R := R)).symm
        (PrimeSpectrum.comap
          (algebraMap (LocallyConstant T R) (PullbackProfinite R T i)) y) :=
  rfl

lemma fst_fiberHomeo (y : PrimeSpectrum (PullbackProfinite R T i)) :
    (fiberHomeo R T i y).1.1 = projT R T i y := by
  rw [coe_fiberHomeo]
  rfl

lemma snd_fiberHomeo (y : PrimeSpectrum (PullbackProfinite R T i)) :
    (fiberHomeo R T i y).1.2 = projSpec R T i y := by
  rw [coe_fiberHomeo, homeomorphPrimeSpectrum_symm_snd, comap_algebraMap_comap]
  rfl

/-- The square
```
Spec D --→ T
  |        |
  ↓        ↓
Spec R --→ π₀(Spec R)
```
is cartesian in the category of topological spaces. This is
`thm:modify-pi0-profinite-properties` (Stacks 097D) in the blueprint. -/
@[stacks 097D]
theorem isPullback :
    CategoryTheory.IsPullback (ofHom (projT R T i)) (ofHom (projSpec R T i)) (ofHom i)
      (ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) := by
  have hcomm : ofHom (projT R T i) ≫ ofHom i = ofHom (projSpec R T i) ≫
      ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
    ext y
    change i (projT R T i y) = ConnectedComponents.mk (projSpec R T i y)
    rw [← fst_fiberHomeo, ← snd_fiberHomeo]
    exact (fiberHomeo R T i y).2
  refine CategoryTheory.IsPullback.of_iso_pullback ⟨hcomm⟩
    (isoOfHomeo (fiberHomeo R T i) ≪≫ (pullbackIsoProdSubtype _ _).symm) ?_ ?_
  · rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Category.assoc, CategoryTheory.Iso.symm_hom,
      pullbackIsoProdSubtype_inv_fst]
    ext y
    exact fst_fiberHomeo R T i y
  · rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Category.assoc, CategoryTheory.Iso.symm_hom,
      pullbackIsoProdSubtype_inv_snd]
    refine TopCat.hom_ext (ContinuousMap.ext fun y ↦ ?_)
    exact snd_fiberHomeo R T i y


end PullbackProfinite

end PullbackProfinite

end WContractification

end


variable {R : Type u} [CommRing R]


variable (R)


