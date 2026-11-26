-- Prove2me | Definitions.Def_ProEtale_Algebra_IndBijectiveOnStalks
-- name    : ProEtale_Algebra_IndBijectiveOnStalks
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T18:04:14.434181+00:00
-- url     : https://prove2.me/theorems/cbbdcc4a-2868-4c5b-86d8-403a8049a786
-- title:
--   A w-local map of w-local rings that identifies local rings is ind-Zariski
-- statement:
--   Let $R \to S$ be a ring map satisfying the following hypotheses:
--
--   - $R$ and $S$ are **w-local rings**: their spectra are w-local spectral spaces, meaning that the closed points form a closed subset and every point specializes to a unique closed point;
--   - the map **identifies local rings**: for every prime $\mathfrak p \subset S$ with $\mathfrak q = \mathfrak p \cap R$, the induced map $R_{\mathfrak q} \to S_{\mathfrak p}$ is bijective;
--   - the map is **w-local**: the induced map $\operatorname{Spec} S \to \operatorname{Spec} R$ is spectral and sends closed points to closed points.
--
--   The file proves that then
--   $$S \text{ is an ind-Zariski } R\text{-algebra,}$$
--   that is, a filtered colimit of $R$-algebras that are local isomorphisms. This is Stacks 097F.
--
--   The file contains only this statement. According to the docstring, the argument compares $S$ with the ind-Zariski algebra realizing $\operatorname{Spec} R \times_{\pi_0(\operatorname{Spec} R)} \pi_0(\operatorname{Spec} S)$ (Stacks 097D). It uses full faithfulness of maps that identify local rings (Stacks 096L) and the bijectivity criterion for w-local maps (Stacks 097E). The result shows that w-local maps of w-local rings identifying local rings are ind-Zariski, which is used in the theory of w-localizations and w-contractible rings.
--
--   **Formalization Note** The Lean name is `Algebra.BijectiveOnStalks.indZariski_of_isWLocal`. $R$ and $S$ are commutative rings in the same universe `u`. The hypotheses are the typeclasses `[IsWLocalRing R]`, `[IsWLocalRing S]` and `[Algebra.BijectiveOnStalks R S]`, together with an explicit hypothesis `(algebraMap R S).IsWLocal`. The conclusion is `Algebra.IndZariski R S`. `IsWLocalRing` asks that `PrimeSpectrum` be a `WLocalSpace`, a spectral space in which closed specializations are unique and the closed points form a closed set.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 097F; Stacks Project, Tag 097D; Stacks Project, Tag 096L; Stacks Project, Tag 097E. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/IndBijectiveOnStalks.lean (declarations needed by the transplanted proofs, unused ones removed).

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
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.StructureSheaf
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
import Definitions.Def_ProEtale_Algebra_IdentifiesLocalRings
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
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
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
# Ring maps that identify local rings are ind-Zariski locally ind-Zariski

In this file we prove Stacks 097F: a w-local ring map between w-local rings that
identifies local rings is ind-Zariski.

The proof follows the Stacks project: let `f : R → S` be such a map and let
`T = π₀(Spec S)`. The profinite space `T` maps to `π₀(Spec R)`, and the ind-Zariski
`R`-algebra `A' = PullbackProfinite R T i` (Stacks 097D) realizes the topological
pullback `Spec R ×_{π₀(Spec R)} T`. By the universal property there is a continuous map
`Spec S → Spec A'` over `Spec R`, which by fully faithfulness (Stacks 096L,
`Algebra.BijectiveOnStalks.algHomOfContinuousMap`) comes from an `R`-algebra map
`g : A' → S`. The map `g` is a w-local map of w-local rings which identifies local
rings and is bijective on connected components, hence is bijective (Stacks 097E,
`RingHom.IsWLocal.bijective_of_bijective`). Thus `S ≅ A'` is ind-Zariski over `R`.
-/

universe u

open CategoryTheory TopCat PrimeSpectrum WContractification

variable {R S : Type u} [CommRing R] [CommRing S]

variable (R S) in
/-- **Stacks 097F**, algebra version: a w-local map of w-local rings that identifies
local rings is ind-Zariski. -/
@[stacks 097F]
lemma Algebra.BijectiveOnStalks.indZariski_of_isWLocal [Algebra R S] [IsWLocalRing R]
    [IsWLocalRing S] [Algebra.BijectiveOnStalks R S]
    (hw : (algebraMap R S).IsWLocal) :
    Algebra.IndZariski R S := by
  -- The profinite space of connected components of `Spec S` with its map to `π₀(Spec R)`.
  set T := _root_.ConnectedComponents (PrimeSpectrum S) with hT
  let i : C(T, _root_.ConnectedComponents (PrimeSpectrum R)) :=
    ⟨(PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap,
      (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap_continuous⟩
  -- The ind-Zariski `R`-algebra realizing `Spec R ×_{π₀(Spec R)} T`.
  set A' := PullbackProfinite R T i with hA'
  have pb := PullbackProfinite.isPullback R T i
  -- The canonical map `Spec S → Spec A'` over `Spec R` via the pullback property.
  let a : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of T :=
    ofHom ⟨_root_.ConnectedComponents.mk, _root_.ConnectedComponents.continuous_coe⟩
  let b : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of (PrimeSpectrum R) :=
    ofHom ⟨PrimeSpectrum.comap (algebraMap R S), PrimeSpectrum.continuous_comap _⟩
  have w : a ≫ ofHom i =
      b ≫ ofHom ⟨_root_.ConnectedComponents.mk, _root_.ConnectedComponents.continuous_coe⟩ := by
    ext y
    exact (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap_mk y
  let φ : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of (PrimeSpectrum A') := pb.lift a b w
  have hφT : ∀ y, PullbackProfinite.projT R T i (φ y) = _root_.ConnectedComponents.mk y := fun y ↦
    ConcreteCategory.congr_hom (pb.lift_fst a b w) y
  have hφR : ∀ y, PullbackProfinite.projSpec R T i (φ y) =
      PrimeSpectrum.comap (algebraMap R S) y := fun y ↦
    ConcreteCategory.congr_hom (pb.lift_snd a b w) y
  -- The continuous map `Spec S → Spec A'` over `Spec R` as a `HomOver`.
  haveI : Algebra.BijectiveOnStalks R A' :=
    RingHom.bijectiveOnStalks_algebraMap.mp <|
      RingHom.IndZariski.bijectiveOnStalks
        ((RingHom.IndZariski.algebraMap_iff (R := R) (S := A')).mpr inferInstance)
  let Φ : Algebra.BijectiveOnStalks.HomOver R A' S :=
    { toContinuousMap := φ.hom
      comp_comap_algebraMap := fun p ↦ hφR p }
  -- By fully faithfulness (Stacks 096L), `Φ` comes from an `R`-algebra map `g : A' → S`.
  let g : A' →ₐ[R] S := Algebra.BijectiveOnStalks.algHomOfContinuousMap R A' S Φ
  have hg : ∀ p, PrimeSpectrum.comap g.toRingHom p = φ p := fun p ↦
    DFunLike.congr_fun
      (Algebra.BijectiveOnStalks.continuousMapOfAlgHom_algHomOfContinuousMap R A' S Φ) p
  -- `Spec A'` is w-local.
  haveI : IsWLocalRing A' := ⟨ConnectedComponents.wlocalSpace_of_isPullback pb⟩
  -- `g` is a w-local map.
  have hgw : RingHom.IsWLocal g.toRingHom := by
    refine ⟨PrimeSpectrum.isSpectralMap_comap _, fun n hn ↦ ?_⟩
    rw [Set.mem_preimage, hg n,
      ← ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback pb,
      Set.mem_preimage, hφR n]
    exact hw.closedPoints_subset_preimage_closedPoints hn
  -- `g` identifies local rings.
  have hgs : g.toRingHom.BijectiveOnStalks := by
    have h1 : (algebraMap R A').BijectiveOnStalks :=
      RingHom.bijectiveOnStalks_algebraMap.mpr inferInstance
    have h2 : (g.toRingHom.comp (algebraMap R A')).BijectiveOnStalks := by
      have heq : g.toRingHom.comp (algebraMap R A') = algebraMap R S :=
        RingHom.ext fun x ↦ g.commutes x
      rw [heq]
      exact RingHom.bijectiveOnStalks_algebraMap.mpr inferInstance
    exact RingHom.BijectiveOnStalks.of_comp h1 h2
  -- `g` is bijective on connected components.
  have hb : (PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap.Bijective := by
    have hL := ConnectedComponents.lift_bijective_of_isPullback pb
    set L := Continuous.connectedComponentsLift (PullbackProfinite.projT R T i).2 with hLdef
    have hkey : ∀ c, L ((PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap c)
        = c := by
      intro c
      obtain ⟨y, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
      rw [Continuous.connectedComponentsMap_mk, hg y]
      exact hφT y
    constructor
    · intro c₁ c₂ h12
      calc c₁ = L ((PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap c₁) :=
            (hkey c₁).symm
        _ = L ((PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap c₂) := by
            rw [h12]
        _ = c₂ := hkey c₂
    · intro d
      exact ⟨L d, hL.injective (hkey (L d))⟩
  -- Hence `g` is bijective, and `S ≅ A'` is ind-Zariski over `R`.
  have hbij : Function.Bijective g.toRingHom :=
    RingHom.IsWLocal.bijective_of_bijective hgw hgs hb
  exact Algebra.IndZariski.of_equiv R A' S (AlgEquiv.ofBijective g hbij)


