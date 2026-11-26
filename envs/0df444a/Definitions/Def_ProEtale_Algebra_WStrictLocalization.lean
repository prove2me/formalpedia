-- Prove2me | Definitions.Def_ProEtale_Algebra_WStrictLocalization
-- name    : ProEtale_Algebra_WStrictLocalization
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:54:07.41749+00:00
-- url     : https://prove2.me/theorems/a3aa2abc-37bf-47b0-9c89-a917627fc9c9
-- title:
--   The w-strict localization: every ring has a faithfully flat, ind-étale, w-strictly-local algebra
-- statement:
--   Let $R$ be a commutative ring and $R_w$ its w-localization. Let $I \subseteq R_w$ be the vanishing ideal of the set of closed points of $\operatorname{Spec} R_w$, so that $V(I)$ is exactly the set of closed points. Let $T$ be the ind-étale contraction of $R_w$, and $IT$ the extension of $I$ to $T$.
--
--   The **w-strict localization** of $R$ is the w-localization of $T$ with respect to the ideal $IT$:
--   $$R^{\mathrm{wsl}} := T_{w, IT}, \qquad T = \mathrm{IndEtaleContraction}(R_w).$$
--   It is an algebra over $T$, over $R_w$ and over $R$, with compatible scalar towers.
--
--   Principal results (Stacks 097X):
--   1. $R^{\mathrm{wsl}}$ is ind-étale and faithfully flat over $R_w$ and over $R$.
--   2. $R^{\mathrm{wsl}}$ is w-local. Its closed points are exactly the zero locus of the extension of $I$ to $R^{\mathrm{wsl}}$.
--   3. $R^{\mathrm{wsl}}$ is w-strictly-local: it is w-local and its localization at every maximal ideal is strictly henselian.
--
--   This is the second step towards w-contractible covers: every ring admits a faithfully flat ind-étale map to a w-strictly-local ring.
--
--   **Formalization Note** The definitions are `WStrictLocalization.closedIdeal`, `WStrictLocalization.contractionIdeal` and `WStrictLocalization R := (contractionIdeal R).WLocalization`, in the same universe as $R$. The main instances are `WStrictLocalization.indEtale`, `faithfullyFlat`, `isWLocalRing` and `isWStrictlyLocalRing`, plus the lemma `zeroLocus_map_eq_closedPoints`. `IsWStrictlyLocalRing` extends `IsWLocalRing` with strict henselianity of `Localization.AtPrime m` for each maximal `m`. `IndEtaleContraction` and `Ideal.WLocalization` are the project's constructions from the published contraction and w-localization files.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 097X. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WStrictLocalization.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
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
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Ring.Fin
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
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
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
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.JacobsonSpace
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
import Definitions.Def_ProEtale_Algebra_Contraction_Covers
import Definitions.Def_ProEtale_Algebra_Etale
import Definitions.Def_ProEtale_Algebra_Etale_Lib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat_Lib
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Algebra_IndEtale
import Definitions.Def_ProEtale_Algebra_IndEtale_Lib
import Definitions.Def_ProEtale_Algebra_IndZariski
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_LocalizationColimit
import Definitions.Def_ProEtale_Algebra_ProEtaleContraction
import Definitions.Def_ProEtale_Algebra_RetractionsStrictlyHenselian
import Definitions.Def_ProEtale_Algebra_StalkAlgebraic
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WLocal_Lib
import Definitions.Def_ProEtale_Algebra_WLocalization_Basic
import Definitions.Def_ProEtale_Algebra_WLocalization_Ideal
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_FromPi1_Etale
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
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
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Prod
import Definitions.Def_ProEtale_Mathlib_RingTheory_Flat_FaithfullyFlat_Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_GoingDown
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents
import Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
import Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_Topology
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# w-strict-localization

In this file we show that every ring admits a faithfully flat, ind-étale w-strictly-local
algebra, following the blueprint (`thm:ind-etale-w-strictly-local-cover`, Stacks 097X):
starting from `R`, pass to the w-localization `R_w`, take the ind-étale contraction
`T = IndEtaleContraction R_w` (whose local rings at maximal ideals are strictly henselian),
and finally w-localize `T` along the pullback of the ideal `I` cutting out the closed points
of `Spec R_w`. The last step produces a w-local ring whose closed points lie over maximal
ideals of `T`, so its local rings at maximal ideals remain strictly henselian.
-/

universe u

open PrimeSpectrum

variable (R : Type u) [CommRing R]

namespace WStrictLocalization

/-- The radical ideal of the w-localization of `R` cutting out the closed points. -/
noncomputable def closedIdeal : Ideal (WLocalization R) :=
  vanishingIdeal (closedPoints (PrimeSpectrum (WLocalization R)))

lemma zeroLocus_closedIdeal :
    zeroLocus (closedIdeal R) = closedPoints (PrimeSpectrum (WLocalization R)) := by
  rw [closedIdeal, zeroLocus_vanishingIdeal_eq_closure,
    IsClosed.closure_eq IsWLocalRing.wLocalSpace_primeSepectrum.isClosed_closedPoints]

/-- The pullback of `closedIdeal R` to the ind-étale contraction of the w-localization. -/
noncomputable def contractionIdeal : Ideal (IndEtaleContraction (WLocalization R)) :=
  (closedIdeal R).map
    (algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R)))

end WStrictLocalization

/-- The w-strict localization of a ring `R`: a faithfully flat, ind-étale, w-strictly-local
`R`-algebra. It is obtained as the w-localization, along the closed points of `Spec R_w`,
of the ind-étale contraction of the w-localization `R_w` of `R`. -/
noncomputable def WStrictLocalization (R : Type u) [CommRing R] : Type u :=
  (WStrictLocalization.contractionIdeal R).WLocalization

namespace WStrictLocalization

noncomputable instance inst_AlgebraWStrictLocalization_L55 : CommRing (WStrictLocalization R) :=
  inferInstanceAs <| CommRing (contractionIdeal R).WLocalization

noncomputable instance algebraContraction :
    Algebra (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  inferInstanceAs <| Algebra _ (contractionIdeal R).WLocalization

noncomputable instance algebraWLocalization :
    Algebra (WLocalization R) (WStrictLocalization R) :=
  inferInstanceAs <| Algebra (WLocalization R)
    ((closedIdeal R).map
      (algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R)))).WLocalization

instance isScalarTower' : IsScalarTower (WLocalization R)
    (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  inferInstanceAs <| IsScalarTower (WLocalization R) _
    ((closedIdeal R).map
      (algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R)))).WLocalization

end WStrictLocalization

noncomputable instance inst_AlgebraWStrictLocalization_L76 : Algebra R (WStrictLocalization R) :=
  Algebra.compHom _ (algebraMap R (WLocalization R))

instance inst_AlgebraWStrictLocalization_L79 : IsScalarTower R (WLocalization R) (WStrictLocalization R) :=
  .of_algebraMap_eq' rfl

namespace WStrictLocalization

instance indEtale' : Algebra.IndEtale (WLocalization R) (WStrictLocalization R) :=
  have : Algebra.IndZariski (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
    inferInstanceAs <| Algebra.IndZariski _ (contractionIdeal R).WLocalization
  Algebra.IndEtale.trans (WLocalization R) (S := IndEtaleContraction (WLocalization R))
    (WStrictLocalization R)

instance indEtale : Algebra.IndEtale R (WStrictLocalization R) :=
  Algebra.IndEtale.trans R (S := WLocalization R) (WStrictLocalization R)

instance faithfullyFlat' :
    Module.FaithfullyFlat (WLocalization R) (WStrictLocalization R) :=
  Ideal.WLocalization.faithfullyFlat_map_algebraMap (zeroLocus_closedIdeal R)
    (fun _ _ ↦ inferInstance)

instance faithfullyFlat : Module.FaithfullyFlat R (WStrictLocalization R) :=
  Module.FaithfullyFlat.trans R (WLocalization R) (WStrictLocalization R)

instance isWLocalRing : IsWLocalRing (WStrictLocalization R) :=
  inferInstanceAs <| IsWLocalRing (contractionIdeal R).WLocalization

/-- The closed points of the w-strict localization are cut out by the pullback of the
ideal of closed points of `Spec R_w`. -/
lemma zeroLocus_map_eq_closedPoints :
    zeroLocus ((closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R))) =
      closedPoints (PrimeSpectrum (WStrictLocalization R)) :=
  Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq
    (zeroLocus_closedIdeal R) (fun _ _ ↦ inferInstance)

instance isWStrictlyLocalRing : IsWStrictlyLocalRing (WStrictLocalization R) := by
  refine ⟨fun n hn ↦ ?_⟩
  haveI : n.IsPrime := hn.isPrime
  set B' := IndEtaleContraction (WLocalization R)
  -- `n` is a closed point of the w-strict localization, hence contains the pulled-back ideal.
  have hn_mem : (⟨n, inferInstance⟩ : PrimeSpectrum (WStrictLocalization R)) ∈
      zeroLocus ((closedIdeal R).map
        (algebraMap (WLocalization R) (WStrictLocalization R))) := by
    rw [zeroLocus_map_eq_closedPoints]
    exact (isClosed_singleton_iff_isMaximal _).mpr hn
  -- Its restriction `q` to the ind-étale contraction contains `contractionIdeal R`.
  set q : Ideal B' := n.comap (algebraMap B' (WStrictLocalization R)) with hq_def
  haveI : q.IsPrime := Ideal.IsPrime.comap _
  have hq_mem : (⟨q, inferInstance⟩ : PrimeSpectrum B') ∈ zeroLocus (contractionIdeal R) := by
    rw [mem_zeroLocus] at hn_mem ⊢
    intro x hx
    have : algebraMap B' (WStrictLocalization R) x ∈ n := by
      apply hn_mem
      have : (closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R)) =
          (contractionIdeal R).map (algebraMap B' (WStrictLocalization R)) := by
        rw [contractionIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      rw [this]
      exact Ideal.mem_map_of_mem _ hx
    exact this
  -- `q` lies in the zero locus of the pullback of `closedIdeal R`, hence is maximal.
  have hq_closed : (⟨q, inferInstance⟩ : PrimeSpectrum B') ∈ closedPoints (PrimeSpectrum B') :=
    zeroLocus_map_algebraMap_subset_closedPoints
      (fun _ _ ↦ inferInstance) (zeroLocus_closedIdeal R).le hq_mem
  haveI : q.IsMaximal := (isClosed_singleton_iff_isMaximal _).mp hq_closed
  -- The local ring of the contraction at `q` is strictly henselian, and the
  -- ind-Zariski map `B' → WStrictLocalization R` identifies local rings.
  haveI := IsStrictlyHenselianLocalRing.localization_atPrime_indEtaleContraction
    (WLocalization R) q
  haveI : Algebra.IndZariski B' (WStrictLocalization R) :=
    inferInstanceAs <| Algebra.IndZariski _ (contractionIdeal R).WLocalization
  have hbos : Algebra.BijectiveOnStalks B' (WStrictLocalization R) :=
    RingHom.bijectiveOnStalks_algebraMap.mp <|
      RingHom.IndZariski.bijectiveOnStalks
        ((RingHom.IndZariski.algebraMap_iff (R := B') (S := WStrictLocalization R)).mpr
          inferInstance)
  exact IsStrictlyHenselianLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (hbos.bijective_localRingHom n))

end WStrictLocalization


