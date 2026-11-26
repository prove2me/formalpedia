-- Prove2me | Definitions.Def_ProEtale_Algebra_WLocalization_Ideal
-- name    : ProEtale_Algebra_WLocalization_Ideal
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:51:31.243596+00:00
-- url     : https://prove2.me/theorems/c87755fb-4c2c-4154-bacb-55ccd25a7310
-- title:
--   w-localization with respect to an ideal: w-local ind-Zariski algebras with prescribed closed points and quotient
-- statement:
--   Let $A$ be a commutative ring with w-localization $A \to A_w$, and let $I \subseteq A$ be an ideal. The **w-localization of $A$ with respect to $I$** is the ring
--   $$A_{w,I} = \big(A_w\big)_{1,\,IA_w},$$
--   the localization of $A_w$ at all elements that become units in $A_w/IA_w$ (the generalization of the closed subset $V(IA_w)$ in the sense of the w-localization file). It is an $A_w$-algebra and an $A$-algebra, w-local, and ind-Zariski over $A$. For an $A$-algebra $B$ the construction is applied to the ideal $IB$ of $B$, giving a $B$-algebra $C = (B)_{w,IB}$.
--
--   Principal results (Stacks, Tag 097A): suppose $V(I)$ consists of closed points of $\operatorname{Spec} A$.
--   1. If $A$ is w-local, the generalization $A_{1,I}$ is w-local and $V(IA_{1,I})$ is its set of closed points. For any $A$-algebra $B$ such that $\kappa(\mathfrak q)/\kappa(\mathfrak m)$ is algebraic for every maximal ideal $\mathfrak m$ of $A$ and prime $\mathfrak q$ of $B$ lying over it, $V(IB)$ consists of closed points of $\operatorname{Spec} B$.
--   2. $V(IA_{w,I})$ is exactly the set of closed points of $\operatorname{Spec} A_{w,I}$; the map $\operatorname{Spec} A_{w,I} \to \operatorname{Spec} A$ restricts to a bijection $V(IA_{w,I}) \to V(I)$; and (Tag 097A (2)(a)) the induced map
--   $$A/I \longrightarrow A_{w,I}/IA_{w,I}$$
--   is bijective.
--   3. (Tag 097A (2)(d)) If $A$ is w-local, $V(I)$ equals the set of closed points of $\operatorname{Spec} A$, and $B$ is an $A$-algebra with algebraic residue field extensions over the maximal ideals of $A$ as in (1), then for $C = B_{w,IB}$ one has $V(IC) = $ the set of closed points of $\operatorname{Spec} C$; i.e. the preimage of the closed points of $\operatorname{Spec} A$ is the set of closed points of $\operatorname{Spec} C$.
--   4. Under the hypotheses of (3), if $B$ is faithfully flat over $A$ then so is $C$.
--
--   These are the steps of Stacks Tag 097A: given a w-local $A$ and an $A$-algebra $B$ with algebraic residue extensions, one finds an ind-Zariski $B \to C$ with $B/IB \cong C/IC$, $C$ w-local, and the closed points of $\operatorname{Spec} C$ lying exactly over those of $\operatorname{Spec} A$. It is used to build w-local and w-contractible covers.
--
--   **Formalization Note** All rings live in one universe `Type u`. The ring is `Ideal.WLocalization I`, defined as `Generalization 1 (I.map (algebraMap A (WLocalization A)))`, with instances `Ideal.WLocalization.isWLocalRing`, `.indZariski`, `.algebra`, `.isScalarTower`. Main results: `isWLocalRing_generalization_one`, `IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq`, `zeroLocus_map_algebraMap_subset_closedPoints`, `Ideal.WLocalization.zeroLocus_map_algebraMap_eq_closedPoints`, `Ideal.WLocalization.quotientMap_algebraMap_bijective`, `Ideal.WLocalization.bijOn_zeroLocus_map`, `Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq` and `Ideal.WLocalization.faithfullyFlat_map_algebraMap`. The algebraicity hypothesis is phrased for every maximal `m` of `A` and prime `q` of `B` lying over it, with `Algebra.IsAlgebraic m.ResidueField q.ResidueField`. In (3) the conclusion is literally the equality of `zeroLocus` of the extended ideal with `closedPoints`, and in (2) the hypothesis is only the inclusion of $V(I)$ in the closed points. The statement that the map $\operatorname{Spec} C \to \operatorname{Spec} A$ is w-local (Tag 097A (2)(c)) is not in this file.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 097A; Stacks Project, Tag 097A (2)(a); Stacks Project, Tag 097A (2)(d). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WLocalization/Ideal.lean (declarations needed by the transplanted proofs, unused ones removed).

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
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Ring.Fin
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
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
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
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
import Definitions.Def_ProEtale_Algebra_StalkAlgebraic
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_Algebra_WLocal
import Definitions.Def_ProEtale_Algebra_WLocal_Lib
import Definitions.Def_ProEtale_Algebra_WLocalization_Basic
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_FilteredColimitCommutesProduct
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_IndSpreads
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_ObjectProperty_FiniteProducts
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Field
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
# w-localization w.r.t an ideal

In this file, we define the w-localization w.r.t an ideal and prove [Tag 097A, Stacks Project].

Let `A` be a w-local ring. Let `I ⊆ A` be an ideal cutting out the set `X^c` of closed points
in `X = Spec(A)`. Let `A → B` be a ring map inducing algebraic extensions on residue fields at
primes. Then there exists an ind-Zariski ring map `B → C` such that

- `B/IB → C/IC` is an isomorphism,
- `C` is w-local
- the map `p : Y = Spec C → X` induced by the ring map `A → B → C` is w-local, and
- `p⁻¹(X^c)` is the set of closed points of `Y`.

In particular, the composition `A → B → C` is faithfully flat if `A → B` is faithfully flat.
-/

universe u

open WLocalization PrimeSpectrum

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A)

instance isWLocalRing_generalization_one [IsWLocalRing A] : IsWLocalRing (Generalization 1 I) := by
  have : WLocalSpace (PrimeSpectrum A) := IsWLocalRing.wLocalSpace_primeSepectrum
  rw [isWLocalRing_iff]
  apply Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range
      (f := PrimeSpectrum.comap (algebraMap A (Generalization 1 I)))
  · exact PrimeSpectrum.localization_comap_isEmbedding (Generalization 1 I)
      (Generalization.submonoid 1 I)
  · rw [Generalization.range_algebraMap_generalization]
    apply StableUnderSpecialization.generalizationHull_of_wLocalSpace
    have hlocClosed : Generalization.locClosedSubset 1 I = zeroLocus I := by
      simp [Generalization.locClosedSubset, PrimeSpectrum.basicOpen_one]
    rw [hlocClosed]
    exact (PrimeSpectrum.isClosed_zeroLocus (↑I : Set A)).stableUnderSpecialization

variable {I}

theorem IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq [IsWLocalRing A]
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A (Generalization 1 I))) =
    closedPoints (PrimeSpectrum (Generalization 1 I)) := by
  have : WLocalSpace (PrimeSpectrum A) := IsWLocalRing.wLocalSpace_primeSepectrum
  have hEmb : Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap A (Generalization 1 I))) :=
    PrimeSpectrum.localization_comap_isEmbedding _ (Generalization.submonoid 1 I)
  have hlocClosed : Generalization.locClosedSubset 1 I = zeroLocus I := by
    simp [Generalization.locClosedSubset, PrimeSpectrum.basicOpen_one]
  have hRange : Set.range (PrimeSpectrum.comap (algebraMap A (Generalization 1 I))) =
      generalizationHull (zeroLocus I) := by
    rw [← hlocClosed]
    exact Generalization.range_algebraMap_generalization 1 I
  have hStable : StableUnderSpecialization (Set.range
      (PrimeSpectrum.comap (algebraMap A (Generalization 1 I)))) := by
    rw [hRange]
    exact StableUnderSpecialization.generalizationHull_of_wLocalSpace
      (PrimeSpectrum.isClosed_zeroLocus (↑I : Set A)).stableUnderSpecialization
  rw [hEmb.closedPoints_eq_preimage hStable]
  ext q
  simp only [Set.mem_preimage, mem_closedPoints_iff]
  refine ⟨fun hmem ↦ ?_, fun hclosed ↦ ?_⟩
  · have h1 : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q ∈ zeroLocus I := by
      simp only [mem_zeroLocus, SetLike.coe_subset_coe, comap_asIdeal]
      exact Ideal.map_le_iff_le_comap.mp ((mem_zeroLocus _ _).mp hmem)
    exact mem_closedPoints_iff.mp (hI h1)
  · have hq_in_range : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q ∈
        generalizationHull (zeroLocus I) := hRange ▸ Set.mem_range_self q
    rw [mem_generalizationHull_iff] at hq_in_range
    obtain ⟨y, hy, hspec⟩ := hq_in_range
    have heq : y = PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q :=
      Set.mem_singleton_iff.mp (hspec.mem_closed hclosed (Set.mem_singleton _))
    simp only [mem_zeroLocus, SetLike.coe_subset_coe]
    rw [Ideal.map_le_iff_le_comap]
    have hy' := (mem_zeroLocus _ _).mp hy
    rwa [heq, comap_asIdeal, SetLike.coe_subset_coe] at hy'

theorem zeroLocus_map_algebraMap_subset_closedPoints [Algebra A B]
    (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime]
      [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
      [Localization.AtPrime.IsLiesOverAlgebra m q],
      Algebra.IsAlgebraic m.ResidueField q.ResidueField)
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A B)) ⊆ closedPoints (PrimeSpectrum B) := by
  intro q hq
  simp only [mem_zeroLocus, SetLike.coe_subset_coe, mem_closedPoints_iff,
    isClosed_singleton_iff_isMaximal] at hq ⊢
  set m := comap (algebraMap A B) q with hm_def
  have hm : m.asIdeal.IsMaximal := by
    simpa [isClosed_singleton_iff_isMaximal] using hI (Ideal.le_comap_of_map_le hq)
  have : q.asIdeal.LiesOver m.asIdeal := ⟨PrimeSpectrum.ext_iff.mp hm_def⟩
  letI := Localization.AtPrime.algebraOfLiesOver m.asIdeal q.asIdeal
  have : Algebra.IsAlgebraic m.asIdeal.ResidueField q.asIdeal.ResidueField :=
    h m.asIdeal q.asIdeal
  exact Ideal.IsMaximal.of_isAlgebraic m.asIdeal q.asIdeal

variable (I) in
/--
The w-localization with respect to an ideal `I`.
-/
protected def Ideal.WLocalization : Type u :=
  Generalization 1 (I.map (algebraMap A (WLocalization A)))

namespace Ideal
namespace WLocalization

noncomputable instance commRing : CommRing I.WLocalization := fast_instance%
  inferInstanceAs <| CommRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

instance isWLocalRing : IsWLocalRing I.WLocalization :=
  inferInstanceAs <| IsWLocalRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebraWLocalization : Algebra (WLocalization A) I.WLocalization :=
  fast_instance% inferInstanceAs <| Algebra (WLocalization A) <|
    Generalization 1 (I.map (algebraMap A (WLocalization A)))

instance isLocalization :
    IsLocalization (Generalization.submonoid 1 (I.map (algebraMap A (WLocalization A))))
      I.WLocalization :=
  inferInstanceAs <| IsLocalization _ <|
    Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebra : Algebra A I.WLocalization :=
  Algebra.compHom _ (algebraMap A (WLocalization A))

instance isScalarTower : IsScalarTower A (WLocalization A) I.WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

instance indZariski : Algebra.IndZariski A I.WLocalization :=
  have : Algebra.IndZariski (WLocalization A) I.WLocalization :=
    inferInstanceAs (Algebra.IndZariski (WLocalization A)
      (Generalization 1 (I.map (algebraMap A (WLocalization A)))))
  Algebra.IndZariski.trans (R := A) (S := WLocalization A) (T := I.WLocalization)

theorem zeroLocus_map_algebraMap_eq_closedPoints
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A I.WLocalization)) =
    closedPoints (PrimeSpectrum I.WLocalization) := by
  have hJ : zeroLocus (I.map (algebraMap A (WLocalization A))) ⊆
      closedPoints (PrimeSpectrum (WLocalization A)) :=
    zeroLocus_map_algebraMap_subset_closedPoints (fun m q _ _ _ _ _ ↦ by
      have : Algebra.IsSeparable m.ResidueField q.ResidueField :=
        Algebra.IndEtale.isSeparable_residueField (R := A) (S := WLocalization A) m q
      infer_instance) hI
  have hmap : I.map (algebraMap A I.WLocalization) = (I.map (algebraMap A (WLocalization A))).map
      (algebraMap (WLocalization A) I.WLocalization) := by
    rw [IsScalarTower.algebraMap_eq A (WLocalization A) I.WLocalization, Ideal.map_map]
  rw [hmap]
  exact IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq hJ

variable (I) in
@[stacks 097A "(2)(a)"]
theorem quotientMap_algebraMap_bijective
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Function.Bijective (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map) := by
  set J := I.map (algebraMap A (WLocalization A)) with hJ_def
  have hKJ : I.map (algebraMap A I.WLocalization) =
      J.map (algebraMap (WLocalization A) I.WLocalization) := by
    rw [hJ_def, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hα := WLocalization.quotientMap_algebraMap_bijective_of_ideal (A := A) I hI
  -- Since `Ideal.Quotient.mk J 1 = 1`, `WLocalization A ⧸ J → Localization.Away (mk J 1)` is an
  -- isomorphism via `IsLocalization.atUnits`, so elements of `Generalization.submonoid 1 J`,
  -- which are units in the target, are already units in `WLocalization A ⧸ J`.
  have h1 : Ideal.Quotient.mk J (1 : WLocalization A) = (1 : WLocalization A ⧸ J) := map_one _
  have hpow : Submonoid.powers (Ideal.Quotient.mk J (1 : WLocalization A)) ≤
      IsUnit.submonoid (WLocalization A ⧸ J) := by
    rintro x ⟨n, rfl⟩
    simp [h1]
  let e : (WLocalization A ⧸ J) ≃+*
      Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)) :=
    (IsLocalization.atUnits (WLocalization A ⧸ J)
      (Submonoid.powers (Ideal.Quotient.mk J (1 : WLocalization A)))
      (S := Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A))) hpow).toRingEquiv
  have hsub_unit : ∀ m ∈ Generalization.submonoid 1 J, IsUnit (Ideal.Quotient.mk J m) := by
    intro m hm
    have hu : IsUnit (algebraMap (WLocalization A) (Localization.Away
        (Ideal.Quotient.mk J (1 : WLocalization A))) m) := Submonoid.mem_comap.mp hm
    have heq : algebraMap (WLocalization A) (Localization.Away
        (Ideal.Quotient.mk J (1 : WLocalization A))) m = e (Ideal.Quotient.mk J m) :=
      IsScalarTower.algebraMap_apply (WLocalization A) (WLocalization A ⧸ J) _ m
    rw [heq] at hu
    simpa using hu.map e.symm.toRingHom
  have hβ : Function.Bijective (Ideal.quotientMap
      (J.map (algebraMap (WLocalization A) I.WLocalization))
      (algebraMap (WLocalization A) I.WLocalization) Ideal.le_comap_map) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem,
        ← map_sub (algebraMap (WLocalization A) I.WLocalization),
        IsLocalization.algebraMap_mem_map_algebraMap_iff (Generalization.submonoid 1 J)] at hxy
      obtain ⟨m, hm, hmem⟩ := hxy
      obtain ⟨u, hu⟩ := hsub_unit m hm
      have hprod : Ideal.Quotient.mk J m * Ideal.Quotient.mk J (x - y) = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact hmem
      rw [← hu] at hprod
      have hsub : Ideal.Quotient.mk J (x - y) = 0 := (Units.mul_right_eq_zero u).mp hprod
      rwa [map_sub, sub_eq_zero] at hsub
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨⟨r, s, hs⟩, hrs⟩ := IsLocalization.surj (Generalization.submonoid 1 J) y
      obtain ⟨u, hueq⟩ := hsub_unit s hs
      obtain ⟨t, ht⟩ : ∃ t : WLocalization A, s * t - 1 ∈ J := by
        obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : WLocalization A ⧸ J)
        refine ⟨t, ?_⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, ← hueq, map_one,
          Units.mul_inv, sub_self]
      refine ⟨Ideal.Quotient.mk J (r * t), ?_⟩
      rw [Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      have hu_s : IsUnit (algebraMap (WLocalization A) I.WLocalization s) :=
        IsLocalization.map_units I.WLocalization (⟨s, hs⟩ : Generalization.submonoid 1 J)
      rw [← Ideal.unit_mul_mem_iff_mem _ hu_s]
      have key : algebraMap (WLocalization A) I.WLocalization s *
          (algebraMap (WLocalization A) I.WLocalization (r * t) - y) =
          algebraMap (WLocalization A) I.WLocalization (r * (s * t - 1)) := by
        rw [mul_sub, mul_comm _ y, hrs, ← map_mul, ← map_sub]
        ring_nf
      rw [key]
      exact Ideal.mem_map_of_mem _ (J.mul_mem_left _ ht)
  have hcomp_eq : Ideal.quotientMap (I.map (algebraMap A I.WLocalization))
      (algebraMap A I.WLocalization) I.le_comap_map =
      (Ideal.quotEquivOfEq hKJ.symm).toRingHom.comp ((Ideal.quotientMap _
        (algebraMap (WLocalization A) I.WLocalization) Ideal.le_comap_map).comp
        (Ideal.quotientMap J (algebraMap A (WLocalization A)) I.le_comap_map)) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    change Ideal.Quotient.mk (I.map (algebraMap A I.WLocalization))
        (algebraMap A I.WLocalization a) =
      (Ideal.quotEquivOfEq hKJ.symm) (Ideal.Quotient.mk _
        (algebraMap (WLocalization A) I.WLocalization (algebraMap A (WLocalization A) a)))
    rw [Ideal.quotEquivOfEq_mk,
      IsScalarTower.algebraMap_apply A (WLocalization A) I.WLocalization]
  rw [hcomp_eq]
  exact (Ideal.quotEquivOfEq hKJ.symm).bijective.comp (hβ.comp hα)

variable (I) in
theorem bijOn_zeroLocus_map (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Set.BijOn (PrimeSpectrum.comap (algebraMap A I.WLocalization))
      (zeroLocus (I.map (algebraMap A I.WLocalization))) (zeroLocus I) := by
  rw [← mk_ker (I := I.map _)]
  conv =>
    enter [3, 1, 1]
    rw [← mk_ker (I := I)]
  rw [← range_comap_of_surjective _ _ Quotient.mk_surjective,
    ← range_comap_of_surjective _ _ Quotient.mk_surjective,
    ← Set.image_univ, ← Set.image_univ]
  apply Set.bijOn_image_image (f := PrimeSpectrum.comap
      (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map))
  · intro
    ext1
    simp only [comap_asIdeal, comap_comap, Quotient.mk_comp_algebraMap]
    congr 1
  · rw [Set.bijOn_univ]
    exact (PrimeSpectrum.comapEquiv
      (RingEquiv.ofBijective _ (quotientMap_algebraMap_bijective I hI))).symm.bijective
  · apply Set.InjOn.image_of_comp
    rw [Set.injOn_univ, ← PrimeSpectrum.comap_comp]
    apply PrimeSpectrum.comap_injective_of_surjective
    rw [← Ideal.quotientMap_comp_mk I.le_comap_map]
    simp only [RingHom.coe_comp]
    apply Function.Surjective.comp
    · exact (quotientMap_algebraMap_bijective I hI).surjective
    · exact Ideal.Quotient.mk_surjective

noncomputable instance inst_AlgebraWLocalizationIdeal_L276 [Algebra A B] : Algebra A (I.map (algebraMap A B)).WLocalization :=
  Algebra.compHom _ (algebraMap A B)

instance inst_AlgebraWLocalizationIdeal_L279 [Algebra A B] : IsScalarTower A B (I.map (algebraMap A B)).WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

@[stacks 097A "(2)(d)"]
theorem algebraMap_specComap_preimage_closedPoints_eq [IsWLocalRing A] [Algebra A B]
    (hI : zeroLocus I = closedPoints (PrimeSpectrum A)) (h : ∀ (m : Ideal A) (q : Ideal B)
    [q.LiesOver m] [m.IsMaximal] [q.IsPrime]
    [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra m q],
    Algebra.IsAlgebraic m.ResidueField q.ResidueField) :
    zeroLocus (I.map (algebraMap A (I.map (algebraMap A B)).WLocalization)) =
    closedPoints (PrimeSpectrum (I.map (algebraMap A B)).WLocalization) := by
  set J := I.map (algebraMap A B)
  have hJ_sub : zeroLocus J ⊆ closedPoints (PrimeSpectrum B) :=
    zeroLocus_map_algebraMap_subset_closedPoints h hI.le
  have hmap : I.map (algebraMap A J.WLocalization) = J.map (algebraMap B J.WLocalization) := by
    rw [IsScalarTower.algebraMap_eq A B J.WLocalization, Ideal.map_map]
  rw [hmap]
  exact zeroLocus_map_algebraMap_eq_closedPoints hJ_sub

theorem faithfullyFlat_map_algebraMap [IsWLocalRing A] [Algebra A B] [Module.FaithfullyFlat A B]
    (hI : zeroLocus I = closedPoints (PrimeSpectrum A))
    (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime]
      [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
      [Localization.AtPrime.IsLiesOverAlgebra m q],
      Algebra.IsAlgebraic m.ResidueField q.ResidueField) :
    Module.FaithfullyFlat A (I.map (algebraMap A B)).WLocalization := by
  have : Module.Flat A (I.map (algebraMap A B)).WLocalization :=
    Module.Flat.trans A B (I.map (algebraMap A B)).WLocalization
  have hJ_sub : zeroLocus (I.map (algebraMap A B)) ⊆ closedPoints (PrimeSpectrum B) :=
    zeroLocus_map_algebraMap_subset_closedPoints h hI.le
  apply Module.FaithfullyFlat.of_comap_surjective
  apply Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
  rw [← hI]
  calc
    zeroLocus I ⊆ PrimeSpectrum.comap (algebraMap A B) '' zeroLocus (I.map (algebraMap A B)) := by
      -- This should be separated as a lemma
      intro p hp
      simp only [mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_image] at hp ⊢
      obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat p (B := B)
      refine ⟨q, ?_, hq⟩
      simp only [← hq, comap_asIdeal] at hp
      exact Ideal.map_le_of_le_comap hp
    _ ⊆ PrimeSpectrum.comap (algebraMap A B) ''
        (PrimeSpectrum.comap (algebraMap B (I.map (algebraMap A B)).WLocalization) ''
        zeroLocus (I.map ((algebraMap B (I.map (algebraMap A B)).WLocalization).comp
        (algebraMap A B)))) := by
      apply Set.image_mono
      rw [← Ideal.map_map]
      intro p hp
      rw [(bijOn_zeroLocus_map (map (algebraMap A B) I) hJ_sub).image_eq]
      exact hp
    _ ⊆ _ := by
      rw [← Set.image_comp, ← comap_comp]
      exact Set.image_subset_range _ _

end WLocalization
end Ideal


