-- Prove2me | Definitions.Def_ProEtale_Algebra_WLocal_Lib
-- name    : ProEtale_Algebra_WLocal_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:44:42.55915+00:00
-- url     : https://prove2.me/theorems/82842209-a83e-476e-865f-4294b2fd9e41
-- title:
--   w-local ring homomorphisms and a bijectivity criterion for maps between w-local rings
-- statement:
--   This file continues the published file *Algebra/WLocal* on w-local rings, i.e. rings whose prime spectrum is a w-local space.
--
--   A ring homomorphism $f : R \to S$ is **w-local** if the induced map $\operatorname{Spec} S \to \operatorname{Spec} R$ is a w-local map of spaces: a spectral map sending closed points to closed points.
--
--   Results:
--
--   1. $f$ is w-local iff $f^{-1}(\mathfrak m)$ is a maximal ideal of $R$ for every maximal ideal $\mathfrak m$ of $S$.
--   2. Let $R$ and $S$ be w-local rings and $f : R \to S$ a w-local homomorphism that is bijective on stalks, i.e. $R_{f^{-1}\mathfrak q} \to S_{\mathfrak q}$ is bijective for every prime $\mathfrak q$ of $S$. If the induced map $\pi_0(\operatorname{Spec} S) \to \pi_0(\operatorname{Spec} R)$ on connected components is bijective, then $f$ is bijective.
--
--   The criterion is used in the study of w-localizations and w-contractible rings.
--
--   **Formalization Note** Main declarations: `RingHom.IsWLocal` (defined as `IsWLocalMap (PrimeSpectrum.comap f)`, for commutative semirings), `RingHom.isWLocal_iff_isMaximal_of_isMaximal` and `RingHom.IsWLocal.bijective_of_bijective`. The w-local ring hypotheses are the instances `[IsWLocalRing R] [IsWLocalRing S]`. Bijectivity on stalks is `RingHom.BijectiveOnStalks`. The condition on components is bijectivity of `connectedComponentsMap` of the continuous map `PrimeSpectrum.comap f`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WLocal.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Algebra_WLocal of the same module.

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient
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
import Definitions.Def_ProEtale_Algebra_LocalIso
import Definitions.Def_ProEtale_Algebra_StalkIso
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_GoingDown
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
import Definitions.Def_ProEtale_Algebra_WLocal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# w-local rings

In this file we define w-local rings. A ring is w-local if its prime spectrum is
a w-local topological space.
-/


attribute [instance] IsWLocalRing.wLocalSpace_primeSepectrum

variable {R S : Type*} [CommRing R] [CommRing S]


/-- A ring homomorphism is w-local if the induced map on spectra is w-local. -/
def RingHom.IsWLocal {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  IsWLocalMap (PrimeSpectrum.comap f)

lemma RingHom.isWLocal_iff_isMaximal_of_isMaximal (f : R →+* S) :
    IsWLocal f ↔ ∀ (m : Ideal S) [m.IsMaximal], (m.comap f).IsMaximal := by
  rw [IsWLocal, isWLocalMap_iff, and_iff_right (PrimeSpectrum.isSpectralMap_comap f)]
  simp_rw [Set.subset_def, Set.mem_preimage, mem_closedPoints_iff,
    PrimeSpectrum.isClosed_singleton_iff_isMaximal, PrimeSpectrum.comap_asIdeal]
  exact ⟨fun h m hm ↦ h ⟨m, hm.isPrime⟩ hm, fun h x hx ↦ @h x.asIdeal hx⟩

namespace RingHom
namespace IsWLocal

/-- A w-local ring map between w-local rings that is bijective on stalks and
bijective on connected components is bijective. -/
lemma bijective_of_bijective [IsWLocalRing R] [IsWLocalRing S] {f : R →+* S} (hw : f.IsWLocal)
    (hs : f.BijectiveOnStalks)
    (hb : (PrimeSpectrum.continuous_comap f).connectedComponentsMap.Bijective) :
    Function.Bijective f := by
  -- Reduce to bijectivity of `PrimeSpectrum.comap f` and then apply `BijectiveOnStalks`.
  refine hs.bijective_of_bijective ⟨?_, ?_⟩
  -- Injectivity of `PrimeSpectrum.comap f`.
  · intro q₁ q₂ heq
    -- Each `qᵢ` specializes to a unique closed point `nᵢ` in `Spec S`.
    obtain ⟨n₁, hn₁_cl, hq₁n₁⟩ := exists_isClosed_specializes q₁
    obtain ⟨n₂, hn₂_cl, hq₂n₂⟩ := exists_isClosed_specializes q₂
    have hn₁_cp := mem_closedPoints_iff.mpr hn₁_cl
    have hn₂_cp := mem_closedPoints_iff.mpr hn₂_cl
    -- `comap f` sends closed points of `Spec S` to closed points of `Spec R` (`hw`).
    have hcomap_n₁_cl : IsClosed ({PrimeSpectrum.comap f n₁} : Set (PrimeSpectrum R)) :=
      mem_closedPoints_iff.mp (hw.closedPoints_subset_preimage_closedPoints hn₁_cp)
    have hcomap_n₂_cl : IsClosed ({PrimeSpectrum.comap f n₂} : Set (PrimeSpectrum R)) :=
      mem_closedPoints_iff.mp (hw.closedPoints_subset_preimage_closedPoints hn₂_cp)
    -- Both `comap f n₁` and `comap f n₂` are closed specializations of `comap f q₁`.
    have h1 : PrimeSpectrum.comap f q₁ ⤳ PrimeSpectrum.comap f n₁ :=
      hq₁n₁.map (PrimeSpectrum.continuous_comap f)
    have h2 : PrimeSpectrum.comap f q₁ ⤳ PrimeSpectrum.comap f n₂ :=
      heq ▸ hq₂n₂.map (PrimeSpectrum.continuous_comap f)
    -- By w-local uniqueness in `Spec R`, they are equal.
    have hcomap_n_eq : PrimeSpectrum.comap f n₁ = PrimeSpectrum.comap f n₂ :=
      WLocalSpace.eq_of_specializes hcomap_n₁_cl hcomap_n₂_cl h1 h2
    -- Hence `n₁` and `n₂` lie in the same connected component of `Spec S`, and as
    -- closed points in a w-local space they coincide.
    obtain rfl : n₁ = n₂ :=
      WLocalSpace.closedPoints_eq_of_mk_eq hn₁_cp hn₂_cp <| hb.1 <| by
        simp [Continuous.connectedComponentsMap_mk, hcomap_n_eq]
    -- Now `q₁, q₂ ≤ n₁` correspond to primes of `S` localised at `n₁`, and the stalk
    -- map at `n₁` is bijective; transport injectivity from `Spec R` to the stalk side.
    have hq₁_le : q₁.asIdeal ≤ n₁.asIdeal :=
      (PrimeSpectrum.le_iff_specializes q₁ n₁).mpr hq₁n₁
    have hq₂_le : q₂.asIdeal ≤ n₁.asIdeal :=
      (PrimeSpectrum.le_iff_specializes q₂ n₁).mpr hq₂n₂
    set m := n₁.asIdeal.comap f
    have hφ_inj : Function.Injective
        (PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl)) :=
      PrimeSpectrum.comap_injective_of_surjective _ (hs n₁.asIdeal).2
    -- Commutativity of the four-square: `algR_R_m ∘ Spec(localRingHom) = comap f ∘ algS_S_n`.
    have hcomm : ∀ (q : PrimeSpectrum (Localization.AtPrime n₁.asIdeal)),
        PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))
          (PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl) q) =
        PrimeSpectrum.comap f
          (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal)) q) := by
      intro q
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 1
      ext x
      simp [Localization.localRingHom_to_map]
    -- Lift `q₁, q₂` to primes of `Localization.AtPrime n₁.asIdeal` via the order iso.
    set oS := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime n₁.asIdeal) n₁.asIdeal
    have hq₁'_val :
        PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal))
          (oS.symm ⟨q₁, hq₁_le⟩) = q₁ :=
      congr_arg Subtype.val (oS.apply_symm_apply ⟨q₁, hq₁_le⟩)
    have hq₂'_val :
        PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal))
          (oS.symm ⟨q₂, hq₂_le⟩) = q₂ :=
      congr_arg Subtype.val (oS.apply_symm_apply ⟨q₂, hq₂_le⟩)
    have hφ_eq :
        PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl) (oS.symm ⟨q₁, hq₁_le⟩) =
        PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl)
          (oS.symm ⟨q₂, hq₂_le⟩) := by
      have hcomap_inj : Function.Injective
          (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))) :=
        Subtype.val_injective.comp
          (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m) m).injective
      exact hcomap_inj <| by rw [hcomm, hcomm, hq₁'_val, hq₂'_val, heq]
    rw [← hq₁'_val, hφ_inj hφ_eq, hq₂'_val]
  -- Surjectivity: via going-down, it suffices to hit every closed point of `Spec R`.
  · letI : Algebra R S := f.toAlgebra
    have : Module.Flat R S :=
      RingHom.flat_of_flat_localRingHom fun P _ ↦ .of_bijective (hs.localRingHom P)
    apply Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
    intro pm hpm
    -- Lift `pm` through the connected-component bijection to a closed point `n₀` of `Spec S`.
    obtain ⟨d, hd⟩ := hb.2 (.mk pm)
    obtain ⟨q₀, rfl⟩ := ConnectedComponents.surjective_coe d
    obtain ⟨n₀, hn₀_cl, hq₀n₀⟩ := exists_isClosed_specializes q₀
    have hn₀_cp : n₀ ∈ closedPoints (PrimeSpectrum S) := mem_closedPoints_iff.mpr hn₀_cl
    have hmk_eq : ConnectedComponents.mk (PrimeSpectrum.comap f n₀) =
        ConnectedComponents.mk pm := by
      rwa [← Specializes.connectedComponents_mk_eq
        (hq₀n₀.map (PrimeSpectrum.continuous_comap f))]
    exact ⟨n₀, WLocalSpace.closedPoints_eq_of_mk_eq
      (hw.closedPoints_subset_preimage_closedPoints hn₀_cp) hpm hmk_eq⟩

end IsWLocal
end RingHom


