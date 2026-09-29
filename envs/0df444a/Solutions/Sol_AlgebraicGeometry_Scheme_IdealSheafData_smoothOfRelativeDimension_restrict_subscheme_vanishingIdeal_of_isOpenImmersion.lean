-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c930e772-a8bd-5cdd-9869-92452cb73c23

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ChartTransfer29

theorem radical_ker {T X : Scheme.{u}} (f : T ⟶ X) [QuasiCompact f] [IsReduced T] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine le_antisymm ?_ Ideal.le_radical
  intro x ⟨n, hn⟩
  rw [RingHom.mem_ker, map_pow] at hn
  rw [RingHom.mem_ker]
  exact IsReduced.eq_zero _ ⟨n, hn⟩

theorem eq_vanishingIdeal_support {X : Scheme.{u}} (I : X.IdealSheafData) (h : I.radical = I) :
    I = Scheme.IdealSheafData.vanishingIdeal I.support := by
  rw [Scheme.IdealSheafData.vanishingIdeal_support, h]

theorem subset_closure_inter_of_isIrreducible {X : Type u} [TopologicalSpace X] {Y U : Set X}
    (hY : IsIrreducible Y) (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) : Y ⊆ closure (Y ∩ U) := by
  intro y hy
  rw [mem_closure_iff]
  intro V hV hyV
  obtain ⟨z, hzY, hzV, hzU⟩ := hY.2 V U hV hU ⟨y, hy, hyV⟩ hne
  exact ⟨z, hzV, hzY, hzU⟩

section

variable {X : Scheme.{u}} (Y : Closeds X) (hY : (Y : Set X) ∈ irreducibleComponents X)
  (A : Type u) [CommRing A] (g : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion g]

include hY in

theorem exists_minimalPrime (hne : (g.base ⁻¹' (Y : Set X)).Nonempty) :
    ∃ P ∈ minimalPrimes A, PrimeSpectrum.zeroLocus (P : Set A) = g.base ⁻¹' (Y : Set X) := by
  have hemb : Topology.IsOpenEmbedding g.base := g.isOpenEmbedding
  have hWirr : IsIrreducible (g.base ⁻¹' (Y : Set X)) := by
    refine hY.1.preimage hemb ?_
    obtain ⟨a, ha⟩ := hne
    exact ⟨g.base a, ha, a, rfl⟩
  have hWcl : IsClosed (g.base ⁻¹' (Y : Set X)) := Y.isClosed.preimage g.continuous
  set P := PrimeSpectrum.vanishingIdeal (g.base ⁻¹' (Y : Set X)) with hP
  have hPprime : P.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hWirr
  have hPZ : PrimeSpectrum.zeroLocus (P : Set A) = g.base ⁻¹' (Y : Set X) := by
    rw [hP, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]; exact hWcl.closure_eq
  refine ⟨P, ?_, hPZ⟩

  refine ⟨⟨hPprime, bot_le⟩, ?_⟩
  rintro Q ⟨hQ, -⟩ hQP

  have hZirr : IsIrreducible (closure (g.base '' PrimeSpectrum.zeroLocus (Q : Set A))) :=
    (((PrimeSpectrum.isIrreducible_zeroLocus_iff Q).2 (by rw [hQ.radical]; exact hQ)).image g.base
      g.continuous.continuousOn).closure
  have hYsub : (Y : Set X) ⊆ closure (g.base '' PrimeSpectrum.zeroLocus (Q : Set A)) := by
    have h1 : (Y : Set X) ⊆ closure ((Y : Set X) ∩ Set.range g.base) :=
      subset_closure_inter_of_isIrreducible hY.1 hemb.isOpenMap.isOpen_range
        (by obtain ⟨a, ha⟩ := hne; exact ⟨g.base a, ha, a, rfl⟩)
    refine h1.trans (closure_mono ?_)
    rintro x ⟨hxY, a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    have : a ∈ PrimeSpectrum.zeroLocus (P : Set A) := by rw [hPZ]; exact hxY
    exact PrimeSpectrum.zeroLocus_anti_mono hQP this
  have hYeq : closure (g.base '' PrimeSpectrum.zeroLocus (Q : Set A)) = (Y : Set X) :=
    le_antisymm (hY.2 hZirr hYsub) hYsub

  have hVQ : PrimeSpectrum.zeroLocus (Q : Set A) ⊆ PrimeSpectrum.zeroLocus (P : Set A) := by
    rw [hPZ]
    intro a ha
    show g.base a ∈ (Y : Set X)
    rw [← hYeq]
    exact subset_closure ⟨a, ha, rfl⟩
  have := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff Q P).1 hVQ
  rwa [hQ.radical] at this

end

end ChartTransfer29

open ChartTransfer29

theorem solution
    {X S : Scheme.{u}} (s : X ⟶ S) (Y : Closeds X) (hY : (Y : Set X) ∈ irreducibleComponents X)
    (A : Type u) [CommRing A] (g : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion g] (n : ℕ)
    (hP : ∀ P : Ideal A, P ∈ minimalPrimes A → PrimeSpectrum.zeroLocus (P : Set A) = g.base ⁻¹' (Y : Set X) →
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ g ≫ s)) :
    SmoothOfRelativeDimension n
      (((Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ⁻¹ᵁ g.opensRange).ι ≫
        (Scheme.IdealSheafData.vanishingIdeal Y).subschemeι ≫ s) := by
  set I := Scheme.IdealSheafData.vanishingIdeal Y with hI
  by_cases hne : (g.base ⁻¹' (Y : Set X)).Nonempty
  · obtain ⟨𝔓, h𝔓min, h𝔓Z⟩ := exists_minimalPrime Y hY A g hne
    haveI h𝔓 : 𝔓.IsPrime := h𝔓min.1.1
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

    have hker : I.comap g = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓))).ker := by
      have h1 : (I.comap g).radical = I.comap g := by
        haveI : IsReduced I.subscheme := by
          rw [hI]; exact AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Y
        haveI : IsReduced (Limits.pullback g I.subschemeι) :=
          isReduced_of_isOpenImmersion (Limits.pullback.snd g I.subschemeι)
        exact radical_ker (Limits.pullback.fst g I.subschemeι)
      have h2 : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓))).ker.radical =
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓))).ker := radical_ker _
      rw [eq_vanishingIdeal_support _ h1, eq_vanishingIdeal_support _ h2]
      congr 1
      apply Closeds.ext
      rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hI,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Hom.support_ker,
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓))).isClosedEmbedding.isClosed_range.closure_eq, ← h𝔓Z]
      change _ = Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk 𝔓))
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

    have hle : I.subschemeι.ker ≤ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓)) ≫ g).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_ker,
        Scheme.IdealSheafData.le_map_iff_comap_le, hker]
    set Zf := IsClosedImmersion.lift I.subschemeι (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓)) ≫ g) hle
      with hZfdef
    have hZf : Zf ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓)) ≫ g :=
      IsClosedImmersion.lift_fac _ _ _
    have sq : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔓))) Zf g I.subschemeι :=
      isPullback_of_isClosedImmersion _ _ _ _ hZf.symm (by rw [Scheme.IdealSheafData.ker_subschemeι, hker])
    haveI : IsOpenImmersion Zf :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) sq inferInstance
    have hrange : Zf.opensRange = I.subschemeι ⁻¹ᵁ g.opensRange := by
      apply TopologicalSpace.Opens.ext
      show Set.range Zf.base = I.subschemeι.base ⁻¹' Set.range g.base
      have hsurj : Function.Surjective sq.isoPullback.hom.base := (Scheme.homeoOfIso sq.isoPullback).surjective
      rw [← Scheme.Pullback.range_snd g I.subschemeι, ← sq.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp,
        Set.range_comp, hsurj.range_eq, Set.image_univ]

    have hsm : SmoothOfRelativeDimension n (Zf ≫ I.subschemeι ≫ s) := by
      rw [← Category.assoc, hZf, Category.assoc]; exact hP 𝔓 h𝔓min h𝔓Z
    rw [← Scheme.Hom.isoOpensRange_hom_ι Zf, Category.assoc] at hsm
    have hsm' := (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n)
      Zf.isoOpensRange.hom (Zf.opensRange.ι ≫ I.subschemeι ≫ s)).1 hsm
    rw [hrange] at hsm'
    exact hsm'
  ·
    haveI : IsEmpty ↥((I.subschemeι ⁻¹ᵁ g.opensRange : I.subscheme.Opens) : Scheme.{u}) := by
      refine ⟨fun c => hne ?_⟩
      obtain ⟨a, ha⟩ := c.2
      refine ⟨a, ?_⟩
      show g.base a ∈ (Y : Set X)
      rw [ha, ← Scheme.IdealSheafData.coe_support_vanishingIdeal Y, ← hI, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨c.1, rfl⟩
    exact ⟨fun x => (IsEmpty.false x).elim⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_smoothOfRelativeDimension_restrict_subscheme_vanishingIdeal_of_isOpenImmersion (solution)
