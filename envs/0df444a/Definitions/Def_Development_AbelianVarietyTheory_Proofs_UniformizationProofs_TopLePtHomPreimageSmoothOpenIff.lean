-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TopLePtHomPreimageSmoothOpenIff
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TopLePtHomPreimageSmoothOpenIff
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:20:46.232474+00:00
-- url     : https://prove2.me/theorems/89d7d69e-a6c5-5db7-9327-5cccd8f5839d
-- title:
--   Top Le Pt Hom Preimage Smooth Open Iff
-- statement:
--   Definitions and structural lemmas for Top Le Pt Hom Preimage Smooth Open Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TopLePtHomPreimageSmoothOpenIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Theorems.Thm_GlobalTheory_ProjPoint_ofHom_preimage_basicOpen
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
namespace GlobalTheory
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
def pderivClass (j : Fin 3) : HomRing W :=
  Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial)
theorem pderivClass_mem (j : Fin 3) : pderivClass W j ∈ grading W 2 :=
  ⟨_, (isHomogeneous_polynomial W).pderiv, rfl⟩
def pderivOpen (j : Fin 3) : (scheme W).Opens := Proj.basicOpen (grading W) (pderivClass W j)
theorem ptHom_preimage_pderivOpen {A : Type u} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (h : IsUnimodularSol (W.map ρ) P) (j : Fin 3) :
    ptHom W ρ P h ⁻¹ᵁ pderivOpen W j = PrimeSpectrum.basicOpen
      (MvPolynomial.eval₂ ρ P (MvPolynomial.pderiv j W.toProjective.polynomial)) :=
  ProjPoint.ofHom_preimage_basicOpen (grading W) _ _ two_pos (pderivClass_mem W j)
def smoothOpen : (scheme W).Opens :=
  ⨆ p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}, coordOpen W p.1.1 ⊓ pderivOpen W p.1.2
theorem nonsingular_iff_exists_pderiv {k : Type*} [Field k] {V : WeierstrassCurve k}
    {P : Fin 3 → k} (h : IsUnimodularSol V P) :
    V.toProjective.Nonsingular P ↔ ∃ i j : Fin 3, j ≠ i ∧ P i ≠ 0 ∧
      MvPolynomial.eval P (MvPolynomial.pderiv j V.toProjective.polynomial) ≠ 0 := by
  set D : Fin 3 → k := fun j =>
    MvPolynomial.eval P (MvPolynomial.pderiv j V.toProjective.polynomial) with hD
  change (_ ∧ (D 0 ≠ 0 ∨ D 1 ≠ 0 ∨ D 2 ≠ 0)) ↔ ∃ i j : Fin 3, j ≠ i ∧ P i ≠ 0 ∧ D j ≠ 0
  constructor
  · rintro ⟨-, hns⟩
    obtain ⟨i, hi⟩ : ∃ i, P i ≠ 0 := by
      by_contra! h0
      have := h.span_eq_top
      rw [Ideal.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; exact h0 i)] at this
      exact bot_ne_top this
    by_contra! hc
    have hj : ∀ j, j ≠ i → D j = 0 := fun j hj => hc i j hj hi
    have euler : 3 * _ = P 0 * D 0 + P 1 * D 1 + P 2 * D 2 := V.toProjective.polynomial_relation P
    have h0 : MvPolynomial.eval P V.toProjective.polynomial = 0 := h.equation
    rw [h0, mul_zero, ← Fin.sum_univ_three
      (fun j => P j * D j), Finset.sum_eq_single i (fun j _ h => by rw [hj j h, mul_zero])
      (by simp)] at euler
    have hall : ∀ j, D j = 0 := fun j => by
      by_cases h : j = i
      · exact h ▸ (mul_eq_zero.mp euler.symm).resolve_left hi
      · exact hj j h
    rcases hns with h | h | h
    exacts [h (hall 0), h (hall 1), h (hall 2)]
  · rintro ⟨i, j, -, -, hj⟩
    refine ⟨h.equation, ?_⟩
    fin_cases j
    exacts [Or.inl hj, Or.inr (Or.inl hj), Or.inr (Or.inr hj)]
theorem top_le_ptHom_preimage_smoothOpen_iff {k : Type u} [Field k] (ρ : R →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol (W.map ρ) P) :
    ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ smoothOpen W ↔ (W.map ρ).toProjective.Nonsingular P := by
  have e : (W.map ρ).toProjective.polynomial = MvPolynomial.map ρ W.toProjective.polynomial :=
    WeierstrassCurve.Projective.map_polynomial ..
  have hb : ∀ (x : PrimeSpectrum k) (a : k), x ∈ PrimeSpectrum.basicOpen a ↔ a ≠ 0 := by
    intro x a
    rw [PrimeSpectrum.mem_basicOpen, Ideal.eq_bot_of_prime x.asIdeal, Ideal.mem_bot]
  rw [nonsingular_iff_exists_pderiv h, e, smoothOpen, Scheme.Hom.preimage_iSup]
  simp only [MvPolynomial.pderiv_map, MvPolynomial.eval_map, Scheme.Hom.preimage_inf,
    ptHom_preimage_coordOpen, ptHom_preimage_pderivOpen]
  constructor
  · intro H
    obtain ⟨⟨⟨i, j⟩, hij⟩, h1, h2⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (H (Set.mem_univ (⟨⊥, inferInstance⟩ : PrimeSpectrum k)))
    exact ⟨i, j, hij, (hb _ _).mp h1, (hb _ _).mp h2⟩
  · rintro ⟨i, j, hij, h1, h2⟩ x -
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨i, j⟩, hij⟩, (hb _ _).mpr h1, (hb _ _).mpr h2⟩
abbrev PderivRing (i j : Fin 3) : Type u :=
  Localization.Away
    (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i)
def pderivChart (i j : Fin 3) : Spec (.of (PderivRing W i j)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (DehomRing W i) (PderivRing W i j))) ≫ dehomChart W i
instance (i j : Fin 3) : IsOpenImmersion (pderivChart W i j) := by
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (DehomRing W i) (PderivRing W i j)))) :=
    IsOpenImmersion.of_isLocalization
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i)
  unfold pderivChart
  infer_instance
theorem range_pderivChart (i j : Fin 3) :
    Set.range (pderivChart W i j) = (coordOpen W i ⊓ pderivOpen W j : (scheme W).Opens) := by
  have hp : dehomChart W i ⁻¹ᵁ pderivOpen W j = PrimeSpectrum.basicOpen
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i) := by
    rw [← eval₂_dehomCoord]
    exact ptHom_preimage_pderivOpen W _ _
      (.of_isUnit (equation_dehomCoord W i) i (by simp)) j
  have hr := PrimeSpectrum.localization_away_comap_range (PderivRing W i j)
    (Ideal.Quotient.mk _ (MvPolynomial.pderiv j W.toProjective.polynomial) : DehomRing W i)
  rw [← hp] at hr
  rw [← opensRange_dehomChart]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [pderivChart, Scheme.Hom.comp_apply]
    exact ⟨⟨_, rfl⟩, hr.le ⟨y, rfl⟩⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    obtain ⟨z, rfl⟩ := hr.ge hy
    exact ⟨z, Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom
      (algebraMap (DehomRing W i) (PderivRing W i j)))) (dehomChart W i) z⟩
theorem coe_smoothOpen : (smoothOpen W : Set (scheme W)) =
    ⋃ p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}, Set.range (pderivChart W p.1.1 p.1.2) := by
  simp only [smoothOpen, TopologicalSpace.Opens.coe_iSup, range_pderivChart]
instance smoothOfRelativeDimension_smoothOpen :
    SmoothOfRelativeDimension 1 ((smoothOpen W).ι ≫ toSpec W) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} 1)
  have hr (p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) :
      Set.range (pderivChart W p.1.1 p.1.2) ⊆ Set.range (smoothOpen W).ι := by
    rw [Scheme.Opens.range_ι, coe_smoothOpen]
    exact Set.subset_iUnion (fun p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1} =>
      Set.range (pderivChart W p.1.1 p.1.2)) p
  let f (p : {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) :=
    IsOpenImmersion.lift (smoothOpen W).ι (pderivChart W p.1.1 p.1.2) (hr p)
  have hf (p) : f p ≫ (smoothOpen W).ι = pderivChart W p.1.1 p.1.2 := IsOpenImmersion.lift_fac ..
  have hi (p) : IsOpenImmersion (f p) := by
    have : IsOpenImmersion (f p ≫ (smoothOpen W).ι) := by
      rw [hf]
      infer_instance
    exact .of_comp _ (smoothOpen W).ι
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (Scheme.Cover.mkOfCovers (ULift.{u} {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) _ (fun p => f p.down)
      fun x => ?_) fun (p : ULift.{u} {p : Fin 3 × Fin 3 // p.2 ≠ p.1}) => ?_
  · have hx : (smoothOpen W).ι x ∈ (smoothOpen W : Set (scheme W)) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    rw [coe_smoothOpen] at hx
    obtain ⟨p, y, hy⟩ := Set.mem_iUnion.mp hx
    refine ⟨⟨p⟩, y, (smoothOpen W).ι.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hf, hy]
  · change SmoothOfRelativeDimension 1 (f p.down ≫ (smoothOpen W).ι ≫ toSpec W)
    rw [← Category.assoc, hf, pderivChart, Category.assoc, dehomChart_toSpec, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_)
    rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact isStandardSmoothOfRelativeDimension_away_pderiv W p.down.2 _
instance quasiCompact_smoothOpen : QuasiCompact ((smoothOpen W).ι ≫ toSpec W) := by
  have hc : IsCompact (smoothOpen W : Set (scheme W)) := by
    rw [coe_smoothOpen]
    exact isCompact_iUnion fun p => isCompact_range (pderivChart W p.1.1 p.1.2).continuous
  have : CompactSpace (smoothOpen W).toScheme := isCompact_iff_compactSpace.mp hc
  exact quasiCompact_of_compactSpace _
instance geometricallyIntegral_smoothOpen :
    GeometricallyIntegral ((smoothOpen W).ι ≫ toSpec W) := by
  refine ⟨geometrically_iff_of_commRing.mpr fun K _ _ Y fst snd h => ?_⟩
  have hb := isPullback_mapHom W (algebraMap R K) rfl
  let g : Y ⟶ scheme (W.map (algebraMap R K)) :=
    hb.lift (fst ≫ (smoothOpen W).ι) snd (by rw [Category.assoc]; exact h.w)
  have hg : g ≫ toSpec _ = snd := hb.lift_snd ..
  have hp : IsPullback fst g (smoothOpen W).ι (mapHom W (algebraMap R K) rfl) :=
    IsPullback.of_bot (by rw [hg]; exact h) (hb.lift_fst ..).symm hb
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp
    inferInstance
  have hz : Set.range (ptHom W (algebraMap R K) ![0, 1, 0] (isUnimodularSol_zero _)) ⊆
      Set.range (smoothOpen W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (top_le_ptHom_preimage_smoothOpen_iff W (algebraMap R K) ![0, 1, 0]
      (isUnimodularSol_zero _)).mpr WeierstrassCurve.Projective.nonsingular_zero (Set.mem_univ x)
  let s : Spec (.of K) ⟶ Y := h.lift (IsOpenImmersion.lift _ _ hz) (𝟙 _)
    (by rw [IsOpenImmersion.lift_fac_assoc, ptHom_toSpec, Category.id_comp])
  have : Nonempty Y := ⟨s (Classical.arbitrary (PrimeSpectrum K))⟩
  exact isIntegral_of_isOpenImmersion g
end WeierstrassCurve
end GlobalTheory


