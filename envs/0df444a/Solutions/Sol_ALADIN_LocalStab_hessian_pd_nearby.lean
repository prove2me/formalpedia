-- Prove2me | solution 1 for ALADIN.LocalStab.hessian_pd_nearby
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:53:12.527009+00:00
-- url     : https://prove2.me/submissions/80795d86-4ed7-4372-946f-f4ed471b2e46

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem
import Definitions.Def_ALADIN_LocalStab_Decoupled

open Matrix

namespace Aux_ALADINHess
open ALADIN.LocalStab

lemma hq_eq {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (i : Fin N) (κ' : Fin nh → ℝ) (ξ d : Fin n → ℝ) :
    hessQuad (P.lagBlock i κ') ξ d =
      hessQuad (P.f i) ξ d + ∑ j, κ' j * hessQuad (fun ξ => P.h i ξ j) ξ d := by
  have hhj : ∀ j, ContDiff ℝ 2 (fun ξ => P.h i ξ j) := fun j => contDiff_pi.1 (hh i) j
  have hfd : Differentiable ℝ (P.f i) := (hf i).differentiable two_ne_zero
  have hhd : ∀ j, Differentiable ℝ (fun ξ => P.h i ξ j) := fun j =>
    (hhj j).differentiable two_ne_zero
  have hf1 : Differentiable ℝ (fderiv ℝ (P.f i)) :=
    ((hf i).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hh1 : ∀ j, Differentiable ℝ (fderiv ℝ (fun ξ => P.h i ξ j)) := fun j =>
    ((hhj j).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hD1 : fderiv ℝ (P.lagBlock i κ') = fun ξ =>
      fderiv ℝ (P.f i) ξ + ∑ j, κ' j • fderiv ℝ (fun ξ => P.h i ξ j) ξ := by
    funext ξ
    have : HasFDerivAt (fun ξ => P.f i ξ + ∑ j, κ' j * P.h i ξ j)
        (fderiv ℝ (P.f i) ξ + ∑ j, κ' j • fderiv ℝ (fun ξ => P.h i ξ j) ξ) ξ :=
      (hfd ξ).hasFDerivAt.add
        (HasFDerivAt.fun_sum (fun j _ => ((hhd j ξ).hasFDerivAt).const_mul (κ' j)))
    exact this.fderiv
  have hD2 : HasFDerivAt (fun ξ =>
      fderiv ℝ (P.f i) ξ + ∑ j, κ' j • fderiv ℝ (fun ξ => P.h i ξ j) ξ)
      (fderiv ℝ (fderiv ℝ (P.f i)) ξ +
        ∑ j, κ' j • fderiv ℝ (fderiv ℝ (fun ξ => P.h i ξ j)) ξ) ξ :=
    (hf1 ξ).hasFDerivAt.add
      (HasFDerivAt.fun_sum (fun j _ => ((hh1 j ξ).hasFDerivAt).const_smul (κ' j)))
  unfold hessQuad
  rw [hD1, hD2.fderiv]
  simp

lemma hq_smul {n : ℕ} (g : (Fin n → ℝ) → ℝ) (ξ d : Fin n → ℝ) (c : ℝ) :
    hessQuad g ξ (c • d) = c ^ 2 * hessQuad g ξ d := by
  unfold hessQuad
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma per_i {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (xs : Fin N → Fin n → ℝ) (κ : Fin N → Fin nh → ℝ) (i : Fin N)
    (hHess : ∀ (d : Fin n → ℝ), d ≠ 0 →
      0 < hessQuad (P.lagBlock i (κ i)) (xs i) d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ δ > 0, ∀ (ξ : Fin n → ℝ) (κ' : Fin nh → ℝ), ‖ξ - xs i‖ < δ → ‖κ' - κ i‖ < δ →
      ∀ d : Fin n → ℝ, d ≠ 0 →
        0 < hessQuad (P.lagBlock i κ') ξ d + ρ * (d ⬝ᵥ (Sig i *ᵥ d)) := by
  let Φ : (Fin n → ℝ) × (Fin nh → ℝ) × (Fin n → ℝ) → ℝ := fun p =>
    hessQuad (P.lagBlock i p.2.1) p.1 p.2.2 + ρ * (p.2.2 ⬝ᵥ (Sig i *ᵥ p.2.2))
  have hhj : ∀ j, ContDiff ℝ 2 (fun ξ => P.h i ξ j) := fun j => contDiff_pi.1 (hh i) j
  have hf2 : Continuous (fderiv ℝ (fderiv ℝ (P.f i))) :=
    ((hf i).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hh2 : ∀ j, Continuous (fderiv ℝ (fderiv ℝ (fun ξ => P.h i ξ j))) := fun j =>
    ((hhj j).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hquad : ∀ g : (Fin n → ℝ) → ℝ, Continuous (fderiv ℝ (fderiv ℝ g)) →
      Continuous (fun p : (Fin n → ℝ) × (Fin nh → ℝ) × (Fin n → ℝ) => hessQuad g p.1 p.2.2) := by
    intro g hg
    unfold hessQuad
    exact ((hg.comp continuous_fst).clm_apply continuous_snd.snd).clm_apply continuous_snd.snd
  have hΦc : Continuous Φ := by
    have e : Φ = fun p => hessQuad (P.f i) p.1 p.2.2 +
        ∑ j, p.2.1 j * hessQuad (fun ξ => P.h i ξ j) p.1 p.2.2 +
        ρ * (p.2.2 ⬝ᵥ (Sig i *ᵥ p.2.2)) := by
      funext p
      simp only [Φ, hq_eq P hf hh]
    rw [e]
    refine ((hquad _ hf2).add (continuous_finset_sum _ (fun j _ =>
      ((continuous_apply j).comp continuous_snd.fst).mul (hquad _ (hh2 j))))).add
      (continuous_const.mul ?_)
    exact continuous_snd.snd.dotProduct (continuous_const.matrix_mulVec continuous_snd.snd)
  set K : Set ((Fin n → ℝ) × (Fin nh → ℝ) × (Fin n → ℝ)) :=
    {xs i} ×ˢ ({κ i} ×ˢ Metric.sphere 0 1) with hK
  have hKc : IsCompact K :=
    isCompact_singleton.prod (isCompact_singleton.prod (isCompact_sphere 0 1))
  have hopen : IsOpen {p | 0 < Φ p} := isOpen_lt continuous_const hΦc
  have hsub : K ⊆ {p | 0 < Φ p} := by
    rintro ⟨a, b, u⟩ ⟨ha, hb, hu⟩
    simp only [Set.mem_singleton_iff] at ha hb
    subst ha; subst hb
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hu0 : u ≠ 0 := by
      intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
    exact hHess u hu0
  obtain ⟨δ, hδ, hth⟩ := hKc.exists_thickening_subset_open hopen hsub
  refine ⟨δ, hδ, ?_⟩
  intro ξ κ' h1 h2 d hd
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  set u : Fin n → ℝ := ‖d‖⁻¹ • d with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdn.ne']
  have hmem : (ξ, κ', u) ∈ Metric.thickening δ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(xs i, κ i, u), ⟨rfl, rfl, by simpa using hu1⟩, ?_⟩
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_eq_norm, dist_eq_norm]
    simp only [max_lt_iff]
    exact ⟨h1, h2, hδ⟩
  have hpos : 0 < Φ (ξ, κ', u) := hth hmem
  have hdu : d = ‖d‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hdn.ne', one_smul]
  have hscale : hessQuad (P.lagBlock i κ') ξ d + ρ * (d ⬝ᵥ (Sig i *ᵥ d)) =
      ‖d‖ ^ 2 * Φ (ξ, κ', u) := by
    simp only [Φ]
    conv_lhs => rw [hdu]
    rw [hq_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [hscale]
  positivity

end Aux_ALADINHess

open ALADIN.LocalStab Aux_ALADINHess in
theorem solution {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (xs : Fin N → Fin n → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hHess : ∀ i (d : Fin n → ℝ), d ≠ 0 →
      0 < hessQuad (P.lagBlock i (κ i)) (xs i) d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ δ > 0, ∀ i (ξ : Fin n → ℝ) (κ' : Fin nh → ℝ), ‖ξ - xs i‖ < δ → ‖κ' - κ i‖ < δ →
      ∀ d : Fin n → ℝ, d ≠ 0 →
        0 < hessQuad (P.lagBlock i κ') ξ d + ρ * (d ⬝ᵥ (Sig i *ᵥ d)) := by
  choose δi hδpos hδ using fun i => per_i P hf hh Sig ρ xs κ i (hHess i)
  by_cases hN : Nonempty (Fin N)
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty δi,
      (Finset.lt_inf'_iff _).2 (fun i _ => hδpos i), ?_⟩
    intro i ξ κ' h1 h2
    have hle : Finset.univ.inf' Finset.univ_nonempty δi ≤ δi i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    exact hδ i ξ κ' (lt_of_lt_of_le h1 hle) (lt_of_lt_of_le h2 hle)
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hN⟩
