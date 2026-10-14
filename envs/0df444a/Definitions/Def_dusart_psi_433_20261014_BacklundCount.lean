-- Prove2me | Definitions.Def_dusart_psi_433_20261014_BacklundCount
-- name    : dusart_psi_433_20261014_BacklundCount
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:17:24.809859+00:00
-- url     : https://prove2.me/theorems/f92c2d70-f635-4ce2-9d72-34d18070a8bf
-- title:
--   Dusart smoothing: Backlund Count
-- statement:
--   This module gives the complete backlund count component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_BacklundSegment
/- Finite partition argument adapted from accepted Prove2Me proof
7e5a818d-3b74-4bef-be81-244dd62afd08, by Anthropic, PBC (2026).
Apache-2.0. Each segment now uses the proved pi estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex Set MeasureTheory Real intervalIntegral

namespace DusartSmoothing.RvM

variable {T : ℝ}

theorem backlund_horizontal_from_finite_re_zeros (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    (P : Finset ℝ) (hP : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ P) :
    ∀ n : ℕ, ∀ u v : ℝ, 1/2 ≤ u → u < v → v ≤ 2 →
      (P.filter (fun x => u < x ∧ x < v)).card ≤ n →
      |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ Real.pi * ((P.filter (fun x => u < x ∧ x < v)).card + 1) := by
  -- the empty-interior case, used twice
  have base : ∀ u v : ℝ, 1/2 ≤ u → u < v → v ≤ 2 →
      (P.filter (fun x => u < x ∧ x < v)).card = 0 →
      |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ Real.pi * ((P.filter (fun x => u < x ∧ x < v)).card + 1) := by
    intro u v hu huv hv hc
    have hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0 := by
      intro σ hσ hre
      have hσP : σ ∈ P.filter (fun x => u < x ∧ x < v) :=
        Finset.mem_filter.mpr ⟨hP σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ hre, hσ.1, hσ.2⟩
      rw [Finset.card_eq_zero] at hc
      simp [hc] at hσP
    rw [hc]
    have := backlund_segment_pi hT hnz hu huv hv hno
    simpa using this
  intro n
  induction n with
  | zero =>
    intro u v hu huv hv hc
    exact base u v hu huv hv (Nat.le_zero.mp hc)
  | succ n ih =>
    intro u v hu huv hv hc
    by_cases hc0 : (P.filter (fun x => u < x ∧ x < v)).card = 0
    · exact base u v hu huv hv hc0
    obtain ⟨m, hm⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
    obtain ⟨-, hum, hmv⟩ := Finset.mem_filter.mp hm
    -- the two halves carry fewer points: c₁ + c₂ + 1 ≤ c
    set S := P.filter (fun x => u < x ∧ x < v) with hSdef
    set S₁ := P.filter (fun x => u < x ∧ x < m) with hS₁def
    set S₂ := P.filter (fun x => m < x ∧ x < v) with hS₂def
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have := (Finset.mem_filter.mp hx1).2.2
      have := (Finset.mem_filter.mp hx2).2.1
      linarith
    have hsubS : S₁ ∪ S₂ ⊆ S.erase m := by
      intro x hx
      rw [Finset.mem_erase]
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxP, hux, hxm⟩ := Finset.mem_filter.mp hx
        exact ⟨hxm.ne, Finset.mem_filter.mpr ⟨hxP, hux, by linarith⟩⟩
      · obtain ⟨hxP, hmx, hxv⟩ := Finset.mem_filter.mp hx
        exact ⟨hmx.ne', Finset.mem_filter.mpr ⟨hxP, by linarith, hxv⟩⟩
    have hcard : S₁.card + S₂.card + 1 ≤ S.card := by
      have h1 : S₁.card + S₂.card = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
      have h2 : (S₁ ∪ S₂).card ≤ (S.erase m).card := Finset.card_le_card hsubS
      have h3 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hm
      have h4 : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hm⟩
      omega
    have hc1 : S₁.card ≤ n := by omega
    have hc2 : S₂.card ≤ n := by omega
    have e1 := ih u m hu hum (by linarith) hc1
    have e2 := ih m v (by linarith) hmv hv hc2
    -- split the integral at m
    have hmI : m ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, by linarith⟩
    have huI : u ∈ Set.Icc (1/2 : ℝ) 2 := ⟨hu, by linarith⟩
    have hvI : v ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, hv⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_logDeriv_horizontal hT hnz huI hmI)
      (intervalIntegrable_logDeriv_horizontal hT hnz hmI hvI), Complex.add_im]
    have hcast : ((S₁.card : ℝ) + 1) + ((S₂.card : ℝ) + 1) ≤ (S.card : ℝ) + 1 := by
      have : ((S₁.card + S₂.card + 1 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
      push_cast at this; linarith
    calc |(∫ σ in u..m, logDeriv riemannZeta (σ + T * I)).im
          + (∫ σ in m..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ |(∫ σ in u..m, logDeriv riemannZeta (σ + T * I)).im|
          + |(∫ σ in m..v, logDeriv riemannZeta (σ + T * I)).im| := abs_add_le _ _
      _ ≤ Real.pi * ((S₁.card : ℝ) + 1) + Real.pi * ((S₂.card : ℝ) + 1) := add_le_add e1 e2
      _ ≤ Real.pi * ((S.card : ℝ) + 1) := by nlinarith [Real.pi_pos]

theorem backlund_horizontal_card_bound (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    (P : Finset ℝ)
    (hP : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ P) :
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤
      Real.pi * (P.card + 1) := by
  have hc : (P.filter (fun σ => (1 / 2 : ℝ) < σ ∧ σ < 2)).card ≤ P.card :=
    Finset.card_filter_le _ _
  have hh := backlund_horizontal_from_finite_re_zeros hT hnz P hP P.card
    (1 / 2) 2 le_rfl (by norm_num) le_rfl hc
  have hcr : ((P.filter (fun σ => (1 / 2 : ℝ) < σ ∧ σ < 2)).card : ℝ) ≤ P.card := by
    exact_mod_cast hc
  have hcr₁ : ((P.filter (fun σ => (1 / 2 : ℝ) < σ ∧ σ < 2)).card : ℝ) + 1 ≤ P.card + 1 := by
    linarith only [hcr]
  exact hh.trans (mul_le_mul_of_nonneg_left hcr₁ Real.pi_pos.le)

end DusartSmoothing.RvM


