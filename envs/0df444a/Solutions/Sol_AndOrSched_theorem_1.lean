-- Prove2me | solution 1 for AndOrSched.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:12:37.967445+00:00
-- url     : https://prove2.me/submissions/5dd8bdcd-df02-480a-80d4-b68eb4338ae3

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_Acyclic
import Definitions.Def_AndOrSched_IsFeasible
import Definitions.Def_AndOrSched_cost
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_normalize
import Definitions.Def_AndOrSched_outSched
import Definitions.Def_AndOrSched_Compat
import Definitions.Def_AndOrSched_horizon
import Definitions.Def_AndOrSched_LP1Optimal
import Definitions.Def_AndOrSched_key
import Definitions.Def_AndOrSched_cand
import Definitions.Def_AndOrSched_numIntervals
import Definitions.Def_AndOrSched_LP5Optimal
import Theorems.Thm_AndOrSched_section_2_normalization
import Theorems.Thm_AndOrSched_section_2_lp1_relaxation
import Theorems.Thm_AndOrSched_lemma_1
import Theorems.Thm_AndOrSched_lemma_2
import Theorems.Thm_AndOrSched_section_2_lp5_relaxation
import Theorems.Thm_AndOrSched_lemma_3
import Theorems.Thm_AndOrSched_section_2_derandomize_alg2
open scoped Classical NNReal

namespace AndOrSched

private lemma scaleD_pos (I : Instance) : (0 : ℝ) < (scaleD I : ℝ) := by
  have hdvd : scaleD I ∣ ∏ j : I.N, (I.p j).den :=
    Finset.lcm_dvd fun j hj => Finset.dvd_prod_of_mem (fun k : I.N => (I.p k).den) hj
  have hprod_pos : 0 < ∏ j : I.N, (I.p j).den :=
    Finset.prod_pos fun j _ => NNRat.den_pos (I.p j)
  exact Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hdvd hprod_pos)

private lemma delta_pos (I : Instance) : (0 : ℝ) < (delta I : ℝ) := by
  have h1 : 1 ≤ delta I := le_max_left 1 _
  exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)

private lemma cost_nonneg (I : Instance) (C : I.N → ℝ) (hC : IsFeasible I C) :
    0 ≤ cost I C := by
  unfold cost
  refine Finset.sum_nonneg fun j _ => mul_nonneg (NNReal.coe_nonneg _) ?_
  exact le_trans (by positivity) (hC.1 j)

private lemma integrableOn_two_mul_const (c : ℝ) :
    MeasureTheory.IntegrableOn (fun β : ℝ => 2 * β * c) (Set.Ioc 0 1) := by
  have hcont : Continuous (fun β : ℝ => 2 * β * c) :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (hcont.intervalIntegrable 0 1)

private lemma integral_two_mul_const (c : ℝ) :
    ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * c = c := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hcont : Continuous (fun β : ℝ => 2 * β * c) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hderiv : ∀ β ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => x ^ 2 * c) (2 * β * c) β := by
    intro β _
    rw [show (2 : ℝ) * β * c = ↑(2 : ℕ) * β ^ (2 - 1) * c by norm_num]
    exact (hasDerivAt_pow 2 β).mul_const c
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
  ring

private lemma le_worstCost (J : Instance) (k : J.N → ℕ)
    (σ : J.N ≃ Fin (Fintype.card J.N)) (hσ : Compat J k σ) :
    cost J (listC J σ) ≤ worstCost J k := by
  unfold worstCost
  exact le_ciSup
    (f := fun s : {s : J.N ≃ Fin (Fintype.card J.N) // Compat J k s} => cost J (listC J s.1))
    (Set.finite_range _).bddAbove ⟨σ, hσ⟩

private lemma best_cand_bound_norm (J : Instance) (x : J.N → ℕ → ℝ) (M : ℕ) (ρ' : ℝ)
    (hInt : MeasureTheory.IntegrableOn
      (fun β : ℝ => 2 * β * worstCost J (key J x β)) (Set.Ioc 0 1))
    (hExp : ∀ C' : J.N → ℝ, IsFeasible J C' →
      ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost J (key J x β) ≤ ρ' * cost J C')
    (hCandCover : ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∃ β' ∈ cand J x M, key J x β' = key J x β) :
    ∃ β ∈ cand J x M,
      ∀ σ, Compat J (key J x β) σ →
        ∀ C' : J.N → ℝ, IsFeasible J C' →
          cost J (listC J σ) ≤ ρ' * cost J C' := by
  have hS_ne : (cand J x M).Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  obtain ⟨β₀, hβ₀_mem, hβ₀_min⟩ :=
    Finset.exists_min_image (cand J x M) (fun β => worstCost J (key J x β)) hS_ne
  refine ⟨β₀, hβ₀_mem, fun σ hσ C' hC' => ?_⟩
  have hmono : ∀ β ∈ Set.Ioc (0 : ℝ) 1,
      2 * β * worstCost J (key J x β₀) ≤ 2 * β * worstCost J (key J x β) := by
    intro β hβ
    obtain ⟨β', hβ'_mem, hkey⟩ := hCandCover β hβ.1 hβ.2
    have hw : worstCost J (key J x β₀) ≤ worstCost J (key J x β) := by
      rw [← hkey]
      exact hβ₀_min β' hβ'_mem
    exact mul_le_mul_of_nonneg_left hw (by linarith [hβ.1])
  have hint_le : worstCost J (key J x β₀) ≤
      ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost J (key J x β) := by
    rw [← integral_two_mul_const (worstCost J (key J x β₀))]
    exact MeasureTheory.setIntegral_mono_on
      (integrableOn_two_mul_const _) hInt measurableSet_Ioc hmono
  exact le_trans (le_worstCost J (key J x β₀) σ hσ) (le_trans hint_le (hExp C' hC'))

private lemma best_cand_bound (I : Instance) (hI : Acyclic I)
    (x : (normalize I).N → ℕ → ℝ) (M : ℕ) (ρ' ρ : ℝ)
    (hρ'0 : 0 ≤ ρ') (hρ : ρ' ≤ ρ)
    (hFeas : ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∀ σ, Compat (normalize I) (key (normalize I) x β) σ →
        IsFeasible (normalize I) (listC (normalize I) σ))
    (hInt : MeasureTheory.IntegrableOn
      (fun β : ℝ => 2 * β * worstCost (normalize I) (key (normalize I) x β)) (Set.Ioc 0 1))
    (hExp : ∀ C' : (normalize I).N → ℝ, IsFeasible (normalize I) C' →
      ∫ β in Set.Ioc (0 : ℝ) 1, 2 * β * worstCost (normalize I) (key (normalize I) x β) ≤
        ρ' * cost (normalize I) C')
    (hCandBounds : ∀ β ∈ cand (normalize I) x M, 0 < β ∧ β ≤ 1)
    (hCandCover : ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∃ β' ∈ cand (normalize I) x M, key (normalize I) x β' = key (normalize I) x β) :
    ∃ β ∈ cand (normalize I) x M,
      ∀ σ, Compat (normalize I) (key (normalize I) x β) σ →
        ∀ C : I.N → ℝ, IsFeasible I C →
          cost I (outSched I σ) ≤ ρ * cost I C := by
  have hNorm := section_2_normalization I hI
  have hFwd := hNorm.2.2.2.2.2.1
  have hBwd := hNorm.2.2.2.2.2.2
  obtain ⟨β₀, hβ₀_mem, hβ₀_bound⟩ :=
    best_cand_bound_norm (normalize I) x M ρ' hInt hExp hCandCover
  refine ⟨β₀, hβ₀_mem, fun σ hσ C hC => ?_⟩
  have ⟨hβ₀0, hβ₀1⟩ := hCandBounds β₀ hβ₀_mem
  have hσ_feas : IsFeasible (normalize I) (listC (normalize I) σ) := hFeas β₀ hβ₀0 hβ₀1 σ hσ
  have hout_cost : cost I (outSched I σ) ≤
      cost (normalize I) (listC (normalize I) σ) / (scaleD I : ℝ) :=
    (hBwd σ hσ_feas).2
  obtain ⟨C', hC'_feas, hC'_cost⟩ := hFwd C hC
  have hD_pos : (0 : ℝ) < (scaleD I : ℝ) := scaleD_pos I
  have hC_nn : 0 ≤ cost I C := cost_nonneg I C hC
  have hDC_nn : 0 ≤ (scaleD I : ℝ) * cost I C := mul_nonneg hD_pos.le hC_nn
  have hlist_bound :
      cost (normalize I) (listC (normalize I) σ) / (scaleD I : ℝ) ≤ ρ * cost I C := by
    rw [div_le_iff₀ hD_pos]
    calc cost (normalize I) (listC (normalize I) σ)
      _ ≤ ρ' * cost (normalize I) C' := hβ₀_bound σ hσ C' hC'_feas
      _ ≤ ρ' * ((scaleD I : ℝ) * cost I C) := mul_le_mul_of_nonneg_left hC'_cost hρ'0
      _ ≤ ρ * ((scaleD I : ℝ) * cost I C) := mul_le_mul_of_nonneg_right hρ hDC_nn
      _ = ρ * cost I C * (scaleD I : ℝ) := by ring
  exact le_trans hout_cost hlist_bound

end AndOrSched

open AndOrSched

theorem solution :
    (∀ I : Instance, Acyclic I → (∀ j, I.p j = 0 ∨ I.p j = 1) →
      (∃ x, LP1Optimal (normalize I) x) ∧
      ∀ x, LP1Optimal (normalize I) x →
        (∀ β : ℝ, 0 < β → β ≤ 1 →
          (∃ σ, Compat (normalize I) (key (normalize I) x β) σ) ∧
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ → IsFeasible I (outSched I σ)) ∧
        (∀ β ∈ cand (normalize I) x (horizon (normalize I)), 0 < β ∧ β ≤ 1) ∧
        horizon (normalize I) ≤ Fintype.card (normalize I).N ∧
        Fintype.card (normalize I).N ≤ 2 * Fintype.card I.N ∧
        (cand (normalize I) x (horizon (normalize I))).card ≤
          Fintype.card (normalize I).N * horizon (normalize I) + 1 ∧
        ∃ β ∈ cand (normalize I) x (horizon (normalize I)),
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ →
            ∀ C : I.N → ℝ, IsFeasible I C →
              cost I (outSched I σ) ≤ 2 * (delta I : ℝ) * cost I C) ∧
    (∀ I : Instance, Acyclic I → ∀ ε : ℝ, 0 < ε →
      (∃ x, LP5Optimal (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) x) ∧
      ∀ x, LP5Optimal (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) x →
        (∀ β : ℝ, 0 < β → β ≤ 1 →
          (∃ σ, Compat (normalize I) (key (normalize I) x β) σ) ∧
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ → IsFeasible I (outSched I σ)) ∧
        (∀ β ∈ cand (normalize I) x (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ)))),
          0 < β ∧ β ≤ 1) ∧
        Fintype.card (normalize I).N ≤ 2 * Fintype.card I.N ∧
        (cand (normalize I) x (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ))))).card ≤
          Fintype.card (normalize I).N *
            numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) + 1 ∧
        (1 ≤ horizon (normalize I) →
          (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ))) : ℝ) ≤
            2 + (1 + ε / (2 * (delta (normalize I) : ℝ))) * Real.log (horizon (normalize I)) /
              (ε / (2 * (delta (normalize I) : ℝ)))) ∧
        ∃ β ∈ cand (normalize I) x (numIntervals (normalize I) (ε / (2 * (delta (normalize I) : ℝ)))),
          ∀ σ, Compat (normalize I) (key (normalize I) x β) σ →
            ∀ C : I.N → ℝ, IsFeasible I C →
              cost I (outSched I σ) ≤ (2 * (delta I : ℝ) + ε) * cost I C) := by
  constructor
  · intro I hI hp01
    obtain ⟨hAcyc', hNorm', hDelta, hCard, hp01_imp, _, hBwd⟩ := section_2_normalization I hI
    have hp01' : ∀ j, (normalize I).p j = 0 ∨ (normalize I).p j = 1 := hp01_imp hp01
    have hp1' : ∀ j, (normalize I).p j ≤ 1 := fun j => by
      rcases hp01' j with h | h <;> simp [h]
    have hint' : ∀ j, ∃ n : ℕ, (normalize I).p j = n := hNorm'.2.1
    refine ⟨(section_2_lp1_relaxation (normalize I) hAcyc' hNorm' hp1').1, fun x hx => ?_⟩
    obtain ⟨hFeas1, hInt1, hExp1⟩ := lemma_1 (normalize I) hAcyc' hNorm' hp1' x hx
    obtain ⟨hCandBounds1, hHoriz1, hCandCard1, hCandCover1⟩ :=
      lemma_2 (normalize I) hint' hp1' x hx.1
    refine ⟨?_, hCandBounds1, hHoriz1, hCard, hCandCard1, ?_⟩
    · intro β hβ0 hβ1
      obtain ⟨hEx, hAll⟩ := hFeas1 β hβ0 hβ1
      exact ⟨hEx, fun σ hσ => (hBwd σ (hAll σ hσ)).1⟩
    · have hDeltaR : 2 * (delta (normalize I) : ℝ) ≤ 2 * (delta I : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hDelta) (by positivity)
      exact best_cand_bound I hI x (horizon (normalize I))
        (2 * (delta (normalize I) : ℝ)) (2 * (delta I : ℝ))
        (by positivity) hDeltaR
        (fun β hβ0 hβ1 => (hFeas1 β hβ0 hβ1).2) hInt1 hExp1 hCandBounds1 hCandCover1
  · intro I hI ε hε
    obtain ⟨hAcyc', hNorm', hDelta, hCard, _, _, hBwd⟩ := section_2_normalization I hI
    set ε' : ℝ := ε / (2 * (delta (normalize I) : ℝ))
    have hε' : 0 < ε' := div_pos hε (mul_pos zero_lt_two (delta_pos (normalize I)))
    refine ⟨(section_2_lp5_relaxation (normalize I) hAcyc' hNorm' ε' hε').1, fun x hx => ?_⟩
    obtain ⟨hFeas2, hInt2, hExp2⟩ := lemma_3 (normalize I) hAcyc' hNorm' ε hε x hx
    obtain ⟨hCandBounds2, hCandCard2, hNumInt2, hCandCover2⟩ :=
      section_2_derandomize_alg2 (normalize I) ε' hε' x hx.1
    refine ⟨?_, hCandBounds2, hCard, hCandCard2, hNumInt2, ?_⟩
    · intro β hβ0 hβ1
      obtain ⟨hEx, hAll⟩ := hFeas2 β hβ0 hβ1
      exact ⟨hEx, fun σ hσ => (hBwd σ (hAll σ hσ)).1⟩
    · have hDeltaR : 2 * (delta (normalize I) : ℝ) + ε ≤ 2 * (delta I : ℝ) + ε := by
        linarith [(Nat.cast_le.mpr hDelta : (delta (normalize I) : ℝ) ≤ (delta I : ℝ))]
      exact best_cand_bound I hI x (numIntervals (normalize I) ε')
        (2 * (delta (normalize I) : ℝ) + ε) (2 * (delta I : ℝ) + ε)
        (by positivity) hDeltaR
        (fun β hβ0 hβ1 => (hFeas2 β hβ0 hβ1).2) hInt2 hExp2 hCandBounds2 hCandCover2
