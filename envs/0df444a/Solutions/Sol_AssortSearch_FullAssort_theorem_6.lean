-- Prove2me | solution 1 for AssortSearch.FullAssort.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:49:13.073394+00:00
-- url     : https://prove2.me/submissions/4f0608b8-0e91-4740-accd-2e8c1dacd751

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model
import Theorems.Thm_AssortSearch_FullAssort_H_tendsto_one

open Filter Topology Set
open AssortSearch.FullAssort

lemma fullAssort6_demand_mem {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (v0 : ℝ) (hv0 : 0 < v0) (b : ℝ) (S : Finset (Fin n)) (hS : S ≠ Finset.univ)
    (i : Fin n) (hi : i ∈ S) : demandSO μ v v0 b S i ∈ Icc (0 : ℝ) 1 := by
  simp only [demandSO, if_neg hS]
  have hsum : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => (hv j).le)
  have hvi : v i ≤ ∑ j ∈ S, v j := Finset.single_le_sum (fun j _ => (hv j).le) hi
  have hd : 0 < ∑ j ∈ S, v j + v0 := by linarith
  have hsh0 : 0 ≤ RetailVariety.Structure.share v v0 S i := by
    unfold RetailVariety.Structure.share; exact div_nonneg (hv i).le hd.le
  have hsh1 : RetailVariety.Structure.share v v0 S i ≤ 1 := by
    unfold RetailVariety.Structure.share; rw [div_le_one hd]; linarith
  have hH0 : 0 < AssortSearch.Cannibal.H μ (Ubar μ v S b) v v0 S := Real.exp_pos _
  have hH1 : AssortSearch.Cannibal.H μ (Ubar μ v S b) v v0 S ≤ 1 := by
    unfold AssortSearch.Cannibal.H
    apply Real.exp_le_one_iff.2
    have : 0 < AssortSearch.Cannibal.lam μ (Ubar μ v S b) := Real.exp_pos _
    have : 0 ≤ AssortSearch.Cannibal.lam μ (Ubar μ v S b) * (v0 + ∑ j ∈ S, v j) := by
      positivity
    linarith
  constructor
  · exact mul_nonneg hsh0 (by linarith)
  · calc _ ≤ 1 * 1 := mul_le_mul hsh1 (by linarith) (by linarith) (by norm_num)
      _ = 1 := by norm_num

theorem solution {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (v0 : ℝ) (hv0 : 0 < v0) (m : Fin n → ℝ) (hm : ∀ j k, v k ≤ v j → m k ≤ m j) (c : ℝ → ℝ)
    (hc_conc : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0) (hpos : 0 < fullProfit v v0 m c) :
    ∃ bbar : ℝ, 0 < bbar ∧ ∀ b : ℝ, 0 < b → b ≤ bbar →
      ∀ S : Finset (Fin n), profitSO μ v v0 m c b S ≤ profitSO μ v v0 m c b Finset.univ := by
  have hS : ∀ S : Finset (Fin n), ∀ᶠ b in 𝓝[>] (0 : ℝ),
      profitSO μ v v0 m c b S ≤ profitSO μ v v0 m c b Finset.univ := by
    intro S
    by_cases hSu : S = Finset.univ
    · subst hSu; exact Eventually.of_forall fun b => le_refl _
    have hT : Tendsto (fun b => ∑ i ∈ S, m i * demandSO μ v v0 b S i) (𝓝[>] 0)
        (𝓝 (∑ i ∈ S, m i * 0)) := by
      apply tendsto_finset_sum
      intro i hi
      exact ((H_tendsto_one μ hμ v hv v0 hv0 S hSu).2 i hi).const_mul (m i)
    simp only [mul_zero, Finset.sum_const_zero] at hT
    refine (hT.eventually (gt_mem_nhds hpos)).mono fun b hb => ?_
    rw [profitSO_univ]
    refine le_trans ?_ hb.le
    unfold profitSO
    apply Finset.sum_le_sum
    intro i hi
    have hq := fullAssort6_demand_mem μ v hv v0 hv0 b S hSu i hi
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
    have := hc_mono h0 hq hq.1
    linarith
  have hall : ∀ᶠ b in 𝓝[>] (0 : ℝ), ∀ S : Finset (Fin n),
      profitSO μ v v0 m c b S ≤ profitSO μ v v0 m c b Finset.univ := eventually_all.2 hS
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  refine ⟨u / 2, by simp only [mem_Ioi] at hu; linarith, fun b hb hbu S => ?_⟩
  have : b ∈ Ioo 0 u := ⟨hb, by simp only [mem_Ioi] at hu; linarith⟩
  exact hsub this S
