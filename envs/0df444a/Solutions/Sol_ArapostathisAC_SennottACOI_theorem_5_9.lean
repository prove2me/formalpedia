-- Prove2me | solution 1 for ArapostathisAC.SennottACOI.theorem_5_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:21:00.280761+00:00
-- url     : https://prove2.me/submissions/77eda5b5-a8f6-423b-9108-1c9d69ce9302

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions
import Theorems.Thm_ArapostathisAC_SennottACOI_theorem_2_1
import Theorems.Thm_ArapostathisAC_SennottACOI_limit_function
import Theorems.Thm_ArapostathisAC_SennottACOI_acoi_limit
import Theorems.Thm_ArapostathisAC_SennottACOI_acoi_avgCost_le
import Theorems.Thm_ArapostathisAC_SennottACOI_avgCost_ge_limit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.SennottACOI

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M) (h15 : Assumption5_15 M)
    (h16 : Assumption5_16 M) :
    ∃ f : StationaryPolicy M, ArapostathisAC.VanishingDiscount.IsAvgOptimal M f := by
  -- discount factors β_n = 1 - 1/(n+2) ↑ 1
  set β : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hβdef
  have hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h3 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one h2]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have h4 : 0 < 1 / ((n : ℝ) + 2) := by positivity
    constructor <;> simp only [hβdef] <;> linarith
  have hβ1 : Tendsto β atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h' : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
        h.comp (tendsto_add_atTop_nat 1)
      refine h'.congr (fun n => ?_)
      push_cast; ring_nf
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub this
    simpa [hβdef] using this
  -- β_n-discount optimal stationary policies (Theorem 2.1 (iii))
  have hex : ∀ n, ∃ f : StationaryPolicy M,
      ArapostathisAC.VanishingDiscount.IsDiscOptimal M (β n) f :=
    fun n => (theorem_2_1 M (β n) (hβ n)).2
  choose fβ hfβ using hex
  obtain ⟨L, hL⟩ := h15
  -- limit policy, limit function, limit constant
  obtain ⟨φ, hφ, f, h, ρ, hρ0, hfconv, hhconv, hhL, hρconv⟩ :=
    limit_function M h14 L hL h16 β hβ hβ1 fβ hfβ
  have hβφ1 : Tendsto (fun n => β (φ n)) atTop (𝓝 1) := hβ1.comp hφ.tendsto_atTop
  -- ACOI for the limit
  have hacoi := acoi_limit M h14 L hL h16 (fun n => β (φ n)) (fun n => hβ (φ n)) hβφ1
    (fun n => fβ (φ n)) (fun n => hfβ (φ n)) f h ρ hfconv hhconv (hρconv 0)
  have hb : BddBelow (Set.range h) := ⟨-(L : ℝ), by rintro _ ⟨i, rfl⟩; exact hhL i⟩
  have hle := acoi_avgCost_le M ρ h hb f (fun i => (hacoi i).1) (fun i => (hacoi i).2)
  refine ⟨f, fun i => ?_⟩
  have hge : ∀ π : ArapostathisAC.VanishingDiscount.Policy M,
      ENNReal.ofReal ρ ≤ ArapostathisAC.VanishingDiscount.avgCost M π i :=
    fun π => avgCost_ge_limit M h14 (fun n => β (φ n)) (fun n => hβ (φ n)) hβφ1 ρ i (hρconv i) π
  apply le_antisymm
  · exact (hle i).trans (le_iInf hge)
  · exact iInf_le _ _
