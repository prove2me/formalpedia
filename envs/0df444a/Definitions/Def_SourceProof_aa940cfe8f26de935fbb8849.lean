-- Prove2me | Definitions.Def_SourceProof_aa940cfe8f26de935fbb8849
-- name    : SourceProof_aa940cfe8f26de935fbb8849
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:19.256473+00:00
-- url     : https://prove2.me/theorems/94dcbf7e-d93e-4783-a8e6-46b0dfe87514
-- title:
--   LevyStochCalc source proof: LevyStochCalc.BSDEJ.PathRegularity.existsUnique_mem_cell
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PathRegularity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell-average rate for a deterministic Lipschitz integrand

For a function `h : ℝ → ℝ` with `|h s - h t| ≤ K * |s - t|` and a strictly monotone partition
`0 = t_0 < ⋯ < t_M = T` of mesh at most `δ`, the pathwise average of `h` over the cell
`(t_n, t_{n+1}]` containing `s` differs from `h s` by at most `K * δ`, so the energy of
`h - cellTimeAverage_Z π h` over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T`.

The integrand treated here is deterministic: it is the process `Z s ω i = h s`, constant in the
sample point and in the coordinate. The cell-average rate for a random integrand is a different,
genuinely stochastic statement and is not covered by anything below.
-/

open MeasureTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u

section Lipschitz

variable {K : ℝ} {h : ℝ → ℝ}

end Lipschitz

section Cells

variable {M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}


theorem _root_.Prove2MeSourceProof.h_aa940cfe8f26de935fbb8849 (hmono : StrictMono π) (h0 : π 0 = 0) (hT : π (Fin.last M) = T)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T) :
    ∃! n : Fin M, π n.castSucc < s ∧ s ≤ π n.succ := by
  classical
  obtain ⟨hs0, hsT⟩ := hs
  have huniq : ∀ m n : Fin M, π m.castSucc < s → s ≤ π m.succ →
      π n.castSucc < s → s ≤ π n.succ → m = n := by
    intro m n hm1 hm2 hn1 hn2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hval : (m : ℕ) < (n : ℕ) := Fin.lt_def.mp hlt
      have hle : (m.succ : Fin (M + 1)) ≤ n.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega
      have := hmono.monotone hle
      linarith
    · have hval : (n : ℕ) < (m : ℕ) := Fin.lt_def.mp hlt
      have hle : (n.succ : Fin (M + 1)) ≤ m.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega
      have := hmono.monotone hle
      linarith
  rcases Nat.eq_zero_or_pos M with hM | hMpos
  · exfalso
    subst hM
    have hlast : (Fin.last 0 : Fin (0 + 1)) = 0 := by ext; simp
    have hT0 : T = 0 := by rw [← hT, ← h0, hlast]
    rw [hT0] at hsT
    linarith
  · have hzero : ((⟨0, hMpos⟩ : Fin M).castSucc : Fin (M + 1)) = 0 := by ext; simp
    have hSne : (Finset.univ.filter fun n : Fin M => π n.castSucc < s).Nonempty := by
      refine ⟨⟨0, hMpos⟩, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hzero, h0]; exact hs0⟩
    obtain ⟨n₀, hn₀mem, hn₀max⟩ :
        ∃ n₀ ∈ Finset.univ.filter fun n : Fin M => π n.castSucc < s,
          ∀ m ∈ Finset.univ.filter fun n : Fin M => π n.castSucc < s, m ≤ n₀ :=
      ⟨_, Finset.max'_mem _ hSne, fun m hm => Finset.le_max' _ m hm⟩
    have hn₀lt : π n₀.castSucc < s := (Finset.mem_filter.mp hn₀mem).2
    have hn₀le : s ≤ π n₀.succ := by
      rw [← not_lt]
      intro hcon
      by_cases hlast : (n₀ : ℕ) + 1 = M
      · have he : (n₀.succ : Fin (M + 1)) = Fin.last M := by
          ext; simp only [Fin.val_succ, Fin.val_last]; omega
        rw [he, hT] at hcon
        linarith
      · have hlt : (n₀ : ℕ) + 1 < M := by have := n₀.isLt; omega
        have hcast : (⟨(n₀ : ℕ) + 1, hlt⟩ : Fin M).castSucc = n₀.succ := by ext; simp
        have hmem : (⟨(n₀ : ℕ) + 1, hlt⟩ : Fin M) ∈
            Finset.univ.filter fun n : Fin M => π n.castSucc < s := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [hcast]; exact hcon⟩
        have hle : (n₀ : ℕ) + 1 ≤ (n₀ : ℕ) := hn₀max _ hmem
        omega
    exact ⟨n₀, ⟨hn₀lt, hn₀le⟩, fun m hm => huniq m n₀ hm.1 hm.2 hn₀lt hn₀le⟩
end Cells

section Deterministic

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

end Deterministic

end LevyStochCalc.BSDEJ.PathRegularity


