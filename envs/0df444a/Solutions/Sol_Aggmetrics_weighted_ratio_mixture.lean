-- Prove2me | solution 1 for Aggmetrics.weighted_ratio_mixture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:52:40.278081+00:00
-- url     : https://prove2.me/submissions/9782f0e1-180d-4ad1-91e3-a07d060e34c8

import Mathlib
import Definitions.Def_Aggmetrics_Basic

set_option autoImplicit true
open Finset
open Aggmetrics
namespace Aggmetrics
theorem _root_.solution {m : ℕ} (hm : 0 < m) (num den : Fin m → ℝ)
    (hden : ∀ j, 0 < den j) :
    (∑ j, num j) / (∑ j, den j) = ∑ j, (den j / ∑ k, den k) * (num j / den j) := by
  have hne : (univ : Finset (Fin m)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  have hS : (0:ℝ) < ∑ k, den k := Finset.sum_pos (fun k _ => hden k) hne
  have step : ∀ j, (den j / ∑ k, den k) * (num j / den j) = num j / ∑ k, den k := by
    intro j
    field_simp [(hden j).ne', hS.ne']
  rw [Finset.sum_congr rfl (fun j _ => step j), ← Finset.sum_div]
end Aggmetrics
