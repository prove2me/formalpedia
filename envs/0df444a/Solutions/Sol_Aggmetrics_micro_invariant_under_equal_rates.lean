-- Prove2me | solution 1 for Aggmetrics.micro_invariant_under_equal_rates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:35.40044+00:00
-- url     : https://prove2.me/submissions/48137526-c683-4338-a31a-e3d7d7a69b50

import Mathlib
import Definitions.Def_Aggmetrics_Basic
import Theorems.Thm_Aggmetrics_weighted_ratio_mixture

set_option autoImplicit true
open Finset
open Aggmetrics
namespace Aggmetrics
theorem _root_.solution {m : ℕ} (hm : 0 < m)
    (tp fp fn tn : Fin m → ℝ) (r s : ℝ)
    (htpfn : ∀ j, 0 < tp j + fn j) (hfptn : ∀ j, 0 < fp j + tn j)
    (hrec : ∀ j, tp j / (tp j + fn j) = r) (hspec : ∀ j, tn j / (fp j + tn j) = s) :
    (∑ j, tp j) / (∑ j, (tp j + fn j)) = r ∧
    (∑ j, tn j) / (∑ j, (fp j + tn j)) = s := by
  have hne : (univ : Finset (Fin m)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  constructor
  · rw [weighted_ratio_mixture hm tp (fun j => tp j + fn j) htpfn]
    have hS : (∑ k : Fin m, (tp k + fn k)) ≠ 0 :=
      (Finset.sum_pos (fun k _ => htpfn k) hne).ne'
    simp only [hrec]
    rw [← Finset.sum_mul, ← Finset.sum_div, div_self hS, one_mul]
  · rw [weighted_ratio_mixture hm tn (fun j => fp j + tn j) hfptn]
    have hS : (∑ k : Fin m, (fp k + tn k)) ≠ 0 :=
      (Finset.sum_pos (fun k _ => hfptn k) hne).ne'
    simp only [hspec]
    rw [← Finset.sum_mul, ← Finset.sum_div, div_self hS, one_mul]
end Aggmetrics
