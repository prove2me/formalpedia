-- Prove2me | solution 1 for Aggmetrics.micro_skew_mixture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:32.578165+00:00
-- url     : https://prove2.me/submissions/d6d38e26-a3c2-4af3-891e-0413cd16b5d4

import Mathlib
import Definitions.Def_Aggmetrics_Basic
import Theorems.Thm_Aggmetrics_weighted_ratio_mixture

set_option autoImplicit true
open Finset
open Aggmetrics
namespace Aggmetrics
theorem _root_.solution {m : ℕ} (hm : 0 < m) (g : ℝ → ℝ → ℝ)
    (tp fp fn tn : Fin m → ℝ)
    (htpfn : ∀ j, 0 < tp j + fn j) (hfptn : ∀ j, 0 < fp j + tn j) :
    g ((∑ j, tp j) / (∑ j, (tp j + fn j))) ((∑ j, tn j) / (∑ j, (fp j + tn j)))
    = g (∑ j, ((tp j + fn j) / ∑ k, (tp k + fn k)) * (tp j / (tp j + fn j)))
        (∑ j, ((fp j + tn j) / ∑ k, (fp k + tn k)) * (tn j / (fp j + tn j))) := by
  rw [weighted_ratio_mixture hm tp (fun j => tp j + fn j) htpfn,
      weighted_ratio_mixture hm tn (fun j => fp j + tn j) hfptn]
end Aggmetrics
