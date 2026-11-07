-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.exists_monomial_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:34:22.609642+00:00
-- url     : https://prove2.me/submissions/55a2f1f9-27e1-4952-b80a-6a5a6c707bbf

import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Definitions.Def_AaronsonAmbainis_DetLow_Corollary
import Theorems.Thm_AaronsonAmbainis_DetLow_exists_lowest_le_bdry

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool)
    (ℓ : ι → ℝ) (hℓ : ∀ j, 0 ≤ ℓ j) :
    ∃ m ∈ (agMatrix g).det.support,
      ∑ j, ℓ j * (m j : ℝ) ≤ ∑ j, ℓ j * (bdry g j : ℝ) := by
  obtain ⟨m, hm, hb⟩ := exists_lowest_le_bdry g
  refine ⟨m, hm.1, Finset.sum_le_sum fun j _ => ?_⟩
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb j) (hℓ j)
end AaronsonAmbainis.DetLow
