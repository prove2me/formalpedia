-- Prove2me | solution 1 for AaronsonAmbainis.Level.cost_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:55.236284+00:00
-- url     : https://prove2.me/submissions/0e7dde50-6df2-4ebc-b47a-63dd0e9e2c22

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_Level_variance_eq_zero_of_const
import Theorems.Thm_AaronsonAmbainis_Level_rowSum_pos

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (hvar : 0 < variance f) : 0 < K := by
  by_contra hK
  have hconst : ∀ x y, f x = f y := by
    intro x y
    by_contra hxy
    exact hK (lt_of_lt_of_le (rowSum_pos ha hrow hxy) (hsum x))
  rw [variance_eq_zero_of_const f hconst] at hvar
  exact lt_irrefl 0 hvar
end AaronsonAmbainis.Level
