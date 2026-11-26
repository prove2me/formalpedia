-- Prove2me | solution 1 for AME125.sum_range_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:47.290458+00:00
-- url     : https://prove2.me/submissions/c43056b8-f93c-40e7-968a-3320caaa0129

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate

set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix
namespace AME125
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ((List.range 12).map f).sum = ∑ j : Fin 12, f j := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range, Finset.sum_range]
end AME125
