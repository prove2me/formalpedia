-- Prove2me | solution 1 for Auto.sqrt_sq_add_sq_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:34.460705+00:00
-- url     : https://prove2.me/submissions/1a13518e-5793-49b0-9178-bfc0e661ba91

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences

set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set
namespace Auto
theorem _root_.solution {a b : ℤ → ℝ} (ha : SpacedSequence a) (hb : SpacedSequence b) :
    SpacedSequence (fun j => Real.sqrt (a j ^ 2 + b j ^ 2)) := by
  intro j
  have hsum : 0 ≤ a j ^ 2 + b j ^ 2 := by positivity
  have hsum' : 0 ≤ a (j + 1) ^ 2 + b (j + 1) ^ 2 := by positivity
  constructor
  · apply Real.sqrt_pos.2
    nlinarith [(ha j).1, (hb j).1]
  · have ha' := (ha j).2
    have hb' := (hb j).2
    have hsq : 4 * (a j ^ 2 + b j ^ 2) ≤ a (j + 1) ^ 2 + b (j + 1) ^ 2 := by
      have ha_nonneg := le_of_lt (ha j).1
      have hb_nonneg := le_of_lt (hb j).1
      nlinarith [sq_nonneg (a (j + 1) - 2 * a j),
        sq_nonneg (b (j + 1) - 2 * b j)]
    have hsqrt := Real.sq_sqrt hsum
    have hsqrt' := Real.sq_sqrt hsum'
    nlinarith [Real.sqrt_nonneg (a j ^ 2 + b j ^ 2),
      Real.sqrt_nonneg (a (j + 1) ^ 2 + b (j + 1) ^ 2)]
end Auto
