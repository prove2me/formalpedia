-- Prove2me | solution 1 for AaronsonAmbainis.Row.disjoint_blocks_of_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:28.653588+00:00
-- url     : https://prove2.me/submissions/9822c06b-25e3-4a67-aebb-63b33b24b4b1

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_DisjointBlocks

set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Row
namespace AaronsonAmbainis.Row
theorem _root_.solution (hBlock : BlockInequality) (ι : Type) [Fintype ι]
    [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d)
    (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι)
    (hS : ∀ b b' : β, b ≠ b' → Disjoint (S b) (S b')) :
    ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 := by
  have hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ 1 := by
    intro i
    rw [Finset.card_le_one]
    intro b hb b' hb'
    by_contra hne
    exact Finset.disjoint_left.mp (hS b b' hne) (Finset.mem_filter.mp hb).2
      (Finset.mem_filter.mp hb').2
  have hc : ((1 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((1 : ℕ) : ℝ))) ≤ 2 := by
    rw [Nat.cast_one, div_one, Real.cos_pi]
    norm_num
  have h := hBlock ι d f hf hdeg x β S 1 1 Nat.one_pos hN hc
  simpa using h
end AaronsonAmbainis.Row
