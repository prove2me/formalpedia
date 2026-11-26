-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
-- name    : CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:21:17.925229+00:00
-- url     : https://prove2.me/theorems/0d9875bf-b39d-5386-9b93-0c0b0895cdef
-- title:
--   Fixed Total Composition Recurrence
-- statement:
--   Definitions and structural lemmas for Fixed Total Composition Recurrence, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCompositionRecurrence.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil


set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
theorem composition_blocks_ne_nil
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    c.blocks ≠ [] := by
  intro hc
  have := c.blocks_sum
  simp [hc] at this
  omega
def increaseFirst
    {N : ℕ} (hN : 0 < N) (c : Composition N) : Composition (N + 1) where
  blocks :=
    (c.blocks.head (composition_blocks_ne_nil hN c) + 1) :: c.blocks.tail
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · apply c.blocks_pos
      rw [← List.cons_head_tail (composition_blocks_ne_nil hN c)]
      exact List.mem_cons_of_mem _ hi
  blocks_sum := by
    have hsplit :=
      congrArg List.sum
        (List.cons_head_tail (composition_blocks_ne_nil hN c))
    simp only [List.sum_cons] at hsplit ⊢
    have hsum : c.blocks.sum = N := c.blocks_sum
    omega
def prependOne
    {N : ℕ} (c : Composition N) : Composition (N + 1) where
  blocks := 1 :: c.blocks
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · norm_num
    · exact c.blocks_pos hi
  blocks_sum := by
    simp only [List.sum_cons, c.blocks_sum]
    omega
def removeLeadingOne
    {N : ℕ} (d : Composition (N + 1))
    (hd : d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1) :
    Composition N where
  blocks := d.blocks.tail
  blocks_pos := by
    intro i hi
    apply d.blocks_pos
    rw [← List.cons_head_tail
      (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)]
    exact List.mem_cons_of_mem _ hi
  blocks_sum := by
    have hsplit :=
      congrArg List.sum
        (List.cons_head_tail
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
    simp only [List.sum_cons] at hsplit
    rw [hd, d.blocks_sum] at hsplit
    omega
def decreaseFirst
    {N : ℕ} (d : Composition (N + 1))
    (hd : d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) ≠ 1) :
    Composition N where
  blocks :=
    (d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) - 1) ::
      d.blocks.tail
  blocks_pos := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · have hpos := d.blocks_pos
        (List.head_mem
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
      omega
    · apply d.blocks_pos
      rw [← List.cons_head_tail
        (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)]
      exact List.mem_cons_of_mem _ hi
  blocks_sum := by
    have hpos := d.blocks_pos
      (List.head_mem
        (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
    have hsplit :=
      congrArg List.sum
        (List.cons_head_tail
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
    simp only [List.sum_cons] at hsplit ⊢
    have hsum : d.blocks.sum = N + 1 := d.blocks_sum
    omega
def compositionSuccEquiv
    (N : ℕ) (hN : 0 < N) :
    Composition N ⊕ Composition N ≃ Composition (N + 1) where
  toFun
    | Sum.inl c => increaseFirst hN c
    | Sum.inr c => prependOne c
  invFun d :=
    if hd :
        d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1
    then Sum.inr (removeLeadingOne d hd)
    else Sum.inl (decreaseFirst d hd)
  left_inv := by
    intro c
    cases c with
    | inl c =>
        have hcne := composition_blocks_ne_nil hN c
        cases hc : c.blocks with
        | nil => exact False.elim (hcne hc)
        | cons k ks =>
            have hkpos : 0 < k := by
              apply c.blocks_pos
              simp [hc]
            simp only [increaseFirst, hc, List.head_cons, List.tail_cons]
            rw [dif_neg (by omega)]
            congr 1
            apply Composition.ext
            simp only [decreaseFirst, List.head_cons, List.tail_cons]
            rw [Nat.add_sub_cancel]
            exact hc.symm
    | inr c =>
        have hcne := composition_blocks_ne_nil hN c
        cases hc : c.blocks with
        | nil => exact False.elim (hcne hc)
        | cons k ks =>
            simp only [prependOne, hc, List.head_cons, List.tail_cons]
            simp only [dite_true]
            congr 1
            apply Composition.ext
            simp only [removeLeadingOne, List.tail_cons]
            exact hc.symm
  right_inv := by
    intro d
    change
      (match
          (if hd :
              d.blocks.head
                  (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1
            then Sum.inr (removeLeadingOne d hd)
            else Sum.inl (decreaseFirst d hd)) with
        | Sum.inl c => increaseFirst hN c
        | Sum.inr c => prependOne c) = d
    by_cases hd :
        d.blocks.head
            (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) = 1
    · simp only [hd, dite_true]
      change prependOne (removeLeadingOne d hd) = d
      apply Composition.ext
      change 1 :: d.blocks.tail = d.blocks
      calc
        1 :: d.blocks.tail =
            d.blocks.head
                (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) ::
              d.blocks.tail := by
          congr 1
          exact hd.symm
        _ = d.blocks :=
          List.cons_head_tail
            (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)
    · simp only [hd, dite_false]
      change increaseFirst hN (decreaseFirst d hd) = d
      apply Composition.ext
      change
        (d.blocks.head
            (composition_blocks_ne_nil (Nat.zero_lt_succ N) d) - 1 + 1) ::
            d.blocks.tail = d.blocks
      have hpos := d.blocks_pos
        (List.head_mem
          (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))
      rw [Nat.sub_add_cancel (by omega : 1 ≤
        d.blocks.head (composition_blocks_ne_nil (Nat.zero_lt_succ N) d))]
      exact List.cons_head_tail
        (composition_blocks_ne_nil (Nat.zero_lt_succ N) d)
end
end FixedTotal
end CollatzEndpointTransport


