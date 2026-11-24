-- Prove2me | Definitions.Def_CSL_Shared_Memory_Streams
-- name    : CSL_Shared_Memory_Streams
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:42.824805+00:00
-- url     : https://prove2.me/theorems/6b05e516-1fd1-4887-8721-24ce58905c43
-- title:
--   Coded sorting library: Shared / Memory / Streams
-- statement:
--   Module `CodedSorting.Shared.Memory.Streams` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Whole-row stream splitting (Section 5.2)
--
--   These are equalities of finite arrays, with their COMPLETE inner coordinates
--   retained. They verify the round-robin assignment and its inverse, not their
--   disk implementation or a recursive I/O bound. `R` is the number of rows in
--   one role stream, `W` the number of roles, and `Inner` includes both exchanged
--   fields and every spectator coordinate and payload-bit offset.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.Streams

import Definitions.Def_CSL_Compat
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Whole-row stream splitting (Section 5.2)

These are equalities of finite arrays, with their COMPLETE inner coordinates
retained. They verify the round-robin assignment and its inverse, not their
disk implementation or a recursive I/O bound. `R` is the number of rows in
one role stream, `W` the number of roles, and `Inner` includes both exchanged
fields and every spectator coordinate and payload-bit offset.
-/

namespace CSL.Streams

variable {R W : ℕ} {Inner Payload : Type*}

/-- Original row `W*j+i` becomes row `j` of role `i` (zero-based). -/
def splitRows (F : Fin (R * W) → Inner → Payload) :
    Fin W → Fin R → Inner → Payload :=
  fun i j x => F (finProdFinEquiv (j, i)) x

/-- Recover the original row order, retaining all coordinates inside a row. -/
def gatherRows (F : Fin W → Fin R → Inner → Payload) :
    Fin (R * W) → Inner → Payload :=
  fun n x => F n.modNat n.divNat x

theorem original_row_number (i : Fin W) (j : Fin R) :
    (finProdFinEquiv (j, i)).val = i.val + W * j.val := rfl

/-- Splitting and gathering preserve every payload value for every input. -/
theorem gather_split (F : Fin (R * W) → Inner → Payload) :
    gatherRows (splitRows F) = F := by
  funext n x
  exact congrArg (fun k => F k x) (finProdFinEquiv.apply_symm_apply n)

/-- The inverse identity also holds for arbitrary contents of all role streams. -/
theorem split_gather (F : Fin W → Fin R → Inner → Payload) :
    splitRows (gatherRows F) = F := by
  funext i j x
  exact congrArg (fun k : Fin R × Fin W => F k.2 k.1 x)
    (finProdFinEquiv.symm_apply_apply (j, i))

/-- The splitter is bijective; in particular it neither duplicates nor loses data. -/
def splitEquiv : (Fin (R * W) → Inner → Payload) ≃
    (Fin W → Fin R → Inner → Payload) where
  toFun := splitRows
  invFun := gatherRows
  left_inv := gather_split
  right_inv := split_gather

/-- Apply the same address transform INSIDE each original complete row. -/
def insideRows (e : Inner ≃ Inner) (F : Fin (R * W) → Inner → Payload) :
    Fin (R * W) → Inner → Payload := fun n x => F n (e.symm x)

/-- Processing every role stream internally and then gathering gives exactly
the same internal transform on every original row. -/
theorem gather_processed_rows (e : Inner ≃ Inner)
    (F : Fin (R * W) → Inner → Payload) :
    gatherRows (fun i j x => splitRows F i j (e.symm x)) = insideRows e F := by
  funext n x
  exact congrArg (fun k => F k (e.symm x)) (finProdFinEquiv.apply_symm_apply n)

/-- A circuit may return role `i` at port `σ i`. This operation sends each
stream to that port without assuming the permutation is the identity. -/
def permuteRoles (σ : Equiv.Perm (Fin W))
    (F : Fin W → Fin R → Inner → Payload) :
    Fin W → Fin R → Inner → Payload := fun k => F (σ.symm k)

/-- Read input role `i` from its designated output port `σ i`. -/
def unpermuteRoles (σ : Equiv.Perm (Fin W))
    (F : Fin W → Fin R → Inner → Payload) :
    Fin W → Fin R → Inner → Payload := fun i => F (σ i)

theorem undo_role_permutation (σ : Equiv.Perm (Fin W))
    (F : Fin W → Fin R → Inner → Payload) :
    unpermuteRoles σ (permuteRoles σ F) = F := by
  funext i j x
  simp [unpermuteRoles, permuteRoles]

/-- Exact result of output-port restoration followed by gathering. -/
theorem gather_permuted_processed_rows (σ : Equiv.Perm (Fin W))
    (e : Inner ≃ Inner) (F : Fin (R * W) → Inner → Payload) :
    gatherRows (unpermuteRoles σ
      (permuteRoles σ (fun i j x => splitRows F i j (e.symm x)))) =
      insideRows e F := by
  rw [undo_role_permutation]
  exact gather_processed_rows e F

section Cardinality

variable [Fintype Inner]

/-- All spectator coordinates contribute to the length of EVERY stream. -/
theorem role_stream_card : Fintype.card (Fin R × Inner) = R * Fintype.card Inner := by
  simp

theorem total_card_eq_roles_times_stream :
    Fintype.card (Fin (R * W) × Inner) =
      W * Fintype.card (Fin R × Inner) := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ac_rfl

/-- This equality is the algebraic meaning of the paper's length `V/W`.
It uses division only when there is at least one role. -/
theorem role_stream_card_eq_div (hW : 0 < W) :
    Fintype.card (Fin R × Inner) =
      Fintype.card (Fin (R * W) × Inner) / W := by
  rw [total_card_eq_roles_times_stream]
  exact (Nat.mul_div_cancel_left _ hW).symm

end Cardinality

end CSL.Streams


