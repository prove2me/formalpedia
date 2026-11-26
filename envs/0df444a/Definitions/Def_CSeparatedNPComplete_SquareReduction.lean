-- Prove2me | Definitions.Def_CSeparatedNPComplete_SquareReduction
-- name    : CSeparatedNPComplete_SquareReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:46:56.335315+00:00
-- url     : https://prove2.me/theorems/7fe86ca3-e3e7-53c6-8a2a-02264e996c2f
-- title:
--   Square Reduction
-- statement:
--   Definitions and structural lemmas for Square Reduction, from Tomislav Prusina (tomo61098/c-separated-np-complete-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Fixed-threshold Gaussian c-separation gadget equivalence and square-partition reduction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CSeparatedNPComplete.SquareReduction
def base {n : ℕ} (a : Fin n → ℕ) : ℕ :=
  2 + n + 2 * ∑ i, a i + ∑ i, (a i) ^ 2
def upper {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : ℕ :=
  base a ^ (n + i.val + 1)
def lower {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : ℕ :=
  a i * base a ^ (n - (i.val + 1))
def values {n : ℕ} (a : Fin n → ℕ) : Vec (n + n) :=
  Fin.append (fun i => (((upper a i + lower a i) ^ 2 : ℕ) : ℝ))
    (fun i => (((upper a i - lower a i) ^ 2 : ℕ) : ℝ))
def HasPartition {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ p : Vec n, is_binary p ∧ dot p (fun i => (a i : ℝ)) = (∑ i, (a i : ℝ)) / 2
def encode {n : ℕ} (a : Fin n → ℕ) : Fin (n + n) → ℕ :=
  Fin.append (fun i => (upper a i + lower a i) ^ 2)
    (fun i => (upper a i - lower a i) ^ 2)
end CSeparatedNPComplete.SquareReduction


