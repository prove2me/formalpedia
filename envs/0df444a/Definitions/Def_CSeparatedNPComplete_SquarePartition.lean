-- Prove2me | Definitions.Def_CSeparatedNPComplete_SquarePartition
-- name    : CSeparatedNPComplete_SquarePartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:46:36.176257+00:00
-- url     : https://prove2.me/theorems/4149fb02-d1d4-5a82-b306-ee3733d30b08
-- title:
--   Square Partition
-- statement:
--   Definitions and structural lemmas for Square Partition, from Tomislav Prusina (tomo61098/c-separated-np-complete-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Fixed-threshold Gaussian c-separation gadget equivalence and square-partition reduction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquarePartition.lean

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CSeparatedNPComplete.SquarePartition
def plus (N : ℕ) (a : ℕ → ℕ) (K i : ℕ) : ℕ :=
  (K ^ (N + i) + a i * K ^ (N - i)) ^ 2
def minus (N : ℕ) (a : ℕ → ℕ) (K i : ℕ) : ℕ :=
  (K ^ (N + i) - a i * K ^ (N - i)) ^ 2
def chooseSum (m : ℕ) (a : ℕ → ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i : Fin m, if b i then a i else 0
def leftSum (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i : Fin m, if b i then plus N a K i else minus N a K i
def rightSum (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i : Fin m, if b i then minus N a K i else plus N a K i
def values (N : ℕ) (a : ℕ → ℕ) (K : ℕ) : Vec (N + N) :=
  Fin.append (fun i : Fin N => (plus N a K i : ℝ))
    (fun i : Fin N => (minus N a K i : ℝ))
def selector (N : ℕ) (b : ℕ → Bool) : Vec (N + N) :=
  Fin.append (fun i : Fin N => if b i then 1 else 0)
    (fun i : Fin N => if b i then 0 else 1)
end CSeparatedNPComplete.SquarePartition


