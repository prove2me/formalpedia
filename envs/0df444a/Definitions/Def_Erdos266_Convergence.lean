-- Prove2me | Definitions.Def_Erdos266_Convergence
-- name    : Erdos266_Convergence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:56:32.597694+00:00
-- url     : https://prove2.me/theorems/65f36caf-37ef-461f-87f9-feaf46c71ad8
-- title:
--   Convergence
-- statement:
--   Definitions and structural lemmas for Convergence, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Theorems.Thm_Erdos266_le_dOf

set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
open Finset Filter Topology
noncomputable def Sinf : ℕ → ℕ → ℤ := fun l j => (run (l + 1)).1 l j
noncomputable def xinf : ℕ → ℚ := fun i => (run (mseq (i + 1))).2 i
noncomputable def cnt (k : ℕ) : ℕ := ∑ l ∈ range k, dOf l
lemma cnt_succ (k : ℕ) : cnt (k + 1) = cnt k + dOf k := sum_range_succ _ k
lemma le_cnt (m : ℕ) : m + 1 ≤ cnt (mseq 1 + m + 1) := by
  induction m with
  | zero =>
    rw [show mseq 1 + 0 + 1 = mseq 1 + 1 from rfl, cnt_succ]
    have h1 : 1 ≤ dOf (mseq 1) := le_dOf le_rfl
    omega
  | succ m ih =>
    rw [show mseq 1 + (m + 1) + 1 = (mseq 1 + m + 1) + 1 from by omega, cnt_succ]
    have h1 : 1 ≤ dOf (mseq 1 + m + 1) := le_dOf (by omega)
    omega
lemma cnt_unbounded (n : ℕ) : ∃ k, n < cnt (k + 1) := by
  refine ⟨mseq 1 + n, ?_⟩
  have := le_cnt n
  omega
noncomputable def kOf (n : ℕ) : ℕ := Nat.find (cnt_unbounded n)
noncomputable def elemZ (l j : ℕ) : ℤ := ((j + 1) * bigN l : ℕ) + Sinf l j
noncomputable def aSeq (n : ℕ) : ℕ := (elemZ (kOf n) (n - cnt (kOf n))).toNat
noncomputable def pSum (i' n : ℕ) : ℝ := ∑ m ∈ range n, f (i' + 1) ((aSeq m : ℕ) : ℝ)
end Erdos266


