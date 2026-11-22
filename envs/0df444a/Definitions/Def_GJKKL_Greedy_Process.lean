-- Prove2me | Definitions.Def_GJKKL_Greedy_Process
-- name    : GJKKL_Greedy_Process
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:34:12.442727+00:00
-- url     : https://prove2.me/theorems/c0118d16-b4f0-4198-9801-897eb0657633
-- title:
--   Process
-- statement:
--   Definitions and structural lemmas for Process, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
def avail (H : Finset (Finset V)) (h : List (Finset V)) : Finset (Finset V) :=
  H.filter (fun e => ∀ f ∈ h, Disjoint e f)
theorem mem_avail {H : Finset (Finset V)} {h : List (Finset V)} {e : Finset V} :
    e ∈ avail H h ↔ e ∈ H ∧ ∀ f ∈ h, Disjoint e f := by
  simp [avail]
@[simp] theorem avail_nil (H : Finset (Finset V)) : avail H [] = H := by
  ext e; simp [mem_avail]
def covered (h : List (Finset V)) : Finset V := h.toFinset.biUnion id
noncomputable def greedyKernel (H : Finset (Finset V)) : Kernel (Finset V) where
  K h a := if a ∈ avail H h then ((avail H h).card : ℝ)⁻¹ else 0
  nonneg h a := by split_ifs <;> positivity
  mass_le h := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    by_cases h0 : (avail H h).card = 0
    · simp [h0]
    · rw [mul_inv_cancel₀ (by exact_mod_cast h0)]
def IsGreedySeq (H : Finset (Finset V)) : List (Finset V) → Prop
  | [] => True
  | a :: h => IsGreedySeq H h ∧ a ∈ avail H h
end GJKKL


