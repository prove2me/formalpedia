-- Prove2me | Definitions.Def_LeanPool_CircuitComplexity_Internal_CircDesc
-- name    : LeanPool_CircuitComplexity_Internal_CircDesc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:10:19.014877+00:00
-- url     : https://prove2.me/theorems/19d4515a-5d5f-415b-9d1a-404f1181e308
-- title:
--   Circ Desc
-- statement:
--   Definitions and structural lemmas for Circ Desc, from Samuel Schlesinger; LeanPool contributors's pinned Circuit Complexity in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/CircDesc.lean

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CircuitComplexity
abbrev GateSlot (W : Nat) := Bool × (Fin W × Fin W) × (Bool × Bool)
abbrev CircDesc (N s : Nat) := Fin s → GateSlot (N + s)
def wireValD {N s : Nat} (d : CircDesc N s) (input : BitString N)
    (w : Fin (N + s)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hi : w.val - N < s := by omega
    let (isAnd, (w1, w2), (n1, n2)) := d ⟨w.val - N, hi⟩
    let v1 := n1.xor (if w1.val < w.val then wireValD d input ⟨w1.val, by omega⟩ else false)
    let v2 := n2.xor (if w2.val < w.val then wireValD d input ⟨w2.val, by omega⟩ else false)
    if isAnd then v1 && v2 else v1 || v2
termination_by w.val
def evalD {N s : Nat} (hs : 0 < s) (d : CircDesc N s) : BitString N → Bool :=
  fun input => wireValD d input ⟨N + s - 1, by omega⟩
theorem five_n_le_two_pow (N : Nat) (hN : 6 ≤ N) : 5 * N ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases h : 6 ≤ n
    · have h5 : 5 ≤ 2 ^ n :=
        le_trans (by norm_num : 5 ≤ 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]; ring
      have ihn := ih h
      omega
    · interval_cases n <;> simp_all
theorem s_pos (N : Nat) (hN : 6 ≤ N) : 0 < 2 ^ N / (5 * N) :=
  Nat.div_pos (five_n_le_two_pow N hN) (by omega)
end CircuitComplexity


