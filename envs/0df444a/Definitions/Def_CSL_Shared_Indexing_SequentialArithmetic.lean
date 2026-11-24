-- Prove2me | Definitions.Def_CSL_Shared_Indexing_SequentialArithmetic
-- name    : CSL_Shared_Indexing_SequentialArithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:48.199739+00:00
-- url     : https://prove2.me/theorems/58072e74-b681-4cb4-b125-4fd74e49d49b
-- title:
--   Coded sorting library: Shared / Indexing / SequentialArithmetic
-- statement:
--   Module `CodedSorting.Shared.Indexing.SequentialArithmetic` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # The monotone streams used for triangular address arithmetic
--
--   Section 5.2 uses multiplication by a fixed positive integer modulo a variable
--   field size. This file proves the actual partition into at most `a` increasing
--   runs; their number does not depend on the modulus. It does not substitute a
--   random-access permutation for a streaming implementation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Indexing.SequentialArithmetic

import Definitions.Def_CSL_Compat
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The monotone streams used for triangular address arithmetic

Section 5.2 uses multiplication by a fixed positive integer modulo a variable
field size. This file proves the actual partition into at most `a` increasing
runs; their number does not depend on the modulus. It does not substitute a
random-access permutation for a streaming implementation.
-/

namespace CSL.SequentialArithmetic

variable {Q a : ℕ}

def multiply (a : ℕ) (hQ : 0 < Q) (x : Fin Q) : Fin Q :=
  ⟨(a * x.val) % Q, Nat.mod_lt _ hQ⟩

def multiplicationRun (ha : 0 < a) (hQ : 0 < Q) (x : Fin Q) : Fin a :=
  ⟨(a * x.val) / Q, (Nat.div_lt_iff_lt_mul hQ).2 (Nat.mul_lt_mul_of_pos_left x.isLt ha)⟩

/-- Two inputs in the same quotient run keep their order after modular multiplication. -/
theorem multiplication_increasing_in_run (ha : 0 < a) (hQ : 0 < Q)
    (x y : Fin Q) (hxy : x < y)
    (hr : multiplicationRun ha hQ x = multiplicationRun ha hQ y) :
    multiply a hQ x < multiply a hQ y := by
  have hx := Nat.mod_add_div (a * x.val) Q
  have hy := Nat.mod_add_div (a * y.val) Q
  have hrun : (a * x.val) / Q = (a * y.val) / Q := congrArg Fin.val hr
  have hmul := Nat.mul_lt_mul_of_pos_left hxy ha
  change (a * x.val) % Q < (a * y.val) % Q
  rw [hrun] at hx
  omega

theorem run_index_monotone (ha : 0 < a) (hQ : 0 < Q) :
    Monotone (multiplicationRun ha hQ) := by
  intro x y hxy
  exact Nat.div_le_div_right (Nat.mul_le_mul_left a hxy)

/-- A run is an interval of the input, rather than a scattered set of addresses. -/
theorem run_interval (ha : 0 < a) (hQ : 0 < Q)
    (x y z : Fin Q) (hxy : x ≤ y) (hyz : y ≤ z)
    (hr : multiplicationRun ha hQ x = multiplicationRun ha hQ z) :
    multiplicationRun ha hQ y = multiplicationRun ha hQ x := by
  apply le_antisymm
  · simpa only [hr] using run_index_monotone ha hQ hyz
  · exact run_index_monotone ha hQ hxy

theorem multiply_injective (hQ : 0 < Q) (hcoprime : a.Coprime Q) :
    Function.Injective (multiply a hQ) := by
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  intro x y h
  have hm : ((a * x.val : ℕ) : ZMod Q) = ((a * y.val : ℕ) : ZMod Q) := by
    apply ZMod.val_injective Q
    simpa only [ZMod.val_natCast, multiply] using congrArg Fin.val h
  rw [Nat.cast_mul, Nat.cast_mul] at hm
  have hunit : IsUnit (a : ZMod Q) := (ZMod.isUnit_iff_coprime a Q).2 hcoprime
  have heq := hunit.mul_left_cancel hm
  have hv := congrArg ZMod.val heq
  apply Fin.ext
  simpa only [ZMod.val_natCast_of_lt x.isLt, ZMod.val_natCast_of_lt y.isLt] using hv

theorem multiply_bijective (hQ : 0 < Q) (hcoprime : a.Coprime Q) :
    Function.Bijective (multiply a hQ) :=
  (Finite.injective_iff_bijective).1 (multiply_injective hQ hcoprime)

noncomputable def multiplicationEquiv (hQ : 0 < Q) (hcoprime : a.Coprime Q) :
    Equiv.Perm (Fin Q) := Equiv.ofBijective _ (multiply_bijective hQ hcoprime)

@[simp] theorem multiplicationEquiv_apply (hQ : 0 < Q) (hcoprime : a.Coprime Q)
    (x : Fin Q) : multiplicationEquiv hQ hcoprime x = multiply a hQ x := rfl

/-- Constant field multiplication has exactly the required finite-run interface:
a bijection, a monotone partition key with `a` possible values, and increasing
output addresses inside each part. -/
theorem multiplication_stream_structure (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) :
    Function.Bijective (multiply a hQ) ∧
    Monotone (multiplicationRun ha hQ) ∧
    ∀ x y : Fin Q, x < y →
      multiplicationRun ha hQ x = multiplicationRun ha hQ y →
      multiply a hQ x < multiply a hQ y :=
  ⟨multiply_bijective hQ hcoprime, run_index_monotone ha hQ,
    multiplication_increasing_in_run ha hQ⟩

/-- Addition has only two quotient runs because both operands are below `Q`. -/
def additionRun (c : Fin Q) (x : Fin Q) : Fin 2 :=
  ⟨(x.val + c.val) / Q,
    (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt c.isLt)).2 (by omega)⟩

def addOffset (c : Fin Q) (x : Fin Q) : Fin Q :=
  ⟨(x.val + c.val) % Q, Nat.mod_lt _ (Nat.zero_lt_of_lt c.isLt)⟩

theorem addition_increasing_in_run (c : Fin Q) (x y : Fin Q) (hxy : x < y)
    (hr : additionRun c x = additionRun c y) : addOffset c x < addOffset c y := by
  have hx := Nat.mod_add_div (x.val + c.val) Q
  have hy := Nat.mod_add_div (y.val + c.val) Q
  have heq : (x.val + c.val) / Q = (y.val + c.val) / Q := congrArg Fin.val hr
  change (x.val + c.val) % Q < (y.val + c.val) % Q
  rw [heq] at hx
  have : x.val < y.val := hxy
  omega

end CSL.SequentialArithmetic


