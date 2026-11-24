-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_FunctionBase
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_FunctionBase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:22:39.730411+00:00
-- url     : https://prove2.me/theorems/1abc36ca-b92c-4b62-8359-269c29758cbb
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / FunctionBase
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.FunctionBase` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.FunctionBase

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Base

namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate

def entryFunctionCheck (p : Projection) (f : Nat → Int) : Bool :=
  (List.range 64).all fun n => p.numerator[n]! == f n

theorem entries_of_check (p : Projection) (f : Nat → Int)
    (hs : p.numerator.size = 64)
    (hc : entryFunctionCheck p f = true)
    (hz : ∀ n, 64 ≤ n → f n = 0) :
    ∀ n, p.numerator[n]! = f n := by
  intro n
  by_cases hn : n < 64
  · exact beq_iff_eq.mp (List.all_eq_true.mp hc n (List.mem_range.mpr hn))
  · rw [getElem!_neg _ _ (by omega), hz n (by omega)]
    rfl

def functionNestedCheck (denominator : Int) (p q : Nat → Int) : Bool :=
  (List.range 8).all fun i => (List.range 8).all fun j =>
    (List.range 8).foldl
      (fun s k => s + q (8*i+k) * p (8*k+j)) 0 ==
      denominator * p (8*i+j)

theorem nestedCheck_eq_function (p q : Projection) (fp fq : Nat → Int)
    (hp : ∀ n, p.numerator[n]! = fp n)
    (hq : ∀ n, q.numerator[n]! = fq n) :
    nestedCheck p q = functionNestedCheck q.denominator fp fq := by
  simp only [nestedCheck, functionNestedCheck, matrixEntry, hp, hq]

theorem functionNestedCheck_zero (denominator : Int) (q : Nat → Int) :
    functionNestedCheck denominator (fun _ => 0) q = true := by
  simp [functionNestedCheck, List.range_succ]

def identityEntries (n : Nat) : Int := if n / 8 = n % 8 then 1 else 0

theorem functionNestedCheck_identity (p : Nat → Int) :
    functionNestedCheck 1 p identityEntries = true := by
  simp [functionNestedCheck, identityEntries, List.range_succ]

end CSL.Construction.PhysicalFramePaths


