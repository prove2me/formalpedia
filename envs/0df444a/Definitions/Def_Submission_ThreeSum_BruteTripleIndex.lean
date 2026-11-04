-- Prove2me | Definitions.Def_Submission_ThreeSum_BruteTripleIndex
-- name    : Submission_ThreeSum_BruteTripleIndex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:54:28.733815+00:00
-- url     : https://prove2.me/theorems/86a125ba-fd51-41a9-8952-d4fadaa6cff5
-- title:
--   Brute Triple Index
-- statement:
--   Definitions and structural lemmas for Brute Triple Index, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BruteTripleIndex.lean

import Definitions.Def_Submission_ThreeSum_Coloring
set_option autoImplicit false
namespace ThreeSum.BruteTripleIndex
def first (n t : ℕ) : ℕ := t/n/n
def second (n t : ℕ) : ℕ := t/n%n
def third (n t : ℕ) : ℕ := t%n
theorem bounds {n t : ℕ} (hn : 0 < n) (ht : t < n^3) :
    first n t < n ∧ second n t < n ∧ third n t < n := by
  have ht' : t < (n*n)*n := by simpa only [pow_succ,pow_zero,one_mul] using ht
  have hq : t/n < n*n := (Nat.div_lt_iff_lt_mul hn).mpr ht'
  exact ⟨(Nat.div_lt_iff_lt_mul hn).mpr hq,Nat.mod_lt _ hn,Nat.mod_lt _ hn⟩
def code {n : ℕ} (i j k : Fin n) : ℕ := (i.val*n+j.val)*n+k.val
def witness {n t : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (ht : t < n^3) : Prop :=
  let a : Fin n := ⟨first n t,(bounds hn ht).1⟩
  let b : Fin n := ⟨second n t,(bounds hn ht).2.1⟩
  let c : Fin n := ⟨third n t,(bounds hn ht).2.2⟩
  a≠b ∧ a≠c ∧ b≠c ∧ x a+x b+x c=0
def Hit {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (t : ℕ) : Prop :=
  ∃ i, ∃ hi : i < n^3, i < t ∧ witness x hn hi
end ThreeSum.BruteTripleIndex


