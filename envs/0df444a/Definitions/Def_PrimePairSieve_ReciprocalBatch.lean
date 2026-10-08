-- Prove2me | Definitions.Def_PrimePairSieve_ReciprocalBatch
-- name    : PrimePairSieve_ReciprocalBatch
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T18:52:30.184103+00:00
-- url     : https://prove2.me/theorems/ae680d4a-8a77-485a-abdf-2287829632df
-- title:
--   Finite row certificates for reciprocal sieve weights
-- statement:
--   A row records an index, a rational weight, and a finite prime-factor set. Its Boolean checker verifies prime factors, exact products and positive numerator-denominator data; a rounded sum filters to an endpoint and sums integer lower contributions. The separate soundness theorem turns these checks into a lower bound for the literal reciprocal sieve sum.
-- source:
--   Finite certificate interface for the bounded verification of https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b, derived from prime-factor identities and integer-division rounding.

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Chain
open scoped BigOperators
set_option autoImplicit false
namespace PrimePairSieve.ReciprocalBatch
noncomputable def weight (n : ℕ) : ℝ :=
  if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2/((p:ℝ)-2) else 0

structure Row where
  n : ℕ
  a : ℕ
  b : ℕ
  factors : Finset ℕ
  deriving DecidableEq

def rowCheck (r : Row) : Bool :=
  decide ((∀ p ∈ r.factors, Nat.Prime p) ∧ (∏ p ∈ r.factors, p) = r.n) &&
    decide (r.a = ∏ p ∈ r.factors, if p = 2 then 1 else 2) &&
    decide (r.b = ∏ p ∈ r.factors, if p = 2 then 1 else p-2) &&
    decide (0 < r.b ∧ 0 < r.n)

def rounded (scale L : ℕ) (r : Row) : ℕ := scale*r.a*L/(r.b*(L+r.n))

def roundedSum (scale L : ℕ) (rows : List Row) : ℕ :=
  ((rows.filter (fun r => r.n ≤ L)).map (rounded scale L)).sum

end PrimePairSieve.ReciprocalBatch


