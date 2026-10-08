-- Prove2me | Definitions.Def_PowerFreeValues
-- name    : PowerFreeValues
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:13.360145+00:00
-- url     : https://prove2.me/theorems/e87592e2-3b84-483c-8441-a523a675cfa8
-- statement:
--   PowerFree(k,a) holds for an integer a when no prime p has p^k dividing a. For an integer polynomial f and natural number q, rho(f,q) is the number of residues a in {0,…,q−1} with q dividing f(a). For a real X, count(f,k,X) is the number of integers n between 1 and ⌊X⌋ for which f(n) is k-th-power-free in this sense. LocallyAdmissible(f,k) says that rho(f,p^k) < p^k for every prime p, so f has a residue class modulo p^k at which p^k does not divide its value. For each prime p, localFactor(f,k,p) is 1 − rho(f,p^k)/p^k, and densityConstant(f,k) is the infinite product of these factors over all primes. DensityStatement(f,k) is a defined proposition, not an established theorem, asserting three things: the family of local factors is multipliable, the density constant is strictly positive, and count(f,k,X) − densityConstant(f,k)·X is little-o of X as X tends to infinity, so count(f,k,X) is asymptotic to densityConstant(f,k)·X. The definitions do not themselves assume that f is nonconstant or that k is at least 2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PowerFreeValues.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PowerFreeValues.lean; bytes 16..1111
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI



open Filter Asymptotics
open scoped Topology

namespace QuarticPowerFree

def PowerFree (k : ℕ) (a : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ k ∣ a

def rho (f : Polynomial ℤ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)).card

noncomputable def count (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊X⌋₊).filter fun n : ℕ => PowerFree k (f.eval (n : ℤ))).card

def LocallyAdmissible (f : Polynomial ℤ) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k

noncomputable def localFactor (f : Polynomial ℤ) (k : ℕ) (p : Nat.Primes) : ℝ :=
  1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k

noncomputable def densityConstant (f : Polynomial ℤ) (k : ℕ) : ℝ :=
  ∏' p : Nat.Primes, localFactor f k p

def DensityStatement (f : Polynomial ℤ) (k : ℕ) : Prop :=
  Multipliable (localFactor f k) ∧
  0 < densityConstant f k ∧
  (fun X : ℝ => (count f k X : ℝ) - densityConstant f k * X) =o[atTop]
    (fun X : ℝ => X)



end QuarticPowerFree
end OAI


