-- Prove2me | Definitions.Def_AKS_alg
-- name    : AKS_alg
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T12:36:11.949918+00:00
-- url     : https://prove2.me/theorems/2f2419be-ee84-4191-891f-222823d98c62
-- title:
--   The algorithm layer: the AKS primality test, the multiplicative order, and the introspective groups
-- statement:
--   The algorithm layer of the AKS mission, carrying the arithmetic scaffolding of Sections 3 to 5 of the paper. logUp is a generous integer ceiling of log2 n, strictly greater than the real logarithm; the algorithm's two log-dependent quantities are measured with it. ordR r a is the multiplicative order of a modulo r, searched in the window k < r (faithful, since every order divides phi(r) < r), with the convention 0 when gcd(a, r) > 1. lcmFirst m is the lcm of the numbers 1 through m, the function that Lemma 3.1 lower-bounds. isPow is the perfect-power predicate of step 1. smallestR n is the least r > 1 with ordR r n > logUp(n)^2, searched within the window that Lemma 4.3 bounds. ell r n is the loop bound of step 5, the floor of the product of the square root of phi(r) and logUp n. AksResult is the output type and aksDecide transcribes the six steps of the paper's algorithm literally: reject perfect powers, fix r, reject nontrivial gcd witnesses up to r, accept n at most r, test congruence (2) for a = 1 to ell r n, accept. inI and Gfin encode the set I = {(n/p)^i p^j} and its residue group G modulo r, the group of size t whose order properties drive the correctness proof. aksWork is a schoolbook arithmetic work measure for the algorithm, the quantity that the poly_time milestone bounds polynomially.
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Sections 3-5.

import Mathlib
import Definitions.Def_AKS_poly

/-!
# The algorithm layer: the AKS primality test and its analysis scaffolding

The algorithm layer of the AKS mission, carrying the arithmetic scaffolding of
Sections 3 to 5 of Agrawal, Kayal, and Saxena, "PRIMES is in P", Annals of
Mathematics 160 (2004) 781-793: the integer logarithm, the multiplicative
order, the lcm of the first numbers, the perfect-power predicate, the search
for r, the loop bound l, the six-step decision function aksDecide, the set I
and the residue group G of Section 4, and the work measure of Section 5.
-/

namespace AKS

open Polynomial

/-- A generous integer ceiling of log2 n: strictly greater than log2 n for
every positive n (and 1 for n = 0). The algorithm's two log-dependent
quantities - the threshold of step 2 and the loop bound of step 5 - are
measured with it; the generosity preserves correctness in both directions. -/
def logUp (n : ℕ) : ℕ := Nat.log2 n + 1

/-- The multiplicative order of a modulo r: the least k with 0 < k < r and
a^k = 1 (mod r), or 0 when no such k exists. Every multiplicative order
divides phi(r) < r, so the window k < r captures the order exactly; in
particular the value is 0 whenever gcd(a, r) > 1. -/
def ordR (r a : ℕ) : ℕ :=
  match (List.range r).filter (fun k => decide (0 < k ∧ a ^ k % r = 1 % r)) with
  | [] => 0
  | k :: _ => k

/-- LCM(m): the least common multiple of the numbers 1, ..., m. Lemma 3.1 of
the paper lower-bounds it by 2^m for m >= 7. -/
def lcmFirst (m : ℕ) : ℕ := (List.range m).foldl (fun acc k => Nat.lcm acc (k + 1)) 1

/-- Step 1 of the algorithm: n is a perfect power a^b with a, b > 1. -/
def isPow (n : ℕ) : Prop := ∃ a b, 1 < a ∧ 1 < b ∧ n = a ^ b

/-- Step 2 of the algorithm: the least r > 1 with ordR r n > logUp(n)^2,
searched within the window that the r_exists milestone (Lemma 4.3 of the
paper) bounds; the default 2 is unreachable for n >= 2. -/
def smallestR (n : ℕ) : ℕ :=
  match (List.range (max 3 ((logUp n) ^ 5) + 1)).filter
      (fun r => decide (1 < r ∧ logUp n ^ 2 < ordR r n)) with
  | [] => 2
  | r :: _ => r

/-- The loop bound of step 5: the floor of the product of the square root of
phi(r) and logUp(n), encoded exactly as the floor of the square root of
phi(r) * logUp(n)^2. -/
def ell (r n : ℕ) : ℕ := Nat.sqrt (Nat.totient r * (logUp n) ^ 2)

/-- The output of the algorithm. -/
inductive AksResult where
  | composite : AksResult
  | prime : AksResult
  deriving Repr

/-- The set I of the paper (Section 4): (n/p)^i * p^j for i, j >= 0, where p
is a prime factor of n. -/
def inI (n p : ℕ) (m : ℕ) : Prop := ∃ i j, m = (n / p) ^ i * p ^ j

/-- The group G of the paper: the residues modulo r of the numbers of I,
encoded by the witness window i, j < r (faithful under coprimality of n/p and
p to r, since both orders then divide phi(r) <= r, so every residue of an
I-number is achieved inside the window). -/
def Gfin (n p r : ℕ) : Finset ℕ :=
  (Finset.range r).biUnion (fun i =>
    (Finset.range r).image (fun j => ((n / p) ^ i * p ^ j) % r))

section
open Classical

/-- The algorithm of Section 4 of the paper, transcribed literally: step 1
rejects perfect powers; step 2 fixes r; step 3 rejects nontrivial gcd
witnesses; step 4 accepts n <= r; step 5 tests congruence (2) for
a = 1, ..., ell r n; step 6 accepts. Stated with classical decision: only
the extensional behavior of the test matters, never its execution. -/
noncomputable def aksDecide (n : ℕ) : AksResult :=
  if 1 < n ∧ ¬ isPow n then
    let r := smallestR n
    if ∃ a, a ≤ r ∧ 1 < Nat.gcd a n ∧ Nat.gcd a n < n then AksResult.composite
    else if n ≤ r then AksResult.prime
    else if ∃ a, 1 ≤ a ∧ a ≤ ell r n ∧ ¬ cycCong n r a then AksResult.composite
    else AksResult.prime
  else AksResult.composite

end

/-- A schoolbook arithmetic work measure for the algorithm: logUp(n)^6 for
step 1, r * (logUp(n) + 1) for the searches of steps 2 and 3, and
(ell r n) * (logUp(n) + 1) * (r + 1)^2 for the congruence loop of step 5. -/
def aksWork (n : ℕ) : ℕ :=
  (logUp n) ^ 6
    + (smallestR n) * ((logUp n) + 1)
    + (ell (smallestR n) n) * ((logUp n) + 1) * ((smallestR n) + 1) ^ 2

end AKS


