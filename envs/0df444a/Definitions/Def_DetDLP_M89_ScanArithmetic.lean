-- Prove2me | Definitions.Def_DetDLP_M89_ScanArithmetic
-- name    : DetDLP_M89_ScanArithmetic
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T16:51:25.101015+00:00
-- url     : https://prove2.me/theorems/e3b0e33e-361c-4d3a-8ce9-a1576801a927
-- title:
--   Arithmetic correctness of the prime-power component scan (definitions)
-- statement:
--   For a prime $p$, consider any ordered list of units, with no generation hypothesis. The residue scan using the prime factor list of $p-1$, modular square-and-multiply, and the first witness for each distinct prime returns the canonical residue of the component product of Proposition 3.3.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3 and its proof, Section 3.3.

import Mathlib
set_option autoImplicit false
namespace DetDLP.M89Scan

/-- Little-endian square-and-multiply, reducing the accumulator and base modulo `p`. -/
def powBits (p a : ℕ) : List Bool → ℕ
  | [] => 1 % p
  | b :: bs => ((if b then a else 1) * powBits p (a * a % p) bs) % p

def powMod (p a e : ℕ) := powBits p a e.bits

def firstWitness (p q : ℕ) (us : List ℕ) := (us.find? (fun u => decide (powMod p u q ≠ 1))).getD 1

def unitRep {p : ℕ} (u : (ZMod p)ˣ) := (u : ZMod p).val

def residueProduct (p : ℕ) : List ℕ → ℕ
  | [] => 1 % p
  | a :: as => (a * residueProduct p as) % p

def scan (p : ℕ) (factors us : List ℕ) : ℕ :=
  let n := p-1
  residueProduct p (factors.dedup.map (fun r => powMod p (firstWitness p (n/r) us) (n / r^(factors.count r))))
end DetDLP.M89Scan


