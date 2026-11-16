-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Supplement_HashedEvaluation
-- name    : ParityBarrier563_Trilinear_Supplement_HashedEvaluation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:41:24.715623+00:00
-- url     : https://prove2.me/theorems/4cdcd99b-66cc-4d50-ba48-2b5306e15f1c
-- title:
--   Padded hashed polynomial evaluation with arbitrary monic modulus
-- statement:
--   For $n\ge64$ let $r=\lceil n^{2/3}\rceil$ and let t be the largest even integer with $t^6\le n$. A Hankel matrix U is specified by $n+r-1$ bits. The modulus is $P(Z)=Z^r+\sum_{i<r}P_iZ^i$ for arbitrary bits $P_i$; each $\beta_j$ has r coefficient bits. Define h(x) as the polynomial whose coefficients are Ux, and accept exactly when
--   $$[Z^0]\left(\left(\sum_{j<t}\beta_jh(x)^j\right)\bmod P\right)=0.$$
--   Polynomial remainder by a monic polynomial gives the quotient-ring operation even when P is reducible. The whole function is decoded from blocks x,U,P,β on every input length $5n,\ldots,5n+4$ and ignores every trailing bit after $2n+(t+2)r-1$. The zero extension of inputBit outside valid offsets makes a total function; for $n\ge64$ every decoded bit is in range. This defines the entire evaluator, rather than an irreducible hard slice.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), §5.2, printed p.20 / PDF 22

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Supplement_FiniteAverages

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- r = ceiling(n^(2/3)); t is the largest even integer with t^6 ≤ n. -/
noncomputable def hashR (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (2 / 3 : ℝ)⌉₊
def hashT (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun t => Even t ∧ t ^ 6 ≤ n).max'
    ⟨0, by simp⟩

/-- Polynomial with coefficients specified by bits, in ascending degree. -/
noncomputable def bitPolynomial {r : ℕ} (a : Fin r → Bool) : Polynomial (ZMod 2) :=
  ∑ i, Polynomial.monomial i.val (if a i then 1 else 0)

/-- Every monic modulus of degree r, not restricted to irreducible ones. -/
noncomputable def hashModulus {r : ℕ} (a : Fin r → Bool) : Polynomial (ZMod 2) :=
  Polynomial.X ^ r + bitPolynomial a

/-- Hankel multiplication, encoded by its n+r-1 antidiagonals. -/
noncomputable def hankelHash {n r : ℕ} (U : Fin (n + r - 1) → Bool) (x : Fin n → Bool) :
    Polynomial (ZMod 2) :=
  ∑ i : Fin r, Polynomial.monomial i.val
    (∑ j : Fin n, if U ⟨i.val + j.val, by omega⟩ && x j then 1 else 0)

/-- Quotient-ring evaluation via the canonical remainder modulo the monic polynomial.
This works also for reducible P. -/
noncomputable def hashAccept {n r t : ℕ} (U : Fin (n + r - 1) → Bool)
    (P : Polynomial (ZMod 2)) (β : Fin t × Fin r → Bool) : BoolFn (Fin n) :=
  fun x => decide (((∑ j : Fin t,
    bitPolynomial (fun i => β (j,i)) * hankelHash U x ^ j.val) %ₘ P).coeff 0 = 0)

/-- A bit of a padded input, with a total zero extension on invalid offsets. All offsets
used below are in range for n≥64 and padded length 5n,...,5n+4. -/
def inputBit {N : ℕ} (w : Fin N → Bool) (i : ℕ) : Bool :=
  if h : i < N then w ⟨i,h⟩ else false

/-- Complete hashed evaluator, block order: n data bits, n+r-1 Hankel bits, r modulus
bits, then tr coefficient bits. Every trailing bit is ignored. -/
noncomputable def hashedFn (n : ℕ) (padding : Fin 5) : BoolFn (Fin (5*n + padding.val)) :=
  let r := hashR n
  let t := hashT n
  fun w => hashAccept
    (fun i : Fin (n+r-1) => inputBit w (n+i.val))
    (hashModulus (fun i : Fin r => inputBit w (2*n+r-1+i.val)))
    (fun ji : Fin t × Fin r => inputBit w (2*n+2*r-1+ji.1.val*r+ji.2.val))
    (fun i : Fin n => inputBit w i.val)

end ParityBarrier563.Trilinear.Supplement


