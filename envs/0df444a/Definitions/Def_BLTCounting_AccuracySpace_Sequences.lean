-- Prove2me | Definitions.Def_BLTCounting_AccuracySpace_Sequences
-- name    : BLTCounting_AccuracySpace_Sequences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:25.97321+00:00
-- url     : https://prove2.me/theorems/ac9a27e3-5b5a-4a47-ad2a-3cc5a424878d
-- title:
--   Square-root sequence, BLT recurrences, finite coefficient error, Hankel and weighted Hankel matrices
-- statement:
--   This module fixes the sequences and Hankel matrices of the paper.
--
--   1. The **square-root sequence** is $f[k]=4^{-k}\binom{2k}{k}$ for $k\ge0$, the Taylor coefficients of $(1-z)^{-1/2}$.
--   2. A complex sequence $c$ is a **BLT sequence of recurrence order $d$** if there are $q[1],\dots,q[d]\in\mathbb C$ with
--   $$c[k]=-\sum_{j=1}^{d}q[j]\,c[k-j]\qquad\text{for every }k\ge d.$$
--   The first $d$ coefficients are unrestricted. No stability, pole, reality or summability condition is imposed, and a shorter recurrence pads with zero coefficients, so this means order at most $d$, as the paper says on PDF p. 5.
--   3. The **finite coefficient error** is $\|a-b\|_{\ell_2(0,n-1)}=\bigl(\sum_{k=0}^{n-1}|a[k]-b[k]|^2\bigr)^{1/2}$. It is not divided by $n$.
--   4. The **Hankel matrix** is $H_m(a)[r,s]=a[r+s]$ for $0\le r,s\le m-1$. For a finite set $S$ of indices, $H_S(a)=(a[r+s])_{r,s\in S}$.
--   5. With $D_S=\mathrm{diag}(r^{-1/4})_{r\in S}$, the **weighted Hankel matrix** is $\widehat H_S(a)=D_SH_S(a)D_S$, with entries $a[r+s]/(rs)^{1/4}$.
--
--   These objects state the approximation problem of Theorem 1.2 and its reduction to low-rank approximation. The weights are finite only for $r\ge1$; every statement using them takes $S$ inside the positive integers.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, equation (1), printed p. 1 (PDF p. 2); equation (3), printed p. 4 (PDF p. 5); Section 2.2, printed p. 10 (PDF p. 11); Section 4, printed pp. 23-24 (PDF pp. 24-25)

import Mathlib

open Matrix

namespace BLTCounting.AccuracySpace

/-- The coefficients of the square-root factorization, equation (1), PDF p. 2:
`f[k] = 4^{-k} C(2k, k)` for `k ≥ 0`, the Taylor coefficients of `(1 - z)^{-1/2}`, embedded in `ℂ`. -/
noncomputable def sqrtSeq (k : ℕ) : ℂ :=
  (((k.centralBinom : ℝ) / 4 ^ k : ℝ) : ℂ)

/-- A BLT sequence of recurrence order (at most) `d`, equation (3), PDF p. 5: there are complex
coefficients `q[1], …, q[d]` with `c[k] = -∑_{j=1}^{d} q[j] c[k-j]` for every `k ≥ d`. The first `d`
coefficients are unrestricted. No stability, pole, reality or summability condition is imposed.
Here `q j` is the source's `q[j+1]`; the natural subtraction never truncates, since `j + 1 ≤ d ≤ k`. -/
def IsBLT (d : ℕ) (c : ℕ → ℂ) : Prop :=
  ∃ q : Fin d → ℂ, ∀ k, d ≤ k → c k = -∑ j : Fin d, q j * c (k - ((j : ℕ) + 1))

/-- The unnormalized finite coefficient norm `‖a - b‖_{ℓ₂(0,n-1)} = (∑_{k=0}^{n-1} |a[k]-b[k]|²)^{1/2}`
(PDF p. 3). It is not divided by `n`. -/
noncomputable def coeffErr (n : ℕ) (a b : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.range n, ‖a k - b k‖ ^ 2)

/-- The `m × m` Hankel matrix `H_m(a)[r, s] = a[r + s]`, `0 ≤ r, s ≤ m - 1` (§2.2, PDF p. 11). -/
def hankel (m : ℕ) (a : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun r s => a ((r : ℕ) + (s : ℕ))

/-- The Hankel matrix `H_S(a) = (a[r + s])_{r, s ∈ S}`, with rows and columns indexed by the finite
set `S` (§4, PDF p. 25). -/
def hankelOn (S : Finset ℕ) (a : ℕ → ℂ) : Matrix S S ℂ :=
  Matrix.of fun r s => a ((r : ℕ) + (s : ℕ))

/-- The diagonal weight matrix `D_S = diag(r^{-1/4})_{r ∈ S}` (§4, PDF p. 25). -/
noncomputable def weightDiag (S : Finset ℕ) : Matrix S S ℂ :=
  Matrix.diagonal fun r => ((((r : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)

/-- The weighted Hankel matrix `Ĥ_S(a) = D_S H_S(a) D_S` (§4, PDF p. 25), whose entries are
`a[r + s] / (rs)^{1/4}`, equation (29). -/
noncomputable def weightedHankel (S : Finset ℕ) (a : ℕ → ℂ) : Matrix S S ℂ :=
  weightDiag S * hankelOn S a * weightDiag S

end BLTCounting.AccuracySpace


