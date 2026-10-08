-- Prove2me | Definitions.Def_SelfDualLP_Complexity_BitLength
-- name    : SelfDualLP_Complexity_BitLength
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:48.627979+00:00
-- url     : https://prove2.me/theorems/f3357ca7-6bac-46b8-9afb-f5dfa3efdd73
-- title:
--   Bit length $L$ of integer LP data and of the (HLP) data
-- statement:
--   For an integer $v$ let $\operatorname{size}(v)=1+\lceil\log_2(|v|+1)\rceil$. For an integer vector $v\in\mathbb Z^p$ let $\operatorname{size}(v)=p+\sum_i\operatorname{size}(v_i)$, and for an integer matrix $A\in\mathbb Z^{m\times n}$ let $\operatorname{size}(A)=mn+\sum_{i,j}\operatorname{size}(a_{ij})$ (Schrijver's encoding size). The **bit length** of integer LP data is
--   $$
--   L(A,b,c)=\operatorname{size}(A)+\operatorname{size}(b)+\operatorname{size}(c).
--   $$
--   Under the choice (7) the (HLP) data are $A,b,c$, $\bar b=b-Ae$, $\bar c=c-e$, $\bar z=c^Te+1$ and the right-hand side $-(n+1)$; their bit length is the sum of the sizes of all of them. The definition also casts integer matrices and vectors to real ones.
--
--   The paper speaks of "integer data with bit length $L$" without fixing an encoding; any standard encoding changes $L$ by at most a constant factor, which the $O(\cdot)$ statements absorb.
--
--   **Formalization Note** `Nat.size k` is the number of binary digits of $k$, i.e. $\lceil\log_2(k+1)\rceil$. Since every entry contributes at least 1, $L\ge mn+m+n$; in particular $L\ge1$ whenever $n\ge1$.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), pp. 53–54 (data length L of the LP problem) and p. 61, Theorem 6; encoding size as in Schrijver, Theory of Linear and Integer Programming (1986), §2.1

import Mathlib

open Matrix

namespace SelfDualLP.Complexity

/-- Encoding size of an integer `v`: `1 + ⌈log₂(|v| + 1)⌉` (sign bit plus binary digits);
`Nat.size k = ⌈log₂(k + 1)⌉` is the number of binary digits of `k`. -/
def intSize (v : ℤ) : ℕ :=
  1 + Nat.size v.natAbs

/-- Encoding size of an integer vector of length `p`: `p + Σᵢ size(vᵢ)`. -/
def vecSize {p : ℕ} (v : Fin p → ℤ) : ℕ :=
  p + ∑ i, intSize (v i)

/-- Encoding size of an integer `m × n` matrix: `mn + Σᵢⱼ size(aᵢⱼ)`. -/
def matSize {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  m * n + ∑ i, ∑ j, intSize (A i j)

/-- The bit length `L` of integer LP data `(A, b, c)`: `size(A) + size(b) + size(c)`. -/
def bitLength {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ) : ℕ :=
  matSize A + vecSize b + vecSize c

/-- `b̄ = b − Ae` over the integers (8). -/
def bbarInt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Fin m → ℤ :=
  b - A *ᵥ (fun _ => 1)

/-- `c̄ = c − e` over the integers (8). -/
def cbarInt {n : ℕ} (c : Fin n → ℤ) : Fin n → ℤ :=
  c - fun _ => 1

/-- `z̄ = cᵀe + 1` over the integers (8). -/
def zbarInt {n : ℕ} (c : Fin n → ℤ) : ℤ :=
  (∑ j, c j) + 1

/-- The bit length of the data of (HLP) under (7): `A, b, c, b̄, c̄, z̄` and the right-hand
side `−(n + 1)` of row (4). -/
def hlpBitLength {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ) :
    ℕ :=
  bitLength A b c + vecSize (bbarInt A b) + vecSize (cbarInt c) + intSize (zbarInt c) +
    intSize (-((n : ℤ) + 1))

/-- The real matrix `A` with integer entries. -/
def castMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℝ :=
  A.map (Int.cast : ℤ → ℝ)

/-- The real vector with integer entries. -/
def castVec {p : ℕ} (v : Fin p → ℤ) : Fin p → ℝ :=
  fun i => (v i : ℝ)

end SelfDualLP.Complexity


