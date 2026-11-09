-- Prove2me | Definitions.Def_ExplicitTensorBarrier694_Explicit_Construction
-- name    : ExplicitTensorBarrier694_Explicit_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:46.009434+00:00
-- url     : https://prove2.me/theorems/3c53085c-8caa-4583-9188-8472d2f049b7
-- title:
--   Equation (3.2) and Theorem 3.5 — integer block tensor and padded family
-- statement:
--   For integers $e\ge2$ and $m\ge e^2$, let each mode have dimension $me^2$. Identify the first-mode coordinate $(i,\alpha)$ with $ie^2+\alpha$, and the second and third coordinates $(j,u),(k,v)$ with $je+u,ke+v$. Here $i<m$, $\alpha<e^2$, $j,k<me$, and $u,v<e$. Define
--
--   $$ (T_{e,m})_{(i,\alpha),(j,u),(k,v)}=\begin{cases}2^{\alpha(j+u+v)}&k=i+j,\\0&k\ne i+j.\end{cases}$$
--
--   Equality is ordinary integer equality, with no modular wraparound. The entry function is extended by zero outside the three mode ranges. For $n\ge16$, compute $e$ as the integer fourth root of $n$, set $m=\lfloor n/e^2\rfloor$, and use these entries in dimension $n$; this is actual zero-padding on all three legs. For $n<16$ choose the zero tensor. Complexification casts each integer entry into $\mathbb C$.
--
--   This defines the explicit intended witness operationally. It assumes neither a border-rank bound nor a running-time bound. The total off-domain choices $e=0$ or $m=0$ give zero entries and are outside the Section 3 theorem hypotheses.
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), §3.1 equation (3.2) p.9; Theorem 3.5 equation (3.3) p.11 (PDF pp.9,11); zero choice below 16 for Theorem 1.1 p.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Tensors

namespace ExplicitTensorBarrier694.Explicit

/-- Equation (3.2), p.9, with mixed-radix pair coordinates and zero outside the
three me²-dimensional factors. The equality k=i+j is in ℕ, with no wraparound.
At e=0 or m=0 the support condition is false and the result is identically zero. -/
def blockEntry (e m a b c : ℕ) : ℤ :=
  if a < m * e ^ 2 ∧ b < m * e ^ 2 ∧ c < m * e ^ 2 ∧
      c / e = a / e ^ 2 + b / e then
    (2 : ℤ) ^ ((a % e ^ 2) * (b / e + b % e + c % e))
  else 0

/-- The complex tensor T_{e,m}, with all three mode dimensions me². -/
def blockTensor (e m : ℕ) : Tensor (m * e ^ 2) (m * e ^ 2) (m * e ^ 2) :=
  fun a b c => (blockEntry e m a.val b.val c.val : ℂ)

/-- floor(n^(1/4)), computed by integer fourth root, equation (3.3), p.11. -/
def fourthRoot (n : ℕ) : ℕ := Nat.nthRoot 4 n

/-- The explicit witness of Theorem 3.5, zero for n<16. Padding is coordinate
inclusion on every leg; it does not assume border-rank preservation. -/
def explicitFamily (n : ℕ) : Fin n → Fin n → Fin n → ℤ :=
  fun a b c => if 16 ≤ n then
    blockEntry (fourthRoot n) (n / (fourthRoot n) ^ 2) a.val b.val c.val
  else 0

/-- Complexification of an integer array, without changing the field for rank. -/
def complexify {n : ℕ} (T : Fin n → Fin n → Fin n → ℤ) : Tensor n n n :=
  fun a b c => (T a b c : ℂ)

end ExplicitTensorBarrier694.Explicit


