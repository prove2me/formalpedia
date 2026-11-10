-- Prove2me | Definitions.Def_RevRedSAT_lam
-- name    : RevRedSAT_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:32.697469+00:00
-- url     : https://prove2.me/theorems/57c19e0b-df9f-4a11-b6a6-7360f82fd978
-- title:
--   The functions $\lambda(t)=\log_2(t+2)$, $\eta(t)=\log_2\log_2(t+4)$ and the rate exponents
-- statement:
--   For a natural number $t$ put
--
--   $$\lambda(t)=\log_2(t+2),\qquad \eta(t)=\log_2\bigl(\log_2(t+4)\bigr).$$
--
--   "The additive shifts ensure that both functions are positive for all $t\ge0$ without changing their asymptotic growth rates" (§3, p.27); in fact $\lambda(t)\ge1$ and $\eta(t)\ge1$.
--
--   The module also fixes the shape of the running-time bounds of the mission:
--
--   1. $\mathrm{expBound}(x,L,c)=\lfloor 2^{x}L^{c}\rfloor$, an exponential factor times a polynomial factor in the input length $L$, rounded down to a number of steps;
--   2. the Vertex Cover rate $C\,k\,\eta(k)/\sqrt{\lambda(k)}$, the exponent of $V(k)=2^{O(k\eta(k)/\sqrt{\lambda(k)})}$ (p.8);
--   3. the $d$-Hitting Set rate $C\,k\,\eta(k)^2/\sqrt{\lambda(k)}$, the exponent of $C(k)=2^{O(k\eta(k)^2/\sqrt{\lambda(k)})}$ (p.8).
--
--   **Formalization Note** Logarithms are `Real.logb 2`; the constant $C$ of a rate is chosen together with the machine.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27 (λ, η); §1.2 rate notation, p.8 (V(k), C(k))

import Mathlib

set_option autoImplicit false

namespace RevRedSAT

/-- **The function `λ(t) = log₂(t + 2)`.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27: "write
λ(t) := log2(t + 2) and η(t) := log2(log2(t + 4)). The additive shifts ensure that both functions
are positive for all t ≥ 0 without changing their asymptotic growth rates." -/
noncomputable def lam (t : ℕ) : ℝ := Real.logb 2 ((t : ℝ) + 2)

/-- **The function `η(t) = log₂(log₂(t + 4))`** (§3, p.27). For every `t ≥ 0`, `λ(t) ≥ 1` and
`η(t) ≥ 1`, so the rates below never divide by zero. -/
noncomputable def eta (t : ℕ) : ℝ := Real.logb 2 (Real.logb 2 ((t : ℝ) + 4))

/-- The time bound `⌊2^x · L^c⌋` (a real exponential factor times a polynomial factor in the input
length `L`, rounded down to a number of steps). -/
noncomputable def expBound (x : ℝ) (L c : ℕ) : ℕ := ⌊(2 : ℝ) ^ x * (L : ℝ) ^ c⌋₊

/-- The Vertex Cover rate of Theorem 1.1 with constant `C`: `C · k η(k) / √λ(k)`, i.e. the exponent
of `V(k) = 2^{O(kη(k)/√λ(k))}` (p.8). -/
noncomputable def vcRate (C : ℝ) (k : ℕ) : ℝ := C * k * eta k / Real.sqrt (lam k)

/-- The `d`-Hitting Set rate of Theorem 1.1 with constant `C`: `C · k η(k)² / √λ(k)`, i.e. the
exponent of `C(k) = 2^{O(kη(k)²/√λ(k))}` (p.8). -/
noncomputable def hsRate (C : ℝ) (k : ℕ) : ℝ := C * k * eta k ^ 2 / Real.sqrt (lam k)

end RevRedSAT


