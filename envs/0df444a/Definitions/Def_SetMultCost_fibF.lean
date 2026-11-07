-- Prove2me | Definitions.Def_SetMultCost_fibF
-- name    : SetMultCost_fibF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:56.816196+00:00
-- url     : https://prove2.me/theorems/f72a777a-8449-4aeb-8077-9f231fc94b66
-- title:
--   Fibonacci numbers $F(k)$ and the exponent $R(\Delta)$
-- statement:
--   The paper's Fibonacci numbers start with $F(0)=F(1)=1$, $F(2)=2$, and the exponent parameter of the main theorem is
--
--   $$R(\Delta)=F(\Delta+1)-1,$$
--
--   so $R(1)=1$, $R(2)=2$, $R(3)=4$. A larger $\Delta$ gives a weaker bound, $d^{1/R(\Delta)}$ in the exponent.
--
--   **Formalization Note** $F(k)$ is Mathlib's `Nat.fib (k + 1)`. $R(0)=0$, and the statements assume $\Delta\ge1$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), pp.3–4; Theorem 1.2, p.4

import Mathlib

namespace SetMultCost

/-- The paper's Fibonacci numbers. Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), pp.3–4: "we use F(k) to denote the kth Fibonacci number,
starting with F(0) = F(1) = 1, F(2) = 2 and so on." -/
def fibF (k : ℕ) : ℕ := Nat.fib (k + 1)

/-- The exponent parameter of Theorem 1.2, p.4: "R(∆) = (F(∆ + 1) − 1)". `R 0 = 0`, `R 1 = 1`,
`R 2 = 2`, `R 3 = 4`. -/
def R (Δ : ℕ) : ℕ := fibF (Δ + 1) - 1

end SetMultCost


