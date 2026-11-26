-- Prove2me | Definitions.Def_LL_Decomp1555b_muPhi
-- name    : LL_Decomp1555b_muPhi
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-26T20:42:20.772233+00:00
-- url     : https://prove2.me/theorems/c247e371-1288-5133-8fd8-4201d23ebe77
-- title:
--   $\mu^2(n)/\varphi(n)$ as a real number
-- statement:
--   For a natural number $n$, muPhi n is $\mu(n)^2/\varphi(n)$, the square of the Möbius function divided by Euler's totient, as a real number. It equals $1/\varphi(n)$ for squarefree $n\ge1$ and $0$ otherwise; at $n=0$ it is $0$.

import Mathlib

namespace LL_Decomp1555b

noncomputable section

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable def muPhi (n : ℕ) : ℝ := ((μ n : ℤ) : ℝ) ^ 2 / (Nat.totient n : ℝ)

end

end LL_Decomp1555b


