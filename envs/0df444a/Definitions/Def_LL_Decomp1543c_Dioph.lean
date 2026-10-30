-- Prove2me | Definitions.Def_LL_Decomp1543c_Dioph
-- name    : LL_Decomp1543c_Dioph
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T17:29:58.465445+00:00
-- url     : https://prove2.me/theorems/c5f25916-f452-4a6a-a5a2-05c2e8f22e6c
-- title:
--   Rational approximation condition
-- statement:
--   For real $\alpha$, integer $a$ and natural $q$, $\operatorname{Dioph}(\alpha,a,q)$ means $q\ge1$, $\gcd(a,q)=1$ and $|\alpha-a/q|\le1/q^2$.

import Mathlib

namespace LL_Decomp1543c

open Real Finset ArithmeticFunction

def Dioph (α : ℝ) (a : ℤ) (q : ℕ) : Prop :=
  1 ≤ q ∧ Int.gcd a q = 1 ∧ |α - a / q| ≤ 1 / (q : ℝ) ^ 2

end LL_Decomp1543c


