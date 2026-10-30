-- Prove2me | Definitions.Def_LL_Decomp1543a_Dioph
-- name    : LL_Decomp1543a_Dioph
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-29T15:33:39.086335+00:00
-- url     : https://prove2.me/theorems/644ecbd8-556c-4183-9b8e-e942400c5b36
-- title:
--   Rational approximation condition
-- statement:
--   For real $\alpha$, integer $a$ and natural $q$, define $\operatorname{Dioph}(\alpha,a,q)$ to mean $q\ge1$, $\gcd(a,q)=1$ and $|\alpha-a/q|\le q^{-2}$.

import Mathlib

open Real Finset ArithmeticFunction

namespace LL_Decomp1543a
def Dioph (α : ℝ) (a : ℤ) (q : ℕ) : Prop :=
  1 ≤ q ∧ Int.gcd a q = 1 ∧ |α - a / q| ≤ 1 / (q : ℝ) ^ 2
end LL_Decomp1543a


