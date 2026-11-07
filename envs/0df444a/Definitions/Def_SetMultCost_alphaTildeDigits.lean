-- Prove2me | Definitions.Def_SetMultCost_alphaTildeDigits
-- name    : SetMultCost_alphaTildeDigits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:46.774195+00:00
-- url     : https://prove2.me/theorems/cb8218b5-2f2c-4f27-985c-dd2c554512a3
-- title:
--   The digits of $\tilde\alpha_{M,c}$
-- statement:
--   The number $\tilde\alpha_{M,c}$ has the continued fraction
--
--   $$\tilde\alpha_{M,c}=[0,1,2c,M,M,M^2,M^3,M^5,\dots],$$
--
--   that is $a_0=0$, $a_1=1$, $a_2=2c$ and $a_{i+3}=M^{F(i)}$. Its convergent denominators satisfy $\tilde q_0=\tilde q_1=1$ and $\tilde q_2=2c+1$. The digit $2c$ is what moves the exponent from $F(\Delta+2)$ to $F(\Delta+1)$ for $(c,\infty,c,\infty,\dots)$-restricted circuits.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), §7.2, p.22

import Mathlib
import Definitions.Def_SetMultCost_fibF

namespace SetMultCost

/-- **The digits of `α̃_{M,c}`.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), §7.2, p.22: "eαm,c = [0, 1, 2c, m, m, m², m³, · · · ]", with
"eai+1 = m^{F(i−2)}" for `i ≥ 2`. So `a₀ = 0`, `a₁ = 1`, `a₂ = 2c`, `a_{i+3} = M^{F(i)}`. -/
def alphaTildeDigits (M c : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2 * (c : ℤ)
  | i + 3 => (M : ℤ) ^ fibF i

end SetMultCost


