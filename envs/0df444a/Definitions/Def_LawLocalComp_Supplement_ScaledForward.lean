-- Prove2me | Definitions.Def_LawLocalComp_Supplement_ScaledForward
-- name    : LawLocalComp_Supplement_ScaledForward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:05:19.342034+00:00
-- url     : https://prove2.me/theorems/9a1479d6-5018-4e80-9739-380228ca4ebd
-- title:
--   Forward scaling $\mathbb E[Y \mid X] = cX$
-- statement:
--   Let $X$, $Y$ be finite nonnegative laws and $c \in \mathbb R$. **$\mathbb E[Y \mid X] = cX$ under some coupling** means there is a coupling $\pi$ of $X$ and $Y$ with
--   $$
--   \sum_y y\,\pi(x, y) = c\,x\,P(X = x) \qquad\text{for every } x,
--   $$
--   that is, $\mathbb E_\pi[Y \mid X = x] = c\,x$ for every atom $x$ of $X$.
--
--   Theorem 6.2's forward upper bound uses $c = 1 + \varepsilon/4$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 6.2, (25), p.10

import Mathlib
import Definitions.Def_LawLocalComp_Supplement_IsCoupling

open Classical

namespace LawLocalComp

namespace Supplement

/-- **`E[Y | X] = c X` under some coupling.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 6.2, (25), p.10 ("E[Ŷ | X] = (1 + ε/4)X").

`ScaledForward c X Y`: there is a coupling `π` of `X` and `Y` such that for every input value
`x`, `∑_y y · π(x, y) = c · x · P(X = x)`, i.e. `E_π[Y | X = x] = c x` whenever `P(X = x) > 0`. -/
def ScaledForward (c : ℝ) (X Y : Law) : Prop :=
  ∃ π : ℝ × ℝ →₀ ℝ, IsCoupling π X Y ∧
    ∀ x : ℝ, ∑ z ∈ π.support with z.1 = x, z.2 * π z = c * x * X.w x

end Supplement

end LawLocalComp


