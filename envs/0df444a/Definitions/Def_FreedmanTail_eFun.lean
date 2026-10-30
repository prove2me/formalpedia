-- Prove2me | Definitions.Def_FreedmanTail_eFun
-- name    : FreedmanTail_eFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:06:50.671337+00:00
-- url     : https://prove2.me/theorems/3d828086-25d9-4ff9-9c19-7a117afd455f
-- title:
--   The function $e(\lambda) = e^\lambda - 1 - \lambda$
-- statement:
--   For a real number $\lambda$ define
--   $$e(\lambda) = e^{\lambda} - 1 - \lambda .$$
--   This is the exponent that appears in Freedman's transformation $Q_\lambda$ and in the tail bound (4.1): $e(\lambda) \ge 0$ for every $\lambda$, and $e(\lambda)$ is the best constant in $E\{\exp(\lambda X)\} \le 1 + e(\lambda)\operatorname{Var} X$ for $X \le 1$, $E(X) \le 0$.
--
--   **Formalization Note** The paper introduces $\lambda$ as a positive number in (1.2) but uses $e(\lambda)$ for $\lambda \ge 0$ in (3.2)–(3.5); the function is defined on all of $\mathbb R$ and each theorem states its own range of $\lambda$.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (1.2) Definition (a), p. 101

import Mathlib

namespace FreedmanTail

/-- **The function `e(λ) = e^λ − 1 − λ`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(1.2) Definition (a), p. 101: "(a) e(λ) = e^λ − 1 − λ".

`eFun l = Real.exp l - 1 - l`.

**Formalization Note.** (1.2) introduces `λ` as "a positive number", but (3.2), (3.3) and (3.5)
use `e(λ)` for `λ ≥ 0`; the function is defined on all of `ℝ` (it is nonnegative everywhere),
and each theorem states its own range of `λ`. -/
noncomputable def eFun (l : ℝ) : ℝ := Real.exp l - 1 - l

end FreedmanTail


