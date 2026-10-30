-- Prove2me | Definitions.Def_KUMultimodular_lam
-- name    : KUMultimodular_lam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:56:53.450354+00:00
-- url     : https://prove2.me/theorems/08fb29c0-be7a-4923-86fa-8c46db43ed9b
-- title:
--   Clipped logarithms and the functions $\lambda_i$
-- statement:
--   Write $\lg x = \max(1, \log_2 x)$ for the binary logarithm clipped below at $1$, and define the iterated logarithm by
--   $$\log^{(0)} x = x, \qquad \log^{(i+1)} x = \lg\bigl(\log^{(i)} x\bigr).$$
--   For $i \ge 1$ and real $x$ put
--   $$\lambda_i(x) = \bar x \cdot \log^{(1)} \bar x \cdot \log^{(2)} \bar x \cdots \log^{(i-1)} \bar x, \qquad \bar x = \max(1, x).$$
--   So $\lambda_1(x) = \bar x$, $\lambda_2(x) = \bar x \lg \bar x$, and $\lambda_i(x) \ge 1$.
--
--   This is the function $\lambda_i(x) = x \log x \log\log x \cdots \log^{(i-1)}(x)$ of Kedlaya and Umans, in which the running times of the multimodular algorithms are expressed. It satisfies $\lambda_i(x) \le x^{1+o(1)}$.
--
--   **Formalization Note** The clipping keeps every factor at least $1$: unclipped, $\lambda_2(1) = 0$, $\lambda_1(0) = 0$ and $\log^{(3)}$ of small arguments is negative, which would make the paper's bounds $0$ or negative on small inputs. `lg`, `ilog`, `lam` are the Lean names.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), §4.2, p. 13 (definition of λ_i)

import Mathlib

namespace KUMultimodular

/-- **Clipped binary logarithm** `lg x = max 1 (log₂ x)`. The paper's running-time bounds
(Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008), §4.2–4.3, pp. 13–16) use `log`; it is
read as base 2 and clipped below at `1`, so that `log 1 = 0`, `log 0` and negative iterated
logarithms cannot make a bound `0` or negative. -/
noncomputable def lg (x : ℝ) : ℝ := max 1 (Real.logb 2 x)

/-- **Iterated logarithm** `log^{(i)} x` (p. 13): `ilog 0 x = x` and `ilog (i+1) x = lg (ilog i x)`.
For `i ≥ 1` it is clipped below at `1`. -/
noncomputable def ilog : ℕ → ℝ → ℝ
  | 0, x => x
  | i + 1, x => lg (ilog i x)

/-- **The function `λ_i`** of p. 13,
`λ_i(x) = x · log x · log log x ⋯ log^{(i-1)} x`, with the argument clipped to `max 1 x` and the
logarithms clipped as in `lg`. So `lam 1 x = max 1 x`, `lam 2 x = max 1 x · lg (max 1 x)`, and
`lam i x ≥ 1` for every `i ≥ 1`. -/
noncomputable def lam (i : ℕ) (x : ℝ) : ℝ :=
  max 1 x * ∏ j ∈ Finset.Ico 1 i, ilog j (max 1 x)

end KUMultimodular


