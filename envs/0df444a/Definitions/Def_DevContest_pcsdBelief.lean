-- Prove2me | Definitions.Def_DevContest_pcsdBelief
-- name    : DevContest_pcsdBelief
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:38.273371+00:00
-- url     : https://prove2.me/theorems/52f8b20e-50e5-4cbf-8078-9f86d1ea31b7
-- title:
--   The belief path $p_t$ and the disclosure probability $\phi^*_t$ of PCSD (corrected: $\bar t=+\infty$)
-- statement:
--   Fix $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. The quantities of Theorem 2 are
--   $$
--   \underline p=\begin{cases}0&\text{if }\bar R\le 7c/(3\lambda),\\ \dfrac{3\bar R-7c/\lambda}{\bar R-c/\lambda}&\text{otherwise,}\end{cases}\qquad
--   \underline t=\frac{\underline p}{\lambda(1-\underline p)},\qquad
--   \bar p=\frac{2(\bar R-2c/\lambda)}{\bar R-c/\lambda}.
--   $$
--   The **belief path** is $p_t=\lambda t/(1+\lambda t)$ for $t\le\underline t$, and for $t\ge\underline t$ it is the solution of (12) with $p_{\underline t}=\underline p$, namely
--   $$
--   p_t=\frac{B(t)\bar p-1}{B(t)-1},\qquad B(t)=\frac{1-\underline p}{\bar p-\underline p}\,e^{2\lambda(1-\bar p)(t-\underline t)}.
--   $$
--   The **disclosure probability** is $\phi^*_t=0$ for $t<\underline t$, and for $t\ge\underline t$
--   $$
--   \phi^*_t=\frac{\frac{4c/\lambda}{\bar R-c/\lambda}-3+p_t}{1-p_t}.
--   $$
--   These are the numbers the principal tunes: $\phi^*_t$ makes a first success worth exactly $c/\lambda$ after the silent phase.
--
--   **Formalization Note** The printed second branch $\phi^*_t=1$ for $t\ge\bar t$ of (11) is dropped: (12) reads $\dot p=2\lambda(1-p)(\bar p-p)$, so the path reaches $\bar p$ only as $t\to\infty$, and $\bar t=+\infty$. The closed form replaces the phrase "the unique solution"; its uniqueness is part of the goal theorem.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, Theorem 2, displays (10)–(12), p.22

import Mathlib

namespace DevContest

/-- The belief `p̲` at the end of the silent phase, display (10), Khorasani, Körpeoğlu, Krishnan,
*Dynamic Development Contests*, author manuscript, Theorem 2, p.22. -/
noncomputable def pLow (lam c Rbar : ℝ) : ℝ :=
  if Rbar ≤ 7 * c / (3 * lam) then 0 else (3 * Rbar - 7 * c / lam) / (Rbar - c / lam)

/-- The end `t̲ = p̲ / (λ (1 - p̲))` of the silent phase, Theorem 2, p.22. -/
noncomputable def tLow (lam c Rbar : ℝ) : ℝ :=
  pLow lam c Rbar / (lam * (1 - pLow lam c Rbar))

/-- The belief `p̄ = 2 (R̄ - 2c/λ) / (R̄ - c/λ)`, Theorem 2, p.22. -/
noncomputable def pBar (lam c Rbar : ℝ) : ℝ :=
  2 * (Rbar - 2 * c / lam) / (Rbar - c / lam)

/-- The factor `B(t) = ((1 - p̲) / (p̄ - p̲)) exp(2 λ (1 - p̄) (t - t̲))` of the closed form of the
belief path. -/
noncomputable def beliefFactor (lam c Rbar t : ℝ) : ℝ :=
  (1 - pLow lam c Rbar) / (pBar lam c Rbar - pLow lam c Rbar) *
    Real.exp (2 * lam * (1 - pBar lam c Rbar) * (t - tLow lam c Rbar))

/-- The belief path `p_t` under PCSD, Theorem 2, p.22: `p_t = λt / (1 + λt)` in the silent phase
`t ≤ t̲`, and for `t ≥ t̲` the solution of display (12) with `p_t̲ = p̲`, in the closed form
`p_t = (B(t) p̄ - 1) / (B(t) - 1)`.

**Formalization Note.** Correction of the printed theorem: `p̄` is a rest point of (12), since
(12) reads `ṗ = 2λ(1-p)(p̄-p)`, so the solution reaches `p̄` only as `t → ∞` and the printed `t̄` is
`+∞`. Only `t ≥ 0` is meaningful. -/
noncomputable def pcsdBelief (lam c Rbar t : ℝ) : ℝ :=
  if t ≤ tLow lam c Rbar then lam * t / (1 + lam * t)
  else (beliefFactor lam c Rbar t * pBar lam c Rbar - 1) / (beliefFactor lam c Rbar t - 1)

/-- The disclosure probability `φ*_t` of PCSD, displays (10)–(11), Theorem 2, p.22: `0` before `t̲`
and `((4c/λ)/(R̄ - c/λ) - 3 + p_t) / (1 - p_t)` from `t̲` on.

**Formalization Note.** Correction of the printed theorem: the printed branch `φ*_t = 1` for
`t ≥ t̄` is empty, because `t̄ = +∞` (see `pcsdBelief`). -/
noncomputable def phiStar (lam c Rbar t : ℝ) : ℝ :=
  if t < tLow lam c Rbar then 0
  else ((4 * c / lam) / (Rbar - c / lam) - 3 + pcsdBelief lam c Rbar t) /
    (1 - pcsdBelief lam c Rbar t)

end DevContest


