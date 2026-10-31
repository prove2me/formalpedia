-- Prove2me | Definitions.Def_MissionAbort_offRate
-- name    : MissionAbort_offRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:25.208991+00:00
-- url     : https://prove2.me/theorems/ad3282c5-544c-47f3-afc0-860f8e4633a1
-- title:
--   Off-diagonal rates (5)
-- statement:
--   The off-diagonal transition rates of the surrogate chain:
--   $$
--   q_{ij}=\begin{cases}\lambda-\zeta,& j=i+1,\ i\in\mathcal X_1,\\ \zeta,& i\in\mathcal X_1,\ j=m_1+m_2+1,\\ \lambda[1-p_{i-m_1}(\lambda)],& j=i+1,\ i,j\in\mathcal X_2,\\ \lambda p_{i-m_1}(\lambda),& i\in\mathcal X_2\setminus\{m_1+m_2\},\ j=m_1+m_2+1,\\ \lambda,& i=m_1+m_2,\ j=m_1+m_2+1,\end{cases}
--   $$
--   and $q_{ij}=0$ for the other $i\ne j$. The first case includes $i=m_1$, $j=m_1+1$: the entry into $\mathcal X_2$ has rate $\lambda-\zeta$. The total rate out of every transient state is $\lambda$.
--
--   **Formalization Note** States are $0$-based, the absorbing state being `y.val = m₁ + m₂`.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, (5), p.14

import Mathlib
import Definitions.Def_MissionAbort_hazard

namespace MissionAbort

open MeasureTheory

/-- The off-diagonal rates (5) of the surrogate chain (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1, p.14):
`q_{i,i+1} = λ − ζ` and `q_{i,m₁+m₂+1} = ζ` for `i ∈ X₁` (including `i = m₁`, into `X₂`);
`q_{i,i+1} = λ[1 − p_{i−m₁}(λ)]` for `i, i + 1 ∈ X₂`; `q_{i,m₁+m₂+1} = λ p_{i−m₁}(λ)` for
`i ∈ X₂ \ {m₁ + m₂}`; `q_{m₁+m₂,m₁+m₂+1} = λ`; and `0` otherwise, in particular out of the absorbing
state.

**Formalization Note.** States are 0-based: `x`, `y` are the page's `i = x + 1`, `j = y + 1`, the
absorbing state is `y.val = m₁ + m₂`, and `x.val + 1 = m₁ + m₂` is the page's `i = m₁ + m₂`. The index
`i − m₁` of the page is `x.val - m₁ + 1`, a natural subtraction guarded by `¬ x.val < m₁`. -/
noncomputable def offRate (F : Measure ℝ) (ζ lam : ℝ) (m₁ m₂ : ℕ)
    (x y : Fin (m₁ + m₂ + 1)) : ℝ :=
  if x.val < m₁ then
    if y.val = x.val + 1 then lam - ζ
    else if y.val = m₁ + m₂ then ζ
    else 0
  else if x.val < m₁ + m₂ then
    if x.val + 1 = m₁ + m₂ then
      if y.val = m₁ + m₂ then lam else 0
    else if y.val = x.val + 1 then lam * (1 - hazard F lam (x.val - m₁ + 1))
    else if y.val = m₁ + m₂ then lam * hazard F lam (x.val - m₁ + 1)
    else 0
  else 0

end MissionAbort


