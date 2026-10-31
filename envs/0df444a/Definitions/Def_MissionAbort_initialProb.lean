-- Prove2me | Definitions.Def_MissionAbort_initialProb
-- name    : MissionAbort_initialProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:04.618997+00:00
-- url     : https://prove2.me/theorems/75fa9d3f-90fc-460c-83cd-ad41ecb7d18d
-- title:
--   Initial distribution (4)
-- statement:
--   The initial distribution of the surrogate chain:
--   $$
--   \pi_{0i}^{(\lambda)}=\begin{cases}1-G\big((m_1-1)/(\lambda-\zeta)\big),& i=1,\\ G\big((m_1+1-i)/(\lambda-\zeta)\big)-G\big((m_1-i)/(\lambda-\zeta)\big),& i=2,\dots,m_1,\\ 0,& i=m_1+1,\dots,m_1+m_2+1.\end{cases}
--   $$
--   Starting at state $i$, the time to reach $\mathcal X_2$ without killing is Erlang with shape $m_1-i+1$, so these weights reproduce the mixture $G^{(\lambda)}$.
--
--   **Formalization Note** The Lean state $x$ is the page's $i=x+1$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4.1, (4), p.13

import Mathlib

namespace MissionAbort

open MeasureTheory

/-- The initial distribution (4) of the surrogate chain (Sun, Hu & Ye, arXiv:2505.03225v1, §4.1,
p.13): `π₀₁ = 1 − G((m₁ − 1)/(λ − ζ))`, `π₀ᵢ = G((m₁ + 1 − i)/(λ − ζ)) − G((m₁ − i)/(λ − ζ))` for
`i = 2, …, m₁`, and `0` for the other states.

**Formalization Note.** States are 0-based: `x` is the page's `i = x + 1`, so `m₁ + 1 − i = m₁ − x` and
`m₁ − i = m₁ − 1 − x`. All subtractions are in `ℝ`. -/
noncomputable def initialProb (G : Measure ℝ) (ζ lam : ℝ) (m₁ m₂ : ℕ)
    (x : Fin (m₁ + m₂ + 1)) : ℝ :=
  if x.val = 0 then 1 - G.real (Set.Iic (((m₁ : ℝ) - 1) / (lam - ζ)))
  else if x.val < m₁ then
    G.real (Set.Iic (((m₁ : ℝ) - x.val) / (lam - ζ))) -
      G.real (Set.Iic (((m₁ : ℝ) - 1 - x.val) / (lam - ζ)))
  else 0

end MissionAbort


