-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_dpValue
-- name    : EffHorizonProphet_Supplement_dpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:55:53.365356+00:00
-- url     : https://prove2.me/theorems/03024e20-96fe-49fd-947a-3a9e45a2ff9d
-- title:
--   Dynamic-programming values $V_i$
-- statement:
--   The **dynamic-programming values** of the finite-horizon problem are defined by the Bellman recursion
--   $$V_{n+1}=0,\qquad V_i=\mathbb E\big[\max\{X_i,V_{i+1}\}\big],\quad i=n,n-1,\dots,1,$$
--   where $X_i=\tilde\gamma^{s-1}Y_i$ for $i\in T_s$ and $Y_i\sim D$. $V_i$ is the optimal expected reward before observing $X_i$.
--
--   **Formalization Note** Stages are numbered from $0$: the Lean value at index $i$ is the paper's $V_{i+1}$, and it is $0$ for every $i\ge n$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), A.5, p.31; Proposition 17, p.33

import Mathlib
import Definitions.Def_EffHorizonProphet_phaseOf

open MeasureTheory

namespace EffHorizonProphet.Supplement

/-- The **dynamic-programming values** of the finite-horizon problem (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), A.5, p.31, and
Proposition 17, p.33): `V_{n+1} = 0` and `V_i = E[max{X_i, V_{i+1}}]`, the optimal expected reward
before observing `X_i`.

**Formalization Note** Stages are `0`-based: `dpValue γ L D i` is the paper's `V_{i+1}`, so
`dpValue … n = 0` (indeed `0` for every `i ≥ n`) and, for `i < n`,
`dpValue … i = ∫ max (γ^{phase(i)} y) (dpValue … (i + 1)) dD(y)`, with `X_i = γ̃^{phase(i)} Y_i`
and `Y_i ∼ D` independent of the past. -/
noncomputable def dpValue {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) (D : Measure ℝ) (i : ℕ) : ℝ :=
  if h : i < ∑ s, L s then
    ∫ y, max (γ ^ (phaseOf L ⟨i, h⟩ : ℕ) * y) (dpValue γ L D (i + 1)) ∂D
  else 0
termination_by (∑ s, L s) - i
decreasing_by omega

end EffHorizonProphet.Supplement


