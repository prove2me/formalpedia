-- Prove2me | Definitions.Def_BorelRobustMDP_histOperators
-- name    : BorelRobustMDP_histOperators
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:26.345271+00:00
-- url     : https://prove2.me/theorems/c1540196-2b22-4673-9f8b-8bf18fde58ae
-- title:
--   The operators $\mathcal T_{n\pi_n\gamma_n}$ and $\mathcal T_{n\pi_n}$ on history-dependent functions
-- statement:
--   For $v$ on histories of length $n+1$:
--
--   $$\mathcal T_{n\pi_n\gamma_n}v(h_n)=\iint c_n(x_n,a_n,T_n(x_n,a_n,z_{n+1}))+v(h_n,a_n,T_n(x_n,a_n,z_{n+1}))\,\gamma_n(dz_{n+1}\mid h_n,a_n)\,\pi_n(da_n\mid h_n),$$
--
--   $$\mathcal T_{n\pi_n}v(h_n)=\int\sup_{Q\in\mathcal Q_{n+1}}\int c_n(x_n,a_n,T_n(x_n,a_n,z_{n+1}))+v(h_n,a_n,T_n(x_n,a_n,z_{n+1}))\,Q(dz_{n+1})\,\pi_n(da_n\mid h_n).$$
--
--   A **maximizing decision rule of nature** for $v$ attains the inner supremum at every feasible history and every $a\in D_n(x_n)$.
--
--   These operators express the cost iteration of Proposition 3.5 and Theorem 3.6.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Definition 3.4, p.7, and Theorem 3.6 b), p.8

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_Policy
import Definitions.Def_BorelRobustMDP_NaturePolicy
import Definitions.Def_BorelRobustMDP_Feasible

open MeasureTheory
open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- The inner integrand of Definition 3.4 (Bäuerle & Glauner, arXiv:2007.13103v1, p.7):
`∫ c_n(x_n, a, T_n(x_n, a, z)) + v(h_n, a, T_n(x_n, a, z)) Q(dz)`. -/
noncomputable def histStage (R : RobustModel E A Z N) (n : ℕ) (v : Hist E A (n + 1) → ℝ)
    (h : Hist E A n) (a : A) (Q : Measure Z) : ℝ :=
  ∫ z, R.c n (histState n h, a) (R.T n (histState n h, a) z) +
    v ((h, a, R.T n (histState n h, a) z) : Hist E A (n + 1)) ∂Q

/-- The operator `𝒯_{nπ_nγ_n}` of Definition 3.4 (Bäuerle & Glauner, arXiv:2007.13103v1, p.7). -/
noncomputable def histTpg (R : RobustModel E A Z N) (π : Policy R.toDecisionModel)
    (γ : NaturePolicy R) (n : ℕ) (v : Hist E A (n + 1) → ℝ) (h : Hist E A n) : ℝ :=
  ∫ a, histStage R n v h a (γ.act n (h, a)) ∂(π.act n h)

/-- The operator `𝒯_{nπ_n}` of Definition 3.4 (Bäuerle & Glauner, arXiv:2007.13103v1, p.7), with the
supremum over `𝒬_{n+1}` inside the integral over the action. -/
noncomputable def histTp (R : RobustModel E A Z N) (π : Policy R.toDecisionModel) (n : ℕ)
    (v : Hist E A (n + 1) → ℝ) (h : Hist E A n) : ℝ :=
  ∫ a, (⨆ Q : R.Amb (n + 1), histStage R n v h a Q.measure) ∂(π.act n h)

/-- A maximizing decision rule of nature for `v` (Bäuerle & Glauner, arXiv:2007.13103v1, Theorem 3.6 b),
p.8): at every feasible history `h_n` and action `a ∈ D_n(x_n)`, the rule attains the supremum of the
inner integral of `𝒯_{nπ_n} v`. -/
def IsHistMaximizer (R : RobustModel E A Z N) (n : ℕ) (v : Hist E A (n + 1) → ℝ)
    (g : Hist E A n × A → R.Amb (n + 1)) : Prop :=
  ∀ h, R.Feasible n h → ∀ a ∈ R.sec n (histState n h),
    histStage R n v h a (g (h, a)).measure = ⨆ Q : R.Amb (n + 1), histStage R n v h a Q.measure

end BorelRobustMDP


