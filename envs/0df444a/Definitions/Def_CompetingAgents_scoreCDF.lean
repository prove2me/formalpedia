-- Prove2me | Definitions.Def_CompetingAgents_scoreCDF
-- name    : CompetingAgents_scoreCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:55.117515+00:00
-- url     : https://prove2.me/theorems/e206ba27-f94c-465e-b29c-906ce0c18ba2
-- title:
--   Score distribution $P(\beta,s)$, quantile map $q(P(\beta,s))$, iteration (3.1), $M_\lambda$ (4.2), raw score law
-- statement:
--   An agent drawn from $F$ is a pair (type $i$, noise $\epsilon$): the type has law $(w_i)$ and $\epsilon\sim N(0,\sigma^2I_d)$ independently. If the agent best responds to $\beta$ and $s$, its **score** is $\beta^TX_i(\beta,s)=\beta^T(x_i^*(\beta,s)+\epsilon)$.
--
--   1. $P(\beta,s)$ is the distribution function of this score: $P(\beta,s)(r)=F\big(\beta^TX_i(\beta,s)\le r\big)$.
--   2. The **population quantile map** is $s\mapsto q(P(\beta,s))$, the $q$-th quantile at the capacity level.
--   3. The **mean-field iteration** (3.1) is $S^t=q(P(\beta,S^{t-1}))$, $t=1,2,\dots$, from an initial $S^0\in\mathbb R$.
--   4. For $\lambda>0$,
--   $$M_\lambda=\inf_{s\in\mathbb R}\min\big\{P(\beta,s)(q(P(\beta,s))+\lambda)-q,\; q-P(\beta,s)(q(P(\beta,s))-\lambda)\big\}.\tag{4.2}$$
--   5. The **raw score law** is the distribution function of $\beta^T(Z_i+\epsilon)$ with $(Z_i,c_i,\epsilon)\sim F$.
--
--   A mean-field equilibrium threshold is a fixed point $s(\beta)=q(P(\beta,s(\beta)))$. $M_\lambda$ is the margin in the concentration bound of Lemma 3.
--
--   **Formalization Note** $P(\beta,s)$ is defined as a distribution function; formula (F.1) is Lemma 30, a theorem. The type space carries the discrete $\sigma$-algebra in every statement. The infimum in (4.2) ranges over the nonempty set $\mathbb R$ of values in $[-1,1]$, so it is never a junk value.
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, §2.1, p.5 ($P(\beta,s)$, $q$); (3.1), p.8; (4.2), Lemma 3, p.10; Lemma 32, p.33

import Mathlib
import Definitions.Def_CompetingAgents_quantile
import Definitions.Def_CompetingAgents_bestResponse

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace CompetingAgents

variable {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι]

/-- The law of the type of an agent drawn from `F`: type `i` has probability `wᵢ` (Sahoo, Wager,
*Policy Learning with Competing Agents*, arXiv:2204.01884v5, Assumption 2, p.8). -/
noncomputable def typeLaw (M : Model d ι) : Measure ι :=
  ∑ i, ENNReal.ofReal (M.w i) • Measure.dirac i

/-- The law `F` of one agent's unobservables, as a pair (type, noise) `(i, ε)`: the type has law
`typeLaw`, and `ε ∼ N(0, σ² I_d)` is independent of it (Sahoo, Wager, arXiv:2204.01884v5, p.6: "`εᵢ`
is independent from the other unobservables and has distribution `N(0, σ² I_d)`"). -/
noncomputable def agentLaw (M : Model d ι) : Measure (ι × Cov d) :=
  (typeLaw M).prod (noiseLaw M)

/-- The score `βᵀ Xᵢ(β, s) = βᵀ(x*ᵢ(β, s) + εᵢ)` of an agent `a = (i, ε)` who best responds to the
criterion `β` and the threshold `s` (Sahoo, Wager, arXiv:2204.01884v5, pp.5–6). -/
noncomputable def score (M : Model d ι) (β : Cov d) (s : ℝ) (a : ι × Cov d) : ℝ :=
  ⟪β, bestResponse M a.1 β s + a.2⟫

/-- `P(β, s)`, the distribution function of the scores `βᵀ Xᵢ(β, s)` of agents drawn from `F` who
best respond to `β` and `s` (Sahoo, Wager, arXiv:2204.01884v5, §2.1, p.5):
`P(β, s)(r) = F(βᵀ Xᵢ(β, s) ≤ r)`.

**Formalization Note.** This is the definition; formula (F.1) is Lemma 30, a theorem. -/
noncomputable def scoreCDF (M : Model d ι) (β : Cov d) (s : ℝ) (r : ℝ) : ℝ :=
  (agentLaw M).real {a | score M β s a ≤ r}

/-- The population quantile mapping `s ↦ q(P(β, s))` (Sahoo, Wager, arXiv:2204.01884v5, (3.1), p.8),
with `q` the lower quantile at the capacity level. -/
noncomputable def eqMap (M : Model d ι) (β : Cov d) (s : ℝ) : ℝ :=
  quantile M.lev (scoreCDF M β s)

/-- The mean-field fixed-point iteration (3.1), `Sᵗ = q(P(β, S^{t−1}))`, `t = 1, 2, …`, started at
`S⁰` (Sahoo, Wager, arXiv:2204.01884v5, (3.1), p.8). -/
noncomputable def meanFieldIter (M : Model d ι) (β : Cov d) (S0 : ℝ) : ℕ → ℝ
  | 0 => S0
  | t + 1 => eqMap M β (meanFieldIter M β S0 t)

/-- `M_λ` of (4.2) (Sahoo, Wager, arXiv:2204.01884v5, Lemma 3, p.10):
`M_λ = inf_{s ∈ ℝ} min{P(β,s)(q(P(β,s)) + λ) − q, q − P(β,s)(q(P(β,s)) − λ)}`.

**Formalization Note.** The infimum is over the nonempty index `ℝ` of values in `[−1, 1]`, so it is
a genuine real infimum and not a junk value. -/
noncomputable def Mlam (M : Model d ι) (β : Cov d) (lam : ℝ) : ℝ :=
  ⨅ s : ℝ, min (scoreCDF M β s (eqMap M β s + lam) - M.lev)
    (M.lev - scoreCDF M β s (eqMap M β s - lam))

/-- The distribution function of the unmodified scores `βᵀ(Zᵢ + εᵢ)` with `(Zᵢ, cᵢ, εᵢ) ∼ F`
(Sahoo, Wager, arXiv:2204.01884v5, Lemma 32, p.33: "the distribution over `βᵀ(Zᵢ + εᵢ)`"). -/
noncomputable def rawScoreCDF (M : Model d ι) (β : Cov d) (r : ℝ) : ℝ :=
  (agentLaw M).real {a | ⟪β, M.Z a.1 + a.2⟫ ≤ r}

end CompetingAgents


