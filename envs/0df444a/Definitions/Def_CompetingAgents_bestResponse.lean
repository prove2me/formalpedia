-- Prove2me | Definitions.Def_CompetingAgents_bestResponse
-- name    : CompetingAgents_bestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:13.631207+00:00
-- url     : https://prove2.me/theorems/2e23d8da-c804-408e-b7f5-625b2d6ecfe9
-- title:
--   Expected utility (2.2), best response $x_i^*(\beta,s)$, expected score $\omega_i(s;\beta)$, Assumption 3
-- statement:
--   An agent of type $i$ facing the selection criterion $\beta$ and the previous threshold $s$ who reports $x$ has **expected utility** (2.2)
--
--   $$\mathbb E_\epsilon[U_i(x;\beta,s)]=-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx).$$
--
--   The **best response** is $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$, and the **expected score** is $\omega_i(s;\beta)=\beta^Tx_i^*(\beta,s)$.
--
--   **Assumption 3** (p.8) says that best responses are interior: $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ for every type $i$, every $\beta\in\mathcal B=\mathbb S^{d-1}$ and every $s\in\mathbb R$.
--
--   The best response is the agent's strategic reaction to the policy. Every later object (scores, their distribution, the thresholds) is built from it.
--
--   **Formalization Note** (2.2) is taken as the definition of the expected utility. For $\|\beta\|=1$ it equals the expectation of $-c_i(x-Z_i)+\mathbb 1(\beta^T(x+\epsilon)>s)$ over $\epsilon\sim N(0,\sigma^2I_d)$; the verification file proves this. The best response is a chosen maximizer over $\mathcal X$ (the point $0$ if none existed). Under Assumption 1 a maximizer exists, and under $\sigma^2>1/(\alpha_i\sqrt{2\pi e})$ it is unique (Proposition 1), so in every statement that uses it the choice is the paper's argmax.
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, (2.2) and best response, p.6; $\omega_i$, Proposition 1, p.7; Assumption 3, p.8

import Mathlib
import Definitions.Def_CompetingAgents_noiseCDF

open scoped RealInnerProductSpace

namespace CompetingAgents

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The expected utility (2.2) of an agent of type `i` who reports `x` when the selection
criterion is `β` and the previous threshold is `s` (Sahoo, Wager, *Policy Learning with Competing
Agents*, arXiv:2204.01884v5, (2.2), p.6):
`E_ε[Uᵢ(x; β, s)] = −cᵢ(x − Zᵢ) + 1 − Φ_σ(s − βᵀx)`.

**Formalization Note.** Formula (2.2) is taken as the definition. For `‖β‖ = 1` it is the
expectation of `Uᵢ(x; β, s) = −cᵢ(x − Zᵢ) + 𝟙(βᵀ(x + ε) > s)` over `ε ∼ N(0, σ² I_d)`; every statement
of this mission takes `β` on the unit sphere. -/
noncomputable def expectedUtility (M : Model d ι) (i : ι) (β : Cov d) (s : ℝ) (x : Cov d) : ℝ :=
  -M.c i (x - M.Z i) + 1 - noiseCDF M (s - ⟪β, x⟫)

/-- The best response `x*ᵢ(β, s) = argmax_{x ∈ 𝒳} E_ε[Uᵢ(x; β, s)]` (Sahoo, Wager,
arXiv:2204.01884v5, p.6).

**Formalization Note.** The definition picks a maximizer of the expected utility over `𝒳` when one
exists. Under Assumption 1 one always exists (Proposition 1), and under the noise condition
`σ² > 1/(αᵢ√(2πe))` it is unique (Proposition 1), which is the regime of every statement that uses
`bestResponse`; so the choice is the paper's `argmax`. If no maximizer existed the value would be
the junk point `0`. -/
noncomputable def bestResponse (M : Model d ι) (i : ι) (β : Cov d) (s : ℝ) : Cov d :=
  open Classical in
  if h : ∃ x ∈ M.X, IsMaxOn (expectedUtility M i β s) M.X x then h.choose else 0

/-- The agent's expected score `ωᵢ(s; β) = βᵀ x*ᵢ(β, s)` (Sahoo, Wager, arXiv:2204.01884v5,
Proposition 1, p.7). -/
noncomputable def omega (M : Model d ι) (i : ι) (β : Cov d) (s : ℝ) : ℝ :=
  ⟪β, bestResponse M i β s⟫

/-- Assumption 3 (Sahoo, Wager, arXiv:2204.01884v5, p.8): for an agent with unobservables in the
support of `F`, `x*ᵢ(β, s) ∈ Int(𝒳)`; here for every type `i`, every `β` on the unit sphere
`𝔅 = 𝕊^{d−1}` and every threshold `s ∈ ℝ`. -/
def Assumption3 (M : Model d ι) : Prop :=
  ∀ i β s, β ∈ Metric.sphere (0 : Cov d) 1 → bestResponse M i β s ∈ interior M.X

end CompetingAgents


