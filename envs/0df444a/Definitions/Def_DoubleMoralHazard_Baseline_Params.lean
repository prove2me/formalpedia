-- Prove2me | Definitions.Def_DoubleMoralHazard_Baseline_Params
-- name    : DoubleMoralHazard_Baseline_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:43.006258+00:00
-- url     : https://prove2.me/theorems/7d59d247-1f42-490d-aa07-3c0246135514
-- title:
--   §2.1–§2.2, pp. 10–17 — parameters r, µ, p, Rᵘ, Rᵒ, c, standing condition (2.5), V̄ (2.3), β (2.4), βᵒ, tenure thresholds (2.8), (2.10)
-- statement:
--   The baseline model of Tian, Astashkina and Duenyas has a principal who hires an agent to run a business. Customers arrive through two channels: with probability $p$ an arriving customer uses the **unobservable channel** $u$ (only the agent sees it) and pays the fee $R^u$; with probability $1-p$ the customer uses the **observable channel** $o$ and pays $R^o$. By exerting effort at flow cost $c$ the agent makes customers arrive at rate $\mu$. Principal and agent discount at the common rate $r$.
--
--   The parameters satisfy $r>0$, $\mu>0$, $0<p<1$, $R^u>0$, $R^o\ge 0$, $c>0$, together with the standing condition (2.5) that inducing effort is socially worthwhile:
--   $$\bar V\ge 0\iff pR^u+(1-p)R^o\ge\beta,\qquad\text{i.e.}\qquad c\le \mu\big(pR^u+(1-p)R^o\big).$$
--
--   The derived constants are
--   $$\bar V=\frac{\mu(pR^u+(1-p)R^o)-c}{r}\ (2.3),\qquad \beta=\frac{c}{\mu}\ (2.4),\qquad \beta^o=\frac{\beta-pR^u}{1-p},$$
--   and the tenure thresholds
--   $$\bar w^1=\frac{\mu p R^u}{r}\ (2.8),\qquad \bar w^2=\bar w^3=\frac{c}{r}\ (2.10).$$
--   $\bar V$ is the total surplus of a business run forever with full effort, $\beta$ the effort cost per expected arrival, and $\bar w^i$ the level of promised utility at which the agent is tenured in Scenario $i$. The three scenarios are $c\le\mu pR^u$, $\mu pR^u<c<\mu R^u$ and $c\ge \mu R^u$.
--
--   **Formalization Note** The positivity of $r,\mu,R^u,c$, the nonnegativity of $R^o$ and $0<p<1$ are the page's implicit reading of "discount rate", "arrival rate", "fee", "costly effort" and of a genuine two-channel model; $p<1$ also keeps the division in $\beta^o$ meaningful. The standing condition (2.5) is a field of the structure, since Lemma 4 (concavity of the value functions) fails without it.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), pp. 10–17, §2.1, (2.3)–(2.5), (2.8), (2.10), Scenario 2 (p. 15)

import Mathlib

namespace DoubleMoralHazard.Baseline

/-- The primitive data of the baseline model (§2.1, pp. 10–12): the common discount rate `r`, the
customer arrival rate `µ` under effort, the probability `p` that a customer arrives to the
unobservable channel `u` (and `1 - p` to the observable channel `o`), the fees `Ru`, `Ro` of the
two channels and the flow cost `c` of effort. The last field is the standing condition (2.5),
`V̄ ≥ 0 ⟺ p Rᵘ + (1 - p) Rᵒ ≥ β`, written as `c ≤ µ (p Rᵘ + (1 - p) Rᵒ)`. -/
structure Params where
  r : ℝ
  mu : ℝ
  p : ℝ
  Ru : ℝ
  Ro : ℝ
  c : ℝ
  r_pos : 0 < r
  mu_pos : 0 < mu
  p_pos : 0 < p
  p_lt_one : p < 1
  Ru_pos : 0 < Ru
  Ro_nonneg : 0 ≤ Ro
  c_pos : 0 < c
  /-- Standing assumption (2.5), p. 12. -/
  effort_worthwhile : c ≤ mu * (p * Ru + (1 - p) * Ro)

namespace Params

variable (P : Params)

/-- `V̄ := (µ (p Rᵘ + (1 - p) Rᵒ) - c) / r`, (2.3). -/
noncomputable def Vbar : ℝ := (P.mu * (P.p * P.Ru + (1 - P.p) * P.Ro) - P.c) / P.r

/-- The adjusted effort cost `β := c / µ`, (2.4). -/
noncomputable def beta : ℝ := P.c / P.mu

/-- `βᵒ := (β - p Rᵘ) / (1 - p)`, Scenario 2, p. 15. -/
noncomputable def betaO : ℝ := (P.beta - P.p * P.Ru) / (1 - P.p)

/-- Tenure threshold of Scenario 1, `w̄¹ := µ p Rᵘ / r`, (2.8). -/
noncomputable def wbar1 : ℝ := P.mu * P.p * P.Ru / P.r

/-- Tenure threshold of Scenario 2, `w̄² := c / r`, (2.10). -/
noncomputable def wbar2 : ℝ := P.c / P.r

/-- Tenure threshold of Scenario 3, `w̄³ := w̄² = c / r`, p. 17. -/
noncomputable def wbar3 : ℝ := P.wbar2

end Params

end DoubleMoralHazard.Baseline


