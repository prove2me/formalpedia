-- Prove2me | Definitions.Def_BestBothWorlds_SAO_Exp3P
-- name    : BestBothWorlds_SAO_Exp3P
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:59:56.841111+00:00
-- url     : https://prove2.me/theorems/12030bdc-6999-423f-ada5-c1f9b6a48ada
-- title:
--   The Exp3.P forecaster and its tuned parameters (Bubeck & Cesa-Bianchi 2012, Fig. 3.1, Thm 3.2)
-- statement:
--   Exp3.P is the adversarial bandit algorithm that SAO switches to once it detects that the rewards are not stochastic. Bubeck and Slivkins only cite it. This file defines it as in Bubeck and Cesa-Bianchi (2012), Fig. 3.1.
--
--   Exp3.P has parameters $\eta>0$ and $\gamma,\beta\in[0,1]$. It starts from the uniform distribution $p_1$. On round $t$ it draws $I_t\sim p_t$ and observes $g_{I_t,t}$. It then forms, for each arm, the estimated gain $\tilde g_{i,t}=(g_{i,t}\mathbb 1_{\{I_t=i\}}+\beta)/p_{i,t}$ and the cumulative estimate $\widetilde G_{i,t}=\sum_{s\le t}\tilde g_{i,s}$, and it plays next
--   $$p_{i,t+1}=(1-\gamma)\frac{\exp(\eta\widetilde G_{i,t})}{\sum_{k=1}^K\exp(\eta\widetilde G_{k,t})}+\frac{\gamma}{K}.$$
--
--   For horizon $m$ and confidence $\delta$, Theorem 3.2, eq. (3.10), of the same monograph uses
--   $$\beta=\sqrt{\frac{\ln(K\delta^{-1})}{mK}},\qquad \eta=0.95\sqrt{\frac{\ln K}{mK}},\qquad \gamma=1.05\sqrt{\frac{K\ln K}{m}},$$
--   and guarantees regret at most $5.15\sqrt{mK\ln(K\delta^{-1})}$ with probability at least $1-\delta$.
--
--   **Formalization Note** Exp3.P's bias parameter is called `betaP`, to keep it apart from SAO's parameter $\beta$. The tuned $\gamma$ and $\beta$ are clipped at $1$, since Fig. 3.1 requires $\gamma,\beta\in[0,1]$. The clipping only takes effect when $5.15\sqrt{mK\ln(K\delta^{-1})}\ge m$, and in that range the regret bound holds trivially.
-- source:
--   Bubeck & Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, Foundations and Trends in ML 5(1), 2012, DOI 10.1561/2200000024, p. 29 (PDF p. 32), Figure 3.1; p. 30 (PDF p. 33), Theorem 3.2, eq. (3.10); cited as [Theorem 2.4, Bubeck 2010] in Bubeck & Slivkins, arXiv:1202.4473v1, p. 13, Algorithm 1, line 13

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction

namespace BestBothWorlds.SAO

/-- The three parameters `η`, `γ`, `β` of Exp3.P (Bubeck & Cesa-Bianchi 2012, Fig. 3.1). The bias
`β` is called `betaP` to keep it apart from SAO's parameter `β`. -/
structure Exp3PParams where
  /-- learning rate `η` -/
  eta : ℝ
  /-- mixing weight `γ` -/
  gamma : ℝ
  /-- bias `β` of the gain estimates -/
  betaP : ℝ

/-- One round of Exp3.P (Fig. 3.1). The state is `(p_t, G̃_{·,t-1})`; after observing the played
arm `a = I_t` and its reward `g = g_{I_t,t}` it computes
`g̃_{i,t} = (g_{i,t} 𝟙{I_t = i} + β) / p_{i,t}`, `G̃_{i,t} = G̃_{i,t-1} + g̃_{i,t}` and
`p_{i,t+1} = (1 - γ) exp(η G̃_{i,t}) / ∑_k exp(η G̃_{k,t}) + γ / K`. -/
noncomputable def exp3PStep (K : ℕ) (prm : Exp3PParams) (s : (Fin K → ℝ) × (Fin K → ℝ))
    (o : Fin K × ℝ) : (Fin K → ℝ) × (Fin K → ℝ) :=
  let G' : Fin K → ℝ := fun i => s.2 i + ((if o.1 = i then o.2 else 0) + prm.betaP) / s.1 i
  (fun i => (1 - prm.gamma) * Real.exp (prm.eta * G' i) / ∑ k, Real.exp (prm.eta * G' k) +
      prm.gamma / K, G')

/-- The Exp3.P state after a history: start from `p_1` uniform and `G̃ = 0`. -/
noncomputable def exp3PState (K : ℕ) (prm : Exp3PParams) (h : History K) :
    (Fin K → ℝ) × (Fin K → ℝ) :=
  h.foldl (exp3PStep K prm) (fun _ => 1 / (K : ℝ), fun _ => 0)

/-- Exp3.P with parameters `prm`, as a policy: the sampling vector after history `h`. -/
noncomputable def exp3P (K : ℕ) (prm : Exp3PParams) : Policy K :=
  fun h => (exp3PState K prm h).1

/-- The parameters of Bubeck & Cesa-Bianchi 2012, Theorem 3.2, eq. (3.10), for horizon `m` and
confidence `δ`: `β = √(ln(K δ⁻¹)/(mK))`, `η = 0.95 √(ln K/(mK))`, `γ = 1.05 √(K ln K/m)`.
`β` and `γ` are clipped at `1` (Fig. 3.1 requires `γ, β ∈ [0,1]`); the clipping only acts when the
bound (3.10) exceeds `m` and is therefore trivial. -/
noncomputable def exp3PTuned (K m : ℕ) (δ : ℝ) : Exp3PParams where
  eta := 0.95 * Real.sqrt (Real.log K / (m * K))
  gamma := min 1 (1.05 * Real.sqrt (K * Real.log K / m))
  betaP := min 1 (Real.sqrt (Real.log (K / δ) / (m * K)))

end BestBothWorlds.SAO


