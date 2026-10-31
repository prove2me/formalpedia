-- Prove2me | Definitions.Def_CompInvestBayes_Params
-- name    : CompInvestBayes_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:54.188259+00:00
-- url     : https://prove2.me/theorems/d5afce35-0c54-436e-85aa-8004d2c9ac68
-- title:
--   Model parameters $\lambda, c_1, c_2, \mu_{i,L}, \mu_{i,H}$ and the standing assumptions
-- statement:
--   Two firms invest in a market whose favorableness $\theta\in\{0,1\}$ is unknown. The model parameters are the common discount rate $\lambda$, the unit investment costs $c_1$ (leader) and $c_2$ (follower), and the expected potential earning rates $\mu_{i,L}$, $\mu_{i,H}$ of firm $i=1,2$ after the follower's entry, in the unfavorable ($\theta=0$) and favorable ($\theta=1$) market. Before entry the leader alone serves the market, with potential earning rate
--
--   $$
--   \mu_L := \mu_{1,L}+\mu_{2,L}, \qquad \mu_H := \mu_{1,H}+\mu_{2,H}.
--   $$
--
--   The **standing assumptions** of the paper are
--
--   1. $\lambda>0$;
--   2. $0<c_i<1/\lambda$ for $i=1,2$;
--   3. $0<\mu_{i,L}<\mu_{i,H}$ for $i=1,2$.
--
--   Every theorem of the mission assumes them.
--
--   **Formalization Note** The volatility $\sigma>0$ is not a parameter field: Proposition 3 and Theorem 4 vary $\sigma$ with everything else fixed, so $\sigma$ is a separate argument wherever it appears.
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), §2, pp.7–10 (PDF 7–10): costs p.7, earning potentials and µ_L, µ_H pp.8–9, λ > 0 and c_i < 1/λ p.10

import Mathlib

namespace CompInvestBayes

/-- **Model parameters** of the competitive investment game.
Sunar, Yu, Kulkarni, *Competitive Investment with Bayesian Learning: Choice of Business Size and
Timing*, SSRN 3408260 (submitted version), §2, pp.7–10 (PDF 7–10).

Fields:
* `lam` is the common discount rate `λ` (p.10);
* `c1`, `c2` are the unit investment costs `c₁`, `c₂` of the leader and the follower (p.7);
* `mu1L`, `mu1H`, `mu2L`, `mu2H` are the expected potential earning rates `µ_{i,L}`, `µ_{i,H}` of
  firm `i` after the follower's entry, in the unfavorable (`θ = 0`) and favorable (`θ = 1`) market
  (p.8).

The volatility `σ` is deliberately **not** a field: Proposition 3 and Theorem 4 vary `σ` with every
other parameter fixed, so `σ` is a separate argument of everything that depends on it.

**Formalization Note.** The standing assumptions are the separate predicate `Params.Standing`. -/
structure Params where
  /-- discount rate `λ` -/
  lam : ℝ
  /-- leader's unit investment cost `c₁` -/
  c1 : ℝ
  /-- follower's unit investment cost `c₂` -/
  c2 : ℝ
  /-- leader's post-entry earning potential `µ_{1,L}` in the unfavorable market -/
  mu1L : ℝ
  /-- leader's post-entry earning potential `µ_{1,H}` in the favorable market -/
  mu1H : ℝ
  /-- follower's earning potential `µ_{2,L}` in the unfavorable market -/
  mu2L : ℝ
  /-- follower's earning potential `µ_{2,H}` in the favorable market -/
  mu2H : ℝ

/-- `µ_L := µ_{1,L} + µ_{2,L}`, the leader's pre-entry earning potential in the unfavorable market
(SSRN 3408260, p.9, PDF 9). -/
noncomputable def Params.muL (p : Params) : ℝ := p.mu1L + p.mu2L

/-- `µ_H := µ_{1,H} + µ_{2,H}`, the leader's pre-entry earning potential in the favorable market
(SSRN 3408260, p.9, PDF 9). -/
noncomputable def Params.muH (p : Params) : ℝ := p.mu1H + p.mu2H

/-- **Standing assumptions** of the paper (SSRN 3408260, pp.7–10, PDF 7–10):
* `λ > 0` ("The discount rate of firms is λ > 0", p.10);
* `cᵢ > 0` ("ci is a strictly positive constant", p.7) and `cᵢ < 1/λ` ("we consider a case where
  ... ci < 1/λ for i = 1, 2", p.10);
* `0 < µ_{i,L} < µ_{i,H}` ("µi,j is a positive constant that satisfies µi,H > µi,L", p.8).

The volatility `σ > 0` (p.7) is stated separately wherever `σ` appears. -/
structure Params.Standing (p : Params) : Prop where
  lam_pos : 0 < p.lam
  c1_pos : 0 < p.c1
  c2_pos : 0 < p.c2
  c1_lt : p.c1 < 1 / p.lam
  c2_lt : p.c2 < 1 / p.lam
  mu1L_pos : 0 < p.mu1L
  mu1L_lt_mu1H : p.mu1L < p.mu1H
  mu2L_pos : 0 < p.mu2L
  mu2L_lt_mu2H : p.mu2L < p.mu2H

end CompInvestBayes


