-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_SingleAgent
-- name    : TransparencyTeamContracts_Submodular_Supplement_SingleAgent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:13:53.319434+00:00
-- url     : https://prove2.me/theorems/c902bdc1-da44-4b22-84b5-ef9dff427e91
-- title:
--   Single-agent outcome probabilities, cutoff, ratio and complementarity witness
-- statement:
--   For one agent, $f(S)=p_0$ on the empty team and $p_1$ otherwise; its value is the base operational contract optimum $V(f,c)$. The cutoff is
--   $$\ell_c(p_0)=p_0+\frac{c+\sqrt{c^2+4cp_0}}2.$$
--   The two-point full and no-information values are computed from the actual stateless value, with states $(0,1)$ and $(p_0,\ell_c(p_0))$ and mass $q$ on the first state.
--
--   For $q=kc$ and $p_0=cX(X-1)$, the module defines $m_0=c(1-kc)X(X-1)$, $m_1=c(k+X^2-kX^2c)$, the exact effort-branch ratio in equation (21), and its limit $R_0(k,X)=1+k(X-1)/[(k+X)(k+X^2-X)]$. Feasibility uses $kc\le1$, so $k=0$ imposes no artificial division-by-zero constraint; ratios require positive full-information denominator.
--
--   The module also records the exact normalized two-agent, two-state data from Theorem 5.1: costs $(1/4,1/2)$; state technologies $(0,1/4,1/4,1)$ and $(0,5/42,0,5/6)$ in empty, singleton-0, singleton-1, full-team order; and contract $(6/19,28/41)$.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), §2 and Appendices A–B; printed pp. 5–8, 23–32 (PDF pp. 7–10, 25–34); Theorem 5.1, printed p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information

open Finset
open scoped Classical

namespace TransparencyTeamContracts.Submodular.Supplement

/-- A one-agent technology specified by its two outcome probabilities. -/
noncomputable def singleReward (p₀ p₁ : ℝ) (S : Finset (Fin 1)) : ℝ :=
  if S = ∅ then p₀ else p₁

/-- This is the base operational contract optimum, not an assumed payoff formula. -/
noncomputable def singleV (c p₀ p₁ : ℝ) : ℝ := V (singleReward p₀ p₁) (fun _ => c)
noncomputable def cutoff (c p₀ : ℝ) : ℝ :=
  p₀ + (c + Real.sqrt (c ^ 2 + 4 * c * p₀)) / 2

/-- The two actual pure-contract benchmarks for the constructed two-point prior. -/
noncomputable def twoPointFull (c p₀ q : ℝ) : ℝ :=
  q * singleV c 0 1 + (1 - q) * singleV c p₀ (cutoff c p₀)
noncomputable def twoPointNo (c p₀ q : ℝ) : ℝ :=
  singleV c ((1 - q) * p₀) (q + (1 - q) * cutoff c p₀)

noncomputable def mean0 (c k X : ℝ) : ℝ := c * (1 - k * c) * X * (X - 1)
noncomputable def mean1 (c k X : ℝ) : ℝ := c * (k + X ^ 2 - k * X ^ 2 * c)
noncomputable def fullDenominator (c k X : ℝ) : ℝ :=
  c * (k * (1 - c) + (1 - k * c) * X * (X - 1))

/-- Positive-denominator feasible domain. k*c ≤ 1 implements 1/k=+∞ at k=0. -/
def RatioDomain (k X c : ℝ) : Prop :=
  0 < c ∧ k * c ≤ 1 ∧ c * X ^ 2 ≤ 1 ∧ 0 < fullDenominator c k X

/-- Exactly equation (21), the effort branch, without an extraneous max. -/
noncomputable def R (c k X : ℝ) : ℝ :=
  mean1 c k X * (1 - c / (mean1 c k X - mean0 c k X)) / fullDenominator c k X
noncomputable def R0 (k X : ℝ) : ℝ :=
  1 + k * (X - 1) / ((k + X) * (k + X ^ 2 - X))

/-- The normalized two-agent/two-state witness in the proof of Theorem 5.1. -/
noncomputable def complementReward (ω : Fin 2) (S : Finset (Fin 2)) : ℝ :=
  if S = ∅ then 0 else if S = univ then
    if ω = 0 then 1 else 5 / 6
  else if ω = 0 then 1 / 4 else if 0 ∈ S then 5 / 42 else 0
noncomputable def complementCost (i : Fin 2) : ℝ := if i = 0 then 1 / 4 else 1 / 2
noncomputable def complementContract (i : Fin 2) : ℝ := if i = 0 then 6 / 19 else 28 / 41

end TransparencyTeamContracts.Submodular.Supplement


