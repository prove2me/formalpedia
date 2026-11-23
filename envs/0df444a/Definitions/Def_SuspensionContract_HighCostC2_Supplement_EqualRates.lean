-- Prove2me | Definitions.Def_SuspensionContract_HighCostC2_Supplement_EqualRates
-- name    : SuspensionContract_HighCostC2_Supplement_EqualRates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:03:52.11202+00:00
-- url     : https://prove2.me/theorems/4c7b08ec-a31b-44e6-a788-65ef7c7b9744
-- title:
--   The equal-discount delay ODE, tangent pair and both extended value functions
-- statement:
--   For $r=\rho$ and $K\ge0$, define $\bar V_e=(\mu R-c)/r$ and $\bar K_e=\bar V_e-\underline v$. The function $V_e$ is selected from the actual delay ODE (EC.15), with $V_e(0)=\underline v$ and constant extension $\bar V_e$ above $\bar w$. No QVI or utility identity is part of its selection.
--
--   For $K<\bar K_e$, the tangent pair satisfies
--   $$V_e(\bar\theta^K)=m^K\bar\theta^K+K+\underline v,\qquad V_e'(\bar\theta^K)=m^K.$$
--   The suspension value is $m^K w+\underline v$ up to $\bar\theta^K$ and $V_e(w)-K$ thereafter, including the constant extension beyond $\bar w$. At zero cost the tangent convention is the limiting root at zero with the right derivative. This construction is independent of the degenerate main-text cutoff construction and does not assume the positive-cost standing predicate at $K=0$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, EC.1.3 pp.ec6–ec8, (EC.14)–(EC.17)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Regimes
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Limits

namespace SuspensionContract.HighCostC2.Supplement

open Set

/-- Cost-free parameter assumptions and K≥0, covering the equal-rate appendix's K=0 case. -/
def NonnegativeCostStanding (P : Params) : Prop := CostFreeStanding (toCB P) ∧ 0 ≤ P.K

/-- The constant terminal value (EC.14), for equal discount rates. -/
noncomputable def equalTerminal (P : Params) : ℝ := (P.μ * P.R - P.c) / P.r

/-- The equal-rate delay ODE (EC.15), its initial value and constant extension. The stray
printed p in the delayed argument is omitted; (25) and the rest of EC.1.3 fix the reading. -/
def EqualSolution (P : Params) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 f (Icc 0 P.wbar) ∧ f 0 = P.vlow ∧
  (∀ w ∈ Icc 0 P.wbar,
    (P.μ + P.r) * f w - P.μ * f (min (w + P.β) P.wbar) +
      P.r * (P.wbar - w) * derivWithin f (Icc 0 P.wbar) w - (P.μ * P.R - P.c) = 0) ∧
  ∀ w, P.wbar ≤ w → f w = equalTerminal P

open Classical in
/-- V_e is selected from the actual ODE, not from its QVI or utility conclusions. -/
noncomputable def equalValue (P : Params) : ℝ → ℝ :=
  if h : ∃ f, EqualSolution P f then Classical.choose h else fun _ => 0

/-- K̄_e of (EC.16). -/
noncomputable def equalThreshold (P : Params) : ℝ := equalTerminal P - P.vlow

/-- Right derivative at zero, ordinary derivative at positive utility, used in EC.1.3. -/
noncomputable def equalDeriv (P : Params) (w : ℝ) : ℝ :=
  derivWithin (equalValue P) (Ici 0) w

/-- The tangent pair above (EC.17); at K=0 its limiting root is θ=0. -/
def EqualTangent (P : Params) (θ m : ℝ) : Prop :=
  θ ∈ Icc 0 P.wbar ∧ m ∈ Icc 0 (equalDeriv P 0) ∧
    equalValue P θ = m * θ + P.K + P.vlow ∧ equalDeriv P θ = m

open Classical in
/-- The source tangent pair, junk only if no pair exists. Theorem EC.1 asserts existence
for the full branch 0≤K<K̄_e, including the zero-cost boundary. -/
noncomputable def equalTangentPair (P : Params) : ℝ × ℝ :=
  if h : ∃ p : ℝ × ℝ, EqualTangent P p.1 p.2 then Classical.choose h else (0, 0)

/-- V_∅ of (EC.17), extended constantly after wbar using the constant extension of V_e. -/
noncomputable def equalSuspension (P : Params) (w : ℝ) : ℝ :=
  if w ≤ (equalTangentPair P).1 then (equalTangentPair P).2 * w + P.vlow
  else equalValue P w - P.K

end SuspensionContract.HighCostC2.Supplement


