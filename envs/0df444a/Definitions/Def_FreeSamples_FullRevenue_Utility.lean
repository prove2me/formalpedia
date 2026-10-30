-- Prove2me | Definitions.Def_FreeSamples_FullRevenue_Utility
-- name    : FreeSamples_FullRevenue_Utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:51:14.062995+00:00
-- url     : https://prove2.me/theorems/fca77673-59ac-4a16-9960-64165ef2caec
-- title:
--   Source utility maxima, finite optimal utility, and Bayes risk via expected regret
-- statement:
--   Let $u(a,x)$ be the Buyer's real utility from action $a\in\mathbb R$ when the real latent state is $x$. For each $x$, the pointwise maximum must be attained; write $M(x)=\max_a u(a,x)$. Under a Gaussian belief $N(m,v)$ with mean $m\in\mathbb R$ and variance $v>0$, define
--   $$L(a;m,v)=\int (M(x)-u(a,x))\,dN(m,v)(x),\qquad BR(m,v)=\inf_{a\in\mathbb R}L(a;m,v),$$
--   $$U(m,v)=\mathbb E_{N(m,v)}[M]-BR(m,v).$$
--   The loss integral takes nonnegative extended values. The well-definedness predicate requires measurable action sections and $M$, integrability of $M$ under every positive-variance Gaussian, and a finite attained minimum of $L$ under each such belief. This is the source's finite attained utility maximum, expressed by subtracting the same integrable $M$ from every candidate. In particular, an unused action may have utility $-\infty$ in expectation. No integrability of every unused action is assumed.
--
--   These definitions give the actual value of information in §§2–3. The selected clairvoyant action is used only under the existence assumption; the Bayes risk is computed from $u$, not supplied independently.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), pp.7–8, §2.1; p.14, definitions of a, U, BR

import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FreeSamples.FullRevenue

/-- A selected clairvoyant maximizing action, guarded by `WellDefined.pointwise`. -/
noncomputable def clairvoyantAction (u : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  Classical.epsilon (fun a => ∀ b, u b x ≤ u a x)

/-- The genuine pointwise maximum M(x) from §2.1, p.8. -/
noncomputable def maximumUtility (u : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  u (clairvoyantAction u x) x

/-- Nonnegative regret of action a, integrated without a finite-integral default. -/
noncomputable def actionLoss (u : ℝ → ℝ → ℝ) (m v a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (maximumUtility u x - u a x) ∂(Revenue.N m v)

/-- Minimal expected regret. It can be infinite outside `WellDefined`. -/
noncomputable def bayesRisk (u : ℝ → ℝ → ℝ) (m v : ℝ) : ℝ≥0∞ :=
  ⨅ a : ℝ, actionLoss u m v a

/-- The real Bayes risk, used only at positive variance under `WellDefined`. -/
noncomputable def BR (u : ℝ → ℝ → ℝ) (m v : ℝ) : ℝ :=
  (bayesRisk u m v).toReal

/-- Finite clairvoyant expected utility. Integrability is part of well-definedness. -/
noncomputable def fullUtility (u : ℝ → ℝ → ℝ) (m v : ℝ) : ℝ :=
  ∫ x, maximumUtility u x ∂(Revenue.N m v)

/-- The attained optimized expected utility: E[M] minus minimal expected regret. -/
noncomputable def U (u : ℝ → ℝ → ℝ) (m v : ℝ) : ℝ :=
  fullUtility u m v - BR u m v

/-- The signed expected utility of any candidate action, possibly -∞.
Under `WellDefined`, E[M] is finite and no +∞ minus +∞ occurs. -/
noncomputable def expectedActionUtility (u : ℝ → ℝ → ℝ) (m v a : ℝ) : EReal :=
  (fullUtility u m v : EReal) - (actionLoss u m v a : EReal)

/-- Precisely the maxima and finite optimized expectations declared on pp.7–8,14.
Unused actions may have infinite expected regret, hence utility -∞. -/
structure WellDefined (u : ℝ → ℝ → ℝ) : Prop where
  pointwise : ∀ x, ∃ a, ∀ b, u b x ≤ u a x
  measurable_action : ∀ a, Measurable (u a)
  measurable_maximum : Measurable (maximumUtility u)
  integrable_maximum : ∀ m v, 0 < v → Integrable (maximumUtility u) (Revenue.N m v)
  attained : ∀ m v, 0 < v → ∃ a, actionLoss u m v a < ⊤ ∧
    ∀ b, actionLoss u m v a ≤ actionLoss u m v b

end FreeSamples.FullRevenue


