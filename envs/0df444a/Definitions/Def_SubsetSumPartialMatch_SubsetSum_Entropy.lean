-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_Entropy
-- name    : SubsetSumPartialMatch_SubsetSum_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:30.323173+00:00
-- url     : https://prove2.me/theorems/e7d5716e-9637-4ca9-8a28-7a6a45fe7907
-- title:
--   Generalized entropy $h(u,v)$ and the volume envelope $V$
-- statement:
--   For $0\le v\le u$ put
--   $$h(u,v)=u\log_2u-v\log_2v-(u-v)\log_2(u-v),\qquad 0\log_20:=0,$$
--   so that $h(t)=h(1,t)$ is the binary entropy function. For real parameters $a,b$ define
--   $$\kappa=h(b)-h(\tfrac12,2a)-h(\tfrac12,1-b-2a),$$
--   $$V_L(\mu,\theta)=\kappa+h(1-b,\mu)+h(2\mu,\theta)-4\mu,\qquad V_R(\mu,\theta)=b-\tfrac12+2a+h(a,\mu-a)+h(\mu,\theta-\mu),$$
--   on the domain $D=\{(\mu,\theta):a\le\mu\le2a,\ \mu\le\theta\le2\mu\}$, and
--   $$V(t)=\max_{(\mu,\theta)\in D}\bigl(t\,V_L(\mu,\theta)+(1-t)\,V_R(\mu,\theta)\bigr).$$
--
--   **Formalization Note** Lean's `Real.logb 2 0 = 0` gives $0\log_20=0$. The maximum is a supremum over the image of $D$; for $a>0$ the set $D$ is compact and nonempty and the objective is continuous on it, so the supremum is attained. All arguments of $h$ used in the mission satisfy $0\le v\le u$ under the hypotheses of Theorem 3.8.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 16 (definition of $h(u,v)$), p. 24 (Theorem 3.8), p. 27 (Corollary 3.9)

import Mathlib

namespace SubsetSumPartialMatch.SubsetSum

/-- `x log₂ x`, with value `0` at `x = 0` (Lean's `Real.logb 2 0 = 0`). -/
noncomputable def xlog2 (x : ℝ) : ℝ := x * Real.logb 2 x

/-- `h(u, v) = u log₂ u - v log₂ v - (u - v) log₂ (u - v)`, for `0 ≤ v ≤ u`. -/
noncomputable def hgen (u v : ℝ) : ℝ := xlog2 u - xlog2 v - xlog2 (u - v)

/-- The binary entropy function `h(t) = h(1, t)`. -/
noncomputable def binEntropy (t : ℝ) : ℝ := hgen 1 t

/-- `κ = h(b) - h(1/2, 2a) - h(1/2, 1 - b - 2a)`. -/
noncomputable def kappa (a b : ℝ) : ℝ :=
  binEntropy b - hgen (1 / 2) (2 * a) - hgen (1 / 2) (1 - b - 2 * a)

/-- `V_L(µ, θ) = κ + h(1 - b, µ) + h(2µ, θ) - 4µ`. -/
noncomputable def VL (a b μ θ : ℝ) : ℝ :=
  kappa a b + hgen (1 - b) μ + hgen (2 * μ) θ - 4 * μ

/-- `V_R(µ, θ) = b - 1/2 + 2a + h(a, µ - a) + h(µ, θ - µ)`. -/
noncomputable def VR (a b μ θ : ℝ) : ℝ :=
  b - 1 / 2 + 2 * a + hgen a (μ - a) + hgen μ (θ - μ)

/-- The domain `a ≤ µ ≤ 2a`, `µ ≤ θ ≤ 2µ`. -/
def colorDomain (a : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ 2 * a ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * p.1}

/-- `V(t) = max_{(µ,θ)} (t V_L(µ, θ) + (1 - t) V_R(µ, θ))`. For `a > 0` the domain is compact and
nonempty and the objective is continuous on it, so the supremum is the maximum. -/
noncomputable def volumeEnvelope (a b t : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => t * VL a b p.1 p.2 + (1 - t) * VR a b p.1 p.2) '' colorDomain a)

end SubsetSumPartialMatch.SubsetSum


