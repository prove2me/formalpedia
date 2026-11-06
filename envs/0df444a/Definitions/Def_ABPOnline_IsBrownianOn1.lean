-- Prove2me | Definitions.Def_ABPOnline_IsBrownianOn1
-- name    : ABPOnline_IsBrownianOn1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:39.775535+00:00
-- url     : https://prove2.me/theorems/1817754a-49cf-4700-88ca-421bf73486bc
-- title:
--   Standard Brownian motion on $[0,1]$
-- statement:
--   A real process $B=(B_t)$ is a **standard Brownian motion on $[0,1]$** if for all times $0\le t_1<\dots<t_n\le1$ the vector $(B_{t_1},\dots,B_{t_n})$ is centred Gaussian with covariance $\mathbb E[B_sB_t]=\min(s,t)$, and almost every path $t\mapsto B_t$ is continuous on $[0,1]$.
--
--   This is the process $B=(B_t)_{0\le t\le1}$ of the Brownian control problem.
--
--   **Formalization Note** The process is indexed by $t\ge0$, and only its values on $[0,1]$ are constrained. Mathlib's Brownian motion on $[0,\infty)$ (`IsBrownianReal`) satisfies this property.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), §2.2, p.6 (PDF p.7)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ABPOnline

/-- `B = (B_t)_{0≤t≤1}` is a **standard Brownian motion on `[0,1]`** (arXiv:2609.02124, §2.2,
printed p.6, PDF p.7): for every finite set of times in `[0,1]` the joint law of `B` is the
centred Gaussian law with covariance `min(s,t)` (Mathlib's `BrownianReal.projectiveFamily`), and
almost every path is continuous on `[0,1]`.

**Formalization Note** The process is indexed by `ℝ≥0` and only its values on `[0,1]` are
constrained; Mathlib's `IsBrownianReal` (a Brownian motion on `[0,∞)`) implies this property. -/
def IsBrownianOn1 {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  (∀ I : Finset ℝ≥0, (∀ t ∈ I, t ≤ 1) →
    HasLaw (fun ω => I.restrict (B · ω)) (BrownianReal.projectiveFamily I) P) ∧
  ∀ᵐ ω ∂P, ContinuousOn (fun t => B t ω) (Set.Iic 1)

end ABPOnline


