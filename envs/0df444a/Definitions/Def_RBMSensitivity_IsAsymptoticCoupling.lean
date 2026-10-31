-- Prove2me | Definitions.Def_RBMSensitivity_IsAsymptoticCoupling
-- name    : RBMSensitivity_IsAsymptoticCoupling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:36.418668+00:00
-- url     : https://prove2.me/theorems/fe4b3cb1-82a6-4d9c-8d16-09bf92c2a9a9
-- title:
--   An asymptotic coupling of $m_1$ and $m_2$
-- statement:
--   For $m_1,m_2\in\mathcal M(\mathbb D(\mathbf X))$ let
--   $$\mathcal C(m_1,m_2):=\{\Upsilon\in\mathcal M(\mathbb D(\mathbf X)\times\mathbb D(\mathbf X)):\Upsilon(\cdot\times\mathbb D(\mathbf X))=m_1(\cdot),\ \Upsilon(\mathbb D(\mathbf X)\times\cdot)=m_2(\cdot)\},$$
--   and define the **diagonal at infinity** by
--   $$\mathcal D:=\{(\zeta_1,\zeta_2):\lim_{t\to\infty}\mathrm{dist}(\zeta_1(t),\zeta_2(t))=0\}.$$
--   $\Upsilon\in\mathcal C(m_1,m_2)$ is an **asymptotic coupling** of $m_1$ and $m_2$ if $\Upsilon(\mathcal D)=1$.
--
--   The joint process is degenerate, so the proof of uniqueness of its stationary distribution rests on this notion.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §8.1, p.33

import Mathlib
import Definitions.Def_RBMSensitivity_Cadlag
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `Υ ∈ C(m_1, m_2)` is an asymptotic coupling of `m_1` and `m_2`: arXiv:1907.00472v2, §8.1, p.33.

`Υ` is a probability measure on `D(S) × D(S)` with marginals `m_1`, `m_2`, and `Υ(D) = 1`, where
`D := {(ζ_1, ζ_2) : lim_{t→∞} dist(ζ_1(t), ζ_2(t)) = 0}` is the diagonal at infinity. -/
def IsAsymptoticCoupling {S : Type*} [MetricSpace S] [MeasurableSpace S]
    (m₁ m₂ : Measure (Cadlag S)) (Υ : Measure (Cadlag S × Cadlag S)) : Prop :=
  IsProbabilityMeasure Υ ∧ Υ.map Prod.fst = m₁ ∧ Υ.map Prod.snd = m₂ ∧
    Υ {p | Tendsto (fun t => dist (p.1.1 t) (p.2.1 t)) atTop (𝓝 0)} = 1

end RBMSensitivity


