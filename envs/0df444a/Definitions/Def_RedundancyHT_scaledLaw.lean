-- Prove2me | Definitions.Def_RedundancyHT_scaledLaw
-- name    : RedundancyHT_scaledLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:42.052923+00:00
-- url     : https://prove2.me/theorems/98a905a7-2d08-47a9-8fe8-517810436e9a
-- title:
--   The law of the scaled job-count vector
-- statement:
--   If a state $x$ has law $p$ and $Q(x)\in\mathbb N^n$ is a vector of job counts, the scaled law is the law of $\varepsilon\,Q(x)$ on $\mathbb R^n$:
--   $$\sum_x p(x)\,\delta_{\varepsilon Q(x)}.$$
--   It is a probability measure when $p$ is a probability distribution.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Theorem 2, p.12

import Mathlib

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The law of the scaled job-count vector** `ε (Q_S)_{S∈𝒮}` when the state has law `p`
(arXiv:2005.14566v5, Theorem 2, p.12): the push-forward of `p` under `x ↦ (ε * Q x i)_i`, written as
a sum of point masses, so that the state space needs no measurable structure. -/
def scaledLaw {X : Type} {n : ℕ} (p : X → ℝ≥0∞) (Q : X → Fin n → ℕ) (ε : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.sum fun x => p x • Measure.dirac (fun i => ε * (Q x i : ℝ))

end RedundancyHT


