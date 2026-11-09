-- Prove2me | Definitions.Def_GevreyGibbsSep_tv
-- name    : GevreyGibbsSep_tv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:39.880348+00:00
-- url     : https://prove2.me/theorems/7606c7be-a3e7-422c-b87e-674709e12400
-- title:
--   Total variation distance on $\mathbb T^d$
-- statement:
--   The **total variation distance** between distributions $p,q$ on $\mathbb T^d$ is
--   $$\mathrm{TV}(p,q)=\sup_{A\subseteq\mathbb T^d}|p(A)-q(A)| ,$$
--   the supremum over measurable sets $A$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (2), p.5

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Total variation distance `TV(p, q) = sup_{A ⊆ T^d} |p(A) − q(A)|`, arXiv:2608.24527
(sha256 d4fd40eb…), Eq. (2), p.5.

**Formalization Note** The supremum runs over measurable sets `A`; it is applied to finite
(probability) measures, for which the set of values is bounded and contains `0` (at `A = ∅`). -/
noncomputable def tv {d : ℕ} (μ ν : Measure (Torus d)) : ℝ :=
  ⨆ (A : Set (Torus d)) (_ : MeasurableSet A), |(μ A).toReal - (ν A).toReal|

end GevreyGibbsSep


