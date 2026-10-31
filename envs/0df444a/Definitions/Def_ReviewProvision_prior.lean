-- Prove2me | Definitions.Def_ReviewProvision_prior
-- name    : ReviewProvision_prior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:51:22.666668+00:00
-- url     : https://prove2.me/theorems/3f0fbad3-bb54-4b62-817c-a9973fcc8a14
-- title:
--   The common Gaussian prior of quality, preferences and rating noise
-- statement:
--   A sample point is a triple $(q,t,\varepsilon)$ of a quality $q\in\mathbb R$, cluster preferences $t\in\mathbb R^N$ and rating noises $\varepsilon\in\mathbb R^N$. The common prior is the product measure under which
--
--   $$
--   q\sim N\!\left(1,\tfrac1\tau\right),\qquad t_1,\dots,t_N\sim N\!\left(0,\tfrac1\eta\right),\qquad \varepsilon_1,\dots,\varepsilon_N\sim N(0,1),
--   $$
--
--   all mutually independent. It is the probability space of the whole mission: quality and preferences are the primitives of §3.1, and the noises carry the conditional independence of the average ratings given $(q,t)$.
--
--   **Formalization Note** The canonical product space makes the profit a function of the parameters and of the sales vector alone. `gaussianReal` takes its variance in $\mathbb R_{\ge0}$.
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), §3.1, pp.9–10; §3.3, p.11; Appendix A, p.34

import Mathlib
import Definitions.Def_ReviewProvision_Params

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ReviewProvision

/-- The **sample space** of the model: a realization `(q, t, ε)` of the quality `q`, of the cluster
preferences `t = (t_1, …, t_N)` and of the standardized rating noises `ε = (ε_1, …, ε_N)`. The
clusters `C = {1, …, N}` of p.10 are `Fin N`. -/
abbrev Sample (N : ℕ) : Type := ℝ × (Fin N → ℝ) × (Fin N → ℝ)

/-- The quality `q` of a sample point. -/
def quality {N : ℕ} (ω : Sample N) : ℝ := ω.1

/-- The preference `t_n` of cluster `n` at a sample point. -/
def taste {N : ℕ} (ω : Sample N) (n : Fin N) : ℝ := ω.2.1 n

/-- The standardized rating noise `ε_n` of cluster `n` at a sample point. -/
def noise {N : ℕ} (ω : Sample N) (n : Fin N) : ℝ := ω.2.2 n

/-- **The common prior**. SSRN 3403322 (manuscript of 2021-05-24), §3.1, pp.9–10 (PDF 9–10):
`q ∼ N(1, 1/τ)`; `t_1, …, t_N ∼ N(0, 1/η)` i.i.d. and independent of `q`; and §3.3, p.11, with the
conditional independence stated on p.34 ("r_n|(q,~t), n ∈ C are all Normally distributed and
independent"): noises `ε_1, …, ε_N ∼ N(0, 1)`, independent of each other and of `(q, t)`.

**Formalization Note.** The canonical product space and the product measure, so that the profit is a
function of the parameters and of the sales vector alone, as in the paper. `gaussianReal` takes its
variance in `ℝ≥0`; `1/τ` and `1/η` are positive, so `Real.toNNReal` loses nothing. -/
noncomputable def prior (p : Params) (N : ℕ) : Measure (Sample N) :=
  (gaussianReal 1 (1 / p.tau).toNNReal).prod
    ((Measure.pi fun _ : Fin N => gaussianReal 0 (1 / p.eta).toNNReal).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1))

instance (p : Params) (N : ℕ) : IsProbabilityMeasure (prior p N) := by
  unfold prior
  infer_instance

end ReviewProvision


