-- Prove2me | Definitions.Def_NonstatNV_Model
-- name    : NonstatNV_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:01:56.910969+00:00
-- url     : https://prove2.me/theorems/34b7a9bc-4a61-4028-ace5-d04178b752ac
-- title:
--   The Nonstationary Newsvendor: model data $(\mu_{\min},\mu_{\max},b_{\max},h_{\max},Q_{\max},Q,\mathcal D)$
-- statement:
--   A **Nonstationary Newsvendor model** consists of
--
--   1. a bounded parameter interval $[\mu_{\min},\mu_{\max}]$;
--   2. bounds $b_{\max}$ and $h_{\max}$ on the per-unit underage cost $b_t\in[0,b_{\max}]$ and overage cost $h_t\in[0,h_{\max}]$;
--   3. a set $Q$ of allowed order quantities together with a bound $Q_{\max}$, with $Q\subseteq[0,Q_{\max}]$;
--   4. a family of demand distributions $\mathcal D=\{D_\mu:\mu\in[\mu_{\min},\mu_{\max}]\}$ on $\mathbb R$.
--
--   In period $t=1,\dots,T$ the decision-maker orders $q_t\in Q$, the demand $d_t\sim D_{\mu_t}$ is realized, and the cost $b_t(d_t-q_t)^++h_t(q_t-d_t)^+$ is incurred. This structure only records the data; all assumptions on it are separate predicates of the mission.
--
--   **Formalization Note** The family is a map $\mu\mapsto D_\mu$ from $\mathbb R$ to probability measures on $\mathbb R$; only its values on $[\mu_{\min},\mu_{\max}]$ are ever used. Making every $D_\mu$ a probability measure lets the joint law of independent demands be a genuine product measure.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2, pp.9–10 (Assumption 1(a), p.10)

import Mathlib

open MeasureTheory

namespace NonstatNV

/-- The data of the Nonstationary Newsvendor (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, §2, pp.9–10).

* `μmin ≤ μmax` bound the parameter interval of the demand family (Assumption 1(a), p.10);
* `bmax`, `hmax` bound the per-unit underage and overage costs `b_t ∈ [0, bmax]`, `h_t ∈ [0, hmax]` (p.9);
* `Q` is the set of allowed order quantities, a subset of `[0, Qmax]` (p.9);
* `D μ` is the demand distribution `D_μ` of the family `𝒟 = {D_μ : μ ∈ [μmin, μmax]}` (Assumption 1(a)).

**Formalization Note** The family is a function `ℝ → ProbabilityMeasure ℝ`; only its values on
`[μmin, μmax]` are ever used, and every assumption on it (mean, integrability, sub-Gaussianity) is
stated in `Model.Standing` and the other predicates, never bundled here. Making every `D μ` a
probability measure lets the product of the demand laws over all periods be a genuine product
measure (`Model.demandLaw`). -/
structure Model where
  /-- Lower end `μmin` of the parameter interval. -/
  μmin : ℝ
  /-- Upper end `μmax` of the parameter interval. -/
  μmax : ℝ
  /-- Bound `bmax` on the per-unit underage cost. -/
  bmax : ℝ
  /-- Bound `hmax` on the per-unit overage cost. -/
  hmax : ℝ
  /-- Bound `Qmax` on the order quantities. -/
  Qmax : ℝ
  /-- The set `Q` of allowed order quantities. -/
  Q : Set ℝ
  /-- The demand distribution `D_μ`. -/
  D : ℝ → ProbabilityMeasure ℝ

end NonstatNV


