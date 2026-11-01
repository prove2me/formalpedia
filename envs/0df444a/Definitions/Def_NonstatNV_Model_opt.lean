-- Prove2me | Definitions.Def_NonstatNV_Model_opt
-- name    : NonstatNV_Model_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:36.63729+00:00
-- url     : https://prove2.me/theorems/7678779a-25b0-434a-ae21-34098233f028
-- title:
--   Clairvoyant cost $\min_{q\in Q}C(\mu,b,h,q)$
-- statement:
--   The **clairvoyant cost** at mean $\mu$ with costs $b,h$ is
--
--   $$
--   \mathrm{opt}(\mu,b,h)=\inf_{q\in Q}C(\mu,b,h,q),
--   $$
--
--   which equals $C_t(\mu_t,q_t^*)$ for any $q_t^*\in\arg\min_{q\in Q}C_t(\mu_t,q)$ as in (2.1). It is the benchmark of the regret: a clairvoyant who knows the demand distribution of the period.
--
--   **Formalization Note** For $b,h\ge0$ the cost is nonnegative, so this is the true infimum over the nonempty set $Q$, and it is the minimum whenever a minimizer exists.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, (2.1), p.11; §2.3, p.14

import Definitions.Def_NonstatNV_Model_cost

namespace NonstatNV

/-- The clairvoyant cost `C_t(μ_t, q*_t)` with `q*_t ∈ argmin_{q∈Q} C_t(μ_t, q)` ((2.1), p.11, of
An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4): the infimum of `C(μ, b, h, ·)` over `Q`.

**Formalization Note** For `b, h ≥ 0` the cost is nonnegative, so the infimum over the nonempty set
`Q` is the true infimum; when a minimizer exists (e.g. under `Model.IsArgminSelection`) it equals
`C(μ, b, h, q*)` for every minimizer `q*`. -/
noncomputable def Model.opt (M : Model) (μ b h : ℝ) : ℝ :=
  ⨅ q : M.Q, M.cost μ b h q

end NonstatNV


