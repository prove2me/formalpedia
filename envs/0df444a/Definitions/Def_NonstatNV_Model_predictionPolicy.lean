-- Prove2me | Definitions.Def_NonstatNV_Model_predictionPolicy
-- name    : NonstatNV_Model_predictionPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:28.941168+00:00
-- url     : https://prove2.me/theorems/cb1b08ef-b2a2-4134-a322-6bcd4f783be2
-- title:
--   The Prediction Policy (Algorithm 3)
-- statement:
--   Given predictions $a_1,\dots,a_T$, the **Prediction Policy** sets in every period $t$
--
--   $$
--   \hat\mu_t=\mathrm{clamp}(a_t),\qquad q_t=\mathrm{sel}(\hat\mu_t,b_t,h_t)\in\arg\min_{q\in Q}C_t(\hat\mu_t,q),
--   $$
--
--   that is, it behaves as if the predictions were exact means. Its orders do not depend on the observed demands.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Algorithm 3, p.20

import Definitions.Def_NonstatNV_Model_clamp

namespace NonstatNV

/-- The Prediction Policy (Algorithm 3 of An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.20): in every period `t`, `μ̂_t ← a_t`
rounded to the nearest value of `[μmin, μmax]`, and `q_t ← argmin_{q∈Q} C_t(μ̂_t, q)`, the argmin
taken by the selection `sel`. The orders do not depend on the demand path. -/
noncomputable def Model.predictionPolicy (M : Model) (sel : ℝ → ℝ → ℝ → ℝ) (b h a : ℕ → ℝ) :
    ℕ → (ℕ → ℝ) → ℝ :=
  fun t _ => sel (M.clamp (a t)) (b t) (h t)

end NonstatNV


