-- Prove2me | Definitions.Def_NonstatNV_Model_clamp
-- name    : NonstatNV_Model_clamp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:32.426332+00:00
-- url     : https://prove2.me/theorems/4811338d-5ca1-4129-8758-78f28ff06197
-- title:
--   Rounding to $[\mu_{\min},\mu_{\max}]$
-- statement:
--   The **rounding** of $x\in\mathbb R$ to the parameter interval is
--
--   $$
--   \mathrm{clamp}(x)=\max\{\mu_{\min},\min\{\mu_{\max},x\}\},
--   $$
--
--   the nearest point of $[\mu_{\min},\mu_{\max}]$ to $x$ when $\mu_{\min}\le\mu_{\max}$. The paper's policies apply it to their mean estimates ("if $\hat\mu_t\notin[\mu_{\min},\mu_{\max}]$, round $\hat\mu_t$ to the nearest value in $[\mu_{\min},\mu_{\max}]$").
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Algorithm 1, p.16; Algorithm 3, p.20

import Definitions.Def_NonstatNV_Model

namespace NonstatNV

/-- Rounding to the nearest value of `[μmin, μmax]` ("if μ̂_t ∉ [μmin, μmax], round μ̂_t to the
nearest value in [μmin, μmax]", Algorithms 1 and 3 of An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, pp.16, 20):
`clamp x = max μmin (min μmax x)`. For `μmin ≤ μmax` this is the nearest point of the interval. -/
def Model.clamp (M : Model) (x : ℝ) : ℝ :=
  max M.μmin (min M.μmax x)

end NonstatNV


