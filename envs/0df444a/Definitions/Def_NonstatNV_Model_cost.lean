-- Prove2me | Definitions.Def_NonstatNV_Model_cost
-- name    : NonstatNV_Model_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:43.664983+00:00
-- url     : https://prove2.me/theorems/7c305cbe-d47f-4707-9dbc-0b54d67c51fb
-- title:
--   Expected newsvendor cost $C(\mu,b,h,q)$
-- statement:
--   For a model with demand family $\{D_\mu\}$, the **expected newsvendor cost** of ordering $q$ with underage cost $b$ and overage cost $h$ under $D_\mu$ is
--
--   $$
--   C(\mu,b,h,q)=\mathbb E_{d\sim D_\mu}\big[b(d-q)^++h(q-d)^+\big],\qquad x^+=\max\{x,0\}.
--   $$
--
--   In period $t$ the paper writes $C_t(\mu,q)=C(\mu,b_t,h_t,q)$. Every regret quantity of the mission is built from this cost.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2.1, p.10

import Definitions.Def_NonstatNV_Model

open MeasureTheory

namespace NonstatNV

/-- The expected newsvendor cost `C(μ, b, h, q) = E_{d∼D_μ}[b(d − q)⁺ + h(q − d)⁺]`
(An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, §2.1, p.10). -/
noncomputable def Model.cost (M : Model) (μ b h q : ℝ) : ℝ :=
  ∫ d, (b * max (d - q) 0 + h * max (q - d) 0) ∂(M.D μ : Measure ℝ)

end NonstatNV


