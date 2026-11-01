-- Prove2me | Definitions.Def_NonstatNV_Model_IsInstance
-- name    : NonstatNV_Model_IsInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:36.736679+00:00
-- url     : https://prove2.me/theorems/bab135aa-bcdd-4b2a-bdc9-0418f98aaac4
-- title:
--   Instance of horizon $T$: means in $[\mu_{\min},\mu_{\max}]$, costs in their boxes
-- statement:
--   An **instance** of horizon $T$ is a triple of sequences $(\mu_t,b_t,h_t)$ such that for every period $t\in\{1,\dots,T\}$
--
--   $$
--   \mu_t\in[\mu_{\min},\mu_{\max}],\qquad b_t\in[0,b_{\max}],\qquad h_t\in[0,h_{\max}] .
--   $$
--
--   The first condition is $D_t\in\mathcal D$; the class $\mathcal D(v)$ adds $V_\mu\le T^v$. Values outside $\{1,\dots,T\}$ are irrelevant.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2, p.9; $\mathcal D(v)$, p.13

import Definitions.Def_NonstatNV_Model

namespace NonstatNV

/-- An instance of horizon `T` (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, §2, pp.9–13): for every period `t ∈ {1, …, T}`, the mean
`μ_t` lies in `[μmin, μmax]` (`D_t ∈ 𝒟`), and the costs satisfy `b_t ∈ [0, bmax]`,
`h_t ∈ [0, hmax]`. Values at `t = 0` and `t > T` are unconstrained and irrelevant. -/
def Model.IsInstance (M : Model) (T : ℕ) (μ b h : ℕ → ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, μ t ∈ Set.Icc M.μmin M.μmax ∧ b t ∈ Set.Icc 0 M.bmax ∧
    h t ∈ Set.Icc 0 M.hmax

end NonstatNV


