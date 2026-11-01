-- Prove2me | Definitions.Def_NonstatNV_Model_IsArgminSelection
-- name    : NonstatNV_Model_IsArgminSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:40.234096+00:00
-- url     : https://prove2.me/theorems/1090a2ba-6359-475c-ad45-f9296249702a
-- title:
--   Measurable argmin selection $\mathrm{sel}(\hat\mu,b,h)\in\arg\min_{q\in Q}C(\hat\mu,b,h,q)$
-- statement:
--   An **argmin selection** is a function $\mathrm{sel}(\hat\mu,b,h)$ such that
--
--   1. for every $\hat\mu\in[\mu_{\min},\mu_{\max}]$, $b\in[0,b_{\max}]$, $h\in[0,h_{\max}]$, the value $\mathrm{sel}(\hat\mu,b,h)$ lies in $Q$ and minimizes $C(\hat\mu,b,h,\cdot)$ over $Q$;
--   2. for fixed $b,h$, the map $\hat\mu\mapsto\mathrm{sel}(\hat\mu,b,h)$ is measurable.
--
--   It is the tie-breaking rule behind the step "$q_t\leftarrow\arg\min_{q\in Q}C_t(\hat\mu_t,q)$" of the paper's policies. Its existence presupposes that the minimum is attained.
--
--   **Formalization Note** Measurability makes the orders random variables, so that expected costs are genuine expectations. Results are stated for every such selection.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, (2.1), p.11; Algorithms 1, 3, 4, pp.16, 20, 23

import Definitions.Def_NonstatNV_Model_cost

namespace NonstatNV

/-- A selection `sel(μ̂, b, h) ∈ argmin_{q∈Q} C(μ̂, b, h, q)`, the tie-breaking rule behind
"`q_t ← argmin_{q∈Q} C_t(μ̂_t, q)`" in Algorithms 1, 3 and 4 of An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4 (pp.16, 20, 23):
for every `μ̂ ∈ [μmin, μmax]`, `b ∈ [0, bmax]`, `h ∈ [0, hmax]`, the value `sel μ̂ b h` lies in `Q`
and minimizes `C(μ̂, b, h, ·)` over `Q`; and for fixed `b, h` the map `μ̂ ↦ sel μ̂ b h` is measurable.

**Formalization Note** Measurability makes the orders of the policies random variables, so their
expected costs are genuine expectations. Values of `sel` off the parameter box are never used. -/
def Model.IsArgminSelection (M : Model) (sel : ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ μ ∈ Set.Icc M.μmin M.μmax, ∀ b ∈ Set.Icc 0 M.bmax, ∀ h ∈ Set.Icc 0 M.hmax,
      sel μ b h ∈ M.Q ∧ ∀ q ∈ M.Q, M.cost μ b h (sel μ b h) ≤ M.cost μ b h q) ∧
    ∀ b h : ℝ, Measurable (fun μ : ℝ => sel μ b h)

end NonstatNV


