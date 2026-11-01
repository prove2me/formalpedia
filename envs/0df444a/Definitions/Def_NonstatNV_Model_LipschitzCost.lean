-- Prove2me | Definitions.Def_NonstatNV_Model_LipschitzCost
-- name    : NonstatNV_Model_LipschitzCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:34.576057+00:00
-- url     : https://prove2.me/theorems/6ce63b6b-e4d6-44a5-ad91-d7928eb576a3
-- title:
--   Assumption 2: the expected cost is $\ell$-Lipschitz in $\mu$
-- statement:
--   A model satisfies **Assumption 2 with constant $\ell\ge0$** if for every $b\in[0,b_{\max}]$, $h\in[0,h_{\max}]$, $q\in Q$ and $\mu_1,\mu_2\in[\mu_{\min},\mu_{\max}]$,
--
--   $$
--   |C(\mu_1,b,h,q)-C(\mu_2,b,h,q)|\le \ell\,|\mu_1-\mu_2| .
--   $$
--
--   This translates errors in the estimate of the mean into excess cost (Lemma 1).
--
--   **Formalization Note** The paper first lets $\ell$ depend on $(b,h,q)$ and then states that a single $\ell$ works for all of them; that single $\ell$ is the constant used in Lemma 1 and in all regret bounds, and it is the one formalized here.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Assumption 2, p.10

import Definitions.Def_NonstatNV_Model_cost

open MeasureTheory

namespace NonstatNV

/-- Assumption 2 with a single Lipschitz constant `ℓ ∈ ℝ₊` (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.10): for every
`b ∈ [0, bmax]`, `h ∈ [0, hmax]`, `q ∈ Q` and `μ₁, μ₂ ∈ [μmin, μmax]`,
`|C(μ₁, b, h, q) − C(μ₂, b, h, q)| ≤ ℓ |μ₁ − μ₂|`.

**Formalization Note** The paper lets `ℓ` depend on `(b, h, q)` and then states that a single `ℓ`
works for all of them simultaneously; that single `ℓ` is the one used in Lemma 1 and every later
bound, and it is the one taken here. -/
def Model.LipschitzCost (M : Model) (ℓ : ℝ) : Prop :=
  0 ≤ ℓ ∧ ∀ b ∈ Set.Icc 0 M.bmax, ∀ h ∈ Set.Icc 0 M.hmax, ∀ q ∈ M.Q,
    ∀ μ₁ ∈ Set.Icc M.μmin M.μmax, ∀ μ₂ ∈ Set.Icc M.μmin M.μmax,
      |M.cost μ₁ b h q - M.cost μ₂ b h q| ≤ ℓ * |μ₁ - μ₂|

end NonstatNV


