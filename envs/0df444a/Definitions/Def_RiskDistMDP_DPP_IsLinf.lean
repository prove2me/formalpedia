-- Prove2me | Definitions.Def_RiskDistMDP_DPP_IsLinf
-- name    : RiskDistMDP_DPP_IsLinf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:41.672568+00:00
-- url     : https://prove2.me/theorems/65f0ed7f-99de-441e-b769-6f022dd31219
-- title:
--   Bounded measurable functions $\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$ and sequences $\ell^\infty(\mathbb N;\mathbb X,\mathcal B(\mathbb X))$
-- statement:
--   $\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$ is the set of bounded real-valued Borel functions on $\mathbb X$ (`IsLinf`). $\ell^\infty(\mathbb N;\mathbb X,\mathcal B(\mathbb X))$ is the set of sequences $\mathfrak v=(v_t)_{t\in\mathbb N}$ of Borel functions with $\|\mathfrak v\|_\infty=\sup_{t\in\mathbb N,x\in\mathbb X}|v_t(x)|<\infty$ (`IsLinfSeq`). The value functions and the uniqueness class of the Bellman equation live in these spaces.
--
--   **Formalization Note** In `IsLinfSeq` the index $0$ is unconstrained, since the paper's $\mathbb N=\{1,2,\dots\}$.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, §2, p. 4; p. 22

import Mathlib

set_option autoImplicit false

namespace RiskDistMDP.DPP

/-- `v ∈ ℓ^∞(𝕏, ℬ(𝕏))` (arXiv:2203.09612v4, §2, p.4): `v` is a bounded real-valued
`ℬ(𝕏)`-measurable function. -/
def IsLinf {𝕏 : Type*} [MeasurableSpace 𝕏] (v : 𝕏 → ℝ) : Prop :=
  Measurable v ∧ ∃ c : ℝ, ∀ x, |v x| ≤ c

/-- `𝔳 = (v_t)_{t∈ℕ} ∈ ℓ^∞(ℕ; 𝕏, ℬ(𝕏))` (arXiv:2203.09612v4, §2, p.4, and p.22): every `v_t` is
`ℬ(𝕏)`-measurable and `‖𝔳‖_∞ = sup_{t∈ℕ, x∈𝕏} |v_t(x)| < ∞`.

**Formalization Note** The paper's `ℕ = {1,2,…}`; `v 0` is unconstrained and unused. -/
def IsLinfSeq {𝕏 : Type*} [MeasurableSpace 𝕏] (v : ℕ → 𝕏 → ℝ) : Prop :=
  (∀ t, 1 ≤ t → Measurable (v t)) ∧ ∃ c : ℝ, ∀ t, 1 ≤ t → ∀ x, |v t x| ≤ c

end RiskDistMDP.DPP


