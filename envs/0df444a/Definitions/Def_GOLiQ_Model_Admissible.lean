-- Prove2me | Definitions.Def_GOLiQ_Model_Admissible
-- name    : GOLiQ_Model_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:02.403061+00:00
-- url     : https://prove2.me/theorems/d0afaa92-1098-42c0-8f99-38e819562f82
-- title:
--   Admissible policy: $x_k\in\mathcal B$ and $\mathcal F_k$-measurable
-- statement:
--   A policy $(x_k)_{k\ge1}$, $x_k=(\mu_k,p_k)$, is **admissible** if every $x_k$ lies in $\mathcal B$ and is $\mathcal F_k$-measurable, i.e. determined by the first $k-1$ iterations. In particular $x_1$ is deterministic.
--
--   The regret analysis of Theorem 1 applies to every admissible policy.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, §3.2, pp.12–13; p.68

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Primitives_info

open MeasureTheory

namespace GOLiQ

/-- **An admissible policy** (Chen, Liu, Hong, arXiv:2009.02911v3, §3.2, pp.12–13): the decision
`xₖ = (µₖ, pₖ)` of every iteration `k ≥ 1` lies in the box `B` and is determined by the information
`𝓕ₖ` of the first `k − 1` iterations (p.68: "note that `xₖ ∈ 𝓕ₖ`"). In particular `x₁` is
deterministic. -/
def Model.Admissible {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (D : ℕ → ℕ) (x : ℕ → Ω → Point) : Prop :=
  ∀ k : ℕ, 1 ≤ k → Measurable[Pr.info D k] (x k) ∧ ∀ ω, x k ω ∈ M.box

end GOLiQ


