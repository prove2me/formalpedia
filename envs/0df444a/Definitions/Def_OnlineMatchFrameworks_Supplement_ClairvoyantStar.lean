-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_ClairvoyantStar
-- name    : OnlineMatchFrameworks_Supplement_ClairvoyantStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:23:51.319609+00:00
-- url     : https://prove2.me/theorems/c0bbdd78-5734-5dee-ba2a-ef7c86e235ae
-- title:
--   Patience laws, the clairvoyant star value and infinitely many copies
-- statement:
--   A **patience law** is a probability distribution $\mu$ of finite support on the positive integers, with tail $q_k=\sum_{\theta\ge k}\mu_\theta$. For a star with items $U$, let $\mathrm{OPT}_\theta$ be the star optimum when the patience is known to be $\theta$. The **clairvoyant value** is
--
--   $$
--   \sum_\theta\mu_\theta\,\mathrm{OPT}_\theta,
--   $$
--
--   the expected reward of an algorithm that sees the realized patience in advance and not the edge coins.
--
--   With **infinitely many copies** every element of $U$ is a kind of item that may be offered repeatedly, each time with an independent coin. The optimum is then the supremum of the star value over finite lists with repetition, and the clairvoyant value is formed from it in the same way. These are the two sides of the hardness result for unknown patience.
--
--   **Formalization Note** The real supremum over lists with repetition has a nonempty index type and is bounded by $\sum_uw_u$.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §5.2, p.23; §6.3, pp.32–33; Appendix A, proof of Theorem 10, p.55

import Definitions.Def_OnlineMatchFrameworks_StarPolicy

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

/-- **A patience law with finite support.** arXiv:1907.03963v6, §5.2, p.23, and §6.3, (8), p.33:
`μ θ = Pr[patience = θ]`, with no mass at `0` (p.23 ignores such customers, so that `q_1 = 1`). -/
structure IsPatienceLaw (μ : ℕ →₀ ℝ) : Prop where
  nonneg : ∀ θ, 0 ≤ μ θ
  zero : μ 0 = 0
  total : ∑ θ ∈ μ.support, μ θ = 1

/-- **The tail `q_k = Pr[patience ≥ k]` of a law.** arXiv:1907.03963v6, §5.2, p.23. -/
noncomputable def lawTail (μ : ℕ →₀ ℝ) (k : ℕ) : ℝ :=
  ∑ θ ∈ μ.support, if k ≤ θ then μ θ else 0

variable {U : Type*}

/-- **The star with patience known to be `θ`.** arXiv:1907.03963v6, §6.3, p.32: the same items, weights
and probabilities, with the deterministic patience `θ` in place of the random one; this is the problem
of a clairvoyant "who sees the realization of θ in advance". Its survival function is
`tailSurvival (deterministicTail θ)`. -/
def withPatience (G : OnlineMatchFrameworks.Instance U Unit) (θ : ℕ) :
    OnlineMatchFrameworks.Instance U Unit where
  p := G.p
  w := G.w
  surv := fun _ l => if l.length + 1 ≤ θ then 1 else 0
  p_nonneg := G.p_nonneg
  p_le_one := G.p_le_one
  w_nonneg := G.w_nonneg
  surv_nonneg := fun _ l => by split_ifs <;> norm_num
  surv_le_one := fun _ l => by split_ifs <;> norm_num
  surv_mono := fun _ l l' h => by
    have := h.length_le
    split_ifs <;> first | omega | norm_num

/-- **The clairvoyant value.** arXiv:1907.03963v6, §6.3, p.32, and proof of Theorem 10, p.55:
`∑_θ Pr[patience = θ] · (star optimum when the patience is known to be θ)`. -/
noncomputable def clairvoyantStarValue [Fintype U] (G : OnlineMatchFrameworks.Instance U Unit)
    (μ : ℕ →₀ ℝ) : ℝ :=
  ∑ θ ∈ μ.support, μ θ * (withPatience G θ).starOpt Finset.univ ()

/-- **The star optimum with infinitely many copies of every item.** arXiv:1907.03963v6, §6.3, pp.32–33:
every element of `U` is a kind of item that can be offered any number of times, each time with an
independent coin. The policies are the finite lists with repetition.

**Formalization Note.** The index type is nonempty and the values are at most `∑_u w_u`. With a patience
law of finite support no list longer than its largest value does better, so infinite lists add
nothing. -/
noncomputable def copiesOpt (G : OnlineMatchFrameworks.Instance U Unit) : ℝ :=
  ⨆ l : List U, G.starValue () l

/-- **The clairvoyant value with infinitely many copies.** arXiv:1907.03963v6, §6.3, pp.32–33. -/
noncomputable def clairvoyantCopiesValue (G : OnlineMatchFrameworks.Instance U Unit)
    (μ : ℕ →₀ ℝ) : ℝ :=
  ∑ θ ∈ μ.support, μ θ * copiesOpt (withPatience G θ)

end OnlineMatchFrameworks.Supplement


