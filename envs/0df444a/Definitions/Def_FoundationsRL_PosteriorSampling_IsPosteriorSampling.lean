-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_IsPosteriorSampling
-- name    : FoundationsRL_PosteriorSampling_IsPosteriorSampling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:17.219224+00:00
-- url     : https://prove2.me/theorems/8688d3bb-9daa-41c0-8613-5226ffded22e
-- title:
--   The posterior sampling algorithm: $p^t(\pi)=\mathbb P(\pi^\star=\pi\mid H^{t-1})$
-- statement:
--   An algorithm with decision kernels $p^t$ is the **posterior sampling algorithm** for the prior $\mu$ over $T$ rounds when, at every round,
--
--   $$
--   p^t(\pi)=\mathbb P(\pi^\star=\pi\mid H^{t-1})\quad\text{almost surely.}
--   $$
--
--   The algorithm samples its decision from the posterior distribution of the optimal decision.
--
--   **Formalization Note** The identity is stated on laws: the law of $(H^{t-1},\pi^\star)$ equals the law of $H^{t-1}$ composed with the kernel $p^t$. Rounds are indexed from $0$. A kernel with this property exists for every prior and every selection.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Posterior Sampling box, p. 31

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_OptimalSelection
import Definitions.Def_FoundationsRL_PosteriorSampling_jointLaw

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- `π` is the posterior sampling algorithm for the prior `μ` over `T` rounds (Foster & Rakhlin,
*Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1,
p. 31): at every round, `pᵗ(π) = ℙ(π⋆ = π | H^{t-1})`.

**Formalization Note.** Rounds are indexed from `0`, so `t : ℕ`, `t < T`, is the book's round
`t + 1` and the history has `t` entries. The identity is the almost-sure one, stated on the joint
law: the law of `(H, π⋆)` under the first `t` rounds is the law of `H` composed with the kernel
`π.select t`. The law of the first `t` rounds uses only earlier kernels, so the condition is not
circular. -/
def IsPosteriorSampling {A : ℕ} (μ : Measure (BanditModel A)) (sel : OptimalSelection A)
    (π : BanditPolicy A) (T : ℕ) : Prop :=
  ∀ t < T,
    (jointLaw μ π t).map (fun p => (p.2, sel.toFun p.1)) = histLaw μ π t ⊗ₘ π.select t

end FoundationsRL.PosteriorSampling


