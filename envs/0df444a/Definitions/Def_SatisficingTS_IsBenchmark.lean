-- Prove2me | Definitions.Def_SatisficingTS_IsBenchmark
-- name    : SatisficingTS_IsBenchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:51.400061+00:00
-- url     : https://prove2.me/theorems/ea7ce524-c192-4551-94d8-980f33ed5d9d
-- title:
--   Benchmark action $\tilde A=f(\theta,\zeta)$
-- statement:
--   A benchmark (satisficing) action is a random action of the form
--   $$
--   \tilde A=f(\theta,\zeta),
--   $$
--   where $f:\Theta\times\mathcal Z\to\mathcal A$ is measurable and $\zeta$ is a random variable in a measurable space $\mathcal Z$ that is independent of the triple $(\theta,(W_t)_{t\ge0},\xi)$, $\xi$ being the policy's exogenous randomness. The benchmark may thus be randomized (as in Example 6), but its randomization is not shared with the policy.
--
--   Theorem 1 compares a policy against such an $\tilde A$, whose expected reward $\tilde R=\mu(\tilde A,\theta)$ is within $D$ of optimal.
--
--   **Formalization Note** The paper writes $\tilde A=f(\theta,\xi)$ and uses $\xi$ for the policy's randomness. If the benchmark could use the policy's $\xi$, Theorem 1 would be false, so here its randomness $\zeta$ is independent of $\xi$ as well (see the goal theorem's differences).
-- source:
--   Russo & Van Roy, Satisficing in Time-Sensitive Bandit Learning, arXiv:1803.02855v2, Theorem 1, p.8 ("any Ã = f(θ, ξ) where ξ is independent of the disturbances"); §2, p.5 (ξ independent of θ and the disturbances); Example 6, p.7

import Mathlib
open MeasureTheory ProbabilityTheory

namespace SatisficingTS

/-- **A benchmark action `Ã = f(θ, ζ)`** (Russo & Van Roy, *Satisficing in Time-Sensitive Bandit
Learning*, arXiv:1803.02855v2, Theorem 1, p.8: "any Ã = f(θ, ξ) where ξ is independent of the
disturbances"; §3, p.6; Example 6, p.7).

`IsBenchmark P θ W ξ ζ f` says that `ζ : Ω → 𝒵` and `f : Θ → 𝒵 → 𝒜` are measurable and that the
benchmark's randomness `ζ` is independent of the triple `(θ, (W_t)_t, ξ)`, where `ξ` is the
policy's exogenous randomness. The benchmark action is then `Ã ω = f (θ ω) (ζ ω)`.

**Formalization Note.** The paper writes `Ã = f(θ, ξ)` and uses `ξ` (§2, p.5) for "some random
variable that is independent of θ and the disturbances". Here the benchmark's randomness is
independent of the policy's randomness as well: if the benchmark could share the policy's `ξ`,
Theorem 1 fails (a policy can reveal the binary digits of `ξ` one per period while
`I(Ã; θ) = 0`), so this independence is the correction the theorem needs. -/
def IsBenchmark {Ω Θ 𝒲 Ξ 𝒵 𝒜 : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace 𝒲] [MeasurableSpace Ξ] [MeasurableSpace 𝒵] [MeasurableSpace 𝒜]
    (P : Measure Ω) (θ : Ω → Θ) (W : ℕ → Ω → 𝒲) (ξ : Ω → Ξ) (ζ : Ω → 𝒵) (f : Θ → 𝒵 → 𝒜) :
    Prop :=
  Measurable ζ ∧ Measurable (fun p : Θ × 𝒵 => f p.1 p.2) ∧
    IndepFun ζ (fun ω => (θ ω, (fun t => W t ω), ξ ω)) P

end SatisficingTS


