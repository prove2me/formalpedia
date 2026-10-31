-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_posterior
-- name    : FoundationsRL_PosteriorSampling_posterior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:26.523956+00:00
-- url     : https://prove2.me/theorems/9064ff9f-19a8-4d6b-9821-e2134daf4428
-- title:
--   Posterior of $(\pi^\star,f^\star)$ and the posterior means $\bar f^t$, $\bar f^t_{\pi'}$
-- statement:
--   For each round, the **posterior** is the conditional law of $(\pi^\star,f^\star)$ given the history. From it come the posterior of $\pi^\star$, the **posterior mean reward function**
--
--   $$
--   \bar f^t(\pi)=\mathbb E_{t-1}[f^\star(\pi)],
--   $$
--
--   and the **posterior mean given the optimal decision**
--
--   $$
--   \bar f^t_{\pi'}(\pi)=\mathbb E_{t-1}[f^\star(\pi)\mid\pi^\star=\pi'].
--   $$
--
--   **Formalization Note** The posterior is a regular conditional distribution, which exists because the values of $(\pi^\star,f^\star)$ lie in a standard Borel space. It is unique up to a null set of histories. Conditioning on $\pi^\star=\pi'$ is elementary, with the value $0$ when that event has posterior probability zero.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, p. 35

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_OptimalSelection
import Definitions.Def_FoundationsRL_PosteriorSampling_jointLaw

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

variable {A : ℕ} (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ]
  (sel : OptimalSelection A) (π : BanditPolicy A)

/-- The posterior of `(π⋆, f⋆)`: the conditional law of `(π⋆, f⋆)` given `H^t` under the joint
law (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §2.6, p. 35, where `E_{t-1}` is conditional expectation given `H^{t-1}`).

**Formalization Note.** A regular conditional distribution, `Measure.condKernel`, which exists
because `Fin A × ℝ^A` is standard Borel. It is unique up to a null set of histories, and every
statement built on it is almost sure in the history. The mean vector is conditioned rather than
the model itself: only `f⋆` and `π⋆` enter the proof, and no standard Borel structure on the
Giry σ-algebra is needed. -/
noncomputable def posterior [NeZero A] (t : ℕ) :
    Kernel (BanditHistory A t) (Fin A × (Fin A → ℝ)) :=
  ((jointLaw μ π t).map fun p =>
    (p.2, (sel.toFun p.1, (fun a => meanReward p.1 a : Fin A → ℝ)))).condKernel

instance [NeZero A] (t : ℕ) : IsMarkovKernel (posterior μ sel π t) := by
  rw [posterior]; infer_instance

/-- The posterior of `π⋆`: `P_{π⋆|H^t = h}`. -/
noncomputable def optPosterior [NeZero A] (t : ℕ) (h : BanditHistory A t) : Measure (Fin A) :=
  (posterior μ sel π t h).map Prod.fst

/-- The posterior mean reward `f̄ᵗ(a) = E_{t-1}[f⋆(a)]` (Foster & Rakhlin, arXiv:2312.16730v1,
§2.6, p. 35). -/
noncomputable def postMean [NeZero A] (t : ℕ) (h : BanditHistory A t) (a : Fin A) : ℝ :=
  ∫ z, z.2 a ∂posterior μ sel π t h

/-- The posterior mean reward given the optimal decision,
`f̄ᵗ_{a'}(a) = E_{t-1}[f⋆(a) | π⋆ = a']` (Foster & Rakhlin, arXiv:2312.16730v1, §2.6, p. 35).

**Formalization Note.** Elementary conditioning of the posterior on the event `π⋆ = a'`
(`ProbabilityTheory.cond`). When that event has posterior probability zero the conditional
measure is `0` and the value is `0`; the book's formulas weigh this term by `pᵗ(a')`, so the
default value does not enter them for a posterior sampling algorithm. -/
noncomputable def postMeanGiven [NeZero A] (t : ℕ) (h : BanditHistory A t) (a' a : Fin A) : ℝ :=
  ∫ z, z.2 a ∂(cond (posterior μ sel π t h) {z | z.1 = a'})

end FoundationsRL.PosteriorSampling


