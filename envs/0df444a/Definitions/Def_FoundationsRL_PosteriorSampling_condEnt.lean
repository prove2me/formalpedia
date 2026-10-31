-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_condEnt
-- name    : FoundationsRL_PosteriorSampling_condEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:07.482731+00:00
-- url     : https://prove2.me/theorems/194bd5f4-0680-4910-9292-385540d94fd6
-- title:
--   Shannon entropy and $\mathrm{Ent}(\pi^\star\mid H^t)$
-- statement:
--   The **Shannon entropy** of a law $P$ on $[A]$ is $\mathrm{Ent}(P)=\sum_x p(x)\log(1/p(x))$, with $0\log(1/0)=0$. The **conditional entropy** of $\pi^\star$ given the history is
--
--   $$
--   \mathrm{Ent}(\pi^\star\mid H^t)=\mathbb E_{h\sim H^t}\big[\mathrm{Ent}(P_{\pi^\star\mid H^t=h})\big].
--   $$
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 33 (Ent(X), Ent(X | Y)); §2.6, p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_posterior

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

variable {A : ℕ} [NeZero A] (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ]
  (sel : OptimalSelection A) (π : BanditPolicy A)

/-- The Shannon entropy `Ent(P) = ∑_x p(x) log(1/p(x))` of a law on `[A]` (Foster & Rakhlin,
*Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1,
p. 33), with the usual convention `0 log(1/0) = 0` (`Real.negMulLog 0 = 0`). -/
noncomputable def shannonEnt (P : Measure (Fin A)) : ℝ :=
  ∑ a, Real.negMulLog (P {a}).toReal

/-- The conditional entropy `Ent(π⋆ | H^t) = E_{h∼H^t}[Ent(P_{π⋆|H^t=h})]` (Foster & Rakhlin,
arXiv:2312.16730v1, p. 33). The integrand lies in `[0, log A]`, so the integral is finite. -/
noncomputable def condEnt (t : ℕ) : ℝ :=
  ∫ h, shannonEnt (optPosterior μ sel π t h) ∂histLaw μ π t

end FoundationsRL.PosteriorSampling


