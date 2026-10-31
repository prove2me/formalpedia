-- Prove2me | Definitions.Def_FoundationsRL_PosteriorSampling_roundLaw
-- name    : FoundationsRL_PosteriorSampling_roundLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:38.90382+00:00
-- url     : https://prove2.me/theorems/766ea496-cd85-4537-ab6c-a0a313958f41
-- title:
--   Conditional law of a round given the history, and $P_{r\mid\pi^\star,\pi,H}$, $P_{r\mid\pi,H}$
-- statement:
--   The **round law** is the conditional law of $(\pi^t,r^t,\pi^\star,f^\star)$ given $H^{t-1}$, so that $\mathbb E_{t-1}[F]$ is the integral of $F$ against it. Conditioning it elementarily on events gives the reward laws $P_{r^t\mid\pi^\star,\pi^t,H^{t-1}}$ and $P_{r^t\mid\pi^t,H^{t-1}}$.
--
--   **Formalization Note** The round law is a regular conditional distribution, unique up to a null set of histories.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, pp. 35–36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_OptimalSelection
import Definitions.Def_FoundationsRL_PosteriorSampling_jointLaw

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

variable {A : ℕ} (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ]
  (sel : OptimalSelection A) (π : BanditPolicy A)

/-- What one round reveals or involves, jointly: `(πᵗ, rᵗ, π⋆, f⋆)`. -/
abbrev RoundOutcome (A : ℕ) : Type := Fin A × ℝ × Fin A × (Fin A → ℝ)

/-- The joint law of `(H^t, (π^{t+1}, r^{t+1}, π⋆, f⋆))`. -/
noncomputable def roundJoint (t : ℕ) : Measure (BanditHistory A t × RoundOutcome A) :=
  (jointLaw μ π (t + 1)).map fun p =>
    (fun s : Fin t => p.2 s.castSucc,
      ((p.2 (Fin.last t)).1, (p.2 (Fin.last t)).2, sel.toFun p.1,
        (fun a => meanReward p.1 a : Fin A → ℝ)))

instance (t : ℕ) : IsFiniteMeasure (roundJoint μ sel π t) := by
  rw [roundJoint]; infer_instance

/-- The conditional law of the next round given the history: the law of `(πᵗ, rᵗ, π⋆, f⋆)`
given `H^{t-1}`, so that `E_{t-1}[F]` is the integral of `F` against `roundLaw t h` (Foster &
Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §2.6, p. 35).

**Formalization Note.** A regular conditional distribution (`Measure.condKernel`), unique up to a
null set of histories. The argument `t` is the number of completed rounds, so `roundLaw t` is
the book's round `t + 1`. -/
noncomputable def roundLaw [NeZero A] (t : ℕ) : Kernel (BanditHistory A t) (RoundOutcome A) :=
  (roundJoint μ sel π t).condKernel

instance [NeZero A] (t : ℕ) : IsMarkovKernel (roundLaw μ sel π t) := by
  rw [roundLaw]; infer_instance

/-- `P_{r | π⋆ = a', π = a, H = h}`: the conditional law of the reward of the round given the
decision played and the optimal decision. Elementary conditioning of `roundLaw t h`; the zero
measure on an event of probability zero. -/
noncomputable def rewardGiven [NeZero A] (t : ℕ) (h : BanditHistory A t) (a a' : Fin A) :
    Measure ℝ :=
  (cond (roundLaw μ sel π t h) {z | z.1 = a ∧ z.2.2.1 = a'}).map fun z => z.2.1

/-- `P_{r | π = a, H = h}`: the conditional law of the reward of the round given the decision
played. Elementary conditioning of `roundLaw t h`. -/
noncomputable def rewardMarginal [NeZero A] (t : ℕ) (h : BanditHistory A t) (a : Fin A) :
    Measure ℝ :=
  (cond (roundLaw μ sel π t h) {z | z.1 = a}).map fun z => z.2.1

end FoundationsRL.PosteriorSampling


