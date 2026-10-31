-- Prove2me | Definitions.Def_FoundationsRL_DECLowerExamples_fullInfoClass
-- name    : FoundationsRL_DECLowerExamples_fullInfoClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:26.89954+00:00
-- url     : https://prove2.me/theorems/4a0facbc-bae4-4dad-8d46-f88d9ba91503
-- title:
--   Bandits with full information
-- statement:
--   Let $\Pi=[A]$ and $\mathcal R=[0,1]$. In the **full-information** setting a random reward vector $r=(r(\pi'))_{\pi'\in[A]}\in[0,1]^A$ is drawn; the learner who plays $\pi$ receives the reward $r(\pi)$ and observes the whole vector $o=(r(\pi'))_{\pi'\in[A]}$. A model is determined by the law $\nu$ of $r$:
--   $$
--   M_\nu(\pi)=\text{law of }\bigl(r(\pi),\,r\bigr)\ \text{ under } r\sim\nu,
--   $$
--   and the class is the set of all $M_\nu$ with $\nu$ a probability measure on $[0,1]^A$.
--
--   Because every decision reveals every reward, the information gained does not depend on the decision; this is the example where the Decision-Estimation Coefficient does not grow with $A$.
--
--   **Formalization Note** The observation space is `Fin A → ℝ` and $M_\nu(\pi)$ is the image of $\nu$ under $r\mapsto(r(\pi),r)$. The notes name the class only as "the full-information variant of the bandit setting"; it is read as all laws of reward vectors with coordinates a.s. in $[0,1]$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 6.6, p. 99

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLowerExamples

/-- **Bandits with full information**: `Π = [A]`, `R = [0, 1]`, and for a decision `π` the learner
receives the reward `r(π)` and observes `o = (r(π'))_{π'∈[A]}`, the rewards of every action.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 6.6, p. 99 (recalled on p. 111).

A model is given by a law `ν` of the reward vector `r ∈ [0, 1]^A`, and `M(π)` is the law of
`(r(π), r)` under `r ∼ ν`. The class is the set of all such models.

**Formalization Note.** Actions are `Fin A` (0-based); the observation space is `Fin A → ℝ`, and
`M(π)` is the image of `ν` under the measurable map `r ↦ (r π, r)`. The notes do not name the model
class beyond "the full-information variant of the bandit setting"; it is read as every law of a
reward vector with coordinates in `[0, 1]` (almost surely). -/
def fullInfoClass (A : ℕ) : Set (Kernel (Fin A) (ℝ × (Fin A → ℝ))) :=
  {M | ∃ ν : Measure (Fin A → ℝ), IsProbabilityMeasure ν ∧
    (∀ᵐ r ∂ν, ∀ π, r π ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ π, M π = ν.map (fun r => (r π, r))}

end FoundationsRL.DECLowerExamples


