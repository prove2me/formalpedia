-- Prove2me | Definitions.Def_FeedbackSwitching_Policy
-- name    : FeedbackSwitching_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:04.344321+00:00
-- url     : https://prove2.me/theorems/0dbd6d6c-1549-4e16-8b3a-c8f84120cff1
-- title:
--   Loss sequences, masked feedback, randomized policies and jointly measurable learners
-- statement:
--   The protocol of §3.1. An oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ before play. In round $t$ the learner picks $I_t$ from its past observations and its internal randomization, incurs $\ell_t(I_t)$, and observes $\ell_t(j)$ for every $(I_t,j)\in E$.
--
--   1. A **loss sequence** is $\ell\in[0,1]^{T\times K}$.
--   2. The **feedback** of playing $i$ on a loss vector $v$ is the vector whose $j$-th entry is $v_j$ if $(i,j)\in E$ and $0$ otherwise.
--   3. A **history** of $t$ rounds lists, for each round, the action played and the feedback received.
--   4. A **policy** consists of a probability space $(\Omega,\mu)$ of internal coins and a rule choosing the action of round $t$ from the history of the first $t$ rounds and the coins.
--   5. A **learner** is a policy whose rule is jointly measurable in (history, coins).
--   6. The **constant policy** plays a fixed action in every round.
--
--   A policy cannot read an unrevealed loss: it sees the losses only through the feedback vectors in its history.
--
--   **Formalization Note** Rounds are 0-based. The learner class over which the minimax regret is taken (`Learner`) adds joint measurability, which the paper leaves implicit; its lower-bound proofs take the law of the transcript.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), §3.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_FeedbackSwitching_FeedbackGraph

open MeasureTheory
open scoped Classical

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

An oblivious loss sequence `ℓ₁, …, ℓ_T ∈ [0,1]^K` (p.13). Round `t : Fin T` is the paper's
round `t + 1`. -/
def LossSeq (K T : ℕ) : Type :=
  {ℓ : Fin T → Fin K → ℝ // ∀ t i, 0 ≤ ℓ t i ∧ ℓ t i ≤ 1}

/-- The **feedback** of playing `i` on the loss vector `v`: the learner observes `v j` for every
`(i, j) ∈ E` (p.13). Unobserved coordinates are masked to `0`; the mask is determined by `i` and
`G`, both known to the learner, so the vector carries exactly the observed losses. -/
noncomputable def reveal {K : ℕ} (G : FeedbackGraph K) (v : Fin K → ℝ) (i : Fin K) : Fin K → ℝ :=
  fun j => if G i j then v j else 0

/-- A history of `t` rounds: the action played and the feedback vector received in each. -/
abbrev Hist (K t : ℕ) : Type := Fin t → Fin K × (Fin K → ℝ)

/-- **Randomized policy** (p.13: "the learner selects `I_t` based on its past observations and
randomization"). A policy has a coin space `Ω` carrying a probability measure `μ` (its internal
randomization, drawn once before play) and a rule `act t h ω` choosing the action of round `t`
(0-based) from the history `h` of the first `t` rounds and the coins `ω`.

**Formalization Note.** A policy reads the losses only through the history, i.e. through
`reveal`; it cannot see an unrevealed loss. No measurability is required here: the class of
learners over which the minimax regret is taken is `Learner` below, and every statement about a
specific algorithm (Theorems 2 and 3) asserts the integrability of its cost. -/
structure Policy (K : ℕ) where
  /-- The coin space of the learner's internal randomization. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The law of the coins. -/
  μ : Measure Ω
  /-- The law of the coins is a probability measure. -/
  [prob : IsProbabilityMeasure μ]
  /-- The action of round `t` given the history of the first `t` rounds and the coins. -/
  act : (t : ℕ) → Hist K t → Ω → Fin K

attribute [instance] Policy.mΩ Policy.prob

/-- **Learner**: a policy whose rule is jointly measurable in (history, coins).

**Formalization Note.** The paper does not state a measurability condition. Its lower-bound
proofs (Proposition 4, Appendix G) average over random loss sequences and take the law of the
transcript, which needs joint measurability; the minimax regret is therefore taken over this
class (a declared `reading`). -/
structure Learner (K : ℕ) extends Policy K where
  /-- The rule is jointly measurable in (history, coins) at every round. -/
  meas : ∀ t, Measurable (fun z : Hist K t × Ω => act t z.1 z.2)

/-- The policy that plays the fixed action `i` in every round ("play a fixed action", pp.23, 34),
with a one-point coin space. -/
noncomputable def constPolicy {K : ℕ} (i : Fin K) : Policy K where
  Ω := Unit
  μ := Measure.dirac ()
  act := fun _ _ _ => i

end FeedbackSwitching


