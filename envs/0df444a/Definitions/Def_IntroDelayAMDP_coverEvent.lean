-- Prove2me | Definitions.Def_IntroDelayAMDP_coverEvent
-- name    : IntroDelayAMDP_coverEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:33.843194+00:00
-- url     : https://prove2.me/theorems/fa6ac639-4702-45a3-9e88-6d83b4705ee0
-- title:
--   The coverage event: $P$ satisfies every constraint of (16)
-- statement:
--   The set of sample points on which, in each of the episodes up to $j$, the true transition satisfies all constraints of (16) at every pair, with the data of the run. A valid $P$ then lies in the confidence sets of these episodes and no pair has its constraints dropped, so this event is contained in $G$.
--
--   Because of the drop rule of (16), "$P\in\mathcal P_k$" alone does not say that $P$ satisfies the constraints: at a pair with unsatisfiable constraints every distribution is allowed. The coverage event is what the proof of Lemma A.1 bounds, and what Lemmas A.13 and A.15 need.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), proof of Lemma A.1, pp.29–30; proof of Lemma A.13, p.42

import Mathlib
import Definitions.Def_IntroDelayAMDP_runState
import Definitions.Def_IntroDelayAMDP_pairConstr

namespace IntroDelayAMDP

/-- **The coverage event: `P` satisfies every constraint of (16)** (the event bounded in the proof
of Lemma A.1, printed pp.29–30, and the fact used in the proof of Lemma A.13, printed p.42, "both
`P″` and `P` satisfy the constraints in Eq. (16)", of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).

`coverEvent K L P ℓ p j` is the set of sample points on which, in each of the 0-based episodes
`0, …, j`, the true transition satisfies all constraints of (16) at every pair, with the data of the
run. A valid `P` then lies in the confidence sets of these episodes and no pair has its constraints
dropped, so this event is contained in `goodEvent K L P ℓ p j`.

**Formalization Note.** Because of the drop rule of (16), "`P ∈ P_k`" alone does not say that `P`
satisfies the constraints: at a pair with unsatisfiable constraints every distribution is allowed.
This event is the stronger statement, and it is what Lemmas A.13 and A.15 need. -/
noncomputable def coverEvent {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H : ℕ} (K : ℕ)
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams) (j : ℕ) : Set (Tape St A K H) :=
  {ω | ∀ j' ≤ j, ∀ s a, pairConstr L p.beta ((runState L P ℓ p ω j').obs s a) (L.layer s) (P s a)}

end IntroDelayAMDP


