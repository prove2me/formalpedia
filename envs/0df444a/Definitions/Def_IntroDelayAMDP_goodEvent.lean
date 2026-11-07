-- Prove2me | Definitions.Def_IntroDelayAMDP_goodEvent
-- name    : IntroDelayAMDP_goodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:53:25.817617+00:00
-- url     : https://prove2.me/theorems/56ee3529-45f2-4f6b-930b-8eacda795786
-- title:
--   The good events $G_k$
-- statement:
--   $G_k$ is the event that $P\in\mathcal P_{k'}$ for all $k'\le k$, and the good event is $G=G_K$. With 0-based index $j$ the event is the paper's $G_{j+1}$, so $G$ is the value at $j=K-1$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.1, p.29

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Conf

namespace IntroDelayAMDP

/-- **The good events `G_k`** (Lemma A.1, printed p.29, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "Let `G_k` be the event that
`P ∈ P_{k′}` for all `k′ ≤ k`, and let `G ≜ G_K` be the good event"). `goodEvent K L P ℓ p j` is the set
of sample points on which the true transition lies in the confidence sets of the 0-based episodes
`0, …, j` (the paper's `G_{j+1}`); the good event `G = G_K` is `goodEvent … (K − 1)`. -/
noncomputable def goodEvent {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H : ℕ} (K : ℕ)
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams) (j : ℕ) : Set (Tape St A K H) :=
  {ω | ∀ j' ≤ j, P ∈ alg1Conf L P ℓ p ω j'}

end IntroDelayAMDP


