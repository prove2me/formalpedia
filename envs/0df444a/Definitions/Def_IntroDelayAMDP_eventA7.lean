-- Prove2me | Definitions.Def_IntroDelayAMDP_eventA7
-- name    : IntroDelayAMDP_eventA7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:54:22.578202+00:00
-- url     : https://prove2.me/theorems/0ca29a3c-0e25-4b16-9385-91d788e9b7d4
-- title:
--   The event of Lemma A.7
-- statement:
--   At the start of every episode $k$ with $G_k$, every pair has fewer than $\nu$ unfinished estimates, and every estimate $(k,s,a)$ started in an episode $k\le K-M$ with $G_k$ has $\sum_\kappa I_{k,\kappa}(s,a)=1$.
--
--   **Formalization Note** With 0-based episodes, the paper's $k$ is $j=k-1$, and "$k\le K-M$" reads $j+1+M\le K$, with no natural-number subtraction.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.7, p.33

import Mathlib
import Definitions.Def_IntroDelayAMDP_goodEvent
import Definitions.Def_IntroDelayAMDP_alg1Unfinished
import Definitions.Def_IntroDelayAMDP_alg1Ind

namespace IntroDelayAMDP

open Classical in
/-- **The event of Lemma A.7** (printed p.33, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "at the start of every episode `k` with
`G_k`, every pair has fewer than `ν` unfinished estimates, and every estimate `(k, s, a)` started in
an episode `k ≤ K − M` with `G_k` has `∑_κ I_{k,κ}(s, a) = 1`").

With 0-based episodes, the paper's episode `k` is `j = k − 1` and `G_k` is `goodEvent … j`; "`k ≤ K − M`"
reads `j + 1 + M ≤ K`. `∑_κ I_{k,κ}(s, a)` is the number of episodes `κ < K` with `I_{k,κ}(s, a)`. -/
noncomputable def eventA7 {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H : ℕ} (K : ℕ)
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams) : Set (Tape St A K H) :=
  {ω | (∀ j < K, ω ∈ goodEvent K L P ℓ p j → ∀ s a, (alg1Unfinished L P ℓ p ω j s a : ℝ) < p.nu) ∧
    (∀ j s a, j + 1 + p.M ≤ K → ω ∈ goodEvent K L P ℓ p j → (runState L P ℓ p ω K).started j s a →
      ((Finset.range K).filter (fun κ => alg1Ind L P ℓ p ω j κ s a)).card = 1)}

end IntroDelayAMDP


