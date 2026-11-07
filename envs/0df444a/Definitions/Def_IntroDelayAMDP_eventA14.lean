-- Prove2me | Definitions.Def_IntroDelayAMDP_eventA14
-- name    : IntroDelayAMDP_eventA14
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:53:30.628894+00:00
-- url     : https://prove2.me/theorems/ae039d8c-77d8-4f6c-b6ef-135e30df972b
-- title:
--   The event of Lemma A.14
-- statement:
--   $$\sum_{k=1}^K\sum_{s,a}\frac{q^{\pi_k}(s,a)}{\max\{1,N_k(s,a)\}}\le 2SA(2+\log K)+2H\iota,$$
--   with the natural logarithm.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.14, p.43

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_alg1Visits
import Definitions.Def_IntroDelayAMDP_occ

namespace IntroDelayAMDP

/-- **The event of Lemma A.14** (printed p.43, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "`∑_{k=1}^K ∑_{s,a} q^{π_k}(s, a)/max{1, N_k(s, a)}
≤ 2SA(2 + log K) + 2Hι`"), with `S = |St|`, `A = |A|`, `ι = p.iota` and the natural logarithm. -/
noncomputable def eventA14 {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H : ℕ} (K : ℕ)
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams) : Set (Tape St A K H) :=
  {ω | ∑ k ∈ Finset.range K, ∑ s, ∑ a,
      occ L P (alg1Policy L P ℓ p ω k) s a / max 1 (alg1Visits L P ℓ p ω k s a : ℝ) ≤
    2 * (Fintype.card St : ℝ) * (Fintype.card A : ℝ) * (2 + Real.log K) + 2 * (H : ℝ) * p.iota}

end IntroDelayAMDP


