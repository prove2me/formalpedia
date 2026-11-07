-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1Unfinished
-- name    : IntroDelayAMDP_alg1Unfinished
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:50:56.2082+00:00
-- url     : https://prove2.me/theorems/75590085-cf9c-45d5-bfb6-906288511929
-- title:
--   The number of unfinished estimates
-- statement:
--   $U_k(s,a)$: the number of earlier episodes $k'<k$ whose estimate $(k',s,a)$ is unfinished at the start of episode $k$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. A, p.29; proof of Lemma A.5, p.32

import Mathlib
import Definitions.Def_IntroDelayAMDP_runState

namespace IntroDelayAMDP

open Classical in
/-- **The number `U_k(s, a)` of unfinished estimates of `(s, a)` at the start of episode `k`** (App.
A, printed p.29, and the proof of Lemma A.5, printed p.32, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)), for the 0-based episode `k`:
the number of earlier episodes `k′ < k` whose estimate `(k′, s, a)` is still unfinished. -/
noncomputable def alg1Unfinished {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) (s : St) (a : A) : ℕ :=
  ((Finset.range k).filter (fun k' => (runState L P ℓ p ω k).active k' s a)).card

end IntroDelayAMDP


