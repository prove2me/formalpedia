-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg4Run
-- name    : IntroDelayAMDP_Supplement_alg4Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:42:59.235403+00:00
-- url     : https://prove2.me/theorems/f6e56764-c114-4248-80a9-f9ce6c5db5e8
-- title:
--   Algorithm 4 — the run on the random tape
-- statement:
--   The state of **Algorithm 4** before episode $t$, on a sample point $\omega$ of the base mission's random tape, for given layered space, transition, oblivious losses $\ell_k$, parameters, delay cap $\bar d$ and delays $d_k$: the initial state of Algorithm 1 (no data, no estimates, zero cumulative loss) before episode $0$, and one application of `alg4Step` per episode.
--
--
--   **Formalization Note** Episodes are $0$-based. The default action used by the sampler is reached only on a null set.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 4, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_initState
import Definitions.Def_IntroDelayAMDP_Supplement_alg4Step

namespace IntroDelayAMDP.Supplement

/-- **The run of Algorithm 4 on the tape** (Algorithm 4, printed p.58, PDF p.60, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). For the layered space `L`, the true transition `P`,
the oblivious losses `ℓ`, the parameters `p`, the cap `d̄`, the oblivious delays `dl` (0-based) and a
sample point `ω` of the tape, `alg4Run … ω t` is the state of Algorithm 4 before the 0-based episode `t`:
`alg4Run … 0` is the initial state of Algorithm 1 (no data, no estimates, zero cumulative loss), and
`alg4Run … (t + 1)` applies `alg4Step` to episode `t`.

**Formalization Note.** Episodes are 0-based (the paper's `1, …, K`). The default action
`Classical.arbitrary A` is the sampler's default, reached only on a null set. -/
noncomputable def alg4Run {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A]
    {H K : ℕ} (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (dbar : ℕ) (dl : ℕ → ℕ) (ω : Tape St A K H) : ℕ → AlgState St A
  | 0 => initState L (Classical.arbitrary A)
  | t + 1 => alg4Step L P ℓ p (Classical.arbitrary A) dbar dl ω (alg4Run L P ℓ p dbar dl ω t) t

end IntroDelayAMDP.Supplement


