-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg3Policy
-- name    : IntroDelayAMDP_Supplement_alg3Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:53:42.808788+00:00
-- url     : https://prove2.me/theorems/ad5c9db6-942c-4dfb-bb0c-b4749c6190a5
-- title:
--   Algorithm 3 — the policy played in episode $\kappa$
-- statement:
--   The policy $\pi_\kappa$ played by **Algorithm 3** (policy optimization with MGRR for linear AMDPs). By App. C.1 ("Without delays, we have $\bar d=0$, and Algorithms 4 and 5 are exactly Algorithms 1 and 3"), Algorithm 3 is Algorithm 5 with all delays $0$ and $\bar d=0$: every episode is processed at the end of its own episode, it is not skipped iff $\sqrt K<\kappa\le K-\sqrt K$ (lines 4 and 13), the regions use the features of episodes $\kappa-\sqrt K,\dots,\kappa-1$ (line 5), and the attempts are those of the estimates started in episodes $k<\kappa$ (line 8). A given fixed policy is played when $\theta>1/2$ or $K<2\sqrt K$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 3, p.19; App. C.1, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_alg5Policy

namespace IntroDelayAMDP.Supplement

/-- **The policy `π_κ` played by Algorithm 3 in episode `κ`** (Algorithm 3, printed p.19, PDF p.21, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). App. C.1 (printed p.58): "Without delays, we have `d̄ = 0`, and Algorithms 4 and 5 are exactly
Algorithms 1 and 3." So Algorithm 3 is Algorithm 5 with all delays `0` and `d̄ = 0`: every episode `κ` is
processed at the end of its own episode; it is not skipped iff `√K < κ ≤ K − √K` (1-based; "at least `√K`
processed before" is `κ − 1 ≥ √K`, and `κ + 0 ≤ K − √K − 0`), which is the condition of lines 4 and 13; the
"last `√K` episodes processed before `κ`" are `κ − √K, …, κ − 1` (line 5); the attempts are those of the
estimates started in episodes `k < κ` (line 8). The fixed policy `πfix` is played when `θ > 1/2` or
`K < 2√K` (printed p.19). -/
noncomputable def alg3Policy {X A : Type} [Fintype A] {d H : ℕ} (L : LayeredSpace X H)
    (φ : X → A → Fin d → ℝ) (ℓ : ℕ → X → A → ℝ) (p : LinParams) (rule : RemovalRule d)
    (K sqrtK : ℕ) (πfix : X → A → ℝ) (traj : ℕ → ℕ → X × A) (coin : ℕ → ℕ → ℕ → ℝ) (t : ℕ) :
    X → A → ℝ :=
  alg5Policy L φ ℓ p rule K sqrtK 0 (fun _ => 0) πfix traj coin t

end IntroDelayAMDP.Supplement


