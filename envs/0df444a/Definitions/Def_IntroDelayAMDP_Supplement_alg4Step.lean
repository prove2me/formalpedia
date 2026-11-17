-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg4Step
-- name    : IntroDelayAMDP_Supplement_alg4Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:42:28.183699+00:00
-- url     : https://prove2.me/theorems/30d8b6fa-5e17-4e74-8457-4ecd1be2e954
-- title:
--   Algorithm 4 — one episode
-- statement:
--   One episode $t$ of **Algorithm 4**: the policy $\pi_t(a\mid s)\propto\exp(-\eta\sum_{t'<t}g_{t'}(s,a))$ is formed at every state, executed (its trajectory is sampled from the action and next-state coins of episode $t$), and stored together with the trajectory; then every episode $\kappa$ with $\kappa+\min\{d_\kappa,\bar d\}=t$ is processed (`alg4Process`), in increasing order of $\kappa$. Episode $\kappa$ is skipped iff $d_\kappa>\bar d$ or $\kappa+d_\kappa>K$.
--
--
--   **Formalization Note** Episodes and delays are $0$-based ($d_\kappa$ of the $0$-based episode $\kappa$ is the paper's $d_{\kappa+1}$), so the skipping test reads $K\le\kappa+d_\kappa$. An episode with $\kappa+\min\{d_\kappa,\bar d\}\ge K$ is never reached by the run.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 4, lines 1–3, p.58; App. C.1, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_AlgParams
import Definitions.Def_IntroDelayAMDP_AlgState
import Definitions.Def_IntroDelayAMDP_Tape
import Definitions.Def_IntroDelayAMDP_coins
import Definitions.Def_IntroDelayAMDP_expPolicy
import Definitions.Def_IntroDelayAMDP_sampleTraj
import Definitions.Def_IntroDelayAMDP_Supplement_alg4Process

namespace IntroDelayAMDP.Supplement

/-- **One episode `t` of Algorithm 4** (Algorithm 4, lines 1–17, printed p.58, PDF p.60, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530); App. C.1, printed p.58).
Given the state `σ` before the 0-based episode `t`:
* line 2: `π_t(a | s) ∝ exp(−η ∑_{t′<t} g_{t′}(s, a))` at every state (`expPolicy` of `σ.cumG`); `π_t` is
  executed and its trajectory sampled from the action and next-state coins of episode `t`; both are
  stored as `pol t`, `traj t`;
* line 3: every episode `κ` with `κ + min{d_κ, d̄} = t` is then processed (`alg4Process`), in increasing
  order of `κ`, with the attempt coins of episode `κ`;
* skipping (App. C.1): `κ` is skipped iff `d_κ > d̄` or `κ + d_κ > K` (1-based), i.e. `K ≤ κ + d_κ` for the
  0-based `κ`.
The delays `dl κ` are those of the 0-based episodes `κ` (the paper's `d_{κ+1}`).

**Formalization Note.** An episode with `κ + min{d_κ, d̄} ≥ K` (0-based) is never reached, since the run
stops after episode `K − 1`; this is the page's "if this is at most `K`". The action fixed by `a0` is the
sampler's default, reached only on a null set. -/
noncomputable def alg4Step {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams) (a0 : A)
    (dbar : ℕ) (dl : ℕ → ℕ) (ω : Tape St A K H) (σ : AlgState St A) (t : ℕ) : AlgState St A :=
  let π : St → A → ℝ := expPolicy p.eta σ.cumG
  let τ : ℕ → St × A := sampleTraj L P π (coins ω t).act (coins ω t).nxt a0
  let σ1 : AlgState St A :=
    { σ with
      pol := fun k => if k = t then π else σ.pol k
      traj := fun k => if k = t then τ else σ.traj k }
  ((List.range (t + 1)).filter (fun κ => κ + min (dl κ) dbar = t)).foldl
    (fun σ' κ => alg4Process L ℓ p K σ' κ (dbar < dl κ ∨ K ≤ κ + dl κ) (coins ω κ)) σ1

end IntroDelayAMDP.Supplement


