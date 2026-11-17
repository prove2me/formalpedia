-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg5Run
-- name    : IntroDelayAMDP_Supplement_alg5Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:51:45.162858+00:00
-- url     : https://prove2.me/theorems/18de1a8b-6d06-4acf-bb60-86c08c125e9a
-- title:
--   Algorithm 5 — the run
-- statement:
--   The run of **Algorithm 5** on a sample path (trajectories $(s_{t,h},a_{t,h})$ and acceptance coins). Before episode $0$ there are no estimates, no processed episodes and $\hat Q\equiv0$. In episode $t$ the policy
--   $$\pi_t(a\mid s)\propto\exp\Bigl(-\eta\sum_{t'<t}g_{t'}(s,a)\Bigr),\qquad\sum_{t'<t}g_{t'}=\sum_k\bigl(\hat Q_k-\eta\hat Q_k^2\bigr)$$
--   is formed and stored, and every episode $\kappa$ with $\kappa+\min\{d_\kappa,\bar d\}=t$ is processed (`alg5Process`) in increasing order of $\kappa$. The identity for $\sum_{t'<t}g_{t'}$ is line 18: $g_{t'}$ is the total change of $\sum_k(\hat Q_k-\eta\hat Q_k^2)$ during episode $t'$, and $\hat Q_k=0$ before its initialization.
--
--
--   **Formalization Note** Episodes and delays are $0$-based. The state before episode $t$ reads only the trajectories of the episodes before $t$ and the coins of the episodes processed before $t$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 5, lines 1–3 and 18, p.59; App. C.1, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_expPolicy
import Definitions.Def_IntroDelayAMDP_Supplement_alg5Process

namespace IntroDelayAMDP.Supplement

/-- **The run of Algorithm 5** (Algorithm 5, lines 1–18, printed p.59, PDF p.61; App. C.1, printed p.58,
PDF p.60, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).
`alg5Run … t` is the state before the 0-based episode `t`. `alg5Run … 0` has no estimates, no processed
episodes and `Q̂ ≡ 0`. Episode `t` (`alg5Run … (t + 1)`):
* line 2: `π_t(a | s) ∝ exp(−η ∑_{t′<t} g_{t′}(s, a))` (`expPolicy`), stored as `pol t`; here
  `∑_{t′<t} g_{t′} = ∑_k (Q̂_k − ηQ̂_k²)` with the current running estimates, because `g_{t′}` is "the total
  change of `∑_k(Q̂_k − ηQ̂_k²)(s, a)` during" episode `t′` (line 18) and `Q̂_k = 0` before its initialization;
* line 3: every `κ` with `κ + min{d_κ, d̄} = t` is processed (`alg5Process`), in increasing order of `κ`.

**Formalization Note.** Episodes and delays are 0-based (`dl κ` is the paper's `d_{κ+1}`). An episode with
`κ + min{d_κ, d̄} ≥ K` (0-based) is never processed: the run is read only before the episodes `t < K`. The
trajectories `traj` and coins `coin` are the whole sample path; the state before `t` reads only the
trajectories of the episodes played before `t` and the coins of the episodes processed before `t`. -/
noncomputable def alg5Run {X A : Type} [Fintype A] {d H : ℕ} (L : LayeredSpace X H)
    (φ : X → A → Fin d → ℝ) (ℓ : ℕ → X → A → ℝ) (p : LinParams) (rule : RemovalRule d)
    (K sqrtK dbar : ℕ) (dl : ℕ → ℕ) (traj : ℕ → ℕ → X × A) (coin : ℕ → ℕ → ℕ → ℝ) :
    ℕ → LinState X A d
  | 0 =>
    { qhat := fun _ _ _ => 0, pol := fun _ _ _ => 0, processed := [], regs := fun _ _ => [],
      active := fun _ _ => False, nAtt := fun _ _ => 0, Z := fun _ _ => 1, Mcap := fun _ _ => 0,
      Y := fun _ _ => 0, reg := fun _ _ => 0 }
  | t + 1 =>
    let σ := alg5Run L φ ℓ p rule K sqrtK dbar dl traj coin t
    let π : X → A → ℝ := expPolicy p.eta
      (fun s a => ∑ k ∈ Finset.range K, (σ.qhat k s a - p.eta * σ.qhat k s a ^ 2))
    let σ1 : LinState X A d := { σ with pol := fun k => if k = t then π else σ.pol k }
    ((List.range (t + 1)).filter (fun κ => κ + min (dl κ) dbar = t)).foldl
      (fun σ' κ => alg5Process L φ ℓ p rule K sqrtK dbar dl traj coin σ' κ) σ1

end IntroDelayAMDP.Supplement


