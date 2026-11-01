-- Prove2me | Definitions.Def_StatefulPricing_candS
-- name    : StatefulPricing_candS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:26:08.002431+00:00
-- url     : https://prove2.me/theorems/b21247c6-7f65-45e4-8ae1-a06774bc4358
-- title:
--   The algorithm C&S (chasing and switching), Algorithm 1
-- statement:
--   **C&S** runs, in parallel, an OLSC algorithm $\mathcal A$ over a finite family $\Gamma$ of policies and an ongoing chasing oracle $\mathcal O$. At the beginning of round $t$, $\mathcal A$ picks a policy $\gamma_t$. If $t>1$ and $\gamma_t\neq\gamma_{t-1}$, the oracle is invoked from scratch with target $\gamma_t$, round $t$ and the current state $s_t$; otherwise the existing run continues. The action played is the oracle's action $\hat x(t)$. After the round, the oracle is fed $g_t,f_t$, and $\mathcal A$ is fed the expert rewards
--   $$
--   F_t(\gamma)=f_t\big(s^\gamma(t),x^\gamma(t)\big),\qquad \gamma\in\Gamma,
--   $$
--   computed by simulating each policy up to time $t$ (Eq. (2)).
--
--   The module defines these expert rewards, the bookkeeping of C&S (current state, start round and start state of the current oracle run), the algorithm itself as a randomized online Dd-MDP algorithm, and the law of its coins.
--
--   **Formalization Note** At round $1$ the oracle is invoked with target $\gamma_1$ and state $s_1$ (the "else" branch of Algorithm 1 has no run to continue at $t=1$). The coins are a pair $(\omega_A,\omega_O)$ with $\omega_A\sim P_A$ for $\mathcal A$ and $\omega_O=(\omega_O(\tau))_{\tau\in\mathbb N}$ i.i.d. $\sim P_O$; a run started at round $\tau$ uses $\omega_O(\tau)$, so every run has fresh coins independent of the earlier runs. The switching cost of $\mathcal A$ is not part of the algorithm; Theorem 3.8 sets it to $\sigma$.
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, Algorithm 1, p.11

import Mathlib
import Definitions.Def_StatefulPricing_DdMDP
import Definitions.Def_StatefulPricing_ChasingOracle
import Definitions.Def_StatefulPricing_OLSCAlg

set_option autoImplicit false

namespace StatefulPricing

open MeasureTheory

variable {ΩA ΩO S X ι : Type*}

/-- The expert rewards fed to the OLSC algorithm by C&S (Algorithm 1, arXiv:2005.01869v2, p.11):
`Ft(γ) ← ft(sγ(t), xγ(t))`, computed by simulating policy `γ` up to time `t` (Eq. (2)). -/
def expertRewards (M : DdMDP S X) (Γ : ι → S → X) : ℕ → ι → ℝ :=
  fun t j => M.f t (M.simState (Γ j) t) (Γ j (M.simState (Γ j) t))

/-- The bookkeeping of C&S at the beginning of a round: its current state, the round at which the
current run of the chasing oracle was started, and the state it was started from. -/
structure CSRecord (S : Type*) where
  /-- The current state `s_t`. -/
  state : S
  /-- The round at which the current oracle run was started. -/
  start : ℕ
  /-- The state from which the current oracle run was started. -/
  startState : S

/-- The run of C&S (Algorithm 1, arXiv:2005.01869v2, p.11) up to the beginning of round `t`, for
coins `ω = (ωA, ωO)`.

**Formalization Note.** At round `1` the oracle is invoked with target `γ₁` and state `s₁` (the
"else" branch has no run to continue at `t = 1`). A run started at round `τ` uses the oracle coins
`ωO τ`, so every run has fresh coins, independent of the earlier runs. -/
def csRecord [DecidableEq ι] (A : OLSCAlg ΩA ι) (O : ChasingOracle ΩO S X) (Γ : ι → S → X)
    (ω : ΩA × (ℕ → ΩO)) (M : DdMDP S X) : ℕ → CSRecord S
  | 0 => ⟨M.s₁, 1, M.s₁⟩
  | 1 => ⟨M.s₁, 1, M.s₁⟩
  | t + 2 =>
    let r := csRecord A O Γ ω M (t + 1)
    let x := O.act (ω.2 r.start) (Γ (A ω.1 (t + 1) (expertRewards M Γ))) r.start r.startState
      (t + 1) M
    let s' := M.g (t + 1) r.state x
    if A ω.1 (t + 2) (expertRewards M Γ) ≠ A ω.1 (t + 1) (expertRewards M Γ) then
      ⟨s', t + 2, s'⟩
    else
      ⟨s', r.start, r.startState⟩

/-- **C&S** (chasing and switching), Algorithm 1 (arXiv:2005.01869v2, p.11): "Invoke A to pick a
policy γt at the beginning of round t; if t > 1 and γt ≠ γt−1 then Invoke OChasing from scratch
with target policy γt, initialized with round t and state st; Select the action xt ← x̂(t)
returned by OChasing; else Continue the existing run of OChasing and select the action
xt ← x̂(t) it returns; … Feed A with Ft(·) as the reward function of round t".

The algorithm's coins are `(ωA, ωO)` with `ωO : ℕ → ΩO` one fresh coin per possible run start.
The switching cost of `A` is a parameter of the statements that use C&S (Theorem 3.8: `Δ = σ`). -/
def candS [DecidableEq ι] (A : OLSCAlg ΩA ι) (O : ChasingOracle ΩO S X) (Γ : ι → S → X) :
    DdAlg (ΩA × (ℕ → ΩO)) S X :=
  fun ω t M =>
    let r := csRecord A O Γ ω M t
    O.act (ω.2 r.start) (Γ (A ω.1 t (expertRewards M Γ))) r.start r.startState t M

/-- The law of the coins of C&S: `ωA ∼ PA` and independent oracle coins `ωO τ ∼ PO`, one per
round `τ`. -/
noncomputable def csLaw [MeasurableSpace ΩA] [MeasurableSpace ΩO] (PA : Measure ΩA)
    (PO : Measure ΩO) : Measure (ΩA × (ℕ → ΩO)) :=
  PA.prod (Measure.infinitePi (fun _ : ℕ => PO))

end StatefulPricing


