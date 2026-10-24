-- Prove2me | Definitions.Def_PicardFO_Fulfill_Picard
-- name    : PicardFO_Fulfill_Picard
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:59.523694+00:00
-- url     : https://prove2.me/theorems/4fe1446e-ab4a-4178-bc7d-98fde497019c
-- title:
--   Controlled dynamical system, sequential policy simulation and the Picard iteration (Algorithm 1) for a general system (pp. 3–5)
-- statement:
--   A **controlled dynamical system** (§2) consists of a state space $S$, an action space $A$, a disturbance space $\Omega$, for each state $s$ and disturbance $w$ a set of feasible actions $A(s, w) \subseteq A$, an *always feasible* action $a_\phi \in A(s, w)$ for all $s, w$, and a transition map $f : S \times A \times \Omega \to S$. A **policy** is a map $\pi : S \times \Omega \to A$.
--
--   Given an initial state $s_1$ and a sequence of disturbances $\omega_1, \omega_2, \dots$, **sequential simulation** produces the states and actions
--   $$
--   a^{\mathrm{seq}}_t = \pi(s_t, \omega_t), \qquad s_{t+1} = f(s_t, a^{\mathrm{seq}}_t, \omega_t).
--   $$
--
--   The **Picard iteration** (Algorithm 1) assigns every time step $t$ to a process $\mathrm{proc}(t)$ (the sets $T_m = \{t : \mathrm{proc}(t) = m\}$ partition the time steps). It keeps a cache of actions, initialised to $\alpha^0_t = a_\phi$ for all $t$. In iteration $k \ge 1$ every process $m$ re-simulates from $s^{k,m}_1 = s_1$: at a time step $t \in T_m$ it evaluates the policy, $a^{k,m}_t = \pi(s^{k,m}_t, \omega_t)$; at any other time step it replays the cached action $a^{k,m}_t = \alpha^{k-1}_t$ if that action is feasible in its own state, $\alpha^{k-1}_t \in A(s^{k,m}_t, \omega_t)$, and takes $a_\phi$ otherwise; then $s^{k,m}_{t+1} = f(s^{k,m}_t, a^{k,m}_t, \omega_t)$. The new cache takes each time step's action from the process responsible for it: $\alpha^k_t = a^{k,\mathrm{proc}(t)}_t$.
--
--   These objects are the general framework of the paper; the fulfillment model instantiates them.
--
--   **Formalization Note** Time steps are 0-based: Lean's `seqState … t` is the paper's $s_{t+1}$ (the state before the $(t+1)$-st step), `seqAct … t` is $a^{\mathrm{seq}}_{t+1}$, and the disturbance of step $t$ is `ω t`. `procState … α m t` is the state of process `m` before step `t` when it simulates with the previous cache `α`, so the paper's iteration $k$ uses `α = cache … (k - 1)`; `cache … k` is $\alpha^k$, with `cache … 0 = fun _ => aPhi`. Runs are defined for all time steps, so no horizon appears here; nothing in a run at step $t$ depends on later steps. The feasible set may depend on the disturbance as well as on the state, because in the fulfillment problem it depends on the ordered product. Decidability of the feasibility test and of `proc t = m` is classical.
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, pp. 3–5, §2 (model, policy simulation, partition T_m) and Algorithm 1 (p. 5)

import Mathlib

namespace PicardFO.Fulfill

/-- A deterministic controlled dynamical system (Farias et al., §2, p. 3): states `S`, actions `A`,
disturbances `Ω`, a set of feasible actions at each state (it may also depend on the current
disturbance), an "always feasible" action `aPhi`, and the transition map `f : S → A → Ω → S`. -/
structure System (S A Ω : Type*) where
  /-- `feasible s w a`: action `a` is feasible at state `s` when the disturbance is `w`. -/
  feasible : S → Ω → A → Prop
  /-- the always-feasible action `aϕ` -/
  aPhi : A
  aPhi_feasible : ∀ s w, feasible s w aPhi
  /-- the transition map -/
  f : S → A → Ω → S

namespace System

variable {S A Ω ι : Type*}

/-- Sequential simulation of policy `π` from `s₁` along the disturbances `ω` (orders indexed
`0, 1, 2, …`): `seqState sys π s₁ ω t` is the state before order `t` is served (the paper's
`s_{t+1}`). -/
def seqState (sys : System S A Ω) (π : S → Ω → A) (s₁ : S) (ω : ℕ → Ω) : ℕ → S
  | 0 => s₁
  | t + 1 => sys.f (seqState sys π s₁ ω t) (π (seqState sys π s₁ ω t) (ω t)) (ω t)

/-- The sequential action at order `t` (the paper's `a^{seq}_{t+1}`). -/
def seqAct (sys : System S A Ω) (π : S → Ω → A) (s₁ : S) (ω : ℕ → Ω) (t : ℕ) : A :=
  π (sys.seqState π s₁ ω t) (ω t)

open Classical in
/-- Line 6–7 of Algorithm 1: the action process `m` takes at order `t` in state `s` when the
cache from the previous iteration is `α`. Order `t` is assigned to process `proc t`. If `t` is
assigned to `m`, the process evaluates `π`; otherwise it replays the cached action `α t` if that
action is feasible in its own state, and takes `aPhi` otherwise. -/
noncomputable def procAct (sys : System S A Ω) (π : S → Ω → A) (ω : ℕ → Ω) (proc : ℕ → ι)
    (α : ℕ → A) (m : ι) (s : S) (t : ℕ) : A :=
  if proc t = m then π s (ω t)
  else if sys.feasible s (ω t) (α t) then α t else sys.aPhi

/-- Lines 4 and 8 of Algorithm 1: the states of process `m` when it simulates from `s₁` with the
cache `α`; `procState … α m t` is its state before order `t`. -/
noncomputable def procState (sys : System S A Ω) (π : S → Ω → A) (s₁ : S) (ω : ℕ → Ω)
    (proc : ℕ → ι) (α : ℕ → A) (m : ι) : ℕ → S
  | 0 => s₁
  | t + 1 =>
      sys.f (procState sys π s₁ ω proc α m t)
        (sys.procAct π ω proc α m (procState sys π s₁ ω proc α m t) t) (ω t)

/-- The cache of Algorithm 1 (lines 1 and 9): `cache … 0 t = aPhi` for every `t`, and the cache
of iteration `k + 1` at order `t` is the action that the process owning `t`, simulating with
the cache of iteration `k`, takes at order `t`. -/
noncomputable def cache (sys : System S A Ω) (π : S → Ω → A) (s₁ : S) (ω : ℕ → Ω)
    (proc : ℕ → ι) : ℕ → ℕ → A
  | 0 => fun _ => sys.aPhi
  | k + 1 => fun t =>
      sys.procAct π ω proc (cache sys π s₁ ω proc k) (proc t)
        (sys.procState π s₁ ω proc (cache sys π s₁ ω proc k) (proc t) t) t

end System

end PicardFO.Fulfill


