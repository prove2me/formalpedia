-- Prove2me | Definitions.Def_MirrorBP_JEA_Model
-- name    : MirrorBP_JEA_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:03.639298+00:00
-- url     : https://prove2.me/theorems/62b3bea3-34ec-4e9c-b8ca-34277c09ce50
-- title:
--   §2, pp. 9–11 — closed network with demand types, no-underflow constraint, feasible policies, expected payoff, W*_T and W* (1)–(5), Definition 1, Condition 1
-- statement:
--   The joint entry-assignment model of Kanoria and Qian (§2, pp. 9–11).
--
--   1. **Network and states.** $K$ identical supply units circulate among a finite set $V$ of $m = |V|$ nodes. The state is the vector of queue lengths $\mathbf q \in \Omega_K = \{\mathbf q \in \mathbb Z_+^m : \mathbf 1^\top \mathbf q = K\}$.
--   2. **Demand.** Exactly one customer arrives in each period $t = 0, 1, 2, \dots$; her type $\tau[t]$ lies in a finite set $\mathcal T$ and is drawn from the rate vector $\boldsymbol\phi^t$, a probability vector on $\mathcal T$, independently of the past. Type $\tau$ has a pick-up neighborhood $\mathcal P(\tau) \subseteq V$ and a drop-off neighborhood $\mathcal D(\tau) \subseteq V$.
--   3. **Decisions and dynamics** ((1)–(3), p. 10). After seeing $\tau[t] = \tau$ the controller either drops the customer (payoff $0$, state unchanged) or serves her with a pair $(j,k) \in \mathcal P(\tau) \times \mathcal D(\tau)$, collecting $w_{j\tau k}$ and moving one unit from $j$ to $k$: $\mathbf q \mapsto \mathbf q - \mathbf e_j + \mathbf e_k$. Serving from $j$ requires $q_j > 0$ (the **no-underflow constraint** (2)).
--   4. **Policies.** A feasible policy assigns, in each period, to each history of past states, types and decisions, the current state and the current type, a probability distribution on decisions supported on the feasible ones.
--   5. **Payoff.** $J^\pi_T(\mathbf q) = \sum_{t=0}^{T-1} \mathbb E[v^\pi[t] \mid \mathbf q[0] = \mathbf q]$ is the expected payoff collected in the first $T$ periods. Then
--   $$W^*_T = \sup_{\pi} \max_{\mathbf q \in \Omega_K} \frac{1}{T} J^\pi_T(\mathbf q), \qquad W^* = \limsup_{T\to\infty} W^*_T \qquad (4),(5).$$
--   6. **Slow variation** (Definition 1, p. 9). The rates vary $\eta$-slowly over the horizon $T$ if $\frac{1}{T-1}\sum_{t=1}^{T-1} \|\boldsymbol\phi^{t+1} - \boldsymbol\phi^t\|_1 \le \eta$.
--   7. **Connectedness** (Condition 1, (7), p. 11).
--   $$\alpha(\boldsymbol\phi, \mathcal P, \mathcal D) = \min_{\emptyset \ne S \subsetneq V} \sum_{\tau \in \mathcal P^{-1}(S) \cap \mathcal D^{-1}(V \setminus S)} \phi_\tau,$$
--   where $\mathcal P^{-1}(S)$ is the set of types with $\mathcal P(\tau) \cap S \ne \emptyset$ and $\mathcal D^{-1}$ is defined likewise. $\alpha_{\min}$ is the minimum of $\alpha(\boldsymbol\phi^t)$ over the periods of the horizon, and $\bar{\boldsymbol\phi} = \frac1T \sum_{t=0}^{T-1} \boldsymbol\phi^t$ (p. 16).
--
--   These objects carry every statement of the mission: the benchmark $W^*_T$ ranges over all feasible policies, which may know the rates.
--
--   **Formalization Note** Periods are numbered from $0$. A decision is `Option (V × V)` (`none` = drop). The expected payoff is a finite recursion over types and decisions threading the history through, which is the law of the controlled chain. The history records the policy's own past decisions; this class contains the paper's. Definition 1 is stated multiplied by $T-1$. `WstarT` is a real `sSup` over a set that is nonempty (the always-drop policy) and bounded under the standing assumptions. `alphaConn` is a `Finset.inf'` over the nonempty proper subsets (nonempty because $m > 1$).
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, pp. 9–11, (1)–(7), Definition 1, Condition 1; p. 16 (φ̄)

import Mathlib

namespace MirrorBP.JEA

open Finset

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- A demand arrival rate vector `φ` on the finite type set `Ty` is a probability vector
(Kanoria–Qian, arXiv:1903.02764v4, §2, p. 9: the type of the period-`t` customer is drawn from
`φᵗ = (φᵗ_τ)_{τ ∈ 𝒯}`). -/
def IsRate (φ : Ty → ℝ) : Prop :=
  (∀ τ, 0 ≤ φ τ) ∧ ∑ τ, φ τ = 1

/-- The state space `Ω_K = {q ∈ ℤ₊^m : 1ᵀq = K}` of queue-length vectors with `K` supply units
(§2, p. 9). -/
def StateSpace (V : Type) [Fintype V] (K : ℕ) : Set (V → ℕ) :=
  {q | ∑ j, q j = K}

/-- A decision for the arriving customer: `none` drops the customer, `some (j, k)` serves them with a
supply unit picked up at `j` and dropped off at `k` (the vector `x_{jτk} ∈ {0,1}` with at most one entry
equal to one, constraint (1), p. 10). -/
abbrev Decision (V : Type) := Option (V × V)

/-- Feasibility of a decision for a type-`τ` customer at state `q` (p. 10): dropping is always feasible;
serving with `(j, k)` requires `j ∈ P(τ)`, `k ∈ D(τ)` (constraint (1)) and a non-empty origin queue
`q_j > 0` (the no-underflow constraint (2)). -/
def Feasible (P D : Ty → Finset V) (τ : Ty) (q : V → ℕ) : Decision V → Prop
  | none => True
  | some (j, k) => j ∈ P τ ∧ k ∈ D τ ∧ 0 < q j

/-- The state after a decision, dynamics (3), p. 10: serving with `(j, k)` moves one supply unit from
`j` to `k`, `q ↦ q − e_j + e_k`; dropping leaves `q` unchanged. (Natural-number subtraction is exact
here because feasible decisions have `q j > 0`.) -/
def step (q : V → ℕ) : Decision V → (V → ℕ)
  | none => q
  | some (j, k) => q - Pi.single j 1 + Pi.single k 1

/-- The payoff `v[t]` of a decision for a type-`τ` customer (p. 10): `w_{jτk}` if served with
`(j, k)`, and `0` if dropped. -/
def pay (w : V → Ty → V → ℝ) (τ : Ty) : Decision V → ℝ
  | none => 0
  | some (j, k) => w j τ k

/-- A history: the list of past (state, type, decision) triples, in chronological order. -/
abbrev History (V Ty : Type) := List ((V → ℕ) × Ty × Decision V)

/-- A feasible (possibly randomized, history-dependent, time-dependent) policy, the class `𝒰` of p. 10.
`act t h q τ d` is the probability that, in period `t`, after history `h`, at current state `q` and with
current customer type `τ`, the policy takes decision `d`. These probabilities are nonnegative, sum to one
over all decisions, and vanish on infeasible decisions (constraints (1), (2)). The history also records the
policy's own past decisions, so this class contains every policy of the paper's class `𝒰`. -/
structure Policy (P D : Ty → Finset V) where
  act : ℕ → History V Ty → (V → ℕ) → Ty → Decision V → ℝ
  nonneg : ∀ t h q τ d, 0 ≤ act t h q τ d
  sum_one : ∀ t h q τ, ∑ d, act t h q τ d = 1
  feasible : ∀ t h q τ d, ¬ Feasible P D τ q d → act t h q τ d = 0

/-- Expected total payoff of the controlled chain over the next `n` periods, starting in period `t` with
history `h` at state `q`, when the type of the period-`s` customer is drawn from `phi s` independently of
the past: the customer's type `τ` has probability `phi t τ`, the policy then takes decision `d` with
probability `π.act t h q τ d`, collects `pay w τ d`, and the chain moves to `step q d` with history
`h ++ [(q, τ, d)]`. This is the law of the chain of §2 written as a finite recursion (finitely many
outcomes per period), so no measure theory is needed. -/
noncomputable def expPayoffFrom {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ)
    (π : Policy P D) : ℕ → ℕ → History V Ty → (V → ℕ) → ℝ
  | 0, _, _, _ => 0
  | n + 1, t, h, q =>
      ∑ τ, phi t τ * ∑ d, π.act t h q τ d *
        (pay w τ d + expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d))

/-- `expPayoff w phi π T q = ∑_{t=0}^{T-1} E[v^π[t] | q[0] = q]`, the expected payoff collected by
policy `π` in periods `0, …, T − 1` from the initial state `q[0] = q` (the sum inside (4), p. 10;
periods are numbered from `0`). -/
noncomputable def expPayoff {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ)
    (π : Policy P D) (T : ℕ) (q : V → ℕ) : ℝ :=
  expPayoffFrom w phi π T 0 [] q

/-- `W*_T = sup_{π ∈ 𝒰} max_{q ∈ Ω_K} (1/T) ∑_t E[v^π[t] | q[0] = q]`, display (4), p. 10. The set is
nonempty when `V` is nonempty (the always-drop policy, any state of `Ω_K`), and, when every `phi t` is a
probability vector and `|w| ≤ 1`, it is bounded above by `1`, so the real `sSup` is the supremum of (4). -/
noncomputable def WstarT (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (K T : ℕ) : ℝ :=
  sSup {x | ∃ π : Policy P D, ∃ q ∈ StateSpace V K, x = expPayoff w phi π T q / T}

/-- `W* = limsup_{T → ∞} W*_T`, display (5), p. 10. Under the standing assumptions (rates are probability
vectors, `|w| ≤ 1`, `V` nonempty) the sequence `W*_T` lies in `[-1, 1]`, so the limsup is that of a
bounded sequence. -/
noncomputable def Wstar (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (K : ℕ) : ℝ :=
  Filter.limsup (fun T : ℕ => WstarT P D w phi K T) Filter.atTop

/-- Definition 1, p. 9: the rates vary `η`-slowly over the horizon `T`,
`(1/(T−1)) ∑_{t=1}^{T−1} ‖φ^{t+1} − φ^t‖₁ ≤ η`, written with periods numbered from `0` and multiplied
out by `T − 1`: `∑_{t=0}^{T−2} ‖φ^{t+1} − φ^t‖₁ ≤ (T − 1) η`. (For `T = 1` the sum is empty and the
condition is `0 ≤ 0`.) -/
def VariesSlowly (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) : Prop :=
  ∑ t ∈ range (T - 1), ∑ τ, |phi (t + 1) τ - phi t τ| ≤ ((T : ℝ) - 1) * eta

/-- The nonempty proper subsets `S ⊊ V`, `S ≠ ∅` (the cuts of Condition 1). -/
def cuts (V : Type) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  (univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ S ≠ univ)

/-- The connectedness of `(φ, P, D)`, display (7) of Condition 1, p. 11:
`α(φ, P, D) = min_{S ⊊ V, S ≠ ∅} ∑_{τ ∈ P⁻¹(S) ∩ D⁻¹(V∖S)} φ_τ`, where `τ ∈ P⁻¹(S)` iff
`P(τ) ∩ S ≠ ∅` and `τ ∈ D⁻¹(V∖S)` iff `D(τ) ∩ (V∖S) ≠ ∅`. The minimum is over a nonempty finite set as
soon as `|V| > 1` (the standing assumption `m > 1`); the value `0` for `|V| ≤ 1` is never used. -/
noncomputable def alphaConn (P D : Ty → Finset V) (φ : Ty → ℝ) : ℝ :=
  if h : (cuts V).Nonempty then
    (cuts V).inf' h (fun S =>
      ∑ τ ∈ univ.filter (fun τ => (P τ ∩ S).Nonempty ∧ (D τ \ S).Nonempty), φ τ)
  else 0

/-- `α_min = min_{t} α(φᵗ, P, D)` over the periods `t = 0, …, T − 1` of the horizon (Theorem 1, p. 13;
the value `0` for `T = 0` is never used). -/
noncomputable def alphaMin (P D : Ty → Finset V) (phi : ℕ → Ty → ℝ) (T : ℕ) : ℝ :=
  if h : (range T).Nonempty then (range T).inf' h (fun t => alphaConn P D (phi t)) else 0

/-- The time-averaged rate vector `φ̄ = (1/T) ∑_{t=0}^{T−1} φᵗ` (p. 16). -/
noncomputable def phibar (phi : ℕ → Ty → ℝ) (T : ℕ) (τ : Ty) : ℝ :=
  (1 / (T : ℝ)) * ∑ t ∈ range T, phi t τ

end MirrorBP.JEA


