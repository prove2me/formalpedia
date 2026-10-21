-- Prove2me | Definitions.Def_MatrixAnalytic_ProductForm_Chain
-- name    : MatrixAnalytic_ProductForm_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:04.897554+00:00
-- url     : https://prove2.me/theorems/2f83711d-a604-4e1b-8ae0-ec2c7026d4b1
-- title:
--   Continuous-time Markov processes on a countable state space — generator, jump chain, regularity, positive recurrence, stationary vector, expected sojourn times
-- statement:
--   Let $V$ be a countable set of states and $Q = (Q_{xy})_{x,y\in V}$ a real matrix. The file fixes the notions of continuous-time Markov process theory used in Chapter 15, each defined by what it means for the process, through its jump chain and the mean lengths of its sojourns.
--
--   1. $Q$ is an **infinitesimal generator** if $Q_{xy}\ge 0$ for $x\ne y$, $Q_{xx}<0$ for every $x$, and every row sums to zero, $\sum_y Q_{xy}=0$. The sojourn in $x$ is exponential with rate $q_x=-Q_{xx}$, hence of mean $1/q_x$.
--   2. The **jump chain** is the discrete-time chain with transition probabilities $\tilde P_{xy}=Q_{xy}/q_x$ for $y\ne x$ and $\tilde P_{xx}=0$. Its $t$-step transition probabilities, the weight $\prod_{k<t}\tilde P_{\omega_k\omega_{k+1}}$ of a trajectory $\omega_0,\dots,\omega_t$, and the tail $P_x[\tau^+_x>t]$ of its first return time to $x$ are the usual sums over finite trajectories.
--   3. The process is **irreducible** if its jump chain is: for all $x,y$ there is $t$ with $\tilde P^{(t)}_{xy}>0$.
--   4. The process is **regular** (it undergoes only finitely many transitions in any interval of finite length) if, for every initial state $x$ and every $M\in\mathbb R$, the probability that the first $t$ mean sojourn times along the jump chain $(Y_k)$ add up to at most $M$,
--   $$P_x\Big[\sum_{k<t} 1/q_{Y_k}\le M\Big],$$
--   tends to $0$ as $t\to\infty$; that is, $\sum_k 1/q_{Y_k}=\infty$ almost surely.
--   5. The **expected first return time** to $x$ is $m_x=\sum_{t\ge 0}\sum_y P_x[Y_t=y,\ \tau^+_x>t]/q_y$, the expected total length of the sojourns before the jump chain returns to $x$ (possibly $+\infty$). The state $x$ is **positive recurrent** if the process returns to $x$ with probability one ($P_x[\tau^+_x>t]\to 0$) and $m_x<\infty$.
--   6. A **stationary probability vector** is a vector $\pi$ with $\pi_x\ge 0$, $\sum_x\pi_x=1$ and $\pi Q=0$, i.e. $\sum_x\pi_xQ_{xy}=0$ for every $y$.
--   7. For a set $T$ of states, the **expected sojourn time** in $y$ before the first visit to $T$, starting from $x$, is
--   $$\sum_{t\ge 0} P_x[Y_t=y,\ Y_1\notin T,\dots,Y_t\notin T]\,/\,q_y ,$$
--   each visit of the jump chain to $y$ contributing the mean sojourn $1/q_y$; the sojourn at time $0$ counts when $y=x$. It takes values in $[0,+\infty]$.
--
--   These are the standing notions of the chapter: a continuous-time QBD is an irreducible, regular Markov process on a countable state space, and the theorems characterize when it is positive recurrent and what its stationary vector is.
--
--   **Formalization Note** The discrete-time notions (t-step probabilities, irreducibility, trajectory weights, return-time tails) restate, with the same bodies, the platform's public definition `mm_countable` (namespace `MarkovMixing`), which is not available as an importable module in the build environment. The continuous-time process is encoded by its jump chain and mean holding times, with no measure theory: an expected time is a sum over jump epochs of the probability of being at a state times its mean holding time, valued in $[0,+\infty]$. Regularity uses the classical fact that a sum of independent exponential sojourns with means $1/q_{Y_k}$ is infinite almost surely exactly when $\sum_k 1/q_{Y_k}=\infty$. Positive recurrence is the return-time notion, not the existence of a stationary vector.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 83 (regular processes, footnote 7), pp. 141–142 (Section 6.4: generator (6.19), irreducible and regular), p. 142 (Theorem 6.4.1: expected sojourn times); restates the platform definition mm_countable

import Mathlib

namespace MatrixAnalytic.ProductForm

noncomputable section

open scoped ENNReal

/-!
Continuous-time Markov processes on a countable state space, the setting of Chapter 15 of
Latouche & Ramaswami (a continuous-time QBD, §6.4 p. 141 and §15.1 p. 296, with possibly
infinitely many phases). A process is given by its infinitesimal generator `Q`; it is described
through its **jump chain** (the discrete-time chain of the states it visits, with transition
probabilities `Q_{xy}/q_x`, `x ≠ y`) and the **mean holding times** `1/q_x`, `q_x = −Q_{xx}`, of
its exponential sojourns. Every probability below is a sum over finite trajectories of the jump
chain of products of one-step transition probabilities, and every expected time is a sum over
jump epochs of such probabilities times mean holding times.

The discrete-time notions (`stepPow`, `IrreducibleC`, `pathWeightC`, `setAvoidTailC`,
`returnTailC`) have the bodies of the platform definition `mm_countable` (namespace
`MarkovMixing`), restated here because that module is not available as an import.
-/

variable {V : Type*} [Countable V] [DecidableEq V]

/-- The `t`-step transition probabilities `P_{xy}(t) = P[X_t = y | X_0 = x]` of a discrete-time
chain. -/
def stepPow (P : V → V → ℝ) : ℕ → V → V → ℝ
  | 0 => fun x y => if y = x then 1 else 0
  | t + 1 => fun x y => ∑' z : V, stepPow P t x z * P z y

/-- Irreducibility of a discrete-time chain: every state reaches every other state. -/
def IrreducibleC (P : V → V → ℝ) : Prop :=
  ∀ x y : V, ∃ t : ℕ, 0 < stepPow P t x y

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a finite trajectory. -/
def pathWeightC (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ :=
  ∏ i : Fin t, P (ω i.castSucc) (ω i.succ)

open Classical in
/-- `P_x[τ⁺_A > t]`: the chain started at `x` avoids the set `A` at all times `1, …, t`. -/
def setAvoidTailC (P : V → V → ℝ) (x : V) (A : Set V) (t : ℕ) : ℝ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ A then pathWeightC P ω else 0

/-- `P_x[τ⁺_x > t]`, the tail of the first return time to `x`. -/
def returnTailC (P : V → V → ℝ) (x : V) (t : ℕ) : ℝ :=
  setAvoidTailC P x {x} t

/-- The weight of a trajectory in `ℝ≥0∞` (used for expected values, which may be infinite). -/
def pathWeightE (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ i : Fin t, ENNReal.ofReal (P (ω i.castSucc) (ω i.succ))

/-- An infinitesimal generator on a countable state space (the form (6.19), p. 141): nonnegative
off-diagonal entries, strictly negative diagonal entries, and every row summing to zero. -/
def IsGeneratorC (Q : V → V → ℝ) : Prop :=
  (∀ x y : V, x ≠ y → 0 ≤ Q x y) ∧ (∀ x : V, Q x x < 0) ∧ ∀ x : V, HasSum (Q x) 0

/-- The rate `q_x = −Q_{xx}` of the exponential sojourn in `x`; its mean is `1/q_x`. -/
def holdRate (Q : V → V → ℝ) (x : V) : ℝ := -Q x x

/-- The jump chain of the process: from `x` it moves to `y ≠ x` with probability `Q_{xy}/q_x`. -/
def jumpP (Q : V → V → ℝ) (x y : V) : ℝ :=
  if y = x then 0 else Q x y / holdRate Q x

/-- The process is irreducible: its jump chain is irreducible. -/
def IrreducibleCT (Q : V → V → ℝ) : Prop :=
  IrreducibleC (jumpP Q)

open Classical in
/-- **Regularity** (non-explosion, p. 83: "only a finite number of transitions in any interval of
finite length"). The time of the `t`-th transition is a sum of `t` independent exponential
sojourns with means `1/q_{Y_0}, …, 1/q_{Y_{t-1}}` along the jump chain `Y`, and their sum is
infinite almost surely exactly when `Σ_k 1/q_{Y_k} = ∞` almost surely. So the process is regular
when, for every start `x` and every bound `M`, the probability that the first `t` mean holding
times along the jump chain add up to at most `M` tends to `0` as `t → ∞`. -/
def RegularCT (Q : V → V → ℝ) : Prop :=
  ∀ (x : V) (M : ℝ), Filter.Tendsto
    (fun t : ℕ => ∑' ω : Fin (t + 1) → V,
      if ω 0 = x ∧ ∑ k : Fin t, (holdRate Q (ω k.castSucc))⁻¹ ≤ M
      then pathWeightE (jumpP Q) ω else 0)
    Filter.atTop (nhds (0 : ℝ≥0∞))

open Classical in
/-- The expected first return time to `x`, starting from `x`: the expected sum of the holding
times at the jump epochs `0, 1, …, τ⁺_x − 1` before the jump chain returns to `x`,
`Σ_{t ≥ 0} Σ_y P_x[Y_t = y, τ⁺_x > t] / q_y`, in `ℝ≥0∞`. -/
def expReturnTimeCT (Q : V → V → ℝ) (x : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ x
    then pathWeightE (jumpP Q) ω * (ENNReal.ofReal (holdRate Q (ω (Fin.last t))))⁻¹ else 0

/-- A state `x` is **positive recurrent**: starting from `x` the process returns to `x` with
probability one (`P_x[τ⁺_x > t] → 0` for the jump chain) and the expected return time is
finite. -/
def PositiveRecurrentCT (Q : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (returnTailC (jumpP Q) x) Filter.atTop (nhds 0) ∧ expReturnTimeCT Q x ≠ ⊤

/-- A stationary probability vector of the process: `π ≥ 0`, `π1 = 1` and `πQ = 0`. -/
def IsStationaryCT (Q : V → V → ℝ) (π : V → ℝ) : Prop :=
  (∀ x : V, 0 ≤ π x) ∧ HasSum π 1 ∧ ∀ y : V, HasSum (fun x => π x * Q x y) 0

open Classical in
/-- The expected time spent in the state `y`, starting from `x`, before the first visit to the
set `T` after time `0`: `Σ_{t ≥ 0} P_x[Y_t = y, Y_1 ∉ T, …, Y_t ∉ T] / q_y` (each visit of the
jump chain to `y` lasts `1/q_y` on average). The sojourn at time `0` counts when `y = x`. -/
def sojournAvoid (Q : V → V → ℝ) (T : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T
    then pathWeightE (jumpP Q) ω * (ENNReal.ofReal (holdRate Q y))⁻¹ else 0

end

end MatrixAnalytic.ProductForm


