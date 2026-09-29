-- Prove2me | Definitions.Def_DelayedBCN_Controllability_Model
-- name    : DelayedBCN_Controllability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:02:55.884327+00:00
-- url     : https://prove2.me/theorems/8b99543e-0542-4e38-8f82-ef9a2e3362bb
-- title:
--   The delayed Boolean control network (2.2), its trajectories, trajectory and state controllability, and the counts ℕ₁, ℕ₂
-- statement:
--   This file sets up the model of Lu, Zhong, Ho, Tang and Cao.
--
--   Write $\mathcal D=\{0,1\}$. A **state** is $x=(x_1,\dots,x_n)\in\mathcal D^n$ and an **input value** is $u=(u_1,\dots,u_m)\in\mathcal D^m$. Fix the delay length $\mu\ge 1$. A **trajectory** (of length $\mu$) is a tuple $X(t)=(x(t-\mu+1),\dots,x(t))$ of $\mu$ consecutive states; its last entry $x(t)$ is the **current state**. The **delayed Boolean control network** (2.2) is
--
--   $$
--   x_i(t+1)=f_i\big(u(t),\,x(t-\mu+1),\dots,x(t)\big),\qquad i=1,\dots,n,
--   $$
--
--   with arbitrary Boolean functions $f_i:\mathcal D^{m+\mu n}\to\mathcal D$, packaged as one map $F$ with $x(t+1)=F(u(t),X(t))$. One step maps $X(t)$ under the input $u(t)$ to $X(t+1)=(x(t-\mu+2),\dots,x(t),x(t+1))$. For an initial trajectory $X(0)$ and a control sequence $U=(u(0),\dots,u(k-1))$, $y(i)=X(i)$ denotes the trajectory after $i\le k$ steps.
--
--   The file defines:
--
--   1. **Definition 3.1.** The $k$-step trajectory reachable set $R^t_k(X(0))$ (trajectories equal to $X(k)$ for some control sequence of length $k$), the reachable set $R^t(X(0))=\bigcup_{k\ge1}R^t_k(X(0))$, and **trajectory controllability**: $R^t(X(0))$ is the set of all trajectories for every $X(0)$.
--   2. **Forbidden trajectories (p. 483).** For a set $C_t$ of trajectories, a control sequence of length $k$ steers $y_a$ to $y_b$ **while avoiding $C_t$** if $y(k)=y_b$ and $y(i)\notin C_t$ for $i=0,1,\dots,k$; $\mathbb N_1(k;y_a,y_b,C_t)$ counts these sequences and $\mathbb N_1(k;y_a,y_b)$ counts the unrestricted ones.
--   3. **Definition 3.11.** The network is **trajectory controllable under the forbidden set $C_t$** if for all trajectories $a,b\notin C_t$ there are $k\ge 0$ and a control sequence of length $k$ steering $a$ to $b$ while avoiding $C_t$.
--   4. **Definition 4.1.** The $k$-step state reachable set $R^s_k(a)$ (states equal to $x(k)$ for some control sequence of length $k$), $R^s(a)=\bigcup_{k\ge1}R^s_k(a)$, and **state controllability**: $R^s(a)=\mathcal D^n$ for every initial trajectory $a$.
--   5. **States and trajectories (pp. 488–489).** $\Xi^p_\mu$, the trajectories whose current state is $p$ (eq. (4.3)); $\Xi^{C_s}$, the trajectories containing a state of a forbidden-state set $C_s$; $\mathbb N_2(k;a,b_s)$, the number of control sequences of length $k$ from $a$ with $x(k)=b_s$; and $\mathbb N_2(k;a,b_s,C_s)$, those among them for which no state $x(i)$, $i=1-\mu,\dots,k$, lies in $C_s$.
--
--   These are the dynamic notions against which every counting and irreducibility result of the paper is stated.
--
--   **Formalization Note** States are `Fin n → Bool` with `true` for the paper's 1 ($\delta^1_2$); a trajectory is `Fin μ → State n` with index 0 the oldest state $x(t-\mu+1)$ and index $\mu-1$ the current state. The paper works with the vector $y(t)=\ltimes_{i=t-\mu+1}^t x(i)\in\Delta_{2^{\mu n}}$, which is in bijection with the trajectory (Lemma 2.6); here the trajectory itself is used. The step range of Definition 3.1 and 4.1 is $k\ge1$ (the paper writes $\bigcup_{j=1}^\infty$ in the proof of Theorem 3.3 and "$k>0$" in Definition 4.1); Definition 3.11 has $k\ge0$. "Avoiding $C_s$" is read as the theorem's own middle term $\mathbb N_1(k;a,b,\Xi^{C_s})$ of (5.1): no trajectory $y(0),\dots,y(k)$ contains a forbidden state. `trajAt` stays at $X(k)$ after step $k$; only indices $0,\dots,k$ are used.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, pp. 478, 480-481, 483, 486, 488-490, Eq. (2.2), Definitions 3.1, 3.11, 4.1, Eq. (4.3), definitions of ℕ₁ (p. 483), ℕ₂ and Ξ^{C_s} (p. 489)

import Mathlib

namespace DelayedBCN.Controllability

/-- A state `x(t) = (x_1(t), …, x_n(t)) ∈ 𝒟^n`; `true` is the paper's `1` (`δ^1_2`). -/
abbrev State (n : ℕ) := Fin n → Bool

/-- An input value `u(t) = (u_1(t), …, u_m(t)) ∈ 𝒟^m`. -/
abbrev Input (m : ℕ) := Fin m → Bool

/-- A trajectory of length `μ`, `X(t) = (x(t-μ+1), …, x(t))`: index `0` is the oldest state
`x(t-μ+1)`, index `μ-1` the current state `x(t)`. -/
abbrev Traj (μ n : ℕ) := Fin μ → State n

/-- The delayed Boolean control network (2.2): the `n` Boolean update functions
`f_i : 𝒟^{m+μn} → 𝒟` packaged as one map `F u X = x(t+1)` of the input `u(t)` and the
current trajectory `X(t)`. The `f_i` are arbitrary. -/
abbrev Network (μ n m : ℕ) := Input m → Traj μ n → State n

/-- One step of (2.2) on trajectories: `(x(t-μ+1), …, x(t))` is mapped under the input `u(t)` to
`(x(t-μ+2), …, x(t), x(t+1))` with `x(t+1) = F u(t) X(t)`. -/
def step {μ n m : ℕ} (F : Network μ n m) (u : Input m) (X : Traj μ n) : Traj μ n :=
  fun i => if h : i.val + 1 < μ then X ⟨i.val + 1, h⟩ else F u X

/-- The trajectory `y(i) = X(i)` after `i` steps from the initial trajectory `X0 = X(0)` under the
control sequence `U = (u(0), …, u(k-1))`; for `i ≥ k` it stays at `X(k)`. -/
def trajAt {μ n m k : ℕ} (F : Network μ n m) (X0 : Traj μ n) (U : Fin k → Input m) :
    ℕ → Traj μ n
  | 0 => X0
  | i + 1 => if h : i < k then step F (U ⟨i, h⟩) (trajAt F X0 U i) else trajAt F X0 U i

/-- The current state `x(t)` of a trajectory `X(t)` (its last entry). -/
def currentState {μ n : ℕ} [NeZero μ] (X : Traj μ n) : State n :=
  X ⟨μ - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne μ)) Nat.one_pos⟩

/-! ### Definition 3.1 (trajectory controllability) -/

/-- `Xd` is trajectory reachable from `X0` at the `k`th step: some control sequence
`U(k) = (u(0), …, u(k-1))` gives `X(k) = Xd`. -/
def IsTrajReachableAt {μ n m : ℕ} (F : Network μ n m) (X0 Xd : Traj μ n) (k : ℕ) : Prop :=
  ∃ U : Fin k → Input m, trajAt F X0 U k = Xd

/-- The `k`-step trajectory reachable set `R^t_k(X0)`. -/
def trajReachableSetAt {μ n m : ℕ} (F : Network μ n m) (X0 : Traj μ n) (k : ℕ) :
    Set (Traj μ n) :=
  {Xd | IsTrajReachableAt F X0 Xd k}

/-- The trajectory reachable set `R^t(X0) = ⋃_{k ≥ 1} R^t_k(X0)`. -/
def trajReachableSet {μ n m : ℕ} (F : Network μ n m) (X0 : Traj μ n) : Set (Traj μ n) :=
  ⋃ k : ℕ, ⋃ (_ : 1 ≤ k), trajReachableSetAt F X0 k

/-- The network is trajectory controllable from `X0`: `R^t(X0)` is every trajectory. -/
def TrajControllableFrom {μ n m : ℕ} (F : Network μ n m) (X0 : Traj μ n) : Prop :=
  trajReachableSet F X0 = Set.univ

/-- The network is trajectory controllable: trajectory controllable from every initial
trajectory. -/
def TrajControllable {μ n m : ℕ} (F : Network μ n m) : Prop :=
  ∀ X0 : Traj μ n, TrajControllableFrom F X0

/-! ### Forbidden trajectories (p. 483) and Definition 3.11 -/

/-- The control sequence `U` of length `k` steers `ya` to `yb` while avoiding `Ct`:
`y(k) = yb` and `y(i) ∉ Ct` for `i = 0, 1, …, k`. -/
def SteersAvoiding {μ n m k : ℕ} (F : Network μ n m) (ya yb : Traj μ n)
    (Ct : Finset (Traj μ n)) (U : Fin k → Input m) : Prop :=
  trajAt F ya U k = yb ∧ ∀ i : Fin (k + 1), trajAt F ya U i ∉ Ct

/-- `ℕ₁(k; ya, yb, Ct)`: the number of control sequences of length `k` steering `ya` to `yb` while
avoiding `Ct` (i.e. satisfying `SteersAvoiding F ya yb Ct`). -/
def numAvoiding {μ n m : ℕ} (F : Network μ n m) (k : ℕ) (ya yb : Traj μ n)
    (Ct : Finset (Traj μ n)) : ℕ :=
  (Finset.univ.filter (fun U : Fin k → Input m =>
    trajAt F ya U k = yb ∧ ∀ i : Fin (k + 1), trajAt F ya U i ∉ Ct)).card

/-- `ℕ₁(k; ya, yb)`: the number of control sequences of length `k` steering `ya` to `yb`
without any restriction. -/
def numSteering {μ n m : ℕ} (F : Network μ n m) (k : ℕ) (ya yb : Traj μ n) : ℕ :=
  (Finset.univ.filter (fun U : Fin k → Input m => trajAt F ya U k = yb)).card

/-- Definition 3.11: trajectory controllable under the forbidden set `Ct` — for all
`a, b ∉ Ct` there are `k ≥ 0` and a control sequence of length `k` steering `a` to `b` while
avoiding `Ct`. -/
def TrajControllableUnder {μ n m : ℕ} (F : Network μ n m) (Ct : Finset (Traj μ n)) : Prop :=
  ∀ a b : Traj μ n, a ∉ Ct → b ∉ Ct →
    ∃ k : ℕ, ∃ U : Fin k → Input m, SteersAvoiding F a b Ct U

/-! ### States: Definition 4.1, `Ξ^p_μ`, `ℕ₂`, forbidden states -/

/-- Definition 4.1 (1)–(2): the `k`-step state reachable set `R^s_k(a)`: states `xd` with
`x(k) = xd` for some control sequence of length `k`. -/
def stateReachableSetAt {μ n m : ℕ} [NeZero μ] (F : Network μ n m) (X0 : Traj μ n) (k : ℕ) :
    Set (State n) :=
  {xd | ∃ U : Fin k → Input m, currentState (trajAt F X0 U k) = xd}

/-- Definition 4.1 (3): `R^s(a) = ⋃_{k ≥ 1} R^s_k(a)`. -/
def stateReachableSet {μ n m : ℕ} [NeZero μ] (F : Network μ n m) (X0 : Traj μ n) :
    Set (State n) :=
  ⋃ k : ℕ, ⋃ (_ : 1 ≤ k), stateReachableSetAt F X0 k

/-- Definition 4.1 (4)–(5): state controllable from every initial trajectory. -/
def StateControllable {μ n m : ℕ} [NeZero μ] (F : Network μ n m) : Prop :=
  ∀ X0 : Traj μ n, stateReachableSet F X0 = Set.univ

/-- `Ξ^p_μ`: the trajectories whose current (last) state is `p`, eq. (4.3). -/
def xiLast {μ n : ℕ} [NeZero μ] (p : State n) : Finset (Traj μ n) :=
  Finset.univ.filter (fun X => currentState X = p)

/-- `Ξ^{C_s}`: the trajectories containing some forbidden state of `Cs` at some position. -/
def xiForbidden {μ n : ℕ} (Cs : Finset (State n)) : Finset (Traj μ n) :=
  Finset.univ.filter (fun X => ∃ i, X i ∈ Cs)

/-- `ℕ₂(k; a, bs)`: the number of control sequences of length `k` steering the initial trajectory
`a` to `x(k) = bs`. -/
def numToState {μ n m : ℕ} [NeZero μ] (F : Network μ n m) (k : ℕ) (a : Traj μ n)
    (bs : State n) : ℕ :=
  (Finset.univ.filter (fun U : Fin k → Input m => currentState (trajAt F a U k) = bs)).card

/-- `ℕ₂(k; a, bs, Cs)`: the number of control sequences of length `k` steering `a` to
`x(k) = bs` while avoiding the forbidden states `Cs`: no state `x(i)`, `i = 1-μ, …, k`, lies in
`Cs` (equivalently, no trajectory `y(0), …, y(k)` contains a state of `Cs`). -/
def numToStateAvoiding {μ n m : ℕ} [NeZero μ] (F : Network μ n m) (k : ℕ) (a : Traj μ n)
    (bs : State n) (Cs : Finset (State n)) : ℕ :=
  (Finset.univ.filter (fun U : Fin k → Input m =>
    currentState (trajAt F a U k) = bs ∧ ∀ i : Fin (k + 1), ∀ j : Fin μ, trajAt F a U i j ∉ Cs)).card

end DelayedBCN.Controllability


