-- Prove2me | Definitions.Def_MonotoneDP_Increase_Model
-- name    : MonotoneDP_Increase_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:54:56.889862+00:00
-- url     : https://prove2.me/theorems/f3e9f40d-607d-47f6-a5a9-1a42f84847d6
-- title:
--   Bertsekas's abstract DP model: constraint sets U(x), monotone mapping H, terminal function J̄; T_μ, T, policy compositions, J_π, J*, J_N and J_∞
-- statement:
--   This file fixes the abstract dynamic programming model of Bertsekas (1977), Sections 2–3, and the value functions built from it.
--
--   **The model.** A model consists of
--
--   1. a nonempty **state space** $S$ and a **control space** $C$;
--   2. for each $x\in S$ a nonempty **control constraint set** $U(x)\subseteq C$;
--   3. a mapping $H: S\times C\times F\to[-\infty,+\infty]$, where $F$ is the set of all extended-real-valued functions $J:S\to[-\infty,\infty]$, ordered pointwise;
--   4. a **terminal function** $\bar J\in F$ with $\bar J(x)>-\infty$ for every $x\in S$.
--
--   The **monotonicity assumption**, in force throughout the paper, is part of the model: for every $x\in S$, $u\in U(x)$ and $J,J'\in F$,
--
--   $$J\le J'\ \Longrightarrow\ H(x,u,J)\le H(x,u,J').$$
--
--   **Policies.** $M$ is the set of functions $\mu:S\to C$ with $\mu(x)\in U(x)$ for all $x$, and $\Pi$ is the set of sequences $\pi=\{\mu_0,\mu_1,\dots\}$ with every $\mu_k\in M$. The policy $\{\mu,\mu,\dots\}$ is called **stationary**.
--
--   **Operators.** For $\mu\in M$ and $J\in F$,
--
--   $$T_\mu(J)(x)=H\bigl(x,\mu(x),J\bigr),\qquad T(J)(x)=\inf_{u\in U(x)}H(x,u,J)\qquad(x\in S),$$
--
--   and $T^k$ is the $k$-fold composition of $T$, with $T^0(J)=J$. For $\pi\in\Pi$, $(T_{\mu_0}T_{\mu_1}\cdots T_{\mu_{N-1}})(J)$ is the composition in which $T_{\mu_{N-1}}$ is applied to $J$ first and $T_{\mu_0}$ last; for $N=0$ it is $J$.
--
--   **Value functions.**
--
--   $$J_\pi(x)=\lim_{N\to\infty}(T_{\mu_0}\cdots T_{\mu_{N-1}})(\bar J)(x),\qquad J^*(x)=\inf_{\pi\in\Pi}J_\pi(x),$$
--
--   $J_\mu=J_{\{\mu,\mu,\dots\}}$, the $N$-stage optimal value $J_N(x)=\inf_{\pi\in\Pi}(T_{\mu_0}\cdots T_{\mu_{N-1}})(\bar J)(x)$, and the limit of the dynamic programming algorithm
--
--   $$J_\infty(x)=\lim_{N\to\infty}T^N(\bar J)(x).$$
--
--   A policy $\pi^*$ is **optimal** if $J_{\pi^*}=J^*$; a stationary policy $\{\mu^*,\mu^*,\dots\}$ is optimal if $J_{\mu^*}=J^*$.
--
--   Every statement of the mission is phrased in this model.
--
--   **Formalization Note** $F$ is `S → EReal`. The limits defining $J_\pi$ and $J_\infty$ are `limUnder atTop`, which is the true limit whenever the sequence converges; under Assumption I (the only regime in which the mission uses them) both sequences are nondecreasing, so the limit exists in $[-\infty,\infty]$. Nonemptiness of $C$ follows from that of $S$ and of each $U(x)$. The infimum defining $T$ ranges over $U(x)$ only, and $J^*$ over admissible policies only.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), pp. 441–442 (PDF pp. 4–5), Section 2 items 1–7, eqs. (15)–(16), Monotonicity assumption; Section 3, eqs. (17), (19); p. 448 (PDF p. 11), eq. (36); p. 455 (PDF p. 18), eq. (49). DOI 10.1137/0315031

import Mathlib

namespace MonotoneDP.Increase

open Filter Topology

/-- The abstract dynamic programming model of Bertsekas (1977), Sections 2–3 (pp. 441–442).

* `S`, `C` are the state and control spaces; `S` is nonempty (Section 2, item 1), and `C` is
  nonempty because every `U x` is.
* `U x ⊆ C` is the nonempty control constraint set at `x` (item 2).
* `H : S → C → (S → EReal) → EReal` is the given mapping `H : S × C × F → [−∞, +∞]` (item 7),
  where `F = S → EReal` is the set of extended-real-valued functions on `S` (item 4).
* `mono` is the Monotonicity assumption, in effect throughout the paper (p. 441).
* `Jbar` is the given terminal function `J̄ ∈ F` with `J̄(x) > −∞` for all `x` (Section 3). -/
structure Model (S C : Type*) where
  S_nonempty : Nonempty S
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  H : S → C → (S → EReal) → EReal
  mono : ∀ x, ∀ u ∈ U x, ∀ J J' : S → EReal, J ≤ J' → H x u J ≤ H x u J'
  Jbar : S → EReal
  Jbar_ne_bot : ∀ x, Jbar x ≠ ⊥

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The set `M` of admissible selectors: functions `μ : S → C` with `μ(x) ∈ U(x)` for all `x`. -/
def Selector : Type _ := {μ : S → C // ∀ x, μ x ∈ m.U x}

/-- The set `Π` of policies: sequences `π = {μ₀, μ₁, …}` of admissible selectors. -/
def Policy : Type _ := ℕ → m.Selector

/-- The stationary policy `{μ, μ, …}`. -/
def stationary (μ : m.Selector) : m.Policy := fun _ => μ

/-- `T_μ(J)(x) = H(x, μ(x), J)`, eq. (15). -/
def Tmu (μ : m.Selector) (J : S → EReal) : S → EReal := fun x => m.H x (μ.1 x) J

/-- `T(J)(x) = inf_{u ∈ U(x)} H(x, u, J)`, eq. (16). `T^k` is `m.T^[k]`, with `T^0 = id`. -/
noncomputable def T (J : S → EReal) : S → EReal := fun x => ⨅ u ∈ m.U x, m.H x u J

/-- The composition `(T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J)`: `T_{μ_{N−1}}` is applied to `J` first and
`T_{μ₀}` last; `comp π 0 J = J`. -/
def comp (π : m.Policy) : ℕ → (S → EReal) → (S → EReal)
  | 0, J => J
  | N + 1, J => comp π N (m.Tmu (π N) J)

/-- The value function of a policy, eq. (17):
`J_π(x) = lim_{N → ∞} (T_{μ₀} ⋯ T_{μ_{N−1}})(J̄)(x)`, as `limUnder`. Under Assumption I the
sequence is nondecreasing in `N` (eq. (24)), so the limit exists in `[−∞, ∞]`; every result
about `J_π` is stated under Assumption I. -/
noncomputable def Jpi (π : m.Policy) : S → EReal :=
  fun x => limUnder atTop (fun N => m.comp π N m.Jbar x)

/-- `J_μ`, the value function of the stationary policy `{μ, μ, …}`. -/
noncomputable def Jmu (μ : m.Selector) : S → EReal := m.Jpi (m.stationary μ)

/-- The optimal value function, eq. (19): `J*(x) = inf_{π ∈ Π} J_π(x)`. -/
noncomputable def Jstar : S → EReal := fun x => ⨅ π : m.Policy, m.Jpi π x

/-- The optimal value function of the `N`-stage problem, eq. (36):
`J_N(x) = inf_{π ∈ Π} (T_{μ₀} ⋯ T_{μ_{N−1}})(J̄)(x)`. -/
noncomputable def JN (N : ℕ) : S → EReal := fun x => ⨅ π : m.Policy, m.comp π N m.Jbar x

/-- The limit of the DP algorithm, eq. (49): `J_∞(x) = lim_{N → ∞} T^N(J̄)(x)`, as `limUnder`.
Under Assumption I the sequence `T^N(J̄)(x)` is nondecreasing, so the limit exists. -/
noncomputable def Jinf : S → EReal := fun x => limUnder atTop (fun N => (m.T)^[N] m.Jbar x)

end Model

end MonotoneDP.Increase


