-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Restless_Instance
-- name    : OptimalQueuingComplexity_Restless_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T11:55:32.285748+00:00
-- url     : https://prove2.me/theorems/dad38602-4188-4a6c-a760-ef63a48168e1
-- title:
--   RESTLESS BANDITS with deterministic transition rules — instances, trajectories and average cost
-- statement:
--   An instance consists of $n$ bandits on a common finite state space $S = \{1, \dots, M\}$; the initial states $X_1(0), \dots, X_n(0) \in S$; two deterministic transition rules $P, Q : S \to S$; rational cost functions $c, d : S \to \mathbb{Q}$; and a rational threshold $K$.
--
--   A **policy** is a map $\pi : S^n \to \{1, \dots, n\}$. Under $\pi$, at each time $t = 0, 1, \dots$ the bandit $i(t) = \pi(X_1(t), \dots, X_n(t))$ is played; it moves by $P$ and every other bandit moves by $Q$:
--   $$X_i(t+1) = \begin{cases} P\bigl(X_i(t)\bigr), & i = i(t),\\ Q\bigl(X_i(t)\bigr), & i \ne i(t).\end{cases}$$
--   The cost at time $t$ is $C(t) = c\bigl(X_{i(t)}(t)\bigr) + \sum_{i \ne i(t)} d\bigl(X_i(t)\bigr)$, and the **average cost** of $\pi$ is
--   $$J(\pi) = \limsup_{T \to \infty} \frac{1}{T} \sum_{t=1}^{T} C(t).$$
--
--   This is the restless bandit model of Whittle (1988) in the special case, used by the paper, in which the transition probability matrices $P$ and $Q$ are deterministic. The classical multi-armed bandit is the case $Q = \mathrm{id}$, $d = 0$.
--
--   **Formalization Note.** Bandits are `Fin n` and states are `Fin M` (both 0-based). The trajectory is deterministic, so the paper's expectation $E[C(t)]$ is $C(t)$ itself and no probability space is used. The average is the real `limsup` of the running averages; they are bounded by $n \max_s \max(|c(s)|, |d(s)|)$, so the `limsup` is the true one. The sum starts at $t = 1$ as printed; including $t = 0$ would not change the limit superior. Policies are all deterministic stationary maps, as on the page. The encoding is $\mathrm{encNat}(n)$, $\mathrm{encNat}(M)$, the tables of $P$, $Q$, $c$, $d$, the initial states and $K$.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 303, Section 3 (the RESTLESS BANDITS problem, deterministic special case)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

namespace OptimalQueuingComplexity.Restless

/-- An instance of **RESTLESS BANDITS with deterministic transition rules**
(Papadimitriou & Tsitsiklis 1999, Section 3, p. 303): `n` bandits evolving on a common finite
state space `S = {1, …, M}`, the initial state of each bandit, a deterministic transition rule
`P : S → S` for the bandit that is played and another `Q : S → S` for every bandit that is not
played (the paper's transition matrices `P`, `Q` in the deterministic special case), the
rational cost functions `c` (played) and `d` (not played) on `S`, and a rational threshold `K`
for the decision version.

* The bandits `1, …, n` are `Fin n` (bandit `i + 1` is the index `i`).
* The states `1, …, M` are `Fin M` (state `s + 1` is the index `s`). -/
structure Instance where
  /-- number of bandits -/
  n : ℕ
  /-- number of states; `S = Fin M` -/
  M : ℕ
  /-- the transition rule of the bandit that is played -/
  P : Fin M → Fin M
  /-- the transition rule of every bandit that is not played -/
  Q : Fin M → Fin M
  /-- the per-step cost `c(s)` of the played bandit in state `s` -/
  c : Fin M → ℚ
  /-- the per-step cost `d(s)` of a bandit not played, in state `s` -/
  d : Fin M → ℚ
  /-- the initial states `X_i(0)` -/
  x0 : Fin n → Fin M
  /-- the threshold of the decision version -/
  K : ℚ

/-- The binary encoding of an instance: `encNat n`, `encNat M`, then the tables of `P`, `Q`
(`encFin` entries), `c`, `d` (`encRat` entries), `x0` (`encFin` entries), and finally `encRat K`.
Its length is polynomial in the bit size of the instance and conversely. -/
def Instance.enc (I : Instance) : List Bool :=
  encNat I.n ++ encNat I.M ++ encTable encFin I.P ++ encTable encFin I.Q ++
    encTable encRat I.c ++ encTable encRat I.d ++ encTable encFin I.x0 ++ encRat I.K

/-- A **policy** `π : S^n → {1, …, n}`: a deterministic stationary rule choosing the bandit
to be played as a function of the current states of all bandits, `i(t) = π(X_1(t), …, X_n(t))`. -/
abbrev Policy (I : Instance) : Type := (Fin I.n → Fin I.M) → Fin I.n

/-- The joint state `(X_1(t), …, X_n(t))` at time `t` under policy `π`: `X(0) = x0`, and
`X_i(t+1) = P(X_i(t))` for the played bandit `i = π(X(t))`, `X_i(t+1) = Q(X_i(t))` for every
other bandit. The dynamics are deterministic, so no probability space is needed. -/
def Instance.state (I : Instance) (π : Policy I) : ℕ → Fin I.n → Fin I.M
  | 0 => I.x0
  | t + 1 => fun i =>
      if i = π (I.state π t) then I.P (I.state π t i) else I.Q (I.state π t i)

/-- The cost incurred at time `t`:
`C(t) = c(X_{i(t)}(t)) + ∑_{i ≠ i(t)} d(X_i(t))` with `i(t) = π(X(t))`. -/
def Instance.cost (I : Instance) (π : Policy I) (t : ℕ) : ℚ :=
  I.c (I.state π t (π (I.state π t))) +
    ∑ i ∈ Finset.univ.filter (fun i => i ≠ π (I.state π t)), I.d (I.state π t i)

/-- The average cost of a policy, `limsup_{T → ∞} (1/T) ∑_{t=1}^{T} C(t)` (the expectation of
the paper's formula is trivial: the dynamics are deterministic). The running averages are
bounded in absolute value by `n · max_s max(|c(s)|, |d(s)|)`, so the real `limsup` is the true
one (no junk value). -/
noncomputable def Instance.avgCost (I : Instance) (π : Policy I) : ℝ :=
  Filter.limsup (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, (I.cost π t : ℝ)) Filter.atTop

end OptimalQueuingComplexity.Restless


