-- Prove2me | Definitions.Def_KumarSeidman_Supervisor_System
-- name    : KumarSeidman_Supervisor_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:19.161797+00:00
-- url     : https://prove2.me/theorems/97b99c26-ba62-4aa2-8c57-c7c3f3097cbc
-- title:
--   Manufacturing system data, load $\rho_m$, capacity condition (1) and set-up allowance (§I, §II, §V)
-- statement:
--   A **manufacturing system** in the sense of Kumar and Seidman consists of $P$ part types and $M$ machines.
--
--   1. Part type $p$ follows a route of $n_p\ge 1$ operations; its $i$-th operation is performed by machine $\mu_{p,i}$. A route may revisit a machine.
--   2. Parts of type $p$ arrive from outside at the constant rate $d_p>0$.
--   3. Each part of type $p$ needs $\tau_{p,i}>0$ time units at machine $\mu_{p,i}$ for its $i$-th operation.
--   4. Parts waiting for their $i$-th operation sit in the **buffer** $b_{p,i}$. Machine $m$ serves the buffers $B_m=\{b_{p,i}:\mu_{p,i}=m\}$, and switching it from buffer $b$ to buffer $b'$ costs a **set-up time** $\delta_{b,b'}\ge 0$. Staying on the same buffer costs nothing, so $\delta_{b,b}=0$.
--
--   The **load** of machine $m$ and the **capacity condition** (1) are
--   $$
--   \rho_m:=\sum_{(p,i):\,\mu_{p,i}=m} d_p\tau_{p,i},\qquad \rho_m<1\quad\text{for }1\le m\le M .
--   $$
--   The file also defines the **set-up allowance** of machine $m$ that appears in (24) and (26),
--   $$
--   \sum_{b\in B_m}\ \max_{b'\in B_m}\ \delta_{b',b},
--   $$
--   which is the time needed to set up once for every buffer of $B_m$, each time from the worst predecessor. For a machine with no buffers the sum is $0$.
--
--   These objects are the data of every statement in this mission. The capacity condition is necessary for stability of any scheduling policy; Theorem 2 of the paper shows that it is also sufficient once the supervisor is applied.
--
--   **Formalization Note** Part types are `Fin P` and machines `Fin M`. The paper's index $i$ is the Lean index $i-1$ (`Fin (n p)`). A buffer is a dependent pair `⟨p, i⟩`. The requirement $\delta_{b,b}=0$ records the paper's convention that a set-up is paid only when a machine *switches* to a different buffer. The maximum over $B_m$ is `Finset.sup'` on the nonempty set $B_m\ni b$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 289, §I items 1–4; p. 290, (1); p. 296, (24) and (26)

import Mathlib

namespace KumarSeidman.Supervisor

/-- A manufacturing system in the sense of Kumar–Seidman (1990), §I, items 1–4 (p. 289).
There are `P` part types (`Fin P`) and `M` machines (`Fin M`). Part type `p` visits the
`n p ≥ 1` machines `μ p 0, μ p 1, …, μ p (n p - 1)` in this order (the paper's
`μ_{p,1}, …, μ_{p,n_p}`; Lean index `i` is the paper's index `i + 1`); revisits are allowed.
It enters the system at rate `d p > 0`, its `i`-th operation takes `τ p i > 0` time units per
part, and switching a machine from buffer `b` to buffer `b'` costs a set-up time
`δ b b' ≥ 0`; continuing on the same buffer costs nothing (`δ b b = 0`). -/
structure System (P M : ℕ) where
  n : Fin P → ℕ
  n_pos : ∀ p, 0 < n p
  μ : (p : Fin P) → Fin (n p) → Fin M
  d : Fin P → ℝ
  d_pos : ∀ p, 0 < d p
  τ : (p : Fin P) → Fin (n p) → ℝ
  τ_pos : ∀ p i, 0 < τ p i
  δ : (Σ p : Fin P, Fin (n p)) → (Σ p : Fin P, Fin (n p)) → ℝ
  δ_nonneg : ∀ b b', 0 ≤ δ b b'
  δ_self : ∀ b, δ b b = 0

variable {P M : ℕ}

/-- The buffers `b_{p,i}`: one per (part type, stage of its route). -/
abbrev Buffer (S : System P M) := Σ p : Fin P, Fin (S.n p)

/-- The machine `μ_{p,i}` serving buffer `b = b_{p,i}`. -/
def System.mach (S : System P M) (b : Buffer S) : Fin M := S.μ b.1 b.2

/-- The processing time `τ_{p,i}` of buffer `b = b_{p,i}`. -/
def System.tau (S : System P M) (b : Buffer S) : ℝ := S.τ b.1 b.2

/-- `B_m = {b_{p,i} : μ_{p,i} = m}`, the buffers served by machine `m`. -/
def System.B (S : System P M) (m : Fin M) : Finset (Buffer S) :=
  Finset.univ.filter (fun b => S.mach b = m)

/-- The buffer preceding `b_{p,i}` on the route of part type `p`, i.e. `b_{p,i-1}`;
`none` for the first buffer of a route (parts arrive there from outside). -/
def System.prev (S : System P M) (b : Buffer S) : Option (Buffer S) :=
  if h : 0 < b.2.val then some ⟨b.1, ⟨b.2.val - 1, by omega⟩⟩ else none

/-- `ρ_m = Σ_{(p,i) : μ_{p,i} = m} d_p τ_{p,i}`, the load of machine `m` in (1) (p. 290). -/
noncomputable def System.rho (S : System P M) (m : Fin M) : ℝ :=
  ∑ b ∈ S.B m, S.d b.1 * S.tau b

/-- The capacity condition (1) (p. 290): `ρ_m < 1` for every machine `m`. -/
def System.CapacityCondition (S : System P M) : Prop := ∀ m, S.rho m < 1

/-- `Σ_{b ∈ B_m} max_{b' ∈ B_m} δ_{b',b}`, the set-up allowance of (24) and (26) (p. 296).
The maximum is over the nonempty set `B_m ∋ b` (`Finset.sup'`); the sum is `0` when `B_m` is
empty. -/
noncomputable def System.setupSum (S : System P M) (m : Fin M) : ℝ :=
  ∑ b ∈ (S.B m).attach, (S.B m).sup' ⟨b.1, b.2⟩ (fun b' => S.δ b' b.1)

end KumarSeidman.Supervisor


