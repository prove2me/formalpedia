-- Prove2me | Definitions.Def_KumarSeidman_CAF_System
-- name    : KumarSeidman_CAF_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:28.652983+00:00
-- url     : https://prove2.me/theorems/12f441df-cef5-43f5-a13d-c132677884fa
-- title:
--   Manufacturing systems with set-up times, the graph of machines, and the capacity conditions (1) and (14)
-- statement:
--   This file fixes the manufacturing systems of Kumar and Seidman (§I, items 1–4, p. 289) and the objects of the sufficient condition of Theorem 1 (§IV, pp. 293–294).
--
--   **Systems.** There are $P$ part types and $M$ machines. Part type $p$ follows a fixed route of $n_p\ge 1$ stages: at its $i$-th stage it is served by machine $\mu_{p,i}$, where it requires the processing time $\tau_{p,i}>0$ per part; while waiting there it is stored in buffer $b_{p,i}$. Routes may revisit machines. Parts of type $p$ enter the system at rate $d_p>0$. Machine $m$ serves the buffers $B_m=\{b_{p,i}:\mu_{p,i}=m\}$, and switching it from buffer $b$ to another buffer $b'\in B_m$ costs a set-up time $\delta_{b,b'}\ge 0$.
--
--   **Loads.** The capacity condition (1) and the more stringent condition (14) are
--
--   $$
--   \rho_m=\sum_{(p,i):\,\mu_{p,i}=m} d_p\,\tau_{p,i}<1,\qquad \rho'_m=\sum_{(p,i):\,\mu_{p,i}=m} d'_{p,i}\,\tau_{p,i}<1\qquad\text{for every machine } m .
--   $$
--
--   **The graph of machines.** There is an arc $m\to m'$ if $m\neq m'$ and some part type visits $m'$ immediately after $m$ (self-loops are removed). $m'$ is *reachable* from $m$ if there is a directed path from $m$ to $m'$ (by convention $m$ is reachable from itself), and $m,m'$ are *diconnected*, $m\leftrightarrow m'$, if each is reachable from the other.
--
--   **Modified input rates (11)–(13).** For a buffer $b_{p,i}$, $\lambda_{p,i}$ is the last stage $j<i$ of route $p$ with $\mu_{p,j}\ne\mu_{p,i}$, and $\lambda_{p,i}=0$ if there is none (all stages $j\le i$ are at $\mu_{p,i}$). The prior machine is $\pi_{p,i}=\varphi$ if $\lambda_{p,i}=0$ and $\pi_{p,i}=\mu_{p,\lambda_{p,i}}$ otherwise, and
--
--   $$
--   d'_{p,i}=\begin{cases}1/\tau_{p,\lambda_{p,i}} & \text{if } \pi_{p,i}\ne\varphi \text{ and } \pi_{p,i}\leftrightarrow\mu_{p,i},\\ d_p & \text{otherwise.}\end{cases}
--   $$
--
--   $d'_{p,i}$ is the peak rate at which parts can reach $b_{p,i}$ from a machine in a common cycle with $\mu_{p,i}$, and the average rate $d_p$ otherwise.
--
--   **Formalization Note** Part types, machines and stages are 0-based (`Fin P`, `Fin M`, `Fin (n p)`); the paper's stage $i$ is Lean's `i - 1`. A buffer is a pair `⟨p, i⟩`. `lam` takes values in `WithBot (Fin (n p))`, with `⊥` for the paper's $\lambda_{p,i}=0$, so that "no prior stage" never collides with the first stage. Set-up times are given for all pairs of buffers; only pairs of distinct buffers of one machine are ever used. Reachability is the reflexive–transitive closure of the arc relation.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 289, §I items 1–4; p. 290, (1); p. 293, arc set A; p. 294, reachability, Theorem 1 (11)–(14)

import Mathlib

namespace KumarSeidman.CAF

/-- A manufacturing system in the sense of Kumar–Seidman (1990), §I, items 1–4 (p. 289).
There are `P` part types (`Fin P`) and `M` machines (`Fin M`). Part type `p` visits the
`n p ≥ 1` machines `μ p 0, μ p 1, …, μ p (n p - 1)` in this order (the paper's
`μ_{p,1}, …, μ_{p,n_p}`; Lean index `i` is the paper's index `i + 1`); revisits are allowed.
It enters the system at rate `d p > 0`, its `i`-th operation takes `τ p i > 0` time units per
part, and switching machine `μ_b` from buffer `b` to buffer `b'` costs a set-up time
`δ b b' ≥ 0` (only used for `b ≠ b'` served by the same machine). -/
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

/-- The arc set `A` of §IV (p. 293): `(m, m') ∈ A` iff `m ≠ m'` and some part type visits `m'`
immediately after `m` (self-loops removed). -/
def System.Arc (S : System P M) (m m' : Fin M) : Prop :=
  m ≠ m' ∧ ∃ (p : Fin P) (i : Fin (S.n p)) (h : i.val + 1 < S.n p),
    S.μ p i = m ∧ S.μ p ⟨i.val + 1, h⟩ = m'

/-- Reachability `m → m'`: a directed path (possibly empty) from `m` to `m'` in `G = (V, A)`. -/
def System.Reach (S : System P M) (m m' : Fin M) : Prop :=
  Relation.ReflTransGen S.Arc m m'

/-- `m ↔ m'` ("diconnected"): `m → m'` and `m' → m`; by convention `m ↔ m`. -/
def System.Dicon (S : System P M) (m m' : Fin M) : Prop :=
  S.Reach m m' ∧ S.Reach m' m

/-- `λ_{p,i}` of (11) (p. 294): the last stage `j < i` of route `p` whose machine differs
from `μ_{p,i}`, or `⊥` (the paper's `λ_{p,i} = 0`) if all stages `j ≤ i` are at `μ_{p,i}`. -/
def System.lam (S : System P M) (b : Buffer S) : WithBot (Fin (S.n b.1)) :=
  (Finset.univ.filter (fun j : Fin (S.n b.1) => j < b.2 ∧ S.μ b.1 j ≠ S.mach b)).max

/-- The "prior machine" `π_{p,i}` of (12): `none` (the paper's `φ`) if `λ_{p,i} = 0`,
otherwise `μ_{p,λ_{p,i}}`. -/
def System.prior (S : System P M) (b : Buffer S) : Option (Fin M) :=
  match S.lam b with
  | ⊥ => none
  | (j : Fin (S.n b.1)) => some (S.μ b.1 j)

open Classical in
/-- The modified input rate `d'_{p,i}` of (13): `1 / τ_{p,λ_{p,i}}` if the prior machine
exists and is diconnected with `μ_{p,i}`, and `d_p` otherwise. -/
noncomputable def System.dPrime (S : System P M) (b : Buffer S) : ℝ :=
  match S.lam b with
  | ⊥ => S.d b.1
  | (j : Fin (S.n b.1)) =>
      if S.Dicon (S.μ b.1 j) (S.mach b) then 1 / S.τ b.1 j else S.d b.1

/-- `ρ_m = Σ_{(p,i) : μ_{p,i} = m} d_p τ_{p,i}`, the load of machine `m` in (1) (p. 290). -/
noncomputable def System.rho (S : System P M) (m : Fin M) : ℝ :=
  ∑ b ∈ S.B m, S.d b.1 * S.tau b

/-- `ρ'_m = Σ_{(p,i) : μ_{p,i} = m} d'_{p,i} τ_{p,i}` of (14) (p. 294). -/
noncomputable def System.rhoPrime (S : System P M) (m : Fin M) : ℝ :=
  ∑ b ∈ S.B m, S.dPrime b * S.tau b

/-- The capacity condition (1): `ρ_m < 1` for every machine. -/
def System.CapacityCondition (S : System P M) : Prop := ∀ m, S.rho m < 1

/-- The more stringent capacity condition (14): `ρ'_m < 1` for every machine. -/
def System.StringentCapacityCondition (S : System P M) : Prop := ∀ m, S.rhoPrime m < 1

end KumarSeidman.CAF


