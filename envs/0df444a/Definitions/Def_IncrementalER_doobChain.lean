-- Prove2me | Definitions.Def_IncrementalER_doobChain
-- name    : IncrementalER_doobChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:07:55.267192+00:00
-- url     : https://prove2.me/theorems/1c9ee817-28e7-4c2c-be16-048dd48da2d3
-- title:
--   The Doob-transformed chain $Q$ and the event $A$
-- statement:
--   Let $S_0\subseteq V$, $K=L^{-1}_{\bar S_0,\bar S_0}$, $b>0$ on $\bar S_0$ and $a=Kb$, so $L_{\bar S_0,\bar S_0}a=b$. The chain $Q$ on $\bar S_0\cup\{\square\}$ has
--
--   $$Q(y,x)=\frac{c_{yx}}{d_y}\frac{a_x}{a_y}\ (y,x\in\bar S_0),\qquad Q(y,\square)=\frac{b_y}{d_ya_y},\qquad Q(\square,\square)=1,$$
--
--   and $0$ otherwise (p.33). For a set $U$ and $v\in U\setminus S_0$, let $(u_t)$ be the chain from $v$, $\tau_\square$ its absorption time and $\bar\tau_v=\sup\{t<\tau_\square:u_t=v\}$. The event is
--
--   $$A=\{u_{\tau_\square-1}\notin U\setminus\{v\}\}\cap\{\forall t\in(\bar\tau_v,\tau_\square):u_t\notin U\}$$
--
--   (p.35), and $\Pr_Q[u_{\tau_\square-1}=u\wedge A]$ is the probability that the last state before absorption is $u$ and $A$ holds.
--
--   This chain lets the paper sample vertices with probability proportional to $K_{vu}b_u$.
--
--   **Formalization Note** The state $\square$ is `none` in `Option V`; vertices of $S_0$ are unreachable. The probability is the sum over trajectories $v=u_0,\dots,u_t=u$ in $\bar S_0$ of their weight times $Q(u,\square)$. The second part of $A$ is written as: every time $s\le t$ with $u_s\in U$ is followed by a visit to $v$ at some time in $[s,t]$.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), (17)–(18), p.31; chain Q, p.33; τ□, τ̄_v and A, p.35

import Mathlib
import Definitions.Def_mm_network
import Definitions.Def_IncrementalER_scCond

open Matrix

namespace IncrementalER

/-!
# The Doob-transformed chain `Q` and the event `A`

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), §5.2–§5.4: the vectors
`a, b` with `L_{S̄0,S̄0} a = b` ((18), p.31), the chain `Q` (p.33), `τ□`, `τ̄_v` and the event `A`
(p.35).

**Formalization Note.**
* `b` is any vector positive on `S̄0` (the paper's `½ deg ≤ b ≤ 2 deg`, (17), is not used by
  Lemma 5.6) and `a = K b` with `K = L^{−1}_{S̄0,S̄0}`, so `L_{S̄0,S̄0} a = b`; `a` and `b` are read
  as `0` on `S0`.
* The state space `S̄0 ∪ {□}` is `Option V` with `□ = none`; states `some y` with `y ∈ S0` are
  unreachable from `S̄0` (all their entries are `0`). `Q(y, x) = (c_yx / d_y)(a_x / a_y)` for
  `y, x ∈ S̄0`, `Q(y, □) = b_y / (d_y a_y)`, `Q(□, □) = 1`, `0` otherwise (p.33).
* `Pr_Q[u_{τ□−1} = u ∧ A]` for the chain started at `v` is the sum, over `t ≥ 0` and trajectories
  `v = u_0, …, u_t = u` in `S̄0`, of the path weight times the absorption probability `Q(u, □)`:
  then `τ□ = t + 1`. The event `A = {u_{τ□−1} ∉ U \ {v}} ∩ {∀ s ∈ (τ̄_v, τ□) : u_s ∉ U}` with
  `τ̄_v = sup{s < τ□ : u_s = v}` is the condition that `u_t ∉ U \ {v}` and every `s ≤ t` with
  `u_s ∈ U` has a visit to `v` at some time in `[s, t]`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `a = K b` on `S̄0` (so `L_{S̄0,S̄0} a = b`, (18)), extended by `0` on `S0`. -/
noncomputable def doobA (c : V → V → ℝ) (S0 : Finset V) (b : V → ℝ) : V → ℝ :=
  fun x => if h : x ∉ S0 then (grounded c S0 *ᵥ fun y => b y) ⟨x, h⟩ else 0

/-- The chain `Q` on `S̄0 ∪ {□}` (p.33), with `□ = none`. -/
noncomputable def doobQ (c : V → V → ℝ) (S0 : Finset V) (b : V → ℝ) :
    Matrix (Option V) (Option V) ℝ
  | some y, some x =>
      if y ∉ S0 ∧ x ∉ S0 then c y x / capDeg c y * (doobA c S0 b x / doobA c S0 b y) else 0
  | some y, none => if y ∉ S0 then b y / (capDeg c y * doobA c S0 b y) else 0
  | none, none => 1
  | none, some _ => 0

/-- `Pr_Q[u_{τ□−1} = u ∧ A]` for the chain `Q` started at `v`, with `A` the event of p.35 for the
set `U`. -/
noncomputable def lastExitAProb (c : V → V → ℝ) (S0 : Finset V) (b : V → ℝ) (U : Finset V)
    (v u : V) : ℝ :=
  ∑' t : ℕ, ∑ ω : Fin (t + 1) → V,
    if ω 0 = v ∧ ω (Fin.last t) = u ∧ (ω (Fin.last t) ∉ U ∨ ω (Fin.last t) = v) ∧
        (∀ i : Fin (t + 1), ω i ∈ U → ∃ j : Fin (t + 1), i ≤ j ∧ ω j = v) then
      MarkovMixing.pathWeight (doobQ c S0 b) (fun i => some (ω i)) * doobQ c S0 b (some u) none
    else 0

end IncrementalER


