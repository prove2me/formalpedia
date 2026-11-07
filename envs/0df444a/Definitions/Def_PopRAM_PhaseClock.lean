-- Prove2me | Definitions.Def_PopRAM_PhaseClock
-- name    : PopRAM_PhaseClock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:11.599721+00:00
-- url     : https://prove2.me/theorems/c75a0759-f970-4550-83e8-8c61b39fa01a
-- title:
--   The phase clock with $m$ phases and its leader check
-- statement:
--   Each agent carries a clock component $(\star,t,x)$ with $\star\in\{L,F\}$ (leader or follower), round $t\in\mathbb N$ and phase $x\in\{1,\dots,m\}$. The transitions, initiator first, are
--   $$\begin{aligned}(\star,t,x)+(F,t,y)&\to(\star,t,x)+(F,t,x)&&\text{if }y<x,\\(\star,t+1,x)+(F,t,y)&\to(\star,t+1,x)+(F,t+1,x),\\(L,t,x)+(F,t,x)&\to(L,t,x+1)+(F,t,x)&&\text{if }x<m,\\(L,t,m)+(F,t,m)&\to(L,t+1,1)+(F,t,m),\\(\star,t',x)+(\star,t,y)&\to\text{clock Anomaly}&&\text{if }|t'-t|>1,\end{aligned}$$
--   and, with priority and in both orientations, a leader meeting a follower whose timestamp $(t',y)$ is lexicographically later than its own $(t,x)$ signals a clock anomaly.
--
--   The **standard initialisation** has one leader $(L,0,1)$ and every other agent $(F,0,1)$. $R_t$ (`roundTime`) is the first time at which the leader has round number $t$.
--
--   **Formalization Note** A signalled anomaly puts both interacting agents into an absorbing state `anomaly`, which has no round number. A pair with a leader as responder and no anomaly is unchanged.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Clock, p.19 (PDF p.20), ll.704–716

import Mathlib
import Definitions.Def_PopRAM_Protocol

set_option autoImplicit false

namespace PopRAM

/-! # The phase clock of §B.1

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), "Clock", p.19 (PDF p.20), ll.704–716: "Each agent
has a clock component of the form (L|F, t, x) … The clock transitions are as follows, where ⋆
denotes either L or F:

    (⋆, t, x) + (F, t, y) → (⋆, t, x) + (F, t, x),  if y < x,
    (⋆, t + 1, x) + (F, t, y) → (⋆, t + 1, x) + (F, t + 1, x),
    (L, t, x) + (F, t, x) → (L, t, x + 1) + (F, t, x),  if x < m,
    (L, t, m) + (F, t, m) → (L, t + 1, 1) + (F, t, m),
    (⋆, t′, x) + (⋆, t, y) → clock Anomaly,  if |t′ − t| > 1.

After leader election, the following additional check has priority in both interaction
orientations: if a leader meets a fine-clock follower whose timestamp (t′, y) is lexicographically
later than the leader's (t, x), it signals a clock anomaly."

**Formalization Note** A clock state is `node lead t x` (`lead = true` for `L`) or `anomaly`. A
signalled clock anomaly puts both interacting agents into `anomaly`, which is absorbing (an anomaly
agent never changes; its partner is unchanged). The rules are applied initiator first, as printed;
the leader check in both orientations. A pair with a leader as responder and no anomaly is
unchanged (no printed rule has a leader responder). The standard phase-clock initialisation is
read as: one leader `(L, 0, 1)`, every other agent `(F, 0, 1)`. `roundTime m a₀ t ω` is the first
time the leader `a₀` has round number `t`. -/

/-- Clock states. -/
inductive ClockState where
  | node (lead : Bool) (t x : ℕ)
  | anomaly
  deriving DecidableEq

/-- Lexicographic order on timestamps: `(t, x) < (t', y)`. -/
def tsLt (t x t' y : ℕ) : Prop := t < t' ∨ (t = t' ∧ x < y)

instance (t x t' y : ℕ) : Decidable (tsLt t x t' y) := by unfold tsLt; infer_instance

/-- The transition function of the clock with `m` phases. -/
def clockδ (m : ℕ) : ClockState → ClockState → ClockState × ClockState
  | .node l t x, .node l' t' y =>
      if t' + 1 < t ∨ t + 1 < t' then (.anomaly, .anomaly)
      else if l = true ∧ l' = false ∧ tsLt t x t' y then (.anomaly, .anomaly)
      else if l = false ∧ l' = true ∧ tsLt t' y t x then (.anomaly, .anomaly)
      else if l' = true then (.node l t x, .node l' t' y)
      else if t' = t ∧ y < x then (.node l t x, .node false t x)
      else if t = t' + 1 then (.node l t x, .node false t x)
      else if l = true ∧ t = t' ∧ x = y ∧ x < m then (.node true t (x + 1), .node false t y)
      else if l = true ∧ t = t' ∧ x = y ∧ x = m then (.node true (t + 1) 1, .node false t y)
      else (.node l t x, .node l' t' y)
  | a, b => (a, b)

/-- The standard phase-clock initialisation with the unique leader `a₀`. -/
def clockInit {n : ℕ} (a₀ : Fin n) : Fin n → ClockState :=
  fun b => if b = a₀ then .node true 0 1 else .node false 0 1

/-- The round number of a clock state (`none` for `anomaly`). -/
def roundOf : ClockState → Option ℕ
  | .node _ t _ => some t
  | .anomaly => none

/-- The first time at which the leader `a₀` has round number `t` (`⊤` if never). -/
noncomputable def roundTime {n : ℕ} (m : ℕ) (a₀ : Fin n) (t : ℕ) (ω : ℕ → Pair n) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : roundOf (run (clockδ m) (clockInit a₀) ω s a₀) = some t), (s : ℕ∞)

end PopRAM


