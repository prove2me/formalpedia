-- Prove2me | Definitions.Def_FCP_BusyBeaver
-- name    : FCP_BusyBeaver
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:07:37.562024+00:00
-- url     : https://prove2.me/theorems/06a42dab-13e2-47c4-b625-cd72fb4479b1
-- title:
--   Two-symbol Turing machines and the busy beaver (maximum shifts) function
-- statement:
--   An $n$-state, $2$-symbol Turing machine is given by a transition table: for each state $q$ and each symbol $s$ read, it prescribes the symbol to write, the direction to move, and either the next state or the instruction to halt. A configuration is a state, a head position on a bi-infinite tape indexed by $\mathbb{Z}$, and the tape contents.
--
--   A machine *halts in $t$ steps* from a configuration if it performs exactly $t$ transitions, the last of which halts it. The **busy beaver function** $\mathrm{BB}(n)$ (maximum shifts) is the supremum of the halting times of the $n$-state machines started on the all-blank tape in state $0$ with the head at position $0$; the set of such halting times is finite, so the supremum is attained for $n \ge 1$, and $\mathrm{BB}(0) = 0$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/BusyBeaver.lean); https://wiki.bbchallenge.org/wiki/Main_Page

import Mathlib

namespace FCP.BusyBeaver

/-- An `n`-state, 2-symbol Turing machine: for each state and each symbol read it prescribes the
symbol to write, the direction to move (`true` = right, `false` = left) and either the next
state, or `none`, meaning the machine halts on performing this transition. -/
structure TM (n : ℕ) where
  trans : Fin n → Bool → Bool × Bool × Option (Fin n)

/-- A configuration: the current state, the head position on a bi-infinite tape indexed by `ℤ`,
and the tape contents. -/
structure Config (n : ℕ) where
  state : Fin n
  head : ℤ
  tape : ℤ → Bool

/-- One transition of the machine: it writes, moves, and either enters a new state or halts
(`none`). -/
def step {n : ℕ} (M : TM n) (c : Config n) : Option (Config n) :=
  match M.trans c.state (c.tape c.head) with
  | (_w, _d, none) => none
  | (w, d, some s) =>
      some ⟨s, if d then c.head + 1 else c.head - 1, Function.update c.tape c.head w⟩

/-- The configuration reached from `c` after `t` transitions, or `none` if the machine has
already halted. -/
def run {n : ℕ} (M : TM n) (c : Config n) : ℕ → Option (Config n)
  | 0 => some c
  | t + 1 => (run M c t).bind (step M)

/-- `HaltsIn M c t` says that started from `c` the machine performs exactly `t` transitions, the
last of which halts it. -/
def HaltsIn {n : ℕ} (M : TM n) (c : Config n) (t : ℕ) : Prop :=
  run M c t = none ∧ ∀ s < t, run M c s ≠ none

/-- The all-blank starting configuration, with the head at position `0` in state `0`. -/
def init {n : ℕ} (h : 0 < n) : Config n := ⟨⟨0, h⟩, 0, fun _ => false⟩

/-- The busy beaver function (maximum shifts): `BB n` is the largest number of transitions that
an `n`-state, 2-symbol machine can perform before halting, when started on the blank tape.
`BB 0 = 0`, since there are no `0`-state machines that can start. -/
noncomputable def BB (n : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ (M : TM n) (h : 0 < n), HaltsIn M (init h) t}

end FCP.BusyBeaver


