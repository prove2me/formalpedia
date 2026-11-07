-- Prove2me | Definitions.Def_FanInSemigroup_RSMachine
-- name    : FanInSemigroup_RSMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:08.397505+00:00
-- url     : https://prove2.me/theorems/7dd98ae4-5a45-44dc-8082-1e57f67aa0af
-- title:
--   The rs machine and the languages it accepts
-- statement:
--   An **rs machine** over an alphabet $\Sigma$ has flipflops $F_1,\dots,F_m$, each in state $0$ or $1$ with a specified initial state, and boolean functions $r_i,s_i$ whose domain is the current input letter together with the states of $F_1,\dots,F_{i-1}$. The values of $r_i$ and $s_i$ are never both one.
--
--   At each time a letter is read. If $s_i$ is one then $F_i$ is forced to $1$, if $r_i$ is one then $F_i$ is forced to $0$, and otherwise $F_i$ is unchanged. The machine accepts its input if the final vector of states lies in a specified set of accepting vectors.
--
--   These restricted automata are what constant-depth circuits simulate.
--
--   **Formalization Note** The update is synchronous: at each time every $r_i,s_i$ reads the states from before the current letter. The page gives no time index on these states. The other reading, with lower flipflops already updated, would make the paper's Theorem 2.5 false: no such machine accepts the set of words over $\{0,1\}$ whose second-to-last letter is $1$, while a two-flipflop synchronous machine does.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, p.55

import Mathlib

set_option autoImplicit false

namespace FanInSemigroup

/-- An **rs machine** over the alphabet `α` with `m` flipflops. Chandra, Fortune, Lipton, STOC
1983, §2, p.55: "An rs machine consists of a set of flipflops {F1,...Fk} and a set of functions
{r1,...,rk} and {s1,...,sk}. Each ri and si is boolean valued; the domain of ri and si is the
current input together with the state of flipflops F1,...,Fi−1. The values of ri and si must never
both be one." and "Each flipflop is either in the 0 (reset) or 1 (set) state, with initial state
chosen in some specified way. … an rs machine accepts its input if its vector of flipflop states
is an element of some specified set of accepting state vectors." -/
structure RSMachine (α : Type*) (m : ℕ) where
  /-- The reset function of each flipflop, on the current input and the lower-numbered states. -/
  r : (i : Fin m) → α → ({j : Fin m // j < i} → Bool) → Bool
  /-- The set function of each flipflop, on the current input and the lower-numbered states. -/
  s : (i : Fin m) → α → ({j : Fin m // j < i} → Bool) → Bool
  /-- The values of `r i` and `s i` are never both one. -/
  never_both : ∀ i a q, ¬ (r i a q = true ∧ s i a q = true)
  /-- The initial state vector. -/
  init : Fin m → Bool
  /-- The accepting state vectors. -/
  accept : Set (Fin m → Bool)

namespace RSMachine

variable {α : Type*} {m : ℕ}

/-- One time step, p.55: "If si is a one then flipflop i is forced to the one state; if ri is one
then flipflop i is forced to the zero state; if both ri and si are zero then the state of the
flipflop is unchanged."

**Formalization Note.** The update is **synchronous**: at each time every `r i`, `s i` reads the
state vector from before the current letter. The page says "the state of flipflops F1,...,Fi−1"
without a time index. The other reading, lower flipflops already updated at the current time,
makes Theorem 2.5 false: no such machine accepts the words over `{0,1}` whose second-to-last letter
is `1`, while a 2-flipflop synchronous machine does. -/
def step (M : RSMachine α m) (a : α) (q : Fin m → Bool) : Fin m → Bool := fun i =>
  let lower : {j : Fin m // j < i} → Bool := fun j => q j
  if M.s i a lower then true else if M.r i a lower then false else q i

/-- The state vector after reading a word, from the initial state vector. -/
def run (M : RSMachine α m) (w : List α) : Fin m → Bool :=
  w.foldl (fun q a => M.step a q) M.init

/-- The language of the machine, p.55: it "accepts its input if its vector of flipflop states is
an element of some specified set of accepting state vectors." -/
def language (M : RSMachine α m) : Language α :=
  {w | M.run w ∈ M.accept}

end RSMachine

/-- `L` is accepted by an rs machine (with some number of flipflops). Chandra, Fortune, Lipton,
STOC 1983, Theorem 2.5, p.55. -/
def AcceptedByRS {α : Type*} (L : Language α) : Prop :=
  ∃ (m : ℕ) (M : RSMachine α m), M.language = L

end FanInSemigroup


