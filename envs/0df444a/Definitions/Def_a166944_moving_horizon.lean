-- Prove2me | Definitions.Def_a166944_moving_horizon
-- name    : a166944_moving_horizon
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-15T00:09:23.660947+00:00
-- url     : https://prove2.me/theorems/16d88836-80e6-4fd2-b56b-dd73543a3e35
-- title:
--   OEIS A166944 — the moving-horizon replay: states, steps, paths, and the attained-maximum cap
-- statement:
--   This bundle fixes the **moving-horizon replay** of the OEIS A166944 recursion: the dynamical system in which the proofs about difference records are carried out.
--
--   Let $a$ be the recursion, $d_n=a_n-a_{n-1}$ its first differences and $D_n=a_n-n$ its offset from the identity. A **moving-horizon state** is a pair $(s,C)$ with $2\le s$, $D_s=C$ and $s<C$: the index $s$ together with the horizon $C$ at which the offset has arrived. Because $D$ is constant along a run of unit increments, the recursion is quiet between states, and a **step**
--
--   $$
--   (s,C)\;\longrightarrow\;(r,C')
--   $$
--
--   records the first index $r>s$ at which the increment $d_r$ is nontrivial, together with the new horizon $C'=D_r$. The step carries the arithmetic content of the transition: $C+2\le C'$, and the entire interval $(s,r)$ is a unit tail in which $d_j=1$.
--
--   A **path** is a finite chain of such steps, recorded by the relation `HasMovingHorizonPathTo s C sf Cf q`, which additionally names the terminal state $(sf,Cf)$ and the number $q$ of steps. This is the object the project bounds: the question of how far a replay travels is the question of how large $sf-(M+2)$ can be, and every quantitative result in the development is a statement about a path.
--
--   Finally, $P$ is an **attained running maximum** through index $k$ when every difference up to $k$ is at most $P$ and the value $P$ itself occurs. A replay from a difference record $M$ is run under this cap, so its steps can never produce an increment exceeding $M$; this is what makes the dynamics terminate at the next record and what the phrase 'capped replay' refers to.
--
--   Together these five declarations are the vocabulary in which the A166944 conjecture is reduced to a single inequality about the terminal index of a path.
--
--   **Formalization Note** The path relation is defined by recursion on the step count, with the base case requiring the named endpoint to be the actual endpoint. The step condition `r <= C` keeps the event inside the horizon; without it the recurrence could not be jumped to a well-defined next state. Indices are restricted to $\ge2$ in `IsAttainedPreviousMaximum`, the range in which `d` is a genuine difference. This bundle imports `Def_a166944_record_core` for the recursion itself, so the two share one vocabulary.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. The replay definitions and their theory are developed at https://github.com/tara-sooo/A166944-Lean (A166944/ResearchDefs.lean for the definitions, A166944/Lemmas.lean for the moving-horizon theory).

import Mathlib.Data.Nat.Prime.Defs
import Definitions.Def_a166944_record_core

namespace A166944Research

/-- A moving-horizon state: the offset `C = D s` exceeds the index. -/
def IsMovingHorizonState (s C : Nat) : Prop :=
  2 ≤ s ∧ D s = C ∧ s < C

/-- One first-event transition, including the unit tail and the next state. -/
def IsMovingHorizonStep (s C r C' : Nat) : Prop :=
  IsMovingHorizonState s C ∧ s < r ∧ r ≤ C ∧ 1 < d r ∧
    (∀ j : Nat, s < j → j < r → d j = 1) ∧
    D (r - 1) = C ∧ C' = D r ∧ C + 2 ≤ C' ∧
    IsMovingHorizonState r C'

/-- A finite first-hit path with an explicitly named endpoint. -/
def HasMovingHorizonPathTo (s C sf Cf : Nat) : Nat → Prop
  | 0 => s = sf ∧ C = Cf ∧ IsMovingHorizonState s C
  | Nat.succ q =>
      IsMovingHorizonState s C ∧
        ∃ r C', IsMovingHorizonStep s C r C' ∧
          HasMovingHorizonPathTo r C' sf Cf q

/-- `P` is an attained running maximum through index `k`: every difference up to
`k` is at most `P`, and `P` itself occurs. This is the cap that makes a replay
'capped'. -/
def IsAttainedPreviousMaximum (P k : Nat) : Prop :=
  (∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ P) ∧
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P

end A166944Research


