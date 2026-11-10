-- Prove2me | Definitions.Def_ArrighiStarFree_HalfLevel_Automata
-- name    : ArrighiStarFree_HalfLevel_Automata
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:06:24.232378+00:00
-- url     : https://prove2.me/theorems/c0d27cd0-c5e2-40d6-bdf9-1e5456324fef
-- title:
--   Finite singleton-start NFAs, total DFAs and explicit tables
-- statement:
--   For an arbitrary finite alphabet $\mathrm{Fin}(k)$, an NFA has a finite state set $\mathrm{Fin}(q)$, an initial state $q_0$, a final-state bit vector, and a Boolean transition table indexed by state, letter and successor. The presence of $q_0$ requires $q>0$. There are no epsilon transitions. Acceptance is Mathlib NFA acceptance with start set exactly $\{q_0\}$:
--   $$L(A)=\{w: \text{some run from }q_0\text{ on }w\text{ ends in a final state}\}.$$
--   The automaton is a DFA precisely when every state/letter pair has exactly one successor, including nonaccepting states. No acyclicity or minimality condition is imposed.
--
--   An automaton record consists of its state count in unary terminated by zero, its initial-state index in the same format, its final-state bits, and its full transition tensor in state/letter/successor order. The shared alphabet size is supplied by an enclosing list. The code $1^n0$ also represents zero. Table dimensions determine record boundaries without a semantic oracle.
--
--   This general finite-automaton representation is separate from the half-level promise and intersection problem.
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), §2, printed p. 23:4, PDF p. 4

import Definitions.Def_ArrighiStarFree_HalfLevel_Words

namespace ArrighiStarFree.HalfLevel

/-- Explicit finite singleton-start, epsilon-free NFA; arbitrary finite alphabet. -/
structure FiniteNFA (k : ℕ) where
  states : ℕ
  start : Fin states
  final : Fin states → Bool
  table : Fin states → Fin k → Fin states → Bool

def FiniteNFA.toNFA {k : ℕ} (A : FiniteNFA k) : NFA (Fin k) (Fin A.states) where
  step q a := {r | A.table q a r = true}
  start := {A.start}
  accept := {q | A.final q = true}

def FiniteNFA.language {k : ℕ} (A : FiniteNFA k) : Language (Fin k) :=
  A.toNFA.accepts

/-- Completeness is included: exactly one successor for every state and letter. -/
def FiniteNFA.IsDFA {k : ℕ} (A : FiniteNFA k) : Prop :=
  ∀ q a, ∃! r, A.table q a r = true

/-- Self-delimiting unary integer. Dense tables below use literal Boolean entries. -/
def unaryCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- State count; unary initial-state index; final bit vector; row-major transition tensor.
The alphabet size is recorded once in the enclosing list. -/
def FiniteNFA.encode {k : ℕ} (A : FiniteNFA k) : List Bool :=
  unaryCode A.states ++ unaryCode A.start.val ++ List.ofFn A.final ++
    (List.finRange A.states).flatMap (fun q =>
      (List.finRange k).flatMap (fun a => List.ofFn (A.table q a)))

end ArrighiStarFree.HalfLevel


