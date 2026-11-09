-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_timedDecider
-- name    : IPPComplexities_Unconditional_timedDecider
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:21.466957+00:00
-- url     : https://prove2.me/theorems/371da4a0-7188-402c-82b9-33faad738284
-- title:
--   Finite deterministic Turing deciders with operational time bounds
-- statement:
--   A decider $M$ is a finite deterministic single-tape Post-Turing machine, using Mathlib's tape and step semantics. It has finitely many states numbered from zero, a finite transition table, and a Boolean verdict table read only after halting. Its tape alphabet consists of blank and the two distinct Boolean input symbols. Every input bit is initially written on consecutive cells; the head starts at the first cell in state zero.
--
--   A transition performs one tape move or one symbol write. The bounded simulator iterates those transitions and leaves a halted configuration unchanged. The assertion
--
--   $$\operatorname{DecidesWithin}(M,L,T)\iff
--   \forall x\in\{0,1\}^*,\ \exists t\le T(|x|),\ M(x)\text{ halts by }t\text{ with verdict }[x\in L]$$
--
--   uses the actual simulated configuration, including the requirement that no transition is enabled there. It does not merely assert a decidability instance or supply a nonuniform truth table. The same finite machine and the same time function apply to every string. This provides the uniform timed conclusion of Theorem 1.1; the IPP verifiers remain computationally unrestricted.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 1, Theorem 1.1; pp. 8–9, exhaustive-search time clause in its proof (PDF pp. 3, 10–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_inputs
import Mathlib.Computability.TuringMachine.PostTuringMachine

namespace IPPComplexities.Unconditional

/-- A genuinely finite, deterministic, single-tape Post-Turing machine.
None is blank, some false/true are the two input symbols. State zero starts.
The finite verdict table is read only upon halting. -/
structure Decider where
  states : ℕ
  transition : Turing.TM0.Machine (Option Bool) (Fin (states + 1))
  verdict : Fin (states + 1) → Bool

/-- A halted configuration is absorbing for bounded-time simulation. -/
def machineStep (M : Decider) :
    Turing.TM0.Cfg (Option Bool) (Fin (M.states + 1)) →
    Turing.TM0.Cfg (Option Bool) (Fin (M.states + 1)) :=
  fun s => (Turing.TM0.step M.transition s).getD s

/-- t individual tape actions from the actual input configuration. -/
def machineRun (M : Decider) (x : List Bool) (t : ℕ) :
    Turing.TM0.Cfg (Option Bool) (Fin (M.states + 1)) :=
  (machineStep M)^[t] (Turing.TM0.init (x.map some))

def StopsWith (M : Decider) (x : List Bool) (t : ℕ) (b : Bool) : Prop :=
  Turing.TM0.step M.transition (machineRun M x t) = none ∧
    M.verdict (machineRun M x t).q = b

/-- Uniform full-input decision with an operational step bound on every string. -/
def DecidesWithin (M : Decider) (L : Property) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ (t : ℕ) (b : Bool),
    t ≤ T x.length ∧ StopsWith M x t b ∧ (b = true ↔ x ∈ L)

end IPPComplexities.Unconditional


