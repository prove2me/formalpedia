-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_RunOutcome
-- name    : FasterPrimeEnum_Supplement_RunOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:46:11.995684+00:00
-- url     : https://prove2.me/theorems/77cbdebe-fce3-4514-94cd-acf4fcab96e8
-- title:
--   A run that returns a word or “FAIL” within time $\tau$; the coin tape
-- statement:
--   A deterministic machine $A$, started from a configuration $c$, **returns the word $w$ within time $\tau$** if it halts after at most $\tau$ steps with answer bit `true` and its output tape holds exactly $w$; it **returns “FAIL” within time $\tau$** if it halts after at most $\tau$ steps with answer bit `false`.
--
--   A **probabilistic run** on input $x$ starts with $x$ on the input tape, a string of coin bits on a designated coin tape, and all other tapes blank; the coin string is drawn uniformly from the strings of a fixed length.
--
--   These are the output conventions of the main theorems with a failure branch (Theorems 1.3, 1.4 and 5.5), and the probabilistic machine model of Theorem 1.3 (p.4: “a Turing machine that is allowed to flip an independent, unbiased coin at each step”).
--
--   **Formalization Note** The machine is the published `PrimitiveMachine`, which halts by entering a state carrying an answer bit. Because the machine is deterministic, at most one outcome holds from a given start. Reading coins from a pre-filled coin tape and flipping a fresh coin per step simulate each other with a constant-factor loss in time.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.4, pp.4–5 (Theorems 1.3, 1.4); §5.3, p.38 (Theorem 5.5)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- **A run with outcome "list" or "FAIL" within time `τ`** — D. Harvey, *Faster enumeration of
primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.4, pp.4–5 (Theorems 1.3, 1.4: "Its
output is either the list of all primes p < N, or "FAIL"") and §5.3, p.38 (Theorem 5.5: "Otherwise
it returns "FAIL"").

Started from the configuration `start`, the machine `A` halts after some number `time ≤ τ` of
steps, and
* for the outcome `some w`: it halts with answer bit `true`, and its tape `out` holds exactly the
  word `w`, head on the first cell;
* for the outcome `none` ("FAIL"): it halts with answer bit `false`.

**Formalization Note.** The machine is the published `PrimitiveMachine`, which halts by entering
a state `Sum.inl b` carrying an answer bit `b`. "FAIL" is the answer bit `false`; a returned word is
the answer bit `true` together with the word on the output tape. So "FAIL" can never be confused
with a returned word. The machine is deterministic, so from a given `start` at most one outcome
holds. -/
def RunOutcome (A : PrimitiveMachine) (start : A.Cfg) (out : Fin A.tapeCount) (τ : ℝ) :
    Option (List Bool) → Prop
  | none => ∃ (time : ℕ) (final : A.Cfg),
      Trace A.step time start final ∧ final.state = Sum.inl false ∧ (time : ℝ) ≤ τ
  | some w => ∃ (time : ℕ) (final : A.Cfg),
      Trace A.step time start final ∧ final.state = Sum.inl true ∧
      final.tapes out = Turing.Tape.mk₁ (w.map some) ∧ (time : ℝ) ≤ τ

/-- **Initial configuration with a coin tape** — the probabilistic machine of p.4: "By a
probabilistic Turing machine, we mean a Turing machine that is allowed to flip an independent,
unbiased coin at each step."

The input word is written on the input tape, the coin string `coins` on the tape `coin`, and all
other tapes are blank; the machine starts in its start state. A probabilistic run is the run from
this configuration with `coins` drawn uniformly from the strings of a fixed length.

**Formalization Note.** A machine that flips a fresh coin at each step and a machine that reads
fresh coins from a pre-filled coin tape simulate each other with a constant-factor loss in time
(reading a new coin is one move and one scan; conversely a coin is flipped the first time a cell of
the coin tape is visited and stored). If `coin` is the input tape, the input wins and the machine
is deterministic. -/
def coinInit (A : PrimitiveMachine) (coin : Fin A.tapeCount) (input coins : List Bool) : A.Cfg :=
  ⟨.inr A.start, fun k =>
    if k = A.inputTape then Turing.Tape.mk₁ (input.map some)
    else if k = coin then Turing.Tape.mk₁ (coins.map some)
    else Turing.Tape.mk₁ []⟩

end Supplement

end FasterPrimeEnum


