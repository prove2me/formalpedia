-- Prove2me | Definitions.Def_ContractionLemma_RunsWithin
-- name    : ContractionLemma_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:31.453555+00:00
-- url     : https://prove2.me/theorems/47307869-45f5-4322-8b55-22210e4a7586
-- title:
--   A machine run within time $\tau$ and space $\sigma$ with a prescribed output
-- statement:
--   Let $A$ be a deterministic multi-tape machine of the published model `SubexponentialSAT`. The predicate says that $A$, started with a word $w$ on its input tape, reaches a halted configuration after some number $t\le\tau$ of steps, that the designated output tape then holds exactly the required output with the head on its first cell, and that at every step up to $t$ the total number of visited cells over all tapes, the input tape included, is at most $\sigma$.
--
--   This is how the clauses "computed in time $\tau$ and space $\sigma$" of the paper are read throughout the mission.
--
--   **Formalization Note** The shape is that of the platform's proved `exact_count_and_sat`. The bounds are real numbers so that they can contain real powers such as $s^{9/10}$.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 2.1, p.16

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **A run within time `τ` and space `σ`** — the machine model used to read the costs of
Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256 049caea1…), Theorem 2.1,
p.16 ("computed … in time … and space …").

`RunsWithin A out input output τ σ` says: started on `input` (on its input tape), the machine
`A` reaches after some number `time ≤ τ` of steps a halted configuration (state `Sum.inl _`)
whose tape `out` holds exactly `output` (head on its first cell), and every configuration
reached in at most `time` steps has visited at most `σ` cells in total.

**Formalization Note.** The machine model is the published `SubexponentialSAT` model:
`PrimitiveMachine` (a deterministic multitape machine over `Option Bool`), its located
configurations, `locatedStep`, and `visitedSpace`, which sums the visited cells of all tapes,
the input tape included. This is the shape of the platform's proved
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`. -/
def RunsWithin (A : PrimitiveMachine) (out : Fin A.tapeCount) (input output : List Bool)
    (τ σ : ℝ) : Prop :=
  ∃ (time : ℕ) (final : LocatedCfg A),
    Trace (locatedStep A) time (locatedInit A input) final ∧
    (∃ b : Bool, final.config.state = Sum.inl b) ∧
    final.config.tapes out = Turing.Tape.mk₁ (output.map some) ∧
    (time : ℝ) ≤ τ ∧
    ∀ (k : ℕ) (c : LocatedCfg A), k ≤ time →
      Trace (locatedStep A) k (locatedInit A input) c → (visitedSpace c : ℝ) ≤ σ

end ContractionLemma


