-- Prove2me | Definitions.Def_CutRankSched_FindsWithin
-- name    : CutRankSched_FindsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:49.357217+00:00
-- url     : https://prove2.me/theorems/7eecb597-cd71-48ec-9d2b-ebb3ea45dd2b
-- title:
--   A machine decides $P$ and writes a witness
-- statement:
--   A machine $M$ **decides $P$ and finds a witness** on input $x$ within time $\tau$ and space $\sigma$ if it decides $P$ as in `DecidesWithin`, and, when $P$ holds, its halting configuration holds on a designated output tape a word $w$ satisfying a given correctness predicate (here: $w$ encodes a feasible layer assignment).
--
--   **Formalization Note** Same machine model and space convention as `DecidesWithin`; the output tape holds exactly $w$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.2, p.10 ("A feasible assignment can be recovered")

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace CutRankSched

/-- A machine decides `P` on `input` within time `τ` and space `σ` (as in `DecidesWithin`) and,
when `P` holds, its halting configuration also holds on tape `out` a word `w` with `Good w`
(the machine reading of "A feasible assignment can be recovered … with polynomial overhead",
Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.2, p.10).

**Formalization Note** Same model and space convention as `DecidesWithin`; the output tape holds
exactly `w`, head on its first cell. -/
noncomputable def FindsWithin (M : PrimitiveMachine) (out : Fin M.tapeCount) (input : List Bool)
    (P : Prop) (Good : List Bool → Prop) (τ σ : ℕ) : Prop := by
  classical
  exact ∃ (time : ℕ) (final : SqrtLogSpace.LocatedCfg M),
    Trace (SqrtLogSpace.locatedStep M) time (SqrtLogSpace.locatedInit M input) final ∧
    final.config.state = Sum.inl (decide P) ∧
    (P → ∃ w : List Bool, Good w ∧ final.config.tapes out = Turing.Tape.mk₁ (w.map some)) ∧
    time ≤ τ ∧
    ∀ (k : ℕ) (c : SqrtLogSpace.LocatedCfg M), k ≤ time →
      Trace (SqrtLogSpace.locatedStep M) k (SqrtLogSpace.locatedInit M input) c →
        SqrtLogSpace.visitedSpace c ≤ σ + input.length

end CutRankSched


