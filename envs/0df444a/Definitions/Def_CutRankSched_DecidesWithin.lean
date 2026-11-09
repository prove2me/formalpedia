-- Prove2me | Definitions.Def_CutRankSched_DecidesWithin
-- name    : CutRankSched_DecidesWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:38.947426+00:00
-- url     : https://prove2.me/theorems/d718a235-8fe6-4996-aa36-6c2f626f20c8
-- title:
--   A machine decides $P$ within time $\tau$ and space $\sigma$
-- statement:
--   A deterministic multitape machine $M$ **decides** a proposition $P$ on an input $x$ within time $\tau$ and space $\sigma$ if, started on $x$, it halts after at most $\tau$ steps in the answer state "$P$ holds" or "$P$ fails" according to the truth of $P$, and every configuration reached during the run has visited at most $\sigma + |x|$ tape cells in total.
--
--   **Formalization Note** The machine model is the published `SubexponentialSAT` primitive multitape machine over the alphabet $\{\text{blank}, 0, 1\}$, with its visited-space accounting, which counts all tapes including the input tape; the additive $|x|$ makes $\sigma$ the space beyond the input.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.2, p.10 ("Its time and space are")

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace CutRankSched

/-- A machine **decides** the proposition `P` on `input` within time `τ` and space `σ`
(the machine reading of "time and space" in Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.2, p.10): started on `input`, it
halts after `time ≤ τ` steps in the answer state `decide P`, and every configuration reached
within `time` steps has visited at most `σ + |input|` cells.

**Formalization Note** The paper names no machine model. The model is the published
`SubexponentialSAT` one (`PrimitiveMachine`, a deterministic multitape machine over
`Option Bool`, with `locatedStep` and `visitedSpace`). `visitedSpace` sums the visited cells of
all tapes, input tape included, so the space bound is read as space beyond the input:
`σ + input.length`. -/
noncomputable def DecidesWithin (M : PrimitiveMachine) (input : List Bool) (P : Prop) (τ σ : ℕ) :
    Prop := by
  classical
  exact ∃ (time : ℕ) (final : SqrtLogSpace.LocatedCfg M),
    Trace (SqrtLogSpace.locatedStep M) time (SqrtLogSpace.locatedInit M input) final ∧
    final.config.state = Sum.inl (decide P) ∧ time ≤ τ ∧
    ∀ (k : ℕ) (c : SqrtLogSpace.LocatedCfg M), k ≤ time →
      Trace (SqrtLogSpace.locatedStep M) k (SqrtLogSpace.locatedInit M input) c →
        SqrtLogSpace.visitedSpace c ≤ σ + input.length

end CutRankSched


