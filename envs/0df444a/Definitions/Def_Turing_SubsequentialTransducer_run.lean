-- Prove2me | Definitions.Def_Turing_SubsequentialTransducer_run
-- name    : Turing_SubsequentialTransducer_run
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T05:46:22.263676+00:00
-- url     : https://prove2.me/theorems/12930cc9-668f-5f66-8fb9-76eaa82311b8
-- title:
--   Evaluation of a subsequential finite-state transducer
-- statement:
--   A deterministic transition reads one input letter, updates the state, and produces a finite output word. The output is the concatenation of the words along the run, followed by the final state’s output word.
-- source:
--   Mehryar Mohri, Finite-State Transducers in Language and Speech Processing, Computational Linguistics 23(2), 1997, p. 272, https://aclanthology.org/J97-2003/.

import Mathlib.Init

namespace Turing.SubsequentialTransducer

/-- Run a finite-state transducer that emits a word on each transition and at end of input. -/
def run {A B S : Type} (step : S → A → S × List B) (finish : S → List B) :
    S → List A → List B
  | s, [] => finish s
  | s, a :: xs => (step s a).2 ++ run step finish (step s a).1 xs

end Turing.SubsequentialTransducer


