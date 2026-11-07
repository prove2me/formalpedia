-- Prove2me | Definitions.Def_UniqueOptScores_output
-- name    : UniqueOptScores_output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:02.548923+00:00
-- url     : https://prove2.me/theorems/d197dd85-09b3-4108-9f92-38b0a6e65fe7
-- title:
--   Output word of an oracle machine
-- statement:
--   For a deterministic oracle machine $M$, an oracle $A$ and an input $w$, $M^A(w)$ denotes the output word of the halting run of $M$ on $w$ with oracle $A$. A deterministic run reaches at most one halting configuration, so this word is well defined whenever the run halts.
--
--   **Formalization Note** If the run never halts the value is the empty word; every class of the mission only uses clocked machines, which always halt, so this default never matters.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.15; Section 4, p.16

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_setOracle

namespace UniqueOptScores

/-- **The output word of an oracle machine.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.15 and §4, p.16 (deterministic polynomial-time oracle machines and transducers).

`output OM A w` is the output word of the halting run of `OM` with oracle `A` on input `w`, and the
empty word if the run never halts.

**Formalization Note.** A deterministic run reaches at most one halting configuration, so the
choice is the output. Every class of this development only uses clocked machines (`IsClocked`),
which halt on every input for every oracle; the default `[]` is never used there. -/
noncomputable def output (OM : HMBinPacking.OracleMachine) (A : Set (List Bool)) (w : List Bool) :
    List Bool :=
  @dite _ (∃ out : List Bool, ∃ s : ℕ, HMBinPacking.oRun OM (setOracle A) w s =
      some (Turing.haltList OM.M.tm (out.map OM.M.outputAlphabet.symm)))
    (Classical.propDecidable _) (fun h => h.choose) (fun _ => [])

end UniqueOptScores


