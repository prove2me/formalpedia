-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_OracleRuns
-- name    : ConstrainedDirSep_STSep_OracleRuns
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:05:16.853664+00:00
-- url     : https://prove2.me/theorems/67be64b4-b14a-4c1a-9cb9-89f6186db121
-- title:
--   Oracle runs with a bounded number of calls and admissible queries
-- statement:
--   Let $M$ be an oracle machine in the sense of the published `HMBinPacking.OracleMachine`: a multi-stack Turing machine with Boolean input and output, a query stack, and labels *ask* and *resume*; at *ask* the query word $q$ is replaced by the oracle's answer $O(q)$, and every step, including each call, costs one unit.
--
--   $M$ **outputs $w$ on input $x$ within $t$ steps and $c$ calls, every query satisfying $P$**, if the run with oracle $O$ halts with output $w$ (all other stacks empty) after at most $t$ steps, at most $c$ of those steps are oracle calls, and the query word at every call satisfies $P$. `callCount` is the number of calls in the first $j$ steps.
--
--   **Formalization Note.** This adds a call counter and a query predicate to the published `HMBinPacking.ORunsWithin`, which bounds only query length.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 2 (PDF 5), Theorem 1.1 (running time 2^{O(k⁴ log k)} n^{O(1)} + 2^{O(k²)} τ_H(k)); p. 26 (PDF 29), proof of Theorem 1.1 (membership table)

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

open Classical in
/-- **Number of oracle calls in the first `steps` steps of a run.** Olkowski, Ramanujan,
*Constrained Directed Separation*, STOC 2027 submission (manuscript sha256 4dd06c29…), §1.1.1,
p. 2 (PDF 5) and proof of Theorem 1.1, p. 26 (PDF 29): the term `2^{O(k²)} τ_H(k)` counts the
membership tests.

The number of indices `j < steps` at which the run of the published oracle machine
`HMBinPacking.OracleMachine` (oracle `O`, input `input`) is at a configuration with label `ask`,
i.e. makes an oracle call. -/
noncomputable def callCount (OM : HMBinPacking.OracleMachine) (O : List Bool → List Bool)
    (input : List Bool) (steps : ℕ) : ℕ :=
  ((Finset.range steps).filter fun j =>
    ∃ c : HMBinPacking.OCfg OM, HMBinPacking.oRun OM O input j = some c ∧ c.l = some OM.ask).card

/-- **An oracle machine outputs a word within `t` steps, with at most `calls` oracle calls, every
query satisfying `Good`.** §1.1.1, p. 2 (PDF 5): running time `2^{O(k⁴ log k)} n^{O(1)} +
2^{O(k²)} τ_H(k)`.

`ORunsWithinCalls OM O input output t calls Good` holds when the run of `OM` with oracle `O` on
`input` reaches the halting configuration with `output` on the output stack (all other stacks empty,
Mathlib's `Turing.haltList`) after `steps ≤ t` steps, at most `calls` of these steps are oracle
calls, and at every oracle call the query word (the contents of the query stack) satisfies `Good`.

**Formalization Note.** Built on the published `HMBinPacking.oRun` (each step, including each
oracle call, costs one unit). It differs from the published `HMBinPacking.ORunsWithin` only in
that it also bounds the number of calls and constrains the query words by a predicate instead of
by their length. -/
def ORunsWithinCalls (OM : HMBinPacking.OracleMachine) (O : List Bool → List Bool)
    (input output : List Bool) (t calls : ℕ) (Good : List Bool → Prop) : Prop :=
  ∃ steps ≤ t,
    HMBinPacking.oRun OM O input steps =
        some (Turing.haltList OM.M.tm (output.map OM.M.outputAlphabet.symm)) ∧
      callCount OM O input steps ≤ calls ∧
      ∀ j < steps, ∀ c : HMBinPacking.OCfg OM, HMBinPacking.oRun OM O input j = some c →
        c.l = some OM.ask → Good ((c.stk OM.qs).map OM.qsAlphabet)

end ConstrainedDirSep.STSep


