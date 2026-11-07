-- Prove2me | Definitions.Def_VecBalPoly_realOps
-- name    : VecBalPoly_realOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:09:44.901196+00:00
-- url     : https://prove2.me/theorems/486abb3a-add8-410f-b8b4-cb9d1e009db1
-- title:
--   Number of real arithmetic operations and comparisons
-- statement:
--   For a program $P$, an input list of reals and a tape $\omega$, $\mathrm{realOps}(P,\mathrm{input},\omega,t)$ is the number of steps $s<t$ of the run at which the executed instruction is a real addition, subtraction, multiplication, division, or a comparison of two reals.
--
--   This is the cost measure of Proposition 2.3 and Lemmas 2.1, D.1 and D.2, which count "additions, subtractions, multiplications, divisions, and comparisons on real numbers".
--
--   **Formalization Note** Index arithmetic, memory moves and literals are not counted, as in the paper. The goal theorem bounds the total number of executed instructions instead.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Proposition 2.3, p.6 (PDF p.7); Lemma 2.1, p.6; Lemma D.1, p.15; Lemma D.2, p.17

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM

namespace VecBalPoly

/-- The instructions counted as real arithmetic operations and comparisons: `radd`, `rsub`,
`rmul`, `rdiv` and the comparison branch `rblt`.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Proposition 2.3, p.6 (PDF p.7). -/
def IsRealOp : Option MatMulTimeLP.Instr → Prop
  | some (MatMulTimeLP.Instr.radd _ _ _) => True
  | some (MatMulTimeLP.Instr.rsub _ _ _) => True
  | some (MatMulTimeLP.Instr.rmul _ _ _) => True
  | some (MatMulTimeLP.Instr.rdiv _ _ _) => True
  | some (MatMulTimeLP.Instr.rblt _ _ _) => True
  | _ => False

/-- **Number of real arithmetic operations and comparisons.** For a program `P`, an input and a
tape `ω`, `realOps P input ω t` is the number of steps `s < t` of the run whose executed
instruction is a real addition, subtraction, multiplication, division or comparison.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Proposition 2.3, p.6 (PDF p.7): "additions, subtractions, multiplications, divisions,
and comparisons on real numbers"; Lemma 2.1, p.6; Lemma D.1, p.15; Lemma D.2, p.17.

**Formalization Note** Index arithmetic, memory moves and literals are not counted, as in the
paper's operation counts. The total running time (every instruction) is used for Theorem 1.1. -/
noncomputable def realOps (P : MatMulTimeLP.Program) (input : List ℝ) (ω : MatMulTimeLP.Tape)
    (t : ℕ) : ℕ := by
  classical
  exact ((Finset.range t).filter
    fun s => IsRealOp P[(MatMulTimeLP.stateAt P input ω s).pc]?).card

end VecBalPoly


