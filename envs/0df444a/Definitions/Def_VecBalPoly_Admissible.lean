-- Prove2me | Definitions.Def_VecBalPoly_Admissible
-- name    : VecBalPoly_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:09:42.70414+00:00
-- url     : https://prove2.me/theorems/19f69a7a-b392-429f-8a88-08ac6354c660
-- title:
--   Admissible programs of the deterministic real RAM
-- statement:
--   A program $P$ of the published unit-cost real RAM (`MatMulTimeLP.RealRAM`) is **admissible** when every instruction of $P$ is one of the paper's operations: every real literal is a rational number, and $P$ contains no square-root instruction and no Gaussian or uniform draw. What remains is exact addition, subtraction, multiplication, division and comparison of real numbers, together with index arithmetic and memory access.
--
--   Every algorithmic statement of the mission asserts the existence of an admissible program. This makes the algorithms deterministic and keeps them inside the paper's model.
--
--   **Formalization Note** The published machine also allows any real literal, a square root and random draws from a tape. Under an existential quantifier over programs each of these would weaken the statements: a real literal can encode unbounded advice, and the draws would make the algorithm randomized. The restriction applies only to the program, so nothing is added to the input.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Theorem 1.1, p.1 (PDF p.2); Proposition 2.3, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM

namespace VecBalPoly

/-- An instruction of the published real RAM is admissible when it is an operation of the paper's
deterministic real-arithmetic model: a real literal must be rational, and the square root, the
Gaussian draw and the uniform draw are not allowed.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Theorem 1.1, p.1 (PDF p.2); Proposition 2.3, p.6 (PDF p.7). -/
def InstrAdmissible : MatMulTimeLP.Instr → Prop
  | MatMulTimeLP.Instr.rconst _ c => ∃ q : ℚ, c = (q : ℝ)
  | MatMulTimeLP.Instr.rsqrt _ _ => False
  | MatMulTimeLP.Instr.gauss _ => False
  | MatMulTimeLP.Instr.unif _ => False
  | _ => True

/-- **Admissible programs.** A program of the published unit-cost real RAM
(`MatMulTimeLP.RealRAM`) is admissible when every instruction is: real literals are rational, and
there is no square root, no Gaussian draw and no uniform draw. What remains is exact addition,
subtraction, multiplication, division and comparison of reals, plus index bookkeeping.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Theorem 1.1, p.1 (PDF p.2): "unit-cost real-RAM model", "deterministic";
Proposition 2.3, p.6 (PDF p.7): "additions, subtractions, multiplications, divisions, and
comparisons on real numbers".

**Formalization Note** The published machine allows any real `rconst`, a square root, and
Gaussian and uniform draws from a tape. Under `∃ program` each would weaken the statements: a real
literal can hold unbounded advice, `√` is not among the paper's operations, and the draws would
make the algorithm randomized. This restricts the existentially chosen program only, so nothing
is added to the input. With no draw left, the output does not depend on the tape. -/
def Admissible (P : MatMulTimeLP.Program) : Prop :=
  ∀ i ∈ P, InstrAdmissible i

end VecBalPoly


