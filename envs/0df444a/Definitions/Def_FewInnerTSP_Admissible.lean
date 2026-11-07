-- Prove2me | Definitions.Def_FewInnerTSP_Admissible
-- name    : FewInnerTSP_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:28.639197+00:00
-- url     : https://prove2.me/theorems/74558356-34f4-4b0c-89c5-baed1914a534
-- title:
--   Admissible programs: the deterministic real RAM with square roots and rational literals
-- statement:
--   A program of the published unit-cost real RAM (`MatMulTimeLP.RealRAM`) is **admissible** when every instruction is one of the paper's real-arithmetic model: real literals are rational numbers, and the Gaussian and uniform draws are not used. What remains is exact addition, subtraction, multiplication, division, square root and comparison of reals, plus index bookkeeping with indirect addressing.
--
--   Every executed instruction costs one step, including index operations and input reads. There is no floor, no conversion of reals to indices and no bit operation. Comparing a sum of edge costs costs its additions plus one comparison.
--
--   This is the model of Theorem 1.1, "a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs", read with the fewest primitives: under "there is a program", every primitive removed makes the statement stronger. Rational literals exclude advice hidden in a real constant, and without draws the algorithm is deterministic.
--
--   **Formalization Note** The paper names no instruction set. Without draws an admissible program's run does not depend on the random tape.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Theorem 1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM

namespace FewInnerTSP

/-- An instruction of the published real RAM is admissible when it is an operation of the paper's
real-arithmetic model: a real literal must be rational, the Gaussian and the uniform draw are not
allowed, and the square root is allowed (the model supports exact Euclidean distances).
Source: Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent*,
STOC 2027 submission (manuscript sha256 6541f631…), Theorem 1.1, p.1 (PDF p.3). -/
def InstrAdmissible : MatMulTimeLP.Instr → Prop
  | MatMulTimeLP.Instr.rconst _ c => ∃ q : ℚ, c = (q : ℝ)
  | MatMulTimeLP.Instr.gauss _ => False
  | MatMulTimeLP.Instr.unif _ => False
  | _ => True

/-- **Admissible programs.** A program of the published unit-cost real RAM
(`MatMulTimeLP.RealRAM`) is admissible when every instruction is: real literals are rational, and
there is no Gaussian and no uniform draw. What remains is exact addition, subtraction,
multiplication, division, square root and comparison of reals, plus index bookkeeping.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), Theorem 1.1, p.1 (PDF p.3):
"deterministically", "a real-arithmetic model supporting exact Euclidean distances and exact
comparison of finite sums of edge costs".

**Formalization Note** The paper names no instruction set. Under `∃ program` each instruction
removed strengthens a theorem: a real literal could hold unbounded advice, and a draw would make the
algorithm randomized. The machine has no floor and no real-to-index cast, every executed instruction
costs `1`, including index bookkeeping and input reads, and comparing a sum of edge costs costs its
additions plus one `rblt`. So a program here runs at no greater cost in any model that has those
primitives. With no draw left, the output does not depend on the tape. -/
def Admissible (A : MatMulTimeLP.Program) : Prop :=
  ∀ i ∈ A, InstrAdmissible i

end FewInnerTSP


