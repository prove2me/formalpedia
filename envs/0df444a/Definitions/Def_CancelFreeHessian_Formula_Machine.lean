-- Prove2me | Definitions.Def_CancelFreeHessian_Formula_Machine
-- name    : CancelFreeHessian_Formula_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:58:27.322739+00:00
-- url     : https://prove2.me/theorems/ae9e7734-095e-4a7f-b797-5e141229941c
-- title:
--   The word RAM of the bookkeeping clause (deterministic CongruencyTU programs with logarithmic words) and the encodings of graphs and circuits
-- statement:
--   The source states that "the bookkeeping takes time of the same order on a RAM" and names no machine model. The model used here is a deterministic unit-cost **word RAM**: a program of the integer RAM `CongruencyTU` (registers indexed by $\mathbb N$ holding integers, unit cost per instruction), with no coin and no oracle instruction, whose registers hold **logarithmic words**: a width constant $w$, fixed with the program, bounds the bit length of every register at every step by
--   $$w\cdot\big(1+\lfloor\log_2(2+\text{scale})\rfloor\big),$$
--   where the scale is the size of the input ($n+s$ for a graph with $n$ variables and $s$ gates). Without such a bound, unit-cost arithmetic on unbounded integers would trivialize running times. Time is the cost counter at halting, and the output is the register block $R[1],\dots,R[R[0]]$ at halting.
--
--   A graph structure is given to the machine as the integer list $[n,s,\mathrm{out}]$ followed by three integers per gate: $[0,i,0]$ for the input $x_i$, $[1,0,0]$ for a constant gate, $[2,p,q]$ for an operation gate with slots $(p,q)$. A circuit is output as its number of gates, five integers per gate (the operation, then two operands of two integers each: a symbol kind $0$–$5$ with its gate, $6$ with a constant, or $7$ with a circuit gate), the number of designated outputs, and each output $(i,o)$ as $i$ followed by its operand.
--
--   **Formalization Note.** `Deterministic`, `WordBounded` and `HaltsWithOutput` follow the published `MinDegST_AddOne_Machine` pattern on `CongruencyTU.run` with `noOracle` and `noCoins`; `HaltsWithOutput P I B out` says the run halts at some step with cost at most $B$ and output exactly `out`. `encDag` and `encCircuit` are the encodings above.
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 11, Theorem 3 ("The bookkeeping takes time of the same order on a RAM")

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CancelFreeHessian_Formula_Circuit

open Classical

namespace CancelFreeHessian.Formula

/-!
# The word RAM of the bookkeeping clause, and the encodings of graphs and circuits

Tianlang Chen, *The Cancellation-Free Cost of Hessian Diagonals*, Theorem 3 (p. 11): "The
bookkeeping takes time of the same order on a RAM". The paper names no machine model. Every
algorithmic statement of the mission is about one program of the published integer RAM
`CongruencyTU.Program` (unit cost per instruction), run without coins and without oracle, whose
registers keep logarithmic words: one width constant `width`, fixed with the program, bounds the
bit length of every register at every step by `width · (1 + log₂(2 + scale))`, where `scale` is
the size of the input (for a graph with `n` variables and `s` gates, `n + s`). Without this
bound unit-cost arithmetic on unbounded integers would trivialize running times. The pattern
follows the published `MinDegST_AddOne_Machine`.

Time is the machine's cost counter at halting; the output is the register block
`R[1], …, R[R[0]]` at halting (`CongruencyTU.outputOf`).
-/

/-- A deterministic program: no coin instruction and no oracle query. -/
def Deterministic (P : CongruencyTU.Program) : Prop :=
  (∀ d, CongruencyTU.Instr.coin d ∉ P) ∧ ∀ a, CongruencyTU.Instr.query a ∉ P

/-- Logarithmic words: on input `I`, at every step every register of the run of `P` (no coins,
no oracle) has bit length at most `width · (1 + log₂(2 + scale))`. -/
def WordBounded (P : CongruencyTU.Program) (I : List ℤ) (width scale : ℕ) : Prop :=
  ∀ t j, Nat.size ((CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t).reg j).natAbs
    ≤ width * (1 + Nat.log2 (2 + scale))

/-- On input `I` the run of `P` (no coins, no oracle) halts with accumulated cost at most `B`,
and its output at halting is `out`. -/
def HaltsWithOutput (P : CongruencyTU.Program) (I : List ℤ) (B : ℕ) (out : List ℤ) : Prop :=
  ∃ t, CongruencyTU.isHalted P (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t)
      = true ∧
    (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t).cost ≤ B ∧
    CongruencyTU.outputOf (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t)
      = out

/-- A gate as three integers: `[0, i, 0]` for the input `x_i`, `[1, 0, 0]` for a constant gate,
`[2, p, q]` for an operation gate with slots `(p, q)`. -/
def encGate {n : ℕ} : Gate n → List ℤ
  | .input i => [0, (i.val : ℤ), 0]
  | .const => [1, 0, 0]
  | .op p q => [2, (p : ℤ), (q : ℤ)]

/-- The input encoding of a graph structure (its DAG with slots, no numerical parameters):
`[n, s, out]` followed by the three integers of each gate `0, …, s − 1`. -/
def encDag {n : ℕ} (D : Dag n) : List ℤ :=
  [(n : ℤ), (D.size : ℤ), (D.out : ℤ)] ++ (List.range D.size).flatMap fun k => encGate (D.gate k)

/-- An operand as two integers: `[0, v], …, [5, v]` for the symbols `val v, d1 v, d2 v, d11 v,
d12 v, d22 v`, `[6, c]` for the constant `c`, `[7, j]` for circuit gate `j`. -/
def encOperand : Operand → List ℤ
  | .sym (.val v) => [0, (v : ℤ)]
  | .sym (.d1 v) => [1, (v : ℤ)]
  | .sym (.d2 v) => [2, (v : ℤ)]
  | .sym (.d11 v) => [3, (v : ℤ)]
  | .sym (.d12 v) => [4, (v : ℤ)]
  | .sym (.d22 v) => [5, (v : ℤ)]
  | .const c => [6, (c : ℤ)]
  | .gate j => [7, (j : ℤ)]

/-- A circuit gate as five integers: `0` (addition) or `1` (multiplication), then its two
operands. -/
def encCGate : CGate → List ℤ
  | .add a b => 0 :: (encOperand a ++ encOperand b)
  | .mul a b => 1 :: (encOperand a ++ encOperand b)

/-- The output encoding of a circuit: the number of gates, the gates in order, the number of
designated outputs, and each output `(i, o)` as `i` followed by the operand `o`. -/
def encCircuit (K : Circuit) : List ℤ :=
  [(K.gates.length : ℤ)] ++ K.gates.flatMap encCGate ++ [(K.outs.length : ℤ)] ++
    K.outs.flatMap fun io => (io.1 : ℤ) :: encOperand io.2

end CancelFreeHessian.Formula


