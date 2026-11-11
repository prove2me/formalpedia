-- Prove2me | Definitions.Def_ConstructiveArboricity_Exact_Machine
-- name    : ConstructiveArboricity_Exact_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:20.869795+00:00
-- url     : https://prove2.me/theorems/6d4c49f4-7df9-49d5-bc7c-2d57a1f3c219
-- title:
--   Finite deterministic word-RAM runs and sparse graph input/output
-- statement:
--   A program is a finite list of instructions of the published deterministic word RAM. Each word has $W$ bits. Instructions write one, perform modular addition, subtraction or multiplication, load or store indirectly, branch on a signed negative word, or halt with an acceptance or rejection verdict. Every executed instruction, including a halt, costs one step. There is no primitive flow-solver instruction.
--
--   For supplied integer lists $I,O$, $\operatorname{Runs}(P,I,O,W,t)$ means that execution from the first instruction, with $I$ in consecutive cells and zeros elsewhere, accepts within $t$ steps. The final signed words immediately after the input equal $O$. Output computation and all subroutine execution occur within this same interpreter.
--
--   The condition on word width is $W\ge b(\lfloor\log_2(s+2)\rfloor+1)$, where $b$ is chosen before the input and $s$ collects its size parameters. All such widths must work. In particular this includes words of logarithmic length, sufficient for labels, addresses and polynomially bounded capacities and costs. The total logarithm convention is $\log(n+2)$.
--
--   This is the operational reading of the source's algorithmic time claims; the general instruction interpreter is reused without modification.
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1476.pdf, Theorem 1, p.4; §2, p.7

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_ConstructiveArboricity_Exact_Graph

/-! Operational reading of the running times of Gholami et al., STOC 2027
submission #1476. A single finite deterministic program precedes every input
and every accuracy exponent. The imported interpreter charges every instruction,
including indirect memory access and halting. There are no native flow oracles.
Input words are preloaded. Output occupies cells after the input. -/
namespace ConstructiveArboricity.Exact

abbrev Program := List TrulySubcubicAPSP.Instr

def Runs (P : Program) (input output : List ℤ) (W t : ℕ) : Prop :=
  ∃ mem, TrulySubcubicAPSP.exec P t 0 (TrulySubcubicAPSP.loadWords W input) =
      some (true, mem) ∧
    ∀ j : Fin output.length, (mem (input.length + j.val : ℕ)).toInt = output[j]

/-- Every width above a fixed multiple of the binary input-parameter length works.
In particular, the assertion includes an O(log size)-bit machine and does not
gain arbitrary unit-cost real or unbounded-integer arithmetic. -/
def WidthEnough (b size W : ℕ) : Prop :=
  b * (Nat.log2 (size + 2) + 1) ≤ W

noncomputable def logSize (n : ℕ) : ℝ := Real.log (n + 2)

end ConstructiveArboricity.Exact


