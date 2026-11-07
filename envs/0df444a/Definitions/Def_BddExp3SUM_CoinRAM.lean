-- Prove2me | Definitions.Def_BddExp3SUM_CoinRAM
-- name    : BddExp3SUM_CoinRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:36.835596+00:00
-- url     : https://prove2.me/theorems/c1371b67-8c1e-4c92-8c74-572ecb67a6bc
-- title:
--   The randomized word RAM: coin tape in the negative cells of the published machine
-- statement:
--   The machine is the published word RAM `EndStatement.exec`: a finite program over the instructions `one`, `add`, `sub`, `mul`, `load`, `store`, `bltz`, `accept`, `reject`, on words of width $W$, with unit cost per step. Randomness is a tape $\tau\in\{0,1\}^{\mathbb N}$ of independent fair bits, preloaded into the memory:
--
--   $$\text{cell } {-1-i} \text{ holds } \tau_i\ (i\ge 0),\qquad \text{cell } a\ge 0 \text{ holds the } a\text{-th input word}.$$
--
--   Reading a coin is one `load`. The law of the tape is the infinite product of fair coins.
--
--   The paper counts "random-bit generation" among its costs and generates all randomness "from C fair bits" (p.7). This definition gives that primitive to the published machine without changing its instruction set.
--
--   **Formalization Note** The machine has no coin instruction; a program can overwrite a coin only by writing to its cell.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §1, p.1 and §6, p.7

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

open MeasureTheory

namespace BddExp3SUM

/-!
# The randomized word RAM: the published machine run on a coin memory

Zeng, Wang, Cao, Dai, Wang, *Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group*,
STOC 2027 submission (manuscript sha256 19546c9a…), §1, p.1 and §6, p.7: the paper counts
"random-bit generation" among the costs and generates everything "from C fair bits".

**Formalization Note.** The machine is the published `EndStatement.exec` on programs
`List EndStatement.Instr` (word width `W`, instructions `one add sub mul load store bltz accept
reject`, each step costs 1), unchanged and without a coin instruction. Randomness is a tape
`ℕ → Bool` preloaded into the memory: negative cell `-1 - i` starts as `1` if bit `i` of the tape
is set and `0` otherwise. Reading a coin is one `load`. The non-negative cells start as
`EndStatement.loadWords W input`. A program can overwrite coins only by writing to them itself.
-/

/-- The memory at the start of a run on input `input` and coin tape `tape`: cell `-1 - i` holds
bit `i` of `tape` (as `1` or `0`), and cell `a ≥ 0` holds the `a`-th input word (and `0` past the
end of the input). -/
def coinMemory (W : ℕ) (input : List ℤ) (tape : ℕ → Bool) : ℤ → BitVec W :=
  fun a => if a < 0 then (if tape (-a - 1).toNat then 1 else 0) else EndStatement.loadWords W input a

/-- The law of the coin tape: independent fair bits. -/
noncomputable def coinLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

end BddExp3SUM


