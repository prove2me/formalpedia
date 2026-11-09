-- Prove2me | Definitions.Def_NadlerCLS_Circ
-- name    : NadlerCLS_Circ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:19.375422+00:00
-- url     : https://prove2.me/theorems/94d26748-8c24-4677-a59d-8b8a8d901c80
-- title:
--   Well-behaved arithmetic circuits
-- statement:
--   An **arithmetic circuit** is a list of gates $g_0, g_1, \dots$, each an input variable, a rational constant, or one of $+, -, \times, \min, \max$ and the comparison $>$ (which returns $1$ or $0$) applied to two earlier gates, together with a list of output gates. On a real input it is evaluated exactly, gate by gate.
--
--   A multiplication gate is a **true multiplication** if neither argument is a rational constant gate. Let $S$ be the binary description length of the circuit, rational constants included. The circuit is **well-behaved** if every directed path ending at an output contains at most $\log_2 S$ true multiplications, i.e. $2^{t}\le S$ for the true-multiplication depth $t$ of every output. A circuit is valid with $a$ inputs and $b$ outputs if every gate reads inputs $<a$ and earlier gates only, there are exactly $b$ outputs, and every output is well-behaved.
--
--   This is the representation of functions and metrics in all problems of the paper.
--
--   **Formalization Note** The gates, their binary code, their real evaluation and the true-multiplication depth are the public `NetworkEquilibriumCLS.LinearNash` ones (`ArithmeticGate`, `gateCode`, `gateEval`, `gateComplexity`). The module also defines the evaluation `Circ.eval` (raw, unclipped values) and the code `encCirc` (gate list, then output list, both length-prefixed).
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Section 2, p.7 (computational model; well-behaved arithmetic circuits, [FGHS23, Section 3.1.3])

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- A **straight-line arithmetic circuit** with a list of output gates (Xiong–Vlatakis-Gkaragkounis,
*On the Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held
version of 2026-11-03, sha256 1fcc5a02…6dc485, Section 2, p.7: "Functions and metrics are
represented by polynomial-size arithmetic circuits over rational constants and the operations
{+, −, ×, min, max, >}, where the comparison gate returns one or zero").

Gate `j` is `gates[j]`, a public `ArithmeticGate` whose arguments are earlier gate indices;
`outputs` lists the gates read as the circuit's outputs, in order.

**Formalization Note** The gate set, the gate code and the true-multiplication depth are the public
`NetworkEquilibriumCLS.LinearNash` ones (`ArithmeticGate`, `gateCode`, `gateComplexity`), which
match p.7: a multiplication is *true* unless one argument is a rational constant gate. Indices
are 0-based. -/
structure Circ where
  gates : List ArithmeticGate
  outputs : List ℕ

/-- The flag/true-multiplication-depth list of the gates of `C`, computed by the public
`gateComplexity` fold exactly as in the public `CLSInstance.Valid`. -/
def Circ.complexities (C : Circ) : List (Bool × ℕ) :=
  C.gates.foldl (fun prior g => prior ++ [gateComplexity prior g]) []

/-- A circuit is a **valid well-behaved circuit with `ins` inputs and `outs` outputs**
(arXiv:2609.14101, p.7: "Denoting S as the binary description length of a circuit C, including its
rational constants, C is well-behaved if every directed path ending at an output contains at most
log2 S true multiplication gates"): every gate reads inputs `< ins` and earlier gates only, there
are exactly `outs` outputs, each an existing gate, and the true-multiplication depth `t` of every
output satisfies `2 ^ t ≤ S`, where `S` is the length of the binary code of the gate list (rational
constants included). The size `S` is the circuit's own. -/
def Circ.Valid (C : Circ) (ins outs : ℕ) : Prop :=
  (∀ j : Fin C.gates.length, GateValid ins j.val C.gates[j.val]) ∧
  C.outputs.length = outs ∧
  ∀ o ∈ C.outputs, o < C.gates.length ∧
    2 ^ (C.complexities[o]?.getD (false, 0)).2 ≤ (encList gateCode C.gates).length

/-- The values of all gates of `C` on the input list `x`, by the public `gateEval` fold (exact
real arithmetic; the comparison gate returns one or zero). -/
noncomputable def Circ.values (C : Circ) (x : List ℝ) : List ℝ :=
  C.gates.foldl (fun prior g => prior ++ [gateEval x prior g]) []

/-- The raw (unclipped) value of output `j` of `C` at the real input `x`. -/
noncomputable def Circ.eval (C : Circ) {ins outs : ℕ} (x : Fin ins → ℝ) (j : Fin outs) : ℝ :=
  (C.values (List.ofFn x))[C.outputs[j.val]?.getD 0]?.getD 0

/-- The binary code of a circuit: its gate list and its output list, each length-prefixed with the
public self-delimiting codes. -/
def encCirc (C : Circ) : List Bool :=
  encList gateCode C.gates ++ encList encNat C.outputs

end NadlerCLS


