-- Prove2me | Definitions.Def_ContractionLemma_Supplement_Common
-- name    : ContractionLemma_Supplement_Common
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:17:12.415375+00:00
-- url     : https://prove2.me/theorems/bf383193-614d-4868-8f73-cc67f13c4256
-- title:
--   Supplement conventions: $f(u)=u/\sqrt{\log_2(u+2)}$, runs within a time bound, output words, fan-in-two circuits, ETH
-- statement:
--   Shared conventions of the supplement.
--
--   1. **The scale function.** Logarithms are base two and $f(u)=u/\sqrt{\log_2(u+2)}$, so that a bound $E(u)=2^{O(u/\sqrt{\log u})}$ is written $2^{C f(u)}$ with an explicit constant $C$.
--   2. **Runs.** A machine is the published primitive multitape machine of the base mission; a run *within time $\tau$* is a halting run of at most $\tau$ steps with the stated output (no space requirement), used where a theorem bounds time only.
--   3. **Output words.** Integers and rationals are written in binary (sign, absolute value; reduced numerator and denominator); an optional answer is $0$ for "none" and $1$ followed by the answer otherwise.
--   4. **Fan-in-two circuits** (§2.3): $b$ input wires, then a sequence of $s$ gates, each an arbitrary Boolean function of two earlier wires, with designated output wires; the size is the number of gates.
--   5. **The Exponential Time Hypothesis** (App. A.7): there is $\delta>0$ such that no algorithm decides satisfiability of 3-CNF formulas $\varphi$ on $n$ variables in time $2^{\delta n}\,\mathrm{poly}(|\varphi|)$.
--
--   These conventions pin every $E(\cdot)$ and $\mathrm{poly}(\cdot)$ of the supplement's theorems to explicit expressions with constants fixed before the instance.
--
--   **Formalization Note** A 3-CNF is a published `SubexponentialSAT` CNF whose clauses have at most three literals, and $|\varphi|$ is the length of its published encoding.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), §2, p.16; p.3 (standing conventions); §2.3, p.18 (circuits); App. A.7, p.78 (ETH)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Shared cost and output conventions of the supplement** — Gajulapalli, *The Contraction Lemma
Beyond ETH* (manuscript, sha256 049caea1…), §2, p.16 ("Logarithms are base two. We write
`E(s) = 2^{O(s/√log s)}` and `f(u) = u/√log(u+2)`") and p.3 ("all algorithms are deterministic and
use polynomial space unless we say otherwise").

`fScale u = u / √(log₂(u+2))` is the paper's `f(u)`; a bound `E(u)` is written `2^{C·f(u)}` with an
explicit constant `C` fixed before the instance.

**Formalization Note.** `log` is `Real.logb 2`, and `f` uses `log₂(u+2)`, as the paper does, which
avoids the junk value of `log` at `0` and `1`. -/
noncomputable def fScale (u : ℝ) : ℝ := u / Real.sqrt (Real.logb 2 (u + 2))

/-- A run within time `τ` with no space requirement (used where a theorem bounds time only, e.g. the
algorithms that ETH excludes, p.78). -/
def RunsInTime (A : PrimitiveMachine) (out : Fin A.tapeCount) (input output : List Bool) (τ : ℝ) :
    Prop :=
  ∃ σ : ℝ, ContractionLemma.RunsWithin A out input output τ σ

/-- An integer in binary: a sign bit and the binary word of `|z|` (`countWord`). -/
def intWord (z : ℤ) : List Bool := Encoding.encodeList id [[decide (z < 0)], countWord z.natAbs]

/-- A rational in binary: its sign, and the numerator and denominator of its reduced form. -/
def ratWord (q : ℚ) : List Bool :=
  Encoding.encodeList id [[decide (q < 0)], countWord q.num.natAbs, countWord q.den]

/-- An optional word: `[false]` for none, `true :: w` for `some w`. -/
def optWord : Option (List Bool) → List Bool
  | none => [false]
  | some w => true :: w

/-- A word of bits, framed (`Encoding.frame`). -/
def bitsWord (w : List Bool) : List Bool := Encoding.frame w

/-- A natural number in binary, framed. -/
def natWord (k : ℕ) : List Bool := Encoding.frame (countWord k)

/-- **A fan-in-two gate** (p.18): an arbitrary Boolean function `op` of two earlier wires `a`, `b`
(indices into the inputs followed by the earlier gates). Functions of fewer arguments ignore one. -/
structure Gate where
  /-- the Boolean function of the gate -/
  op : Bool → Bool → Bool
  /-- first argument wire -/
  a : ℕ
  /-- second argument wire -/
  b : ℕ

/-- **A fan-in-two circuit** (§2.3, p.18): `nIn` input wires `0, …, nIn−1`, then a sequence of gates,
gate `j` being wire `nIn + j`; `outs` are the designated output wires. The size is the number of
gates. -/
structure FCircuit where
  /-- number of inputs -/
  nIn : ℕ
  /-- the gates in order -/
  gates : List Gate
  /-- designated output wires -/
  outs : List ℕ

namespace FCircuit

/-- Every gate reads earlier wires only, and every output is a wire. -/
def WellFormed (C : FCircuit) : Prop :=
  (∀ (j : ℕ) (h : j < C.gates.length), C.gates[j].a < C.nIn + j ∧ C.gates[j].b < C.nIn + j) ∧
  ∀ o ∈ C.outs, o < C.nIn + C.gates.length

/-- The size `s` of the circuit: its number of gates. -/
def size (C : FCircuit) : ℕ := C.gates.length

/-- The values of all wires on input `x` (inputs, then gates in order). -/
def wires (C : FCircuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun w g => w ++ [g.op (w.getD g.a false) (w.getD g.b false)]) x

/-- The values of the designated outputs on input `x`. -/
def eval (C : FCircuit) (x : List Bool) : List Bool :=
  C.outs.map fun o => (C.wires x).getD o false

/-- The encoding of a circuit: the number of inputs, each gate as the four values of its function and
its two argument wires in binary, and the output wires. -/
def encode (C : FCircuit) : List Bool :=
  Encoding.encodeList id
    [countWord C.nIn,
      Encoding.encodeList (fun g : Gate =>
        [g.op false false, g.op false true, g.op true false, g.op true true] ++
          Encoding.encodeList id [countWord g.a, countWord g.b]) C.gates,
      Encoding.encodeList countWord C.outs]

end FCircuit

/-- **The Exponential Time Hypothesis** (App. A.7, p.78): "there is a `δ > 0` such that no algorithm
decides satisfiability of 3-CNF formulas on `n` variables in time `2^{δn} poly(|φ|)`".

**Formalization Note.** A 3-CNF on `n` variables is a published `SubexponentialSAT` CNF over `Fin n`
whose clauses have at most three literals; `|φ|` is the length of its published encoding
`encodeCNF`. An algorithm is a `PrimitiveMachine` that outputs the one-bit word `[b]`, `b` the
satisfiability of `φ`; `poly(|φ|)` is `C (|φ|+1)^C` with `C` fixed before the formula. -/
def ETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬ ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
    ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost 3 F →
      RunsInTime A out (Encoding.encodeCNF F) [decide (0 < SAT.count F)]
        (C * (2 : ℝ) ^ (δ * n) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ C)

end ContractionLemma.Supplement


