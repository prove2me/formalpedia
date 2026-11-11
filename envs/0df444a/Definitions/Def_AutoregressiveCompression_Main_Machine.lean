-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Machine
-- name    : AutoregressiveCompression_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:10:52.136145+00:00
-- url     : https://prove2.me/theorems/5a5cce7c-bd1e-4fd4-92e3-802027a532bc
-- title:
--   Bit encodings, finite Turing-machine programs and Boolean circuits with rational outputs
-- statement:
--   Binary strings, unary numbers, a self-delimiting injective tuple encoding, one-hot symbol encodings, encodings of sample blocks, coin strings and rationals. A program is a Mathlib finite multi-stack Turing machine (Turing.FinTM2) whose input and output stacks hold bits; P.OutputsWithin x y t says that on input x it halts with output y within t steps. A circuit is a straight-line Boolean circuit (input, constant, NOT, AND, OR gates) with numerator and denominator output wires, so that it computes a rational value; it has an injective bit description. An autoregressive circuit for length N computes P(u,a) ∈ (0,1) ∩ ℚ with Σₐ P(u,a) = 1 for all u of length < N (Definition 4.5(c)), and represents Q_P(z) = ∏ᵢ P(z_{<i}, zᵢ). KL divergence (in bits, +∞ on support mismatch) and statistical distance against such weights, and the joint law of m samples and r independent fair coins.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Sections 4.2–4.4, printed pp.16–21 / PDF pp.18–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Prefix

/-!
Computational substrate for Hirahara–Nanashima, STOC 2027 submission #793
(October 2026), §4.2–§4.4, printed pp.16–21 / PDF pp.18–23.

* Algorithms are Mathlib finite multi-stack Turing machines (`Turing.FinTM2`) whose
  input and output stacks hold bits; their cost is the actual number of machine steps.
* A randomized algorithm is a machine that additionally reads a uniformly random
  coin string of polynomial length on its input.
* Finite objects (unary numbers, blocks of samples, coin strings, rationals and
  circuits) are written as bits by explicit injective encodings.
* Circuits are explicit straight-line Boolean circuits with an evaluation semantics;
  an autoregressive circuit outputs a rational number as numerator and denominator
  bits.
-/

open scoped Classical

noncomputable section

namespace AutoregressiveCompression.Main

/-- Binary strings. -/
abbrev Bits := List Bool

/-- The unary string `1ᵏ`. -/
def unary (k : ℕ) : Bits := List.replicate k true

/-- Self-delimiting encoding of a tuple of bit strings: every bit is doubled and
each component is followed by the separator `01`. This is injective. -/
def frame : List Bits → Bits
  | [] => []
  | b :: bs => (b.flatMap fun x => [x, x]) ++ [false, true] ++ frame bs

/-- One-hot encoding of a symbol of a finite alphabet (a fixed enumeration). -/
def symBits {Γ : Type} [Fintype Γ] (a : Γ) : Bits :=
  List.ofFn fun i : Fin (Fintype.card Γ) => decide (i = Fintype.equivFin Γ a)

/-- A string over a finite alphabet, written symbol by symbol. -/
def stringBits {Γ : Type} [Fintype Γ] (u : List Γ) : Bits :=
  u.flatMap symBits

/-- A block of samples, as the list of its strings. -/
def blockList {Γ : Type} {N m : ℕ} (xs : Fin m → Word Γ N) : List (List Γ) :=
  List.ofFn fun i => List.ofFn (xs i)

/-- Encoding of a block of strings (each string framed). -/
def blockBits {Γ : Type} [Fintype Γ] (xs : List (List Γ)) : Bits :=
  frame (xs.map stringBits)

/-- A coin string as bits. -/
def coinBits {r : ℕ} (ω : Fin r → Bool) : Bits := List.ofFn ω

/-- Uniform law of `r` fair coins. -/
def coinLaw (r : ℕ) : PMF (Fin r → Bool) := PMF.uniformOfFintype (Fin r → Bool)

/-- Binary digits of a natural number (least significant first, no leading zero). -/
def natBits (k : ℕ) : Bits := (Nat.digits 2 k).map fun d => decide (d = 1)

/-- Value of a list of bits, least significant first. -/
def bitsValue : Bits → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsValue bs

/-- Encoding of a rational number: sign, numerator magnitude, denominator. -/
def ratBits (q : ℚ) : Bits :=
  frame [[decide (q < 0)], natBits q.num.natAbs, natBits q.den]

/-- A program: a finite multi-stack Turing machine whose input and output stack
alphabets are identified with bits. -/
structure Program where
  tm : Turing.FinTM2
  inAlph : tm.Γ tm.k₀ ≃ Bool
  outAlph : tm.Γ tm.k₁ ≃ Bool

/-- `P` on input `x` halts with output `y` within `t` machine steps
(Mathlib's `TM2OutputsInTime`). -/
def Program.OutputsWithin (P : Program) (x y : Bits) (t : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime P.tm (x.map P.inAlph.symm)
    (some (y.map P.outAlph.symm)) t)

/-! ### Boolean circuits -/

/-- A gate of a straight-line circuit. Wire `i` is the output of the `i`th gate;
a gate may read input bits and outputs of earlier gates. -/
inductive Gate
  | input (i : ℕ)
  | const (b : Bool)
  | not (i : ℕ)
  | and (i j : ℕ)
  | or (i j : ℕ)

/-- Value of a gate, given the input and the values of the earlier gates. A
reference to a not-yet-computed wire or a missing input bit reads `false`. -/
def Gate.eval (x : Bits) (vals : List Bool) : Gate → Bool
  | .input i => x.getD i false
  | .const b => b
  | .not i => !(vals.getD i false)
  | .and i j => vals.getD i false && vals.getD j false
  | .or i j => vals.getD i false || vals.getD j false

/-- A Boolean circuit with a rational output: the value is the number written on
the numerator wires divided by the number written on the denominator wires
(a zero denominator gives the value `0`, which no valid model may output). -/
structure Circuit where
  gates : List Gate
  numWires : List ℕ
  denWires : List ℕ

/-- Values of all gates on input `x`. -/
def Circuit.wires (C : Circuit) (x : Bits) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [g.eval x vals]) []

/-- Rational output of the circuit on input `x`. -/
def Circuit.value (C : Circuit) (x : Bits) : ℚ :=
  let w := C.wires x
  (bitsValue (C.numWires.map fun i => w.getD i false) : ℚ) /
    (bitsValue (C.denWires.map fun i => w.getD i false) : ℚ)

/-- Injective bit encoding of a gate. -/
def Gate.bits : Gate → Bits
  | .input i => frame [[false, false], unary i]
  | .const b => frame [[false, true], [b]]
  | .not i => frame [[true, false], unary i]
  | .and i j => frame [[true, true], [false], unary i, unary j]
  | .or i j => frame [[true, true], [true], unary i, unary j]

/-- Injective bit encoding of a circuit (its description). -/
def Circuit.bits (C : Circuit) : Bits :=
  frame [frame (C.gates.map Gate.bits), frame (C.numWires.map unary),
    frame (C.denWires.map unary)]

/-- Circuit input for a context `u` (of length `< N`) and a next symbol `a`:
`N` one-hot slots over `Σ ∪ {⊥}` (unused slots are `⊥`), then `a` one-hot. -/
def contextBits {Sym : Type} [Fintype Sym] (N : ℕ) (u : List Sym) (a : Sym) : Bits :=
  (List.ofFn fun i : Fin N => symBits (u[i.val]? : Option Sym)).flatten ++ symBits a

/-- The value `P(u,a)` computed by an autoregressive circuit, as a real number. -/
def Circuit.nextProb {Sym : Type} [Fintype Sym] (C : Circuit) (N : ℕ)
    (u : List Sym) (a : Sym) : ℝ :=
  (C.value (contextBits N u a) : ℝ)

/-- Definition 4.5(c): the circuit is an autoregressive model on `Σᴺ`: for every
`u` of length `< N` and every `a`, `P(u,a) ∈ (0,1) ∩ ℚ`, and `∑ₐ P(u,a) = 1`. -/
def Circuit.IsAutoregressive {Sym : Type} [Fintype Sym] (C : Circuit) (N : ℕ) : Prop :=
  ∀ u : List Sym, u.length < N →
    (∀ a, 0 < C.nextProb N u a ∧ C.nextProb N u a < 1) ∧
    ∑ a, C.nextProb N u a = 1

/-- `Q_P(z) = ∏_{i=1}^N P(z_{<i}, z_i)`. -/
def Circuit.modelMass {Sym : Type} [Fintype Sym] (C : Circuit) (N : ℕ)
    (z : Word Sym N) : ℝ :=
  ∏ i : Fin N, C.nextProb N ((List.ofFn z).take i.val) (z i)

/-- KL divergence in bits of a PMF against a nonnegative weight function, with the
same `+∞` support-mismatch convention as `klBits`. -/
def klBitsWeights {Ω : Type} [Fintype Ω] (P : PMF Ω) (q : Ω → ℝ) : EReal :=
  if ∃ x, P x ≠ 0 ∧ q x = 0 then ⊤
  else ((∑ x, if P x = 0 then 0
    else mass P x * Real.logb 2 (mass P x / q x) : ℝ) : EReal)

/-- Statistical distance between a PMF and a weight function. -/
def tvWeights {Ω : Type} [Fintype Ω] (P : PMF Ω) (q : Ω → ℝ) : ℝ :=
  (∑ x, |mass P x - q x|) / 2

/-- Law of `m` samples together with `r` independent fair coins. -/
def samplesAndCoins {Ω : Type} (P : PMF Ω) (m r : ℕ) :
    PMF ((Fin m → Ω) × (Fin r → Bool)) :=
  (iid P m).bind fun xs => (coinLaw r).map fun ω => (xs, ω)

end AutoregressiveCompression.Main


