-- Prove2me | Definitions.Def_AnyWE_CEFCorrectness_Circuit
-- name    : AnyWE_CEFCorrectness_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:50:10.501197+00:00
-- url     : https://prove2.me/theorems/f012576f-f0e9-47fa-b6d8-1819d132ad6a
-- title:
--   Bit strings, Boolean circuits with gates $g(l,r)$, circuit composition, probabilities over coins, polynomial bounds
-- statement:
--   A **bit string** of length $n$ is an element of $\{0,1\}^n$. A **Boolean circuit** $C$ with $a$ inputs and $b$ outputs consists of input wires $0,\dots,a-1$ and a list of gates; gate $j$ has a type $g_j\in\{\wedge,\vee,\oplus,\to,=,\neg,0,1\}$ and two input wires $l_j,r_j$, and defines wire $a+j$ with value $g_j(\omega_{l_j},\omega_{r_j})$ (negation reads only its first input, a constant reads neither). The list $\mathrm{out}(C)$ names the wire carrying each output, and $C(x)$ is the vector of output values on input $x\in\{0,1\}^a$. A gate that reads a wire that is not yet defined reads $0$; a circuit is **well formed** if every wire a gate reads is an earlier wire and every output is a wire. The **size** $|C|$ is the number of gates, and the **encoding length** of $C$ with explicit input and output wire lists is $a+b+|C|$.
--
--   Larger circuits are built by composition: a circuit is embedded into a partially built one with its inputs wired to existing wires, and the copy's wires are returned for further use. A probabilistic circuit is a circuit whose last input block is its random tape.
--
--   For a property $P$ of strings $r\in\{0,1\}^L$, $\Pr_r[P(r)]$ is the fraction of the $2^L$ strings satisfying it. A function $f:\mathbb N\to\mathbb N$ is **polynomial** if $f(\lambda)=p(\lambda)$ for a polynomial $p$ with natural coefficients, and $f=O(\log\lambda)$ if $f(\lambda)\le C\log_2\lambda$ for a constant $C$ and all sufficiently large $\lambda$.
--
--   These circuits are the paper's computation model throughout: every polynomial-time algorithm, relation and sampler is represented by its unrolling into circuits (Remark 4.2), and adversaries are non-uniform circuits whose advice is hardwired as constant gates.
--
--   **Formalization Note.** The gate basis is the set of connectives of §4.1.1 plus negation and constants. Undefined wire references read $0$ both in evaluation and in the gate equations of the formula item, so every circuit (well formed or not) has one meaning.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), p. 22, §4.2 (security conventions, Remark 4.2); p. 34, Definition 4.25 (gates g(l, r)); p. 39, Definition 5.1

import Mathlib
set_option autoImplicit false

/-!
# Bit strings, Boolean circuits, probabilities over coins, polynomial bounds

Jain, Jin, Mathialagan, *SNARGs from any Witness Encryption, and More*, STOC 2027 submission
(manuscript sha256 9bc2f227…), §4.2 p. 22 (security conventions, Remark 4.2: algorithms and
relations are unrolled into circuits), §4.3.1 p. 34 (Definition 4.25 uses circuits with gates
`g(l, r)`), §5.1 p. 39 (circuits with hardwired data).

A circuit `C : Circuit a b` has `a` input wires `0, …, a-1`; gate `j` of `C.gates` defines wire
`a + j` as `op(wire l, wire r)`; `C.out i` is the wire carrying output `i`. A reference to a wire
that is not yet defined (an index `≥ a + j` at gate `j`, or `≥ a + |gates|` at an output) reads the
constant `0`; `WF` excludes such references. The size `|C|` is the number of gates. All algorithms
of the paper (polynomial-time machines) are represented by their unrollings into such circuits.
-/

namespace AnyWE.CEFCorrectness

/-- A bit string of length `n`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The first `a` entries of a vector of length `a + b`. -/
def vleft {α : Type} {a b : ℕ} (v : Fin (a + b) → α) : Fin a → α := fun i => v (Fin.castAdd b i)

/-- The last `b` entries of a vector of length `a + b`. -/
def vright {α : Type} {a b : ℕ} (v : Fin (a + b) → α) : Fin b → α := fun i => v (Fin.natAdd a i)

/-- The first `a` bits of a string of length `a + b`. -/
def Bits.left {a b : ℕ} (v : Bits (a + b)) : Bits a := vleft v

/-- The last `b` bits of a string of length `a + b`. -/
def Bits.right {a b : ℕ} (v : Bits (a + b)) : Bits b := vright v

/-- Bit `j` of a string (`0` past the end). -/
def Bits.bitAt {n : ℕ} (v : Bits n) (j : ℕ) : Bool := if h : j < n then v ⟨j, h⟩ else false

/-- The `len` bits starting at position `off` (bits past the end read `0`). -/
def Bits.slice {n : ℕ} (v : Bits n) (off len : ℕ) : Bits len :=
  fun j => if h : off + j.val < n then v ⟨off + j.val, h⟩ else false

/-- A string read at another length: identical on the common prefix, `0` beyond. -/
def Bits.resize {n : ℕ} (v : Bits n) (m : ℕ) : Bits m := Bits.slice v 0 m

/-- The number with binary digits `v` (bit `j` has weight `2^j`). -/
def Bits.toNat {n : ℕ} (v : Bits n) : ℕ := ∑ j : Fin n, if v j then 2 ^ j.val else 0

/-- The binary encoding of `i` with `w` digits (bit `j` has weight `2^j`). -/
def binBits (w i : ℕ) : Bits w := fun j => i.testBit j.val

/-- Gate types: the connectives of §4.1.1 (`∧, ∨, ⊕, →, =`), negation and the constants. -/
inductive GateOp
  | and | or | xor | imp | iff | not
  | const (c : Bool)
  deriving DecidableEq

/-- The Boolean function computed by a gate type (`not` reads its first input only, a constant
reads neither). -/
def GateOp.apply : GateOp → Bool → Bool → Bool
  | .and, x, y => x && y
  | .or, x, y => x || y
  | .xor, x, y => Bool.xor x y
  | .imp, x, y => !x || y
  | .iff, x, y => x == y
  | .not, x, _ => !x
  | .const c, _, _ => c

/-- The number of inputs a gate type reads. -/
def GateOp.arity : GateOp → ℕ
  | .not => 1
  | .const _ => 0
  | _ => 2

/-- A gate: its type and its two input wires `l`, `r`. -/
structure Gate where
  op : GateOp
  l : ℕ
  r : ℕ
  deriving DecidableEq

/-- A Boolean circuit with `a` input wires and `b` output wires. -/
structure Circuit (a b : ℕ) where
  gates : List Gate
  out : Fin b → ℕ

namespace Circuit

variable {a b : ℕ}

/-- The size `|C|`: the number of gates. -/
def size (C : Circuit a b) : ℕ := C.gates.length

/-- The encoding length of a circuit with explicit input and output wire lists (Definition 5.3):
inputs, outputs and gates. -/
def encLen (C : Circuit a b) : ℕ := a + b + C.gates.length

/-- The number of wires. -/
def numWires (C : Circuit a b) : ℕ := a + C.gates.length

/-- Well-formedness: every input a gate reads is an earlier wire, every output is a wire. -/
def WF (C : Circuit a b) : Prop :=
  (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (1 ≤ g.op.arity → g.l < a + j) ∧ (2 ≤ g.op.arity → g.r < a + j)) ∧
    ∀ i, C.out i < a + C.gates.length

/-- The values of all wires on input `x`, in wire order (a gate reading an undefined wire reads `0`). -/
def wireVals (C : Circuit a b) (x : Bits a) : List Bool :=
  C.gates.foldl (fun (vals : List Bool) (g : Gate) =>
    vals ++ [g.op.apply (vals.getD g.l false) (vals.getD g.r false)]) (List.ofFn x)

/-- The output `C(x)`. -/
def eval (C : Circuit a b) (x : Bits a) : Bits b :=
  fun i => (C.wireVals x).getD (C.out i) false

end Circuit

/-! ### Building circuits by composition -/

section Build
variable {a b : ℕ}

/-- A partially built circuit: `nin` input wires and the gates so far (gate `j` is wire `nin + j`). -/
structure Builder where
  nin : ℕ
  gates : Array Gate

/-- The index of the next wire. -/
def Builder.next (B : Builder) : ℕ := B.nin + B.gates.size

/-- The builder monad. -/
abbrev BM := StateM Builder

/-- Add a gate and return its wire. -/
def BM.gate (op : GateOp) (l r : ℕ) : BM ℕ :=
  modifyGet fun B => (B.next, { B with gates := B.gates.push ⟨op, l, r⟩ })

/-- A constant wire. -/
def BM.const (c : Bool) : BM ℕ := BM.gate (.const c) 0 0

/-- `x ∧ y`. -/
def BM.and (x y : ℕ) : BM ℕ := BM.gate .and x y

/-- A vector of results computed one coordinate after the other. -/
def BM.vec {α : Type} : (n : ℕ) → (Fin n → BM α) → BM (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, f => do
    let x ← f 0
    let xs ← BM.vec n (fun i => f i.succ)
    pure (Fin.cons x xs)

/-- Copy the gates of a circuit (gate `j` read relative to `a + j`), wiring its inputs by `wmap`
and redirecting every undefined reference to the wire `z`. -/
def BM.copyGates (a : ℕ) (wmap : ℕ → ℕ) (z : ℕ) : ℕ → List Gate → BM Unit
  | _, [] => pure ()
  | j, g :: gs => do
    let rd : ℕ → ℕ := fun w => if w < a + j then wmap w else z
    let _ ← BM.gate g.op (rd g.l) (rd g.r)
    BM.copyGates a wmap z (j + 1) gs

/-- Embed a circuit with its inputs wired to `inp`; returns the new wire of every wire of `C`
(undefined wires map to a fresh constant-`0` wire). -/
def BM.embedAll (C : Circuit a b) (inp : Fin a → ℕ) : BM (ℕ → ℕ) := do
  let z ← BM.const false
  let base := (← get).next
  let wmap : ℕ → ℕ := fun w =>
    if h : w < a then inp ⟨w, h⟩ else if w < a + C.gates.length then base + (w - a) else z
  BM.copyGates a wmap z 0 C.gates
  pure wmap

/-- Embed a circuit with its inputs wired to `inp`; returns its output wires. -/
def BM.embed (C : Circuit a b) (inp : Fin a → ℕ) : BM (Fin b → ℕ) := do
  let w ← BM.embedAll C inp
  pure fun i => w (C.out i)

/-- Run a builder on `a` fresh input wires; its result is the output wire list. -/
def Circuit.build (a b : ℕ) (m : (Fin a → ℕ) → BM (Fin b → ℕ)) : Circuit a b :=
  let p := (m (fun i => i.val)).run { nin := a, gates := #[] }
  { gates := p.2.gates.toList, out := p.1 }

end Build

/-! ### Coins, probabilities and asymptotics -/

/-- `Pr_r[P r]` for a uniformly random `r ∈ {0,1}^L`. -/
noncomputable def prob (L : ℕ) (P : Bits L → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ L

/-- `f` is (the evaluation of) a polynomial with natural coefficients. -/
def IsPoly (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n = p.eval n

/-- `f = O(log λ)`: `f λ ≤ C log₂ λ` for some constant `C` and all sufficiently large `λ`. -/
def IsOLog (f : ℕ → ℕ) : Prop := ∃ C : ℕ, ∀ᶠ n in Filter.atTop, f n ≤ C * Nat.log 2 n

end AnyWE.CEFCorrectness


