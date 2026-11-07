-- Prove2me | Definitions.Def_LowDepthPRF_Circuit
-- name    : LowDepthPRF_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:33:56.110509+00:00
-- url     : https://prove2.me/theorems/c1a22e7f-0d90-493e-a3d6-a8da954c51eb
-- title:
--   Boolean circuits with oracle gates: size, depth, query count
-- statement:
--   A **circuit** with $n$ input bits and $m$ output bits is a list of gates in topological order. Wires are numbered: the inputs are wires $0,\dots,n-1$, and each gate appends its output wires after all existing wires. The gates are constants, NOT (fan-in 1), AND and OR (fan-in 2), and **oracle gates**. An oracle gate reads $a$ wires and appends the $b$ answer wires of an oracle $O:\{0,1\}^a\to\{0,1\}^b$. Fan-out is unbounded, and a later oracle gate may read the answers of earlier ones, so queries can be adaptive. Each output bit is one wire.
--
--   A circuit is **well formed** if each gate reads only wires that already exist and each output is an existing wire. Its **size** is the number of gates; an oracle gate counts $1$ whatever its arity, and inputs are not gates. Its **depth** is the length of the longest path to an output, counted in gates: inputs and constants have depth $0$, and every other gate has depth one more than the deepest wire it reads. Its **query count** is the number of oracle gates. A function $f:\{0,1\}^n\to\{0,1\}^m$ is computed within size $s$ and depth $d$ if **one** well-formed circuit without oracle access has both bounds and agrees with $f$ on every input.
--
--   This is the circuit model of the paper ("bounded fan-in $\{\mathrm{AND},\mathrm{OR},\mathrm{NOT}\}$ gates"). Its adversaries are the same circuits with oracle gates.
--
--   **Formalization Note** Bit strings are `Fin n → Bool`. A circuit without oracle access is a `Circuit 0 0 n m`. Evaluation reads a missing wire as `false`, which never happens in a well-formed circuit. Counting an oracle gate as $1$, and not counting inputs, is what makes the output-restriction lemma (Lemma 3.12) lossless.
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), §3 'Circuit model', p.11 (pdf 13); Definitions 3.1–3.2, p.11 (pdf 13)

import Mathlib

namespace LowDepthPRF

/-!
# Boolean circuits with oracle gates

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), §3 "Circuit model", p.11, and Definitions 3.1–3.2, p.11: "We work in the
Boolean circuit model with bounded fan-in {AND, OR, NOT} gates", and "We model an adversary by a
circuit equipped with oracle gates".

**Formalization Note.**
* Bit strings of length `n` are `Fin n → Bool`.
* A circuit is a straight-line program. Wires are numbered: the `n` input wires are `0, …, n-1`;
  every instruction appends its output wires after all existing wires. The instructions are
  `const` (one wire), `not` (fan-in 1), `and`, `or` (fan-in 2), and `oracle`, which reads `oa`
  wires and appends the `ob` answer wires of the oracle `(Fin oa → Bool) → (Fin ob → Bool)`.
  Fan-out is unbounded. Because an oracle gate may read the answer wires of earlier oracle gates,
  queries can be adaptive.
* A circuit is well formed (`WF`) when every instruction reads only wires that already exist and
  every output is an existing wire. All complexity statements quantify over well-formed circuits
  only. (Evaluation reads a missing wire as `false`; that value is never used for a well-formed
  circuit.)
* **Size** is the number of instructions, i.e. of non-input gates: a constant gate counts 1 and
  an oracle gate counts 1, whatever its arity. **Depth** is the length of the longest path to an
  output, counted in gates: input wires and constant gates have depth 0, a `not`/`and`/`or` gate
  or an oracle answer wire has depth one more than the deepest wire it reads. The query count is
  the number of oracle gates.
* A circuit without oracle access is a `Circuit 0 0 n m` (oracle gates there read and return no
  wires and are useless); it is evaluated with the unique oracle of that type.
-/

/-- One instruction of a circuit whose oracle has `oa` input and `ob` output bits. Wire indices
refer to the wire numbering described in the module docstring. -/
inductive Instr (oa ob : ℕ) : Type
  /-- A constant gate. -/
  | const (v : Bool)
  /-- A NOT gate reading wire `i`. -/
  | not (i : ℕ)
  /-- An AND gate reading wires `i`, `j`. -/
  | and (i j : ℕ)
  /-- An OR gate reading wires `i`, `j`. -/
  | or (i j : ℕ)
  /-- An oracle gate whose `k`-th input bit is wire `args k`; it appends `ob` answer wires. -/
  | oracle (args : Fin oa → ℕ)

namespace Instr

variable {oa ob : ℕ}

/-- Number of wires the instruction appends. -/
def width : Instr oa ob → ℕ
  | .oracle _ => ob
  | _ => 1

/-- Every wire the instruction reads is `< k`. -/
def ReadsBelow (k : ℕ) : Instr oa ob → Prop
  | .const _ => True
  | .not i => i < k
  | .and i j => i < k ∧ j < k
  | .or i j => i < k ∧ j < k
  | .oracle args => ∀ a, args a < k

/-- Whether the instruction is an oracle gate. -/
def isOracle : Instr oa ob → Bool
  | .oracle _ => true
  | _ => false

/-- Append the values of the instruction's output wires to the wire values `w`. -/
def step (O : (Fin oa → Bool) → (Fin ob → Bool)) (w : List Bool) : Instr oa ob → List Bool
  | .const v => w ++ [v]
  | .not i => w ++ [!(w.getD i false)]
  | .and i j => w ++ [w.getD i false && w.getD j false]
  | .or i j => w ++ [w.getD i false || w.getD j false]
  | .oracle args => w ++ List.ofFn (O (fun a => w.getD (args a) false))

/-- Append the depths of the instruction's output wires to the wire depths `dw`. -/
def depthStep (dw : List ℕ) : Instr oa ob → List ℕ
  | .const _ => dw ++ [0]
  | .not i => dw ++ [dw.getD i 0 + 1]
  | .and i j => dw ++ [max (dw.getD i 0) (dw.getD j 0) + 1]
  | .or i j => dw ++ [max (dw.getD i 0) (dw.getD j 0) + 1]
  | .oracle args =>
      dw ++ List.replicate ob ((Finset.univ : Finset (Fin oa)).sup (fun a => dw.getD (args a) 0) + 1)

end Instr

/-- A circuit with `n` input bits, `m` output bits, and oracle gates for an oracle
`(Fin oa → Bool) → (Fin ob → Bool)`. -/
structure Circuit (oa ob n m : ℕ) where
  /-- The gates, in topological order. -/
  gates : List (Instr oa ob)
  /-- The wire carrying each output bit. -/
  out : Fin m → ℕ

namespace Circuit

variable {oa ob n m : ℕ}

/-- Well-formedness of a gate list started with `k` existing wires: each gate reads only existing
wires. -/
def GatesWF : ℕ → List (Instr oa ob) → Prop
  | _, [] => True
  | k, g :: gs => g.ReadsBelow k ∧ GatesWF (k + g.width) gs

/-- Number of wires after running a gate list started with `k` wires. -/
def wireCount : ℕ → List (Instr oa ob) → ℕ
  | k, [] => k
  | k, g :: gs => wireCount (k + g.width) gs

/-- A well-formed circuit: gates read only existing wires and outputs are existing wires. -/
def WF (C : Circuit oa ob n m) : Prop :=
  GatesWF n C.gates ∧ ∀ j, C.out j < wireCount n C.gates

/-- Size: the number of non-input gates (an oracle gate counts 1). -/
def size (C : Circuit oa ob n m) : ℕ := C.gates.length

/-- Number of oracle gates (oracle queries). -/
def queries (C : Circuit oa ob n m) : ℕ := C.gates.countP Instr.isOracle

/-- The values of all wires on input `x` with oracle `O`. -/
def wires (C : Circuit oa ob n m) (O : (Fin oa → Bool) → (Fin ob → Bool)) (x : Fin n → Bool) :
    List Bool :=
  C.gates.foldl (Instr.step O) (List.ofFn x)

/-- The output of the circuit on input `x` with oracle `O`. -/
def eval (C : Circuit oa ob n m) (O : (Fin oa → Bool) → (Fin ob → Bool)) (x : Fin n → Bool) :
    Fin m → Bool :=
  fun j => (C.wires O x).getD (C.out j) false

/-- The depths of all wires. -/
def wireDepths (C : Circuit oa ob n m) : List ℕ :=
  C.gates.foldl Instr.depthStep (List.replicate n 0)

/-- Depth: the longest input-to-output path, counted in gates (`0` with no outputs). -/
def depth (C : Circuit oa ob n m) : ℕ :=
  (Finset.univ : Finset (Fin m)).sup (fun j => C.wireDepths.getD (C.out j) 0)

/-- Evaluation of a circuit without oracle access. -/
def evalPlain (C : Circuit 0 0 n m) (x : Fin n → Bool) : Fin m → Bool :=
  C.eval (fun _ i => i.elim0) x

end Circuit

/-- A plain Boolean circuit computes `f` within size `s` and depth `d`: one well-formed circuit,
with both bounds, whose output equals `f` on every input. -/
def ComputesWithin {n m : ℕ} (f : (Fin n → Bool) → (Fin m → Bool)) (s d : ℝ) : Prop :=
  ∃ C : Circuit 0 0 n m, C.WF ∧ (C.size : ℝ) ≤ s ∧ (C.depth : ℝ) ≤ d ∧ ∀ x, C.evalPlain x = f x

end LowDepthPRF


