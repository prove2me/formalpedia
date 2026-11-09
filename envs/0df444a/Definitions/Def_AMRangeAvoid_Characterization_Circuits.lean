-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Circuits
-- name    : AMRangeAvoid_Characterization_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:04.31444+00:00
-- url     : https://prove2.me/theorems/1b19ebcf-c9db-400a-8a1b-104d856f65e2
-- title:
--   Ordinary multi-output Boolean circuits
-- statement:
--   A circuit has an explicit input arity, a finite list of gates in topological order, and an ordered list of output wires. Gates are constants, input reads, NOT, AND and OR. Validity requires existing input indices and references only to earlier gates; there is no fan-out restriction. Evaluation follows the gate list and returns the indicated outputs. Each input bit has an explicit code slot, and gates and output references have binary codes. Decoding rejects invalid references and trailing data.
--
--   For a circuit $C$ with $a$ input bits,
--   $$\operatorname{Im}(C)=\{C(u):u\in\{0,1\}^a\}.$$
--   This representation supports ordinary expanding circuits and membership/structure circuits without substituting truth tables or oracle gates.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Definition 2.7, printed p.10 (PDF p.12), §2.2, printed p.11 (PDF p.13), Definition 3.1, printed p.14 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Encoding

/-! Ordinary multi-output circuits and their explicit binary syntax.
Li, STOC 2027 submission #502, Definition 2.7, printed p.10; Definition 3.1,
printed p.14. This is a general circuit object, independent of SSLB and AM.
-/
namespace AMRangeAvoid.Characterization

inductive Gate where
  | const (b : Bool)
  | input (i : ℕ)
  | neg (i : ℕ)
  | conj (i j : ℕ)
  | disj (i j : ℕ)
  deriving DecidableEq, Repr, Inhabited

def Gate.eval (x values : Bits) : Gate → Bool
  | .const b => b
  | .input i => x.getD i false
  | .neg i => !(values.getD i false)
  | .conj i j => values.getD i false && values.getD j false
  | .disj i j => values.getD i false || values.getD j false

def Gate.valid (inputs earlier : ℕ) : Gate → Bool
  | .const _ => true
  | .input i => decide (i < inputs)
  | .neg i => decide (i < earlier)
  | .conj i j | .disj i j => decide (i < earlier ∧ j < earlier)

structure Circuit where
  inputs : ℕ
  gates : List Gate
  outputs : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Evaluate each gate once in list order. Outputs are ordered gate references. -/
def Circuit.eval (C : Circuit) (x : Bits) : Bits :=
  let values := C.gates.foldl (fun vs g => vs ++ [g.eval x vs]) []
  C.outputs.map (fun j => values.getD j false)

def Circuit.valid (C : Circuit) : Bool :=
  (C.gates.zipIdx.all (fun gi => gi.1.valid C.inputs gi.2)) &&
    C.outputs.all (fun j => decide (j < C.gates.length))

/-- Every input bit has an explicit placeholder in the code. -/
def Gate.code : Gate → Bits
  | .const b => natCode 0 ++ [b]
  | .input i => natCode 1 ++ natCode i
  | .neg i => natCode 2 ++ natCode i
  | .conj i j => natCode 3 ++ natCode i ++ natCode j
  | .disj i j => natCode 4 ++ natCode i ++ natCode j

def readGate (b : Bits) : Option (Gate × Bits) := do
  let (tag, rest) ← readNat b
  match tag with
  | 0 => match rest with
    | [] => none
    | v :: tail => pure (.const v, tail)
  | 1 => let (i, tail) ← readNat rest; pure (.input i, tail)
  | 2 => let (i, tail) ← readNat rest; pure (.neg i, tail)
  | 3 =>
    let (i, tail) ← readNat rest
    let (j, tail') ← readNat tail
    pure (.conj i j, tail')
  | 4 =>
    let (i, tail) ← readNat rest
    let (j, tail') ← readNat tail
    pure (.disj i j, tail')
  | _ => none

def readGates : ℕ → Bits → Option (List Gate × Bits)
  | 0, b => some ([], b)
  | n + 1, b => do
    let (g, rest) ← readGate b
    let (gs, tail) ← readGates n rest
    pure (g :: gs, tail)

def readNats : ℕ → Bits → Option (List ℕ × Bits)
  | 0, b => some ([], b)
  | n + 1, b => do
    let (a, rest) ← readNat b
    let (as, tail) ← readNats n rest
    pure (a :: as, tail)

/-- Arity is explicit, gates share previous values, and output wires are explicit. -/
def Circuit.code (C : Circuit) : Bits :=
  frame (List.replicate C.inputs false) ++ natCode C.gates.length ++
    (C.gates.map Gate.code).flatten ++ natCode C.outputs.length ++
    (C.outputs.map natCode).flatten

def readCircuit (b : Bits) : Option (Circuit × Bits) := do
  let (inputSlots, rest) ← readFrame b
  if inputSlots.any id then none else do
    let (ng, rest) ← readNat rest
    let (gs, rest) ← readGates ng rest
    let (no, rest) ← readNat rest
    let (os, rest) ← readNats no rest
    let C : Circuit := ⟨inputSlots.length, gs, os⟩
    if C.valid then pure (C, rest) else none

/-- Invalid syntax, forward references and trailing bits have no circuit meaning. -/
def decodeCircuit (b : Bits) : Option Circuit := do
  let (C, rest) ← readCircuit b
  if rest = [] then pure C else none

def Circuit.image (C : Circuit) : Set Bits :=
  {y | ∃ u : Word C.inputs, C.eval (wordBits u) = y}

end AMRangeAvoid.Characterization


