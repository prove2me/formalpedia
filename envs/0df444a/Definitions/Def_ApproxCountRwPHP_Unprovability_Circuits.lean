-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Circuits
-- name    : ApproxCountRwPHP_Unprovability_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:56:52.414928+00:00
-- url     : https://prove2.me/theorems/9b7d4300-a7e9-4482-85e4-d9e808d32501
-- title:
--   Finite signatures and oracle Boolean circuits
-- statement:
--   A finite signature lists its symbols and their natural-number arities; constants have arity zero. A circuit is an explicit ordered list of Boolean and primitive-oracle gates, with a declared input length and one output wire. Oracle gates contain explicit argument wires and a requested output bit; counting-oracle gates are excluded. Validity requires every wire to have been defined earlier and every input index to be in range.
--
--   $$\operatorname{Fix}_b(C)(z)=C(zb).$$
--
--   Fixing removes the rightmost input position and replaces every read of that position with its fixed bit. The serialization uses self-delimiting fields; the parser rejects invalid descriptions. Fixed-width word gates can be expanded to bit gates with polynomial overhead. These objects provide the common circuit interface for both relativizations.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §2.2, §3.1–3.2, printed p. 13–19, PDF p. 15–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=15–21

import Definitions.Def_ApproxCountRwPHP_Unprovability_Cobham

namespace ApproxCountRwPHP.Unprovability

/-- Finite function signature. Arity zero includes constants. -/
structure Signature where
  count : ℕ
  arity : Fin count → ℕ

def Signature.language (S : Signature) : FirstOrder.Language where
  Functions n := {s : Fin S.count // S.arity s = n}
  Relations _ := Empty

/-- Boolean oracle gates have explicit input wires and return one bit.
Word outputs are represented by one gate for each desired output bit. There
are no counting-oracle gates. Indices and list lengths use self-delimiting unary
fields, giving a polynomially equivalent encoding of ordinary valid circuits. -/
inductive Gate (S : Signature) where
  | constant (b : Bool)
  | input (i : ℕ)
  | neg (i : ℕ)
  | conj (i j : ℕ)
  | query (symbol : Fin S.count) (args : Fin (S.arity symbol) → List ℕ) (bit : ℕ)

structure OracleCircuit (S : Signature) where
  inputLength : ℕ
  gates : List (Gate S)
  output : ℕ

def Gate.fields {S : Signature} : Gate S → List ℕ
  | .constant b => [0, b.toNat]
  | .input i => [1, i]
  | .neg i => [2, i]
  | .conj i j => [3, i, j]
  | .query s args b => [4, s.val, b] ++
      (List.ofFn args).flatMap (fun xs => xs.length :: xs)

def encodeFields (xs : List ℕ) : BitString :=
  xs.flatMap (fun n => List.replicate n true ++ [false])

def decodeFields (xs : BitString) : Option (List ℕ) :=
  let state := xs.foldl (fun (st : List ℕ × ℕ) b =>
    if b then (st.1, st.2 + 1) else (st.1 ++ [st.2], 0)) ([], 0)
  if state.2 = 0 then some state.1 else none

def OracleCircuit.encode {S : Signature} (C : OracleCircuit S) : BitString :=
  encodeFields ([C.inputLength, C.gates.length] ++ C.gates.flatMap Gate.fields ++ [C.output])

def parseLists : ℕ → List ℕ → Option (List (List ℕ) × List ℕ)
  | 0, xs => some ([], xs)
  | n + 1, k :: xs => do
      if k ≤ xs.length then
        let (ys, rest) ← parseLists n (xs.drop k)
        pure (xs.take k :: ys, rest)
      else none
  | _ + 1, [] => none

def parseGate (S : Signature) : List ℕ → Option (Gate S × List ℕ)
  | 0 :: b :: xs => if b ≤ 1 then some (.constant (b = 1), xs) else none
  | 1 :: i :: xs => some (.input i, xs)
  | 2 :: i :: xs => some (.neg i, xs)
  | 3 :: i :: j :: xs => some (.conj i j, xs)
  | 4 :: s :: b :: xs => do
      if hs : s < S.count then
        let symbol : Fin S.count := ⟨s, hs⟩
        let (args, rest) ← parseLists (S.arity symbol) xs
        pure (.query symbol (fun i => args.getD i.val []) b, rest)
      else none
  | _ => none

def parseGates (S : Signature) : ℕ → List ℕ → Option (List (Gate S) × List ℕ)
  | 0, xs => some ([], xs)
  | n + 1, xs => do
      let (g, xs') ← parseGate S xs
      let (gs, rest) ← parseGates S n xs'
      pure (g :: gs, rest)

def Gate.valid {S : Signature} (ℓ available : ℕ) : Gate S → Bool
  | .constant _ => true
  | .input i => i < ℓ
  | .neg i => i < available
  | .conj i j => i < available && j < available
  | .query _ args _ => (List.ofFn args).all (fun xs => xs.all (· < available))

def OracleCircuit.valid {S : Signature} (C : OracleCircuit S) : Bool :=
  (C.gates.zipIdx).all (fun gi => gi.1.valid C.inputLength gi.2) && C.output < C.gates.length

def parseCircuit (S : Signature) (x : BitString) : Option (OracleCircuit S) := do
  let fields ← decodeFields x
  match fields with
  | ℓ :: count :: rest =>
      let (gs, tail) ← parseGates S count rest
      match tail with
      | [out] =>
          let C : OracleCircuit S := ⟨ℓ, gs, out⟩
          if C.valid then pure C else none
      | _ => none
  | _ => none

def Gate.eval {S : Signature}
    (oracle : ∀ s, (Fin (S.arity s) → BitString) → BitString)
    (input : BitString) (wires : List Bool) : Gate S → Bool
  | .constant b => b
  | .input i => input.getD i false
  | .neg i => !(wires.getD i false)
  | .conj i j => wires.getD i false && wires.getD j false
  | .query s args bit => (oracle s (fun i => (args i).map (fun j => wires.getD j false))).getD bit false

def OracleCircuit.eval {S : Signature}
    (oracle : ∀ s, (Fin (S.arity s) → BitString) → BitString)
    (C : OracleCircuit S) (input : BitString) : Bool :=
  (C.gates.foldl (fun wires gate => wires ++ [gate.eval oracle input wires]) []).getD C.output false

def OracleCircuit.noInputs {S : Signature} (C : OracleCircuit S) : Bool :=
  C.gates.all (fun g => match g with | .input _ => false | _ => true)

/-- Fix the rightmost input bit, preserving all earlier input positions. -/
def OracleCircuit.fix {S : Signature} (C : OracleCircuit S) (b : Bool) : OracleCircuit S :=
  if C.inputLength = 0 then C else
  { inputLength := C.inputLength - 1
    gates := C.gates.map (fun g => match g with
      | .input i => if i = C.inputLength - 1 then .constant b else g
      | _ => g)
    output := C.output }

/-- Maximum arity, with zero for an empty signature or constants only. -/
def maximumArity (S : Signature) : ℕ := Finset.univ.sup S.arity

end ApproxCountRwPHP.Unprovability


