-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_PPAD
-- name    : CorrelatedAuctionComplexity_Main_PPAD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:55.546855+00:00
-- url     : https://prove2.me/theorems/87850472-d85e-49a0-bc32-4e8a19c5bea8
-- title:
--   Operational End-of-Line, total search, and standard PPAD
-- statement:
--   A Boolean circuit is an explicitly listed sequence of input, AND and NOT wires with references only to earlier wires, followed by its output indices. End-of-Line inputs encode Boolean predecessor and successor circuits $P,S$ on $n$-bit vertices, with
--
--   $$P(0)=0,\quad S(0)\ne0,\quad P(S(0))=0.$$
--
--   An answer is a nonzero $n$-bit vertex $v$ with $P(S(v))\ne v$ or $S(P(v))\ne v$. The decoder and circuit evaluation have explicit bodies.
--
--   A total search relation is polynomially balanced and polynomially verifiable, has a polynomial-time decidable valid-instance domain, and has an answer on every valid instance. PPAD consists of those relations with a polynomial-time search reduction to End-of-Line. PPAD hardness quantifies over every relation in this class; completeness includes membership. Reductions reuse the published definition with actual Cook-machine runtime and an answer map correct for every target answer, reading the original input as well.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Theorems 1, 2, 7 and Lemmas 16, 20; standard operational meaning of PPAD used throughout pp. 3–24 (PDF same pages)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec
import Definitions.Def_CardinalMatching_SearchReduces

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


inductive BoolWire where
  | input (i : ℕ)
  | conj (i j : ℕ)
  | neg (i : ℕ)
  deriving DecidableEq

structure BoolCircuit where
  width : ℕ
  wires : List BoolWire
  outputs : List ℕ
  deriving DecidableEq

namespace BoolCircuit

def WellFormed (C : BoolCircuit) : Prop :=
  C.outputs.length = C.width ∧
  (∀ j ∈ C.outputs, j < C.wires.length) ∧
  ∀ t : Fin C.wires.length, match C.wires[t] with
    | .input j => j < C.width
    | .conj i j => i < t.val ∧ j < t.val
    | .neg i => i < t.val

def eval (C : BoolCircuit) (v : Bits) : Bits :=
  let vals := C.wires.foldl (fun bs g => bs ++ [match g with
    | .input j => v.getD j false
    | .conj i j => bs.getD i false && bs.getD j false
    | .neg i => !(bs.getD i false)]) []
  C.outputs.map fun i => vals.getD i false

def wireData : BoolWire → List ℕ
  | .input i => [0,i,0]
  | .conj i j => [1,i,j]
  | .neg i => [2,i,0]

def data (C : BoolCircuit) : List ℕ :=
  [C.width,C.wires.length] ++ C.wires.flatMap wireData ++ C.outputs

def decodeData (ns : List ℕ) : Option BoolCircuit :=
  let n := ns.getD 0 0
  let k := ns.getD 1 0
  if n ≤ ns.length ∧ k ≤ ns.length ∧ ns.length = 2+3*k+n then
    let C : BoolCircuit := {
      width := n
      wires := (List.range k).map fun j =>
        match ns.getD (2+3*j) 0 with
        | 0 => .input (ns.getD (3+3*j) 0)
        | 1 => .conj (ns.getD (3+3*j) 0) (ns.getD (4+3*j) 0)
        | _ => .neg (ns.getD (3+3*j) 0)
      outputs := ns.drop (2+3*k) }
    if C.data = ns then some C else none
  else none
end BoolCircuit

structure EndOfLineData where
  predecessor : BoolCircuit
  successor : BoolCircuit

namespace EndOfLineData

def WellFormed (C : EndOfLineData) : Prop :=
  0 < C.predecessor.width ∧ C.successor.width = C.predecessor.width ∧
  C.predecessor.WellFormed ∧ C.successor.WellFormed ∧
  let z := List.replicate C.predecessor.width false
  C.predecessor.eval z = z ∧ C.successor.eval z ≠ z ∧
  C.predecessor.eval (C.successor.eval z) = z

def Endpoint (C : EndOfLineData) (v : Bits) : Prop :=
  v.length = C.predecessor.width ∧ v ≠ List.replicate C.predecessor.width false ∧
  (C.predecessor.eval (C.successor.eval v) ≠ v ∨ C.successor.eval (C.predecessor.eval v) ≠ v)

def encode (C : EndOfLineData) : Bits :=
  pack (C.predecessor.data.length :: (C.predecessor.data ++ C.successor.data))

def decode (s : Bits) : Option EndOfLineData := do
  let ns ← unpack s
  match ns with
  | [] => none
  | k :: ts =>
    if k ≤ ts.length then
      let p ← BoolCircuit.decodeData (ts.take k)
      let q ← BoolCircuit.decodeData (ts.drop k)
      pure ⟨p,q⟩
    else none
end EndOfLineData

/-- A concrete, binary, circuit-defined End-of-Line relation. Malformed inputs are invalid. -/
def EndOfLine : TetrisHard.Rows.SearchProblem where
  valid s := ∃ C, EndOfLineData.decode s = some C ∧ C.WellFormed
  answer s t := ∃ C, EndOfLineData.decode s = some C ∧ C.WellFormed ∧ C.Endpoint t

/-- Polynomially balanced, polynomially verifiable, total search on a decidable promise. -/
def IsTFNP (S : TetrisHard.Rows.SearchProblem) : Prop :=
  (∃ k : ℕ, ∀ s t, S.answer s t → t.length ≤ s.length^k+k) ∧
  (CookPvsNP.checkLang S.answer ∈ CookPvsNP.P (Option (Bool ⊕ Bool))) ∧
  ({s | S.valid s} ∈ CookPvsNP.P Bool) ∧
  (∀ s, S.valid s → ∃ t, S.answer s t)

/-- Standard PPAD, using actual Cook-machine reductions to End-of-Line. -/
def InPPAD (S : TetrisHard.Rows.SearchProblem) : Prop :=
  IsTFNP S ∧ CardinalMatching.SearchReduces S EndOfLine

def PPADHard (S : TetrisHard.Rows.SearchProblem) : Prop :=
  ∀ Q : TetrisHard.Rows.SearchProblem, InPPAD Q → CardinalMatching.SearchReduces Q S

def PPADComplete (S : TetrisHard.Rows.SearchProblem) : Prop := InPPAD S ∧ PPADHard S

end CorrelatedAuctionComplexity.Main


