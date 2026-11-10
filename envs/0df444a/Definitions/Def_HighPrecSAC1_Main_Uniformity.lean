-- Prove2me | Definitions.Def_HighPrecSAC1_Main_Uniformity
-- name    : HighPrecSAC1_Main_Uniformity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:21:41.570901+00:00
-- url     : https://prove2.me/theorems/82282a88-e3ed-4d1c-95bd-f3a18232b403
-- title:
--   Uniform Boolean AC circuits, explicit descriptions and asymptotic bounds
-- statement:
--   The published Boolean DAG is restricted to AND, OR and unary NOT. Size counts source nodes, gates, wires and output wires; depth is the maximum output-path gate depth with sources at zero. Binary descriptions print every gate and source index. Uniformity is a real finite transducer printing this description in logarithmic work space from unary n. This module also defines positive polynomial logspace parameter functions, explicit uniform asymptotic bounds, the base-two depth target, and the gap-majority promise.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 9 (PDF 10)

import Mathlib
import Definitions.Def_TreeEdgeRankPC_Transducer
import Definitions.Def_SmolenskyAC_Operations
import Definitions.Def_SmolenskyAC_Circuit

namespace HighPrecSAC1.Main

/-- Base-two logarithm, as throughout §2. -/
noncomputable def lg (x : ℝ) : ℝ := Real.log x / Real.log 2

def bitLength (n : ℕ) : ℕ := n.size

def binary (n : ℕ) : List Bool :=
  (List.range (max 1 (bitLength n))).map fun i => n.testBit i

/-- Self-delimiting binary integer: unary length, zero delimiter, little-endian bits. -/
def codeNat (n : ℕ) : List Bool :=
  List.replicate (binary n).length true ++ [false] ++ binary n

def codeList {α : Type} (f : α → List Bool) (xs : List α) : List Bool :=
  codeNat xs.length ++ xs.flatMap f

def UniformWords (w : ℕ → List Bool) (start : ℕ := 1) : Prop :=
  ∃ M : TreeEdgeRankPC.Transducer, ∃ c : ℕ, ∀ n, start ≤ n →
    M.ComputesWithin (List.replicate n true) (w n) (c * (Nat.log 2 (n+1) + 1))

def Logspace (f : ℕ → ℕ) : Prop := UniformWords (fun n => binary (f n))

def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, 1 ≤ n → f n ≤ c * (n+1)^d

def Parameter (f : ℕ → ℕ) : Prop :=
  (∀ n, 1 ≤ n → 1 ≤ f n) ∧ Logspace f ∧ PolyBound f

noncomputable def Bound (f g : ℕ → ℝ) (start : ℕ := 3) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n, start ≤ n → f n ≤ c * g n

noncomputable def LogBound (f : ℕ → ℕ) : Prop := Bound (fun n => f n) (fun n => lg n)
noncomputable def PolylogBound (f : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ n, 3 ≤ n → (f n : ℝ) ≤ c * (lg n)^d

inductive BKind where
  | and | or | not
  deriving DecidableEq

def boolOp : BKind → SmolenskyAC.Operation
  | .and => SmolenskyAC.AND
  | .or => SmolenskyAC.OR
  | .not => SmolenskyAC.NOT

abbrev BRaw (n o : ℕ) := SmolenskyAC.Circuit BKind n (Fin o)

/-- Definition 2.1: NOT has exactly one input. -/
abbrev BCircuit (n o : ℕ) :=
  {C : BRaw n o // ∀ j, (C.gate j).kind = .not → (C.gate j).arity = 1}

def bEval {n o : ℕ} (C : BCircuit n o) : (Fin n → Bool) → Fin o → Bool :=
  C.val.eval boolOp

/-- Inputs and the two shared constant nodes, gates, incoming wires and output wires. -/
def bSize {n o : ℕ} (C : BCircuit n o) : ℕ :=
  n + 2 + C.val.size + (∑ j, (C.val.gate j).arity) + o

/-- Output-path depth; unused gates do not affect it. Inputs have depth zero. -/
def bDepth {n o : ℕ} (C : BCircuit n o) : ℕ :=
  Finset.univ.sup fun i => (C.val.out i).depth C.val.gateDepth

def codeWire {n g : ℕ} : SmolenskyAC.Wire n g → List Bool
  | .input i => [false,false] ++ codeNat i.val
  | .const b => [false,true,b]
  | .gate j => [true,false] ++ codeNat j.val

def codeKind : BKind → List Bool
  | .and => [false,false]
  | .or => [false,true]
  | .not => [true,false]

def bDescription {n o : ℕ} (C : BCircuit n o) : List Bool :=
  codeNat n ++ codeNat C.val.size ++
  (List.finRange C.val.size).flatMap (fun j =>
    codeKind (C.val.gate j).kind ++
    codeList codeWire ((List.finRange (C.val.gate j).arity).map (C.val.gate j).src)) ++
  codeList codeWire ((List.finRange o).map C.val.out)

def BUniform {i o : ℕ → ℕ} (C : ∀ n, BCircuit (i n) (o n)) (start : ℕ := 1) : Prop :=
  UniformWords (fun n => bDescription (C n)) start

def BPoly {i o : ℕ → ℕ} (C : ∀ n, BCircuit (i n) (o n)) : Prop :=
  PolyBound (fun n => bSize (C n))

noncomputable def BDepthBound {i o : ℕ → ℕ} (C : ∀ n, BCircuit (i n) (o n))
    (d : ℕ → ℝ) (start : ℕ := 3) : Prop := Bound (fun n => bDepth (C n)) d start

noncomputable def BAC1 {i o : ℕ → ℕ} (C : ∀ n, BCircuit (i n) (o n)) : Prop :=
  BUniform C ∧ BPoly C ∧ BDepthBound C (fun n => lg n)

noncomputable def depthTarget (n K t : ℕ) : ℝ :=
  K + lg n / lg (lg n) * lg (2 + (t : ℝ) / K)

/-- Definition 7.1: outputs in the gap are unrestricted. -/
def GapMaj {B : ℕ} (a b : ℕ) (C : BCircuit B 1) : Prop :=
  ∀ x, (SmolenskyAC.countOnes x ≤ a → bEval C x 0 = false) ∧
    (b ≤ SmolenskyAC.countOnes x → bEval C x 0 = true)

end HighPrecSAC1.Main


