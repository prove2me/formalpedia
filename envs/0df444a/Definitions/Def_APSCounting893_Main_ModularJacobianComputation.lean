-- Prove2me | Definitions.Def_APSCounting893_Main_ModularJacobianComputation
-- name    : APSCounting893_Main_ModularJacobianComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T19:08:02.72459+00:00
-- url     : https://prove2.me/theorems/1208d7ad-b491-465f-ab91-7bbc2e0f9ef0
-- title:
--   Executable rational-circuit decoding and modular Jacobian verification
-- statement:
--   This module supplies finite data and total executable operations for the Jacobian witness used in the image-dimension procedure.
--
--   A rational arithmetic gate is stored by its operation tag, binary wire or variable indices, and the signed numerator and positive denominator of a scalar. Length-delimited decoders recover circuits and lists. Their list loops use the input-word length as fuel and cap each parsing cursor at that length.
--
--   Given a modulus, a sparse integer assignment and a selected variable, the evaluator propagates numerator–denominator pairs with their first derivatives. All four components are reduced modulo a modulus of at least two. For selected outputs and variables, it forms the row-cleared Jacobian matrix and tests an explicitly supplied matrix inverse:
--
--   $$A B=I.$$
--
--   The definitions retain ordinary binary arithmetic, finite lists, actual wire lookup, sparse-assignment lookup, and a multiplication check for every matrix entry. Correctness, size bounds and machine-time claims are separate proof targets. The inverse test avoids expanding a determinant. Its role is to implement the nonzero-minor condition in the characteristic-zero dimension argument.
-- source:
--   Executable implementation of the rational-circuit Jacobian witnesses in Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, p. 23, Lemma 6.1 and equation (6.1), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf#page=23. The modular bounded-certificate reduction is formalized as APSCounting893.Main.bounded_modular_dimension_certificates (theorem cc3fb8a2-e6b4-4e4e-a1c3-c6123bfcb92c).

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Option
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM

def decoderBind {α β : Type} (da : Word → Option (α × Word))
    (db : α → Word → Option (β × Word)) (w : Word) : Option (β × Word):=
  (da w).elim none (fun p=>db p.1 p.2)

def decoderPair {α β : Type} (da : Word → Option (α × Word))
    (db : Word → Option (β × Word)) (w : Word) : Option ((α × β) × Word):=
  decoderBind da (fun a rest=>(db rest).elim none (fun q=>some ((a,q.1),q.2))) w

def decodeSignedNat (w : Word) : Option ((Bool × ℕ) × Word):=
  (decodeNat (w.drop 1)).map (fun p=>((w.getD 0 false,p.1),p.2))

abbrev RawRational := (Bool × ℕ) × ℕ

def decodeRawRational : Word → Option (RawRational × Word):=decoderPair decodeSignedNat decodeNat

abbrev ManyState (α : Type) := Option (List α × Word)

def decoderManyStep {α : Type} (da : Word → Option (α × Word))
    (input : ℕ × Word) (state : ManyState α) : ManyState α :=
  state.elim none fun s =>
    if s.1.length = input.1 then some s
    else (da (s.2.take input.2.length)).elim none fun p => some (p.1 :: s.1,p.2)

def decoderManyLoop {α : Type} (da : Word → Option (α × Word)) (input : ℕ × Word) : ManyState α :=
  (decoderManyStep da input)^[input.2.length] (some ([],input.2))

def decoderMany {α : Type} (da : Word → Option (α × Word)) (input : ℕ × Word) :
    Option (List α × Word) :=
  (decoderManyLoop da input).elim none fun s =>
    if s.1.length = input.1 then some (s.1.reverse,s.2) else none

def decoderMap {α β : Type} (f : α → β) (da : Word → Option (α × Word))
    (w : Word) : Option (β × Word) := (da w).map fun p => (f p.1,p.2)

def decoderWith {α β γ : Type} (da : Word → Option (β × Word))
    (f : α → β → γ) (p : α × Word) : Option (γ × Word) :=
  (da p.2).map fun q => (f p.1 q.1,q.2)

def decoderList {α : Type} (da : Word → Option (α × Word)) : Word → Option (List α × Word) :=
  decoderBind decodeNat (fun n w => decoderMany da (n,w))

abbrev RawGate := ℕ × (ℕ × (ℕ × Bool))

def encRawGate : RawGate ↪ Word := encPair encNat (encPair encNat (encPair encNat encBool))

def rawVariable (i : ℕ) : RawGate := (0,(i,(0,false)))

def rawConstant (q : RawRational) : RawGate := (1,(q.1.2,(q.2,q.1.1)))

def rawOperation (tag : ℕ) (ab : ℕ × ℕ) : RawGate := (tag,(ab.1,(ab.2,false)))

def decodeRawConstantBody (p : ℕ × Word) : Option (RawGate × Word) :=
  if p.1=0 then some (rawConstant ((false,0),1),p.2)
  else if p.1=1 then decoderMap rawConstant decodeRawRational p.2
  else none

def decodeRawConstant : Word → Option (RawGate × Word) :=
  decoderBind decodeNat (fun n w => decodeRawConstantBody (n,w))

def decodeRawGateBody (p : ℕ × Word) : Option (RawGate × Word) :=
  if p.1=0 then decoderMap rawVariable decodeNat p.2
  else if p.1=1 then decodeRawConstant p.2
  else if p.1≤5 then decoderWith (decoderPair decodeNat decodeNat) rawOperation p
  else none

def decodeRawGate : Word → Option (RawGate × Word) :=
  decoderBind decodeNat (fun n w => decodeRawGateBody (n,w))

abbrev RawCircuit := ℕ × (List RawGate × List ℕ)

def encRawCircuit : RawCircuit ↪ Word :=
  encPair encNat (encPair (encList encRawGate) (encList encNat))

def decodeRawCircuit : Word → Option (RawCircuit × Word) :=
  decoderPair decodeNat (decoderPair (decoderList decodeRawGate) (decoderList decodeNat))

def ArithmeticGate.raw {n : ℕ} : ArithmeticGate n → RawGate
  | .variable i => rawVariable i.val
  | .constant cs => let q:=cs.headD 0;rawConstant ((decide (q.num<0),q.num.natAbs),q.den)
  | .add a b => rawOperation 2 (a,b)
  | .sub a b => rawOperation 3 (a,b)
  | .mul a b => rawOperation 4 (a,b)
  | .div a b => rawOperation 5 (a,b)

def ArithmeticCircuit.raw {n : ℕ} (C : ArithmeticCircuit n) : RawCircuit :=
  (n,(C.gates.map ArithmeticGate.raw,C.outputs))

def modAdd (p a b : ℕ) : ℕ := (a+b)%p

def modMul (p a b : ℕ) : ℕ := (a*b)%p

def modSub (p a b : ℕ) : ℕ := (a%p+p-b%p)%p

def modSigned (p : ℕ) (a : Bool × ℕ) : ℕ :=
  if a.1 then modSub p 0 a.2 else a.2%p

abbrev ResidueJet := ℕ × ℕ

abbrev ResidueFraction := ResidueJet × ResidueJet

def encResidueJet : ResidueJet ↪ Word := encPair encNat encNat

def encResidueFraction : ResidueFraction ↪ Word := encPair encResidueJet encResidueJet

def residueJetAdd (p : ℕ) (a b : ResidueJet) : ResidueJet :=
  (modAdd p a.1 b.1,modAdd p a.2 b.2)

def residueJetSub (p : ℕ) (a b : ResidueJet) : ResidueJet :=
  (modSub p a.1 b.1,modSub p a.2 b.2)

def residueJetMul (p : ℕ) (a b : ResidueJet) : ResidueJet :=
  (modMul p a.1 b.1,modAdd p (modMul p a.1 b.2) (modMul p a.2 b.1))

def residueFractionAdd (p : ℕ) (a b : ResidueFraction) : ResidueFraction :=
  (residueJetAdd p (residueJetMul p a.1 b.2) (residueJetMul p b.1 a.2),
    residueJetMul p a.2 b.2)

def residueFractionSub (p : ℕ) (a b : ResidueFraction) : ResidueFraction :=
  (residueJetSub p (residueJetMul p a.1 b.2) (residueJetMul p b.1 a.2),
    residueJetMul p a.2 b.2)

def residueFractionMul (p : ℕ) (a b : ResidueFraction) : ResidueFraction :=
  (residueJetMul p a.1 b.1,residueJetMul p a.2 b.2)

def residueFractionDiv (p : ℕ) (a b : ResidueFraction) : ResidueFraction :=
  (residueJetMul p a.1 b.2,residueJetMul p a.2 b.1)

abbrev RawAssignment := List (ℕ × (Bool × ℕ))

def encRawAssignment : RawAssignment ↪ Word := encList (encPair encNat (encPair encBool encNat))

def rawPointEntry (a : RawAssignment) (i : ℕ) : Bool × ℕ :=
  ((a.find? (fun e => decide (e.1=i))).getD (0,(false,0))).2

def rawPointResidue (p : ℕ) (a : RawAssignment) (i : ℕ) : ℕ :=
  modSigned p (rawPointEntry a i)

def rawAssignmentOf {n : ℕ} (a : List (Fin n × ℤ)) : RawAssignment :=
  a.map fun e => (e.1.val,(decide (e.2<0),e.2.natAbs))

def signedNatValue (a : Bool × ℕ) : ℤ := if a.1 then -(a.2 : ℤ) else (a.2 : ℤ)

def residueBinaryOperation (p tag : ℕ) (a b : ResidueFraction) : ResidueFraction :=
  if tag=2 then residueFractionAdd p a b
  else if tag=3 then residueFractionSub p a b
  else if tag=4 then residueFractionMul p a b
  else residueFractionDiv p a b

def residueGateBinary (p : ℕ) (prior : List ResidueFraction) (g : RawGate) : Option ResidueFraction :=
  let left:=prior[g.2.1]?
  let right:=prior[g.2.2.1]?
  if left.isSome && right.isSome then
    some (residueBinaryOperation p g.1 (left.getD ((0,0),(1,0)))
      (right.getD ((0,0),(1,0))))
  else none

def residueGateValue (p : ℕ) (a : RawAssignment) (j : ℕ)
    (prior : List ResidueFraction) (g : RawGate) : Option ResidueFraction :=
  if g.1=0 then
    some ((rawPointResidue p a g.2.1,if g.2.1=j then 1%p else 0),(1%p,0))
  else if g.1=1 then some ((modSigned p (g.2.2.2,g.2.1),0),(g.2.2.1%p,0))
  else residueGateBinary p prior g

abbrev GateParameters := ℕ × (RawAssignment × ℕ)

def encGateParameters : GateParameters ↪ Word :=
  encPair encNat (encPair encRawAssignment encNat)

abbrev ResidueGateInput := GateParameters × (List ResidueFraction × RawGate)

def encResidueGateInput : ResidueGateInput ↪ Word :=
  encPair encGateParameters (encPair (encList encResidueFraction) encRawGate)

def safeModulus (p : ℕ) : ℕ := if 2 ≤ p then p else 2

def residueCircuitStep (par : GateParameters) (acc : Option (List ResidueFraction))
    (g : RawGate) : Option (List ResidueFraction) :=
  acc.elim none fun prior =>
    (residueGateValue (safeModulus par.1) par.2.1 par.2.2 prior g).elim none
      fun value => some (prior++[value])

def encResidueValues : Option (List ResidueFraction) ↪ Word := encOption (encList encResidueFraction)

def residueCircuitValues (par : GateParameters) (gates : List RawGate) : Option (List ResidueFraction) :=
  gates.foldl (residueCircuitStep par) (some [])

def residueCircuitOutput (par : GateParameters) (gates : List RawGate) (wire : ℕ) : ResidueFraction :=
  (((residueCircuitValues par gates).getD [])[wire]?).getD ((0,0),(1%safeModulus par.1,0))

def residueDerivativePair (p : ℕ) (f : ResidueFraction) : ℕ × ℕ :=
  (modSub p (modMul p f.1.2 f.2.1) (modMul p f.1.1 f.2.2),modMul p f.2.1 f.2.1)

def modularProduct (p : ℕ) (values : List ℕ) : ℕ :=
  values.foldl (modMul (safeModulus p)) (1%safeModulus p)

abbrev MatrixParameters := ℕ × (RawCircuit × (RawAssignment × (List ℕ × List ℕ)))

def encMatrixParameters : MatrixParameters ↪ Word :=
  encPair encNat (encPair encRawCircuit (encPair encRawAssignment (encPair (encList encNat) (encList encNat))))

def residueJacobianEntry (par : MatrixParameters) (i j : ℕ) : ℕ × ℕ :=
  let circuit:=par.2.1
  let vlabel:=par.2.2.2.2.getD j 0
  let output:=par.2.2.2.1.getD i 0
  let wire:=circuit.2.2.getD output 0
  residueDerivativePair (safeModulus par.1)
    (residueCircuitOutput (par.1,(par.2.2.1,vlabel)) circuit.2.1 wire)

def residueClearedEntry (par : MatrixParameters) (i j : ℕ) : ℕ :=
  modMul (safeModulus par.1) (residueJacobianEntry par i j).1
    (modularProduct par.1 ((List.range par.2.2.2.2.length).map
      (fun l => if l=j then 1 else (residueJacobianEntry par i l).2)))

def residueMatrixProductEntry (par : MatrixParameters) (inverse : List ℕ) (i j : ℕ) : ℕ :=
  ((List.range par.2.2.2.1.length).map fun l =>
    modMul (safeModulus par.1) (residueClearedEntry par i l)
      (inverse.getD (l*par.2.2.2.1.length+j) 0)).sum % safeModulus par.1

def residueMatrixInverseTest (par : MatrixParameters) (inverse : List ℕ) : Bool :=
  (List.range par.2.2.2.1.length).all fun i =>
    (List.range par.2.2.2.1.length).all fun j =>
      decide (residueMatrixProductEntry par inverse i j = if i=j then 1 else 0)
end APSCounting893.Main


