-- Prove2me | Definitions.Def_PricingWithTips3DM_34f689a9d26798ba8c29780b
-- name    : PricingWithTips3DM_34f689a9d26798ba8c29780b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T05:25:36.516618+00:00
-- url     : https://prove2.me/theorems/a651c00b-4e78-4735-9510-4fd16dbedbbf
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConjunctionCompiler
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_d3e2580dc467c0d558da9c39
import Definitions.Def_PricingWithTips3DM_c8535193d1fccda9ef37fd9d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Complete raw-input compiler for the final conjunction frame

The frame start is the accepting-boundary endpoint, its sources are the
verified tail-first constraint stream, and one final marker closes the frame.
Joining this field to the previous body compiler leaves only the circuit
output-wire block.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete unary runtime input for the final verifier conjunction. -/
def verifierFinalConjunctionInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierAcceptingBoundaryEndFrame W input ++
    verifierConstraintOutputReversedSource W input ++ [.frameEnd]

/-- The generated target is exactly the semantic conjunction-frame encoding. -/
theorem verifierFinalConjunctionInputTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierFinalConjunctionInputTarget W input =
      encodeAffineConjunctionFrame
        (verifierFinalConjunctionFrame W input) := by
  unfold verifierFinalConjunctionInputTarget
    verifierFinalConjunctionFrame encodeAffineConjunctionFrame
  rw [verifierAcceptingBoundaryEndFrame_eq,
    verifierAcceptingBoundary_gates_length_eq_end,
    verifierConstraintOutputReversedSource_eq]
  simp [encodeUnaryFrame, List.append_assoc]

/-- One fixed polynomial-time TM2 emits the complete final-conjunction field. -/
noncomputable def verifierFinalConjunctionInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierFinalConjunctionInputTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let start := verifierAcceptingBoundaryEndFrame_computableInPolyTime W
  let wires := verifierConstraintOutputReversedSource_computableInPolyTime W
  let joined := unaryFrameSameInputConcat_computableInPolyTime start wires
  let boundary := constantUnarySingleton_computableInPolyTime
    (Γ := Γ) .frameEnd
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    joined boundary
  exact
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := fun input => by
        have run := complete.outputsFun input
        simpa only [id_eq, verifierFinalConjunctionInputTarget,
          constantUnarySingleton, List.append_assoc] using run }

/-- Complete unary verifier body through the final conjunction field. -/
def verifierBodyThroughConjunctionUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierBodyThroughAcceptingUnaryTarget W input ++
    verifierFinalConjunctionInputTarget W input

/-- After this compiler only the circuit output-wire block remains. -/
theorem encodeAffineVerifierBodyUnary_eq_throughConjunction_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyUnary (compileVerifierBodyScript W input) =
      verifierBodyThroughConjunctionUnaryTarget W input ++
        encodeUnaryFrameBlock (verifierCircuit W input).output := by
  rw [encodeAffineVerifierBodyUnary_eq_throughAccepting_append]
  rw [← verifierFinalConjunctionInputTarget_eq]
  simp [verifierBodyThroughConjunctionUnaryTarget, List.append_assoc]

/-- A fixed polynomial-time TM2 emits the unary body through conjunction. -/
noncomputable def
    verifierBodyThroughConjunctionUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughConjunctionUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let bodyPrefix :=
    verifierBodyThroughAcceptingUnaryTarget_computableInPolyTime W
  let conjunction :=
    verifierFinalConjunctionInputTarget_computableInPolyTime W
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    bodyPrefix conjunction
  exact
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := fun input => by
        have run := complete.outputsFun input
        simpa only [id_eq,
          verifierBodyThroughConjunctionUnaryTarget] using run }

/-- Common-alphabet body target through final conjunction. -/
def verifierBodyThroughConjunctionTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineStmtScriptSym :=
  (verifierBodyThroughConjunctionUnaryTarget W input).map .data

/-- The typed body encoding now differs only by its final output-wire field. -/
theorem encodeAffineVerifierBodyScript_eq_throughConjunction_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyScript (compileVerifierBodyScript W input) =
      verifierBodyThroughConjunctionTarget W input ++
        (encodeUnaryFrameBlock (verifierCircuit W input).output).map .data := by
  unfold encodeAffineVerifierBodyScript verifierBodyThroughConjunctionTarget
  rw [encodeAffineVerifierBodyUnary_eq_throughConjunction_append]
  simp only [List.map_append]

/-- The common-alphabet conjunction-complete body is polynomial-time
computable from the original input. -/
noncomputable def verifierBodyThroughConjunctionTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughConjunctionTarget W) := by
  let unary :=
    verifierBodyThroughConjunctionUnaryTarget_computableInPolyTime W
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch unary
      (listMap_computableInPolyTime AffineStmtScriptSym.data)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (verifierBodyThroughConjunctionUnaryTarget W input).map
        AffineStmtScriptSym.data)
  simpa only [Function.comp_def] using Classical.choice mappedExists

end CLRS.Chapter34.Turing.CookLevin


