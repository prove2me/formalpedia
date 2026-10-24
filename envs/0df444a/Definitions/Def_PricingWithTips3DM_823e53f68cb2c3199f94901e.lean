-- Prove2me | Definitions.Def_PricingWithTips3DM_823e53f68cb2c3199f94901e
-- name    : PricingWithTips3DM_823e53f68cb2c3199f94901e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:28:53.90446+00:00
-- url     : https://prove2.me/theorems/14dd4809-a3b6-412a-959a-4674915f5bc8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmOptionalSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_42934d19310e8c054b5508bb
import Definitions.Def_PricingWithTips3DM_3e4b5fb84cd3af16f2874725
import Definitions.Def_PricingWithTips3DM_a206cc095a01ca62b6c2f66a
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete optional-conjunction input and gate source for verifier-input arms

Every published candidate length fits the tableau, so every optional entry is
present.  The generic all-present formatter converts the exact conjunction
frames into the input of the established optional-family gate controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Arithmetic optional-frame family of all candidate certificate lengths. -/
def verifierInputArmOptionalFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (Option AffineConjunctionFrame) :=
  List.ofFn fun arm :
      Fin (W.certificateBound.eval input.length + 1) =>
    some (verifierInputArmArithmeticFrame W input arm)

/-- Exact delimiter-bearing input of the optional conjunction controller. -/
def verifierInputArmOptionalInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFramePresentMarkedRowFamily
    (verifierInputArmArithmeticFrameFamily W input)

private theorem flatMap_two_ofFn
    {α γ β : Type} {count : Nat}
    (leftItems : Fin count → α) (rightItems : Fin count → γ)
    (left : α → List β) (right : γ → List β)
    (h : ∀ index, left (leftItems index) = right (rightItems index)) :
    (List.ofFn leftItems).flatMap left =
      (List.ofFn rightItems).flatMap right := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [List.flatMap_cons]
      rw [h 0]
      exact congrArg (right (rightItems 0) ++ ·)
        (ih (fun index => leftItems index.succ)
          (fun index => rightItems index.succ)
          (fun index => h index.succ))

/-- The formatted marked rows are byte-for-byte the canonical all-present
optional conjunction-family encoding. -/
theorem verifierInputArmOptionalInputTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputArmOptionalInputTarget W input =
      encodeAffineOptionalConjunctionFamily
        (verifierInputArmOptionalFrames W input) := by
  unfold verifierInputArmOptionalInputTarget
    encodeUnaryFramePresentMarkedRowFamily
    verifierInputArmOptionalFrames
    encodeAffineOptionalConjunctionFamily
    encodeAffineOptionalConjunctionEntries
  rw [verifierInputArmArithmeticFrameFamily_rows]
  apply congrArg (fun stream => stream ++ [UnaryFrameSym.frameEnd])
  apply flatMap_two_ofFn
  intro arm
  unfold encodeAffineOptionalConjunctionEntry
    encodeAffineConjunctionFrame
  rfl

/-- One fixed polynomial-time TM2 constructs the exact optional-family input
from the raw verifier word. -/
noncomputable def
    verifierInputArmOptionalInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputArmOptionalInputTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierInputArmArithmeticFrameFamily_computableInPolyTime W)
      unaryFrameMarkedRowPresent_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def, id_eq,
          verifierInputArmOptionalInputTarget] using run }

/-- Literal circuit-byte stream of every candidate-length conjunction arm. -/
def verifierInputArmGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List CircuitSym :=
  affineOptionalConjunctionFamilyGateStream
    (verifierInputArmOptionalFrames W input)

/-- The arithmetic arm stream is exactly the arm phase of the canonical
semantic input-boundary script. -/
theorem verifierInputArmGateStream_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputArmGateStream W input =
      affineOptionalConjunctionFamilyGateStream
        (verifierInputBoundaryScript W input).armFrames := by
  unfold verifierInputArmGateStream verifierInputArmOptionalFrames
  rw [verifierInputBoundaryScript_armFrames_eq_arithmetic]

/-- End-to-end concrete polynomial TM2 from the raw verifier word to every
serialized input-arm gate. -/
noncomputable def verifierInputArmGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputArmGateStream W) := by
  letI : Fintype Γ := W.alphabetFintype
  let source : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineOptionalConjunctionFamily
      (verifierInputArmOptionalFrames W) := by
    let raw := verifierInputArmOptionalInputTarget_computableInPolyTime W
    exact
      { tm := raw.tm
        inputAlphabet := raw.inputAlphabet
        outputAlphabet := raw.outputAlphabet
        time := raw.time
        outputsFun := fun input => by
          have run := raw.outputsFun input
          rw [verifierInputArmOptionalInputTarget_eq W input] at run
          simpa only [id_eq] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      affineOptionalConjunctionFamilyGateStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def, id_eq,
          verifierInputArmGateStream] using run }

end CLRS.Chapter34.Turing.CookLevin


