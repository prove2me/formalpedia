-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionCompactProgramKernel
-- name    : CK_GeneralCK_Certificates_ReflectionCompactProgramKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:14:13.447082+00:00
-- url     : https://prove2.me/theorems/b9e50f87-21ea-48a3-8500-ed08c73b1bc8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionCompactProgramKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionCompactProgramKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionCompactProgramKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionCompactProgramKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionCompactProgramKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_CorrectionHybridProgramKernel
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionFastTranscendental

-- ===== source module GeneralCK.Certificates.ReflectionCompactProgramKernel =====
section

/-!
# Sparse fixed-shape reflection programs

Arithmetic proposals are recomputed inside Lean.  Generated certificates store
an enclosure only for reciprocal, logarithm, and contact instructions.
-/

namespace GeneralCK.Certificates.ReflectionCompactProgramKernel

open BivariateJetProgram (Shape zeroBox)
open BivariateProvedProgram

def needsPayload : Shape → Bool
  | .log _ | .contact _ => true
  | _ => false

def arithmeticOutput {p : ℕ} (shape : Shape)
    (boxes : List (DyadicBivariateJetEnclosure p)) :
    DyadicBivariateJetEnclosure p :=
  match shape with
  | .add i j => (boxes.getD i (zeroBox p)).add (boxes.getD j (zeroBox p))
  | .neg i => (boxes.getD i (zeroBox p)).neg
  | .mul i j => (boxes.getD i (zeroBox p)).mul (boxes.getD j (zeroBox p))
  | .inv i => (boxes.getD i (zeroBox p)).inv
  | _ => zeroBox p

inductive Payload where
  | log (proposed : DyadicBivariateJetEnclosure 40)
      (witness : ReflectionFastTranscendental.LogWitness)
  | contact (proposed : DyadicBivariateJetEnclosure 40)
      (witness : ReflectionFastTranscendental.ContactWitness)

def Payload.proposed : Payload → DyadicBivariateJetEnclosure 40
  | .log proposed _ | .contact proposed _ => proposed

def payloadCheck (shape : Shape) (boxes : List (DyadicBivariateJetEnclosure 40))
    (payload : Payload) : Bool :=
  match shape, payload with
  | .log i, .log proposed witness =>
      witness.check (boxes.getD i (zeroBox 40)).value proposed.value &&
        ((boxes.getD i (zeroBox 40)).log proposed.value).subsetCheck proposed
  | .contact i, .contact proposed witness =>
      witness.check (boxes.getD i (zeroBox 40)).value &&
        (DyadicBivariateJetEnclosure.outerCompose witness.outer
          (boxes.getD i (zeroBox 40))).subsetCheck proposed
  | _, _ => false

def build40 : List Shape → List Payload → List (DyadicBivariateJetEnclosure 40) →
    List (Instruction 40)
  | [], _, _ => []
  | shape :: shapes, payloads, boxes =>
      if needsPayload shape then
        match payloads with
        | [] => []
        | payload :: rest =>
            ⟨shape, payload.proposed⟩ ::
              build40 shapes rest (payload.proposed :: boxes)
      else
        let out := arithmeticOutput shape boxes
        ⟨shape, out⟩ :: build40 shapes payloads (out :: boxes)

def nonlinearCheck : List Shape → List Payload →
    List (DyadicBivariateJetEnclosure 40) → Bool
  | [], _, _ => true
  | shape :: shapes, payloads, boxes =>
      if needsPayload shape then
        match payloads with
        | [] => false
        | payload :: rest => payloadCheck shape boxes payload &&
            nonlinearCheck shapes rest (payload.proposed :: boxes)
      else
        let out := arithmeticOutput shape boxes
        nonlinearCheck shapes payloads (out :: boxes)

theorem build40_shapes (shapes : List Shape) (payloads : List Payload)
    (boxes : List (DyadicBivariateJetEnclosure 40))
    (hn : nonlinearCheck shapes payloads boxes = true) :
    BivariateProvedProgram.shapes (build40 shapes payloads boxes) = shapes := by
  induction shapes generalizing payloads boxes with
  | nil => rfl
  | cons shape shapes ih =>
      cases hp : needsPayload shape
      · simp only [build40, hp, Bool.false_eq_true, ↓reduceIte,
          BivariateProvedProgram.shapes, List.map_cons]
        have hn' : nonlinearCheck shapes payloads
            (arithmeticOutput shape boxes :: boxes) = true := by
          simpa [nonlinearCheck, hp] using hn
        change shape :: BivariateProvedProgram.shapes
          (build40 shapes payloads (arithmeticOutput shape boxes :: boxes)) = shape :: shapes
        rw [ih _ _ hn']
      · cases payloads with
        | nil => simp [nonlinearCheck, hp] at hn
        | cons payload payloads =>
            have parts := Bool.and_eq_true_iff.mp (by simpa [nonlinearCheck, hp] using hn)
            simp only [build40, hp, ↓reduceIte, BivariateProvedProgram.shapes, List.map_cons]
            change shape :: BivariateProvedProgram.shapes
              (build40 shapes payloads (payload.proposed :: boxes)) = shape :: shapes
            rw [ih _ _ parts.2]

theorem nonlinearValid_of_checks (shapes : List Shape) (payloads : List Payload)
    (boxes : List (DyadicBivariateJetEnclosure 40))
    (ha : CorrectionHybridProgramKernel.arithmeticCheck
      (build40 shapes payloads boxes) boxes = true)
    (hn : nonlinearCheck shapes payloads boxes = true) :
    CorrectionHybridProgramKernel.NonlinearValid
      (build40 shapes payloads boxes) boxes := by
  induction shapes generalizing payloads boxes with
  | nil => trivial
  | cons shape shapes ih =>
      cases shape with
      | add i j =>
          have ha' := (Bool.and_eq_true_iff.mp ha).2
          exact ⟨True.intro, ih _ _ ha' hn⟩
      | neg i =>
          have ha' := (Bool.and_eq_true_iff.mp ha).2
          exact ⟨True.intro, ih _ _ ha' hn⟩
      | mul i j =>
          have ha' := (Bool.and_eq_true_iff.mp ha).2
          exact ⟨True.intro, ih _ _ ha' hn⟩
      | inv i =>
          have ha' := (Bool.and_eq_true_iff.mp ha).2
          exact ⟨True.intro, ih _ _ ha' hn⟩
      | log i =>
          cases payloads with
          | nil => simp [nonlinearCheck, needsPayload] at hn
          | cons payload payloads =>
              cases payload with
              | contact proposed witness => simp [nonlinearCheck, needsPayload, payloadCheck] at hn
              | log proposed witness =>
                  have haParts := Bool.and_eq_true_iff.mp ha
                  have stepParts := Bool.and_eq_true_iff.mp haParts.1
                  have range : InRange (.log i) boxes.length :=
                    of_decide_eq_true stepParts.1
                  have hnParts := Bool.and_eq_true_iff.mp hn
                  have payloadParts := Bool.and_eq_true_iff.mp hnParts.1
                  refine ⟨⟨range, witness.input_positive payloadParts.1,
                    witness.sound payloadParts.1, payloadParts.2⟩, ?_⟩
                  exact ih _ _ haParts.2 hnParts.2
      | contact i =>
          cases payloads with
          | nil => simp [nonlinearCheck, needsPayload] at hn
          | cons payload payloads =>
              cases payload with
              | log proposed witness => simp [nonlinearCheck, needsPayload, payloadCheck] at hn
              | contact proposed witness =>
                  have haParts := Bool.and_eq_true_iff.mp ha
                  have stepParts := Bool.and_eq_true_iff.mp haParts.1
                  have range : InRange (.contact i) boxes.length :=
                    of_decide_eq_true stepParts.1
                  have hnParts := Bool.and_eq_true_iff.mp hn
                  have payloadParts := Bool.and_eq_true_iff.mp hnParts.1
                  refine ⟨⟨range, witness.input_positive payloadParts.1,
                    witness.outer, (fun y hy => witness.sound payloadParts.1 hy),
                    payloadParts.2⟩, ?_⟩
                  exact ih _ _ haParts.2 hnParts.2

theorem accepted40_of_checks (shapes : List Shape) (payloads : List Payload)
    (boxes : List (DyadicBivariateJetEnclosure 40))
    (ha : CorrectionHybridProgramKernel.arithmeticCheck
      (build40 shapes payloads boxes) boxes = true)
    (hn : nonlinearCheck shapes payloads boxes = true) :
    Accepted (build40 shapes payloads boxes) boxes :=
  CorrectionHybridProgramKernel.accepted_of_arithmeticCheck_of_nonlinearValid
    _ _ ha (nonlinearValid_of_checks shapes payloads boxes ha hn)

def build {p : ℕ} : List Shape → List (DyadicBivariateJetEnclosure p) →
    List (DyadicBivariateJetEnclosure p) → List (Instruction p)
  | [], _, _ => []
  | shape :: shapes, payloads, boxes =>
      let out := if needsPayload shape then payloads.getD 0 (zeroBox p)
        else arithmeticOutput shape boxes
      let restPayloads := if needsPayload shape then payloads.drop 1 else payloads
      ⟨shape, out⟩ :: build shapes restPayloads (out :: boxes)

def finalBoxes {p : ℕ} (shapes : List Shape)
    (payloads boxes : List (DyadicBivariateJetEnclosure p)) :
    List (DyadicBivariateJetEnclosure p) :=
  BivariateProvedProgram.finalBoxes (build shapes payloads boxes) boxes

theorem build_shapes {p : ℕ} (shapes : List Shape)
    (payloads boxes : List (DyadicBivariateJetEnclosure p)) :
    BivariateProvedProgram.shapes (build shapes payloads boxes) = shapes := by
  induction shapes generalizing payloads boxes with
  | nil => rfl
  | cons shape shapes ih =>
      simp only [build, BivariateProvedProgram.shapes, List.map_cons]
      change shape :: BivariateProvedProgram.shapes
        (build shapes (if needsPayload shape then payloads.drop 1 else payloads)
          ((if needsPayload shape then payloads.getD 0 (zeroBox p)
            else arithmeticOutput shape boxes) :: boxes)) = shape :: shapes
      rw [ih]

theorem accepted_of_checks {p : ℕ} (shapes : List Shape)
    (payloads boxes : List (DyadicBivariateJetEnclosure p))
    (ha : CorrectionHybridProgramKernel.arithmeticCheck
      (build shapes payloads boxes) boxes = true)
    (hn : CorrectionHybridProgramKernel.NonlinearValid
      (build shapes payloads boxes) boxes) :
    Accepted (build shapes payloads boxes) boxes :=
  CorrectionHybridProgramKernel.accepted_of_arithmeticCheck_of_nonlinearValid
    _ _ ha hn

#print axioms build_shapes
#print axioms accepted_of_checks

end GeneralCK.Certificates.ReflectionCompactProgramKernel

end


