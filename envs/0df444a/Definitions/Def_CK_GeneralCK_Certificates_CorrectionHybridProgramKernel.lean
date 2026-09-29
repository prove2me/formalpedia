-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_CorrectionHybridProgramKernel
-- name    : CK_GeneralCK_Certificates_CorrectionHybridProgramKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:09:07.416365+00:00
-- url     : https://prove2.me/theorems/6bfb3010-ee9b-4061-8ce9-af9daf55feff
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.CorrectionHybridProgramKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.CorrectionHybridProgramKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.CorrectionHybridProgramKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.CorrectionHybridProgramKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/CorrectionHybridProgramKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram

-- ===== source module GeneralCK.Certificates.CorrectionHybridProgramKernel =====
section

/-!
# One Boolean arithmetic pass for correction programs

Correction programs have a fixed, long arithmetic skeleton and only a small
number of logarithm/contact instructions.  This kernel checks every arithmetic
instruction in one Boolean traversal.  The accompanying `NonlinearValid`
predicate contains proof fields only at the transcendental instructions.  The
soundness theorem reconstructs the ordinary `Accepted` proposition used by the
existing semantic API.
-/

namespace GeneralCK.Certificates.CorrectionHybridProgramKernel

open BivariateJetProgram (Shape zeroBox)
open BivariateProvedProgram

def arithmeticStepCheck {p : ℕ} (shape : Shape)
    (boxes : List (DyadicBivariateJetEnclosure p))
    (out : DyadicBivariateJetEnclosure p) : Bool :=
  decide (InRange shape boxes.length) && match shape with
  | .add i j => ((boxes.getD i (zeroBox p)).add
      (boxes.getD j (zeroBox p))).subsetCheck out
  | .neg i => (boxes.getD i (zeroBox p)).neg.subsetCheck out
  | .mul i j => ((boxes.getD i (zeroBox p)).mul
      (boxes.getD j (zeroBox p))).subsetCheck out
  | .inv i => (boxes.getD i (zeroBox p)).invCheck out
  | .log _ | .contact _ => true

def arithmeticCheck {p : ℕ} : List (Instruction p) →
    List (DyadicBivariateJetEnclosure p) → Bool
  | [], _ => true
  | instruction :: rest, boxes =>
      arithmeticStepCheck instruction.shape boxes instruction.proposed &&
        arithmeticCheck rest (instruction.proposed :: boxes)

def nonlinearStepValid {p : ℕ} (shape : Shape)
    (boxes : List (DyadicBivariateJetEnclosure p))
    (out : DyadicBivariateJetEnclosure p) : Prop :=
  match shape with
  | .log _ | .contact _ => StepValid shape boxes out
  | _ => True

def NonlinearValid {p : ℕ} : List (Instruction p) →
    List (DyadicBivariateJetEnclosure p) → Prop
  | [], _ => True
  | instruction :: rest, boxes =>
      nonlinearStepValid instruction.shape boxes instruction.proposed ∧
      NonlinearValid rest (instruction.proposed :: boxes)

theorem arithmeticStepCheck_sound_of_nonlinear {p : ℕ} {shape : Shape}
    {boxes : List (DyadicBivariateJetEnclosure p)}
    {out : DyadicBivariateJetEnclosure p}
    (hc : arithmeticStepCheck shape boxes out = true)
    (hn : nonlinearStepValid shape boxes out) :
    StepValid shape boxes out := by
  have parts := Bool.and_eq_true_iff.mp hc
  have hrange : InRange shape boxes.length := of_decide_eq_true parts.1
  cases shape with
  | add _ _ => exact ⟨hrange, parts.2⟩
  | neg _ => exact ⟨hrange, parts.2⟩
  | mul _ _ => exact ⟨hrange, parts.2⟩
  | inv _ => exact ⟨hrange, parts.2⟩
  | log _ => exact hn
  | contact _ => exact hn

theorem accepted_of_arithmeticCheck_of_nonlinearValid {p : ℕ}
    (program : List (Instruction p))
    (boxes : List (DyadicBivariateJetEnclosure p))
    (hc : arithmeticCheck program boxes = true)
    (hn : NonlinearValid program boxes) : Accepted program boxes := by
  induction program generalizing boxes with
  | nil => trivial
  | cons instruction rest ih =>
      have checks := Bool.and_eq_true_iff.mp hc
      exact ⟨arithmeticStepCheck_sound_of_nonlinear checks.1 hn.1,
        ih _ checks.2 hn.2⟩

theorem nonlinearValid_of_accepted {p : ℕ}
    (program : List (Instruction p))
    (boxes : List (DyadicBivariateJetEnclosure p))
    (h : Accepted program boxes) : NonlinearValid program boxes := by
  induction program generalizing boxes with
  | nil => trivial
  | cons instruction rest ih =>
      constructor
      · cases hs : instruction.shape <;> simp only [nonlinearStepValid]
        all_goals simpa only [hs] using h.1
      · exact ih _ h.2

#print axioms arithmeticStepCheck_sound_of_nonlinear
#print axioms accepted_of_arithmeticCheck_of_nonlinearValid
#print axioms nonlinearValid_of_accepted

end GeneralCK.Certificates.CorrectionHybridProgramKernel

end


