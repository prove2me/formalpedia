-- Prove2me | Definitions.Def_PricingWithTips3DM_f1062b85fcc07826ef0bc683
-- name    : PricingWithTips3DM_f1062b85fcc07826ef0bc683
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:54:56.143892+00:00
-- url     : https://prove2.me/theorems/e56b0782-b368-47ae-8a1d-41c46376aa77
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Canonicalizer.Semantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_6bf3e19aca9b962b1545960f
import Definitions.Def_PricingWithTips3DM_7caf3b49bf2277fb12c6ba35
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input canonicalizer: decoder semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

/-- Total certificate value, using the empty selection on malformed input. -/
def certificateValue (input : List CliqueSym) : List Nat :=
  (decodeCliqueCertificate input).getD []

/-- Fixed typed empty graph used on malformed instance input. -/
def emptyInstance : CliqueInstance :=
  { vertexCount := 0, targetSize := 0, edges := [] }

/-- Total graph value, using the empty graph on malformed input. -/
def instanceValue (input : List CliqueSym) : CliqueInstance :=
  (decodeCliqueInstance input).getD emptyInstance

/-- The certificate controller emits the canonical encoding of its total
decoded value on every raw string. -/
theorem canonicalStream_certificate_eq (input : List CliqueSym) :
    canonicalStream .certificate input =
      encodeCliqueCertificate (certificateValue input) := by
  cases hdecode : decodeCliqueCertificate input with
  | none =>
      have haccepts :
          accepts .certificate
              (scanSymbols (initialMode .certificate) input) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        have hsyntax : certificateSyntaxAccepts input = true := by
          simpa [certificateSyntaxAccepts, initialMode, accepts] using htrue
        rcases (certificateSyntaxAccepts_eq_true_iff input).1 hsyntax with
          ⟨vertices, hvertices⟩
        rw [hdecode] at hvertices
        contradiction
      simp [canonicalStream, haccepts, fallback, certificateValue, hdecode]
  | some vertices =>
      have hsyntax : certificateSyntaxAccepts input = true :=
        (certificateSyntaxAccepts_eq_true_iff input).2 ⟨vertices, hdecode⟩
      have haccepts :
          accepts .certificate
              (scanSymbols (initialMode .certificate) input) = true := by
        simpa [certificateSyntaxAccepts, initialMode, accepts] using hsyntax
      rw [canonicalStream, if_pos haccepts]
      simp only [certificateValue, hdecode, Option.getD_some]
      exact (encodeCliqueCertificate_eq_of_decode_eq_some
        input vertices hdecode).symm

/-- The instance controller emits the canonical encoding of its total decoded
value on every raw string. -/
theorem canonicalStream_instance_eq (input : List CliqueSym) :
    canonicalStream .instance input =
      encodeCliqueInstance (instanceValue input) := by
  cases hdecode : decodeCliqueInstance input with
  | none =>
      have haccepts :
          accepts .instance
              (scanSymbols (initialMode .instance) input) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        have hsyntax : instanceSyntaxAccepts input = true := by
          simpa [instanceSyntaxAccepts, initialMode, accepts] using htrue
        rcases (instanceSyntaxAccepts_eq_true_iff input).1 hsyntax with
          ⟨I, hI⟩
        rw [hdecode] at hI
        contradiction
      simp [canonicalStream, haccepts, fallback, instanceValue,
        emptyInstance, hdecode, encodeCliqueInstance, prependCliqueTicks]
  | some I =>
      have hsyntax : instanceSyntaxAccepts input = true :=
        (instanceSyntaxAccepts_eq_true_iff input).2 ⟨I, hdecode⟩
      have haccepts :
          accepts .instance
              (scanSymbols (initialMode .instance) input) = true := by
        simpa [instanceSyntaxAccepts, initialMode, accepts] using hsyntax
      rw [canonicalStream, if_pos haccepts]
      simp only [instanceValue, hdecode, Option.getD_some]
      exact (encodeCliqueInstance_eq_of_decode_eq_some input I hdecode).symm

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer


