-- Prove2me | Definitions.Def_N25_CanonicalSchemeFunctionField
-- name    : N25_CanonicalSchemeFunctionField
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:24.988331+00:00
-- url     : https://prove2.me/theorems/923afb2e-70e6-4287-b7da-88f73f4ccdee
-- title:
--   The generic-point function field of the canonical curve
-- statement:
--   Assume that the canonical projective curve $X_K$ is integral. The file defines its function field as the generic-point stalk $$K(X_K)=\mathcal O_{X_K,\eta},$$ together with the coefficient homomorphism $K→K(X_K)$ obtained from the structure morphism and the germ at the generic point. This fixes the scalar action used when comparing scheme sections, places, and the explicit canonical function field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_CanonicalFunctionField
import Mathlib.AlgebraicGeometry.FunctionField
/-! The actual generic-point field and its selected structural coefficient action. -/
noncomputable section
universe u
namespace N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K] [IsIntegral (CanonicalProjectiveCurve25 K)]

/-- The function field is the generic-point stalk of the literal projective curve. -/
abbrev CanonicalSchemeFF25 : CommRingCat.{u} :=
  (CanonicalProjectiveCurve25 K).functionField

/-- Coefficients act through the selected structure morphism and its generic-point germ. -/
def canonicalSchemeFF25_baseMap : K →+* CanonicalSchemeFF25 K := by
  let X := CanonicalProjectiveCurve25 K
  letI : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), by simp⟩⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (canonicalProjectiveCurveToSpec25 K).appTop ≫ X.germToFunctionField ⊤).hom

/-- The coefficient action is defined by the structural map. -/
instance canonicalSchemeFF25_algebra : Algebra K (CanonicalSchemeFF25 K) :=
  (canonicalSchemeFF25_baseMap K).toAlgebra

end N25


