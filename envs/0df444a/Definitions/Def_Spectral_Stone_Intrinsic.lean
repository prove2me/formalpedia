-- Prove2me | Definitions.Def_Spectral_Stone_Intrinsic
-- name    : Spectral_Stone_Intrinsic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:10:08.185812+00:00
-- url     : https://prove2.me/theorems/48ba5dc7-af9e-56d4-9630-4236a5a03a84
-- title:
--   Intrinsic
-- statement:
--   Definitions and structural lemmas for Intrinsic, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Stone/Intrinsic.lean

import Definitions.Def_Spectral_Stone_Theorem
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
def StrongContUnitary.Generates (U : StrongContUnitary E)
    (A : E →ₗ.[ℂ] E) : Prop :=
  (∀ x : E, x ∈ A.domain ↔
    ∃ y, Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
      (nhdsWithin 0 {0}ᶜ) (nhds y)) ∧
  ∀ x : A.domain, Filter.Tendsto
    (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
    (nhdsWithin 0 {0}ᶜ) (nhds (A x))


