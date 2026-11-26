-- Prove2me | Definitions.Def_Spectral_Spectral_Intrinsic
-- name    : Spectral_Spectral_Intrinsic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:11:09.32246+00:00
-- url     : https://prove2.me/theorems/36771d96-877e-4ff9-9592-0b6ef240d4a4
-- title:
--   Intrinsic
-- statement:
--   Definitions and structural lemmas for Intrinsic, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Intrinsic.lean

import Definitions.Def_Spectral_Spectral_Uniqueness
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
def PVM.Represents (E_pvm : PVM E) (A : E →ₗ.[ℂ] E) : Prop :=
  ∃ scalarMeasure : E → Measure ℝ,
    (∀ (x : E) (S : Set ℝ), MeasurableSet S →
      scalarMeasure x S =
        ENNReal.ofReal ((@inner ℂ E _ (E_pvm.proj S x) x).re)) ∧
    (∀ x : E, x ∈ A.domain ↔
      ∫⁻ t, ‖(t : ℂ)‖₊ ^ 2 ∂(scalarMeasure x) < ⊤) ∧
    (∀ x : A.domain,
      @inner ℂ E _ (x : E) (A x) =
        ∫ t, (t : ℂ) ∂(scalarMeasure (x : E)))


