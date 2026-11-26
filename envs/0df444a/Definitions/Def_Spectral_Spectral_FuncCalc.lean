-- Prove2me | Definitions.Def_Spectral_Spectral_FuncCalc
-- name    : Spectral_Spectral_FuncCalc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:07:39.577733+00:00
-- url     : https://prove2.me/theorems/4b3821d1-edf9-49e0-850a-a6678e351935
-- title:
--   Func Calc
-- statement:
--   Definitions and structural lemmas for Func Calc, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/FuncCalc.lean

import Definitions.Def_Spectral_Spectral_Existence
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_spectral_theorem_existence

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
noncomputable def spectralFuncCalc
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (f : ℝ → ℂ) (hf : Measurable f) : E →ₗ.[ℂ] E :=
  (Classical.choose (spectral_theorem_existence A hA)).unboundedIntegral f hf


