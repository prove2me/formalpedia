-- Prove2me | Definitions.Def_Spectral_Spectral_Uniqueness
-- name    : Spectral_Spectral_Uniqueness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:10:05.752196+00:00
-- url     : https://prove2.me/theorems/d4562c48-616e-504e-9b20-54a44765dec5
-- title:
--   Uniqueness
-- statement:
--   Definitions and structural lemmas for Uniqueness, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Uniqueness.lean

import Definitions.Def_Spectral_Stone_Theorem
import Definitions.Def_Spectral_Spectral_FuncCalc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
set_option autoImplicit false
open Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
noncomputable def characteristicPhase (t r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))


