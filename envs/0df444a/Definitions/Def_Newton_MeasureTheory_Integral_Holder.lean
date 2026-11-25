-- Prove2me | Definitions.Def_Newton_MeasureTheory_Integral_Holder
-- name    : Newton_MeasureTheory_Integral_Holder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:05.401349+00:00
-- url     : https://prove2.me/theorems/90d4652b-976d-43ee-acc5-1deb9c4768d4
-- title:
--   Holder
-- statement:
--   Definitions and structural lemmas for Holder, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Holder.lean

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option autoImplicit false
open MeasureTheory ENNReal NNReal
open scoped ENNReal BigOperators
namespace Newton
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
def IsConjugateExponent (p q : ℝ≥0∞) : Prop :=
  (p = 1 ∧ q = ∞) ∨ (p = ∞ ∧ q = 1) ∨
  (1 < p ∧ p < ∞ ∧ 1 < q ∧ q < ∞ ∧ 1 / p + 1 / q = 1)
section HolderGeneral
end HolderGeneral
section MinkowskiAux
variable {β : Type*} [MeasurableSpace β]
variable {ν : Measure β}
end MinkowskiAux
end Newton


