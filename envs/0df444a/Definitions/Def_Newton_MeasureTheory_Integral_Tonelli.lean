-- Prove2me | Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
-- name    : Newton_MeasureTheory_Integral_Tonelli
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:05.750924+00:00
-- url     : https://prove2.me/theorems/fc5b9b18-06cb-4586-90d1-8f6639d81bd9
-- title:
--   Tonelli
-- statement:
--   Definitions and structural lemmas for Tonelli, from frourios contributors (frourios/newton; see pinned CC0-1.0 LICENSE)'s pinned Young convolution inequality, Lp duality, Schwartz density, and gauge foundations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/MeasureTheory/Integral/Tonelli.lean

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
section TonelliForConvolution
variable [SFinite μ]
end TonelliForConvolution
section ConvolutionKernelIntegrability
variable [AddCommGroup G]
end ConvolutionKernelIntegrability
section TonelliProductDecomposition
variable [AddCommGroup G]
end TonelliProductDecomposition
section AEMeasurableTonelli
end AEMeasurableTonelli
section TripleProductFiniteness
end TripleProductFiniteness
end Newton


