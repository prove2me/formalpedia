-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierDescendedFunctionEqPartialFourier
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierDescendedFunctionEqPartialFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:03.753044+00:00
-- url     : https://prove2.me/theorems/295004b2-32b8-410b-8df1-34cad4dcfa5f
-- title:
--   Fourier Descended Function Eq Partial Fourier
-- statement:
--   Definitions and structural lemmas for Fourier Descended Function Eq Partial Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierDescendedFunctionEqPartialFourier.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaarStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.FourDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
end GlobalTheory.JR.FourDesc


