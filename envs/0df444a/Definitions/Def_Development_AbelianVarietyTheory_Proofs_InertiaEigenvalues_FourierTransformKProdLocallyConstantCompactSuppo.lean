-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppo
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:46.185845+00:00
-- url     : https://prove2.me/theorems/526867ee-43ef-4add-b024-dca44ff2da59
-- title:
--   Fourier Transform KProd Locally Constant Compact Suppo
-- statement:
--   Definitions and structural lemmas for Fourier Transform KProd Locally Constant Compact Suppo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FourierTransformKProdLocallyConstantCompactSuppo.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
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
namespace GlobalTheory.FourKTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
def betaK (A : Et F E) : LinearMap.BilinForm F (A.K × A.K) :=
  (Algebra.traceForm F A.K).compl₁₂ (LinearMap.fst F A.K A.K) (LinearMap.snd F A.K A.K) +
    (Algebra.traceForm F A.K).compl₁₂ (LinearMap.snd F A.K A.K) (LinearMap.fst F A.K A.K)
end GlobalTheory.FourKTest


