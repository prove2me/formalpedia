-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:16.192313+00:00
-- url     : https://prove2.me/theorems/883ba992-5dbe-4bb8-ba5a-02b572c868ed
-- title:
--   Normalized Row Coefficient Matrices Det Norm
-- statement:
--   Definitions and structural lemmas for Normalized Row Coefficient Matrices Det Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedRowCoefficientMatricesDetNorm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PMonE
open Finset
section Pw
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
end Pw
section Det
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
end Det
end GlobalTheory.PMonE
end
namespace GlobalTheory.PMonE
open Finset
end GlobalTheory.PMonE


