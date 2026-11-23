-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OrthonormalIffUnitary
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OrthonormalIffUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:19.373808+00:00
-- url     : https://prove2.me/theorems/7283b45a-67de-4871-bb3b-1feb7c86200d
-- title:
--   Orthonormal Iff Unitary
-- statement:
--   Definitions and structural lemmas for Orthonormal Iff Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OrthonormalIffUnitary.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
noncomputable section
namespace GlobalTheory.UnitLemma.BaseChange
variable {K : UQ} (B : InvAlg K)
end GlobalTheory.UnitLemma.BaseChange


