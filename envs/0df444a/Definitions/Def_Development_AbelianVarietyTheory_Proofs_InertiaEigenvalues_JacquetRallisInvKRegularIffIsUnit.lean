-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:17:35.9338+00:00
-- url     : https://prove2.me/theorems/e19edeb1-0725-48cf-af77-441d583e8192
-- title:
--   Jacquet Rallis Inv KRegular Iff Is Unit
-- statement:
--   Definitions and structural lemmas for Jacquet Rallis Inv KRegular Iff Is Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisInvKRegularIffIsUnit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
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
namespace GlobalTheory.JR.EtInv
section Gen
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]
variable {r : ℕ} {τ : K}
end Gen
section Comp
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] {r : ℕ} {τ : K} {p : Fin r → F}
end Comp
end GlobalTheory.JR.EtInv


