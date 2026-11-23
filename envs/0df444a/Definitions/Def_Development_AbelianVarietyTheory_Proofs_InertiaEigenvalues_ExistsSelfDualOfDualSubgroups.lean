-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:54.088121+00:00
-- url     : https://prove2.me/theorems/4a117355-9d48-4a48-a933-45e96e181c62
-- title:
--   Exists Self Dual Of Dual Subgroups
-- statement:
--   Definitions and structural lemmas for Exists Self Dual Of Dual Subgroups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
namespace GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
end GlobalTheory.JR.AbsInv


