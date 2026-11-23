-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:12.657422+00:00
-- url     : https://prove2.me/theorems/d26b2a62-eafe-4e05-849d-c9f18b410491
-- title:
--   Card Window Zeros Inner Eq Shifted Outer
-- statement:
--   Definitions and structural lemmas for Card Window Zeros Inner Eq Shifted Outer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardWindowZerosInnerEqShiftedOuter.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
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
section WinInner
variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
def frobPerm : Equiv.Perm F := (frobeniusEquiv F p).toEquiv
end WinInner
end GlobalTheory.PMonE
end


