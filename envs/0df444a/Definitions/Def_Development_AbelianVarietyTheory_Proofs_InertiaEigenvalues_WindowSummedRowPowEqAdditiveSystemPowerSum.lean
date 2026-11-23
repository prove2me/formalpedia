-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:01.462954+00:00
-- url     : https://prove2.me/theorems/51df5e57-9ab3-419c-8f2d-8c0106563739
-- title:
--   Window Summed Row Pow Eq Additive System Power Sum
-- statement:
--   Definitions and structural lemmas for Window Summed Row Pow Eq Additive System Power Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowSummedRowPowEqAdditiveSystemPowerSum.lean

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
open GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE.WinCoef
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
noncomputable abbrev frobAut : RingAut F := frobeniusEquiv F p
end GlobalTheory.PMonE.WinCoef


