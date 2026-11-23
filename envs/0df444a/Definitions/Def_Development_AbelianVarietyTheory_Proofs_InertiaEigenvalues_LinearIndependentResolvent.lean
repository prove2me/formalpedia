-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentResolvent
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentResolvent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:58.522951+00:00
-- url     : https://prove2.me/theorems/543fe5f0-3a74-4b1c-b2f2-58cd229a129c
-- title:
--   Linear Independent Resolvent
-- statement:
--   Definitions and structural lemmas for Linear Independent Resolvent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinearIndependentResolvent.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.NonUnitShift
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end GlobalTheory.NonUnitShift


