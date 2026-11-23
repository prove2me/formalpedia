-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:19.468353+00:00
-- url     : https://prove2.me/theorems/18e62334-d586-4419-8da0-dced7bebc8f1
-- title:
--   Exists Not XPow Dvd Adjugate Of First Order Kernel
-- statement:
--   Definitions and structural lemmas for Exists Not XPow Dvd Adjugate Of First Order Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
namespace GlobalTheory
namespace CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
end CofactorOrder
end GlobalTheory


