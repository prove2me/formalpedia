-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:36.357318+00:00
-- url     : https://prove2.me/theorems/a0bf0e16-b125-439d-acae-3d1aab0642e4
-- title:
--   Laurent Degeneration First Order Kernel
-- statement:
--   Definitions and structural lemmas for Laurent Degeneration First Order Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentDegenerationFirstOrderKernel.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory
noncomputable def laurentCoeffForm (k : Type) [Field k] (n : ℤ) :
    letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
    HahnSeries ℤ k →ₗ[k] k :=
  HahnSeries.coeff.linearMap n
end GlobalTheory


