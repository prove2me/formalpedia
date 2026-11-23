-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:09.026955+00:00
-- url     : https://prove2.me/theorems/1cc9af14-c2ee-4e51-8663-a462ec0ed06a
-- title:
--   Exists Integral Basis Unramified Involution Ext
-- statement:
--   Definitions and structural lemmas for Exists Integral Basis Unramified Involution Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralBasisUnramifiedInvolutionExt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
namespace GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
abbrev adicVal (K : UQ) : Valuation K.E (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
end GlobalTheory.UnitLemma.Unr.IntBasis


