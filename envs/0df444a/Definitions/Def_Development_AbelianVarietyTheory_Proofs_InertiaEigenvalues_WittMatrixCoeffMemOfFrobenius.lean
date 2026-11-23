-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:28.89038+00:00
-- url     : https://prove2.me/theorems/ea22a0f3-b2d6-4050-aed1-032d0c5dc24c
-- title:
--   Witt Matrix Coeff Mem Of Frobenius
-- statement:
--   Definitions and structural lemmas for Witt Matrix Coeff Mem Of Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
namespace GlobalTheory
namespace WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
noncomputable def S : Subring (WittVector p C) := (WittVector.map (p := p) A.subtype).range
variable {p}
variable [CharP C p]
variable [PerfectRing C p]
noncomputable def tail (x : WittVector p C) : WittVector p C :=
  WittVector.mk p fun k => (frobeniusEquiv C p).symm (x.coeff (k + 1))
end WittIntegrality
end GlobalTheory


