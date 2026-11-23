-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:32.111806+00:00
-- url     : https://prove2.me/theorems/ad864c01-9aa2-44aa-b195-fadac2ff74f5
-- title:
--   Lattice Determined By Invariants
-- statement:
--   Definitions and structural lemmas for Lattice Determined By Invariants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
namespace GlobalTheory
section
variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h
end
end GlobalTheory


