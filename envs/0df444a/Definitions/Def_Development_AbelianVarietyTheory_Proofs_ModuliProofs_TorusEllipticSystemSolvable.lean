-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:34.083734+00:00
-- url     : https://prove2.me/theorems/7f8e953d-46f5-4e60-b001-769ab13df768
-- title:
--   Torus Elliptic System Solvable
-- statement:
--   Definitions and structural lemmas for Torus Elliptic System Solvable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorusEllipticSystemSolvable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
namespace GlobalTheory
namespace TorusElliptic
def Rapid {n : ℕ} (c : (Fin n → ℤ) → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C
noncomputable def ch {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) : ℂ :=
  cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))
end TorusElliptic
end GlobalTheory


