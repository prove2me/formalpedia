-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:09.702921+00:00
-- url     : https://prove2.me/theorems/b69e05c5-574a-4af3-997b-74d9998d63c3
-- title:
--   Mul Vec Of Real Vec Add Mem Span Period Lattice
-- statement:
--   Definitions and structural lemmas for Mul Vec Of Real Vec Add Mem Span Period Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def periodCoordFst (τ : Matrix ι ι ℂ) (w : ι → ℂ) : ι → ℝ :=
  (τ.map Complex.im)⁻¹ *ᵥ fun i => (w i).im
def periodCoordSnd (τ : Matrix ι ι ℂ) (w : ι → ℂ) : ι → ℝ :=
  (fun i => (w i).re) - τ.map Complex.re *ᵥ periodCoordFst τ w
end GlobalTheory


