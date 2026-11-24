-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.694007+00:00
-- url     : https://prove2.me/theorems/b1c3d048-30ab-4395-9776-3d9feb3d8128
-- title:
--   Dense C
-- statement:
--   Definitions and structural lemmas for Dense C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/CayleyTransform/DenseC.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
namespace PositivityTheory.SiegelWeilFormula.Krd.DC
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def InU (J h : Matrix ι ι ℂ) : Prop := hᴴ * J * h = J
def InLie (J Y : Matrix ι ι ℂ) : Prop := Yᴴ * J + J * Y = 0
def cay (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 + Y) * (1 - Y)⁻¹
def proj (J : Matrix ι ι ℂ) (d : ℂ) (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := Y - d⁻¹ • (J * Yᴴ * J)
end PositivityTheory.SiegelWeilFormula.Krd.DC
end


