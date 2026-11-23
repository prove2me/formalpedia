-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:21.917488+00:00
-- url     : https://prove2.me/theorems/79ad1cef-5cfb-4f62-bb1d-de7f67a32f01
-- title:
--   Dp Dual
-- statement:
--   Definitions and structural lemmas for Dp Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
namespace PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
section detD
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end detD
section blocks
variable {n : ℕ}
def dp_incl (s : Finset (Fin n)) : Matrix (Fin n) s ℂ := fun a c => if a = (c : Fin n) then 1 else 0
def proj (s : Finset (Fin n)) : Matrix s (Fin n) ℂ := fun c b => if (c : Fin n) = b then 1 else 0
end blocks
section group
variable {n : ℕ}
end group
section cm
variable {n : ℕ}
def CmI (n : ℕ) : M2 n := (-(Complex.I / 2)) • Matrix.fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)
def Lr (n : ℕ) : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := Matrix.fromCols 1 (Complex.I • 1)
def Rc (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows 1 0
end cm
section main
variable {n : ℕ}
end main
end PositivityTheory.Rg.Sw.LVs


