-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetColumnPerturbation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:08.670715+00:00
-- url     : https://prove2.me/theorems/65be74b3-9c99-4949-b49d-257286137c73
-- title:
--   Det Column Perturbation
-- statement:
--   Definitions and structural lemmas for Det Column Perturbation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetColumnPerturbation.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
def phiF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Fin.cons 0 X
def piF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ := fun k l => X k l.succ
def colQ (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun k l => if l = c then X k 0 else 0
@[simp] theorem phiF_zero_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (j : Fin (N + 1)) : phiF X 0 j = 0 := rfl
@[simp] theorem phiF_succ_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (k : Fin N) (j : Fin (N + 1)) :
    phiF X k.succ j = X k j := rfl
def phiL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := phiF
      map_add' := fun X Y => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp
      map_smul' := fun a X => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp }
def piL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := piF
      map_add' := fun X Y => by ext k l; simp [piF]
      map_smul' := fun a X => by ext k l; simp [piF] }
end PositivityTheory.Rg.Sw.LVs.CK


