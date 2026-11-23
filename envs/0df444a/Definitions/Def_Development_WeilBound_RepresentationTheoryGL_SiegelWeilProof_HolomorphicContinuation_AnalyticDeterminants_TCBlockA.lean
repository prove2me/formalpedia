-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:32.800717+00:00
-- url     : https://prove2.me/theorems/12a65f05-4249-4c65-8b72-8d7f8a69291c
-- title:
--   TCBlock A
-- statement:
--   Definitions and structural lemmas for TCBlock A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlockA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
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
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def embL (s : Finset (Fin n)) : Matrix s s ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := embOn s
      map_add' := fun T T' => by
        ext a b
        simp only [embOn, Matrix.add_apply]
        split_ifs <;> simp
      map_smul' := fun x T => by
        ext a b
        simp only [embOn, Matrix.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
def bdL (j : ℕ) (c c' : ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := bdiag j c c'
      map_add' := fun T T' => by
        ext a b
        simp only [bdiag, Matrix.add_apply]
        split_ifs <;> ring
      map_smul' := fun x T => by
        ext a b
        simp only [bdiag, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> ring }
end PositivityTheory.Rg.Sw.LVs.TC


