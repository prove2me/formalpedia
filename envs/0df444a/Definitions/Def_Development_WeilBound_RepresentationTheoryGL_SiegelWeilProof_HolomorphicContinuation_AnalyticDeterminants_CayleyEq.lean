-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:54.342876+00:00
-- url     : https://prove2.me/theorems/e050eb1c-ae02-4fe3-ad76-f98a6956d38c
-- title:
--   Cayley Eq
-- statement:
--   Definitions and structural lemmas for Cayley Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
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
namespace PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def Dg {n : ℕ} (f : κ ≃ Fin n) (F : Matrix κ κ ℂ → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm κ, (Equiv.Perm.sign σ : ℂ) *
    iteratedFDeriv ℂ n F 0 (fun i => Matrix.single (f.symm i) (σ (f.symm i)) 1)
end PositivityTheory.Rg.Sw.LVs.CEq
namespace PositivityTheory.Rg.Sw.LVs
end PositivityTheory.Rg.Sw.LVs


