-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_StarExpNegI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:31.349056+00:00
-- url     : https://prove2.me/theorems/77237e82-a2a1-4627-85c2-0b11a9c857ce
-- title:
--   Star Exp Neg I
-- statement:
--   Definitions and structural lemmas for Star Exp Neg I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/StarExpNegI.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCMatC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
namespace PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}
def dA (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (θ * Complex.I) else Complex.exp (-θ * Complex.I)
def dB (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (-θ * Complex.I) else Complex.exp (θ * Complex.I)
end PositivityTheory.Rg.Sw.LVs.TC


