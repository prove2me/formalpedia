-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDiv
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:39.50983+00:00
-- url     : https://prove2.me/theorems/882bcdb4-0127-4678-8cba-b017b022aa9d
-- title:
--   Cay Div
-- statement:
--   Definitions and structural lemmas for Cay Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDiv.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
def Sop (s : ℂ) (m n : ℕ) : Set (Module.End ℂ (Fm n)) :=
  Set.range fun x : Bool × Fin n × Fin n => opH s m x.1 x.2.1 x.2.2
end PositivityTheory.Rg.Sw.SP


