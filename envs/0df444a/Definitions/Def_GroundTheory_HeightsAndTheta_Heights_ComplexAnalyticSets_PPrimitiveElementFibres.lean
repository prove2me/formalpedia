-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:34.523013+00:00
-- url     : https://prove2.me/theorems/6db5a396-82e8-40c3-a89d-1b947728c8ae
-- title:
--   PPrimitive Element Fibres
-- statement:
--   Definitions and structural lemmas for PPrimitive Element Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveElementFibres.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
namespace PrimitiveElementFibres
variable {n d : ℕ}
def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) (hx : x ∈ zeroSet J) :
    MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
  Ideal.Quotient.lift J (eval x) (fun q hq => hx q hq)
end PrimitiveElementFibres
end
end GroundTheory.Heights₂.Heights.ComplexSets


