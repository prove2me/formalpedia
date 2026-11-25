-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:29.424101+00:00
-- url     : https://prove2.me/theorems/f57db0f2-b0f9-425b-8d50-47c560135684
-- title:
--   PCone Proj Hyperplane Dim
-- statement:
--   Definitions and structural lemmas for PCone Proj Hyperplane Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeProjHyperplaneDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)
namespace ConeProjHyperplaneDim
def coneForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    MvPolynomial (Fin n) ℂ :=
  rename (fun p : Σ k : Unit, PBlk n k => p.2) (psiPoly Ψ j)
end ConeProjHyperplaneDim
end GroundTheory.Heights₂.Heights


