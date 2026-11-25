-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T15:39:20.48732+00:00
-- url     : https://prove2.me/theorems/9eed1bcd-837c-5d31-97f6-a21561a3dcc8
-- title:
--   Fourier Integral Bound
-- statement:
--   Definitions and structural lemmas for Fourier Integral Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FourierIntegralBound.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
section Lemmas
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace Res
variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)
end Res
end Lemmas
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


