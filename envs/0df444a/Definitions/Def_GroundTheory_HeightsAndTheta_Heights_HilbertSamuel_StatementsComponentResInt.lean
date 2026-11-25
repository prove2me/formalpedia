-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResInt
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResInt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:39:44.60821+00:00
-- url     : https://prove2.me/theorems/56d6d72b-4a1e-4269-a9f1-512b0c7bf035
-- title:
--   Statements Component Res Int
-- statement:
--   Definitions and structural lemmas for Statements Component Res Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComponentResInt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def ComponentResInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    Nonempty (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) →
    ptsIntegral P (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) =
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.zInt W e (fun j => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.logH (L j))
        (fun _ => 1)
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


