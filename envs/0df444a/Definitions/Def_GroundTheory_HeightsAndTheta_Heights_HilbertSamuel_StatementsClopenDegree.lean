-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:37.721856+00:00
-- url     : https://prove2.me/theorems/6cb8f219-8a07-4e5c-82e5-657268986769
-- title:
--   Statements Clopen Degree
-- statement:
--   Definitions and structural lemmas for Statements Clopen Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsClopenDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
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
def ClopenDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (A : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → A ⊆ mcPts P →
    IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) →
    ptsIntegral P (pot L) (A.indicator fun _ => (1 : ℝ)) =
      NumbersDVR.intNum ℂ (vanishingIdeal ℂ A) (fun j => (L j).a)
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


