-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:37.581319+00:00
-- url     : https://prove2.me/theorems/e102fc4e-ecb7-4060-9591-c84089349f3f
-- title:
--   Statements Clopen Components
-- statement:
--   Definitions and structural lemmas for Statements Clopen Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsClopenComponents.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenDegree
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
def ClopenComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (A : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → A ⊆ mcPts P → IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) →
    ∃ S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) ∧
      A = mcPts P ∩ ⋃ W ∈ S, zeroLocus ℂ W ∧
      vanishingIdeal ℂ A = ⨅ W ∈ S, W
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


