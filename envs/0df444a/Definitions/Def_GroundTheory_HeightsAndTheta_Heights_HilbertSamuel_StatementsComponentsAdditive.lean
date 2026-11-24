-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentsAdditive
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentsAdditive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:57.300049+00:00
-- url     : https://prove2.me/theorems/21f6dff6-8f9b-4e1c-94fc-70ba73d207e2
-- title:
--   Statements Components Additive
-- statement:
--   Definitions and structural lemmas for Statements Components Additive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComponentsAdditive.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
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
def ComponentsAdditive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ))),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) →
    ptsIntegral P (pot L) ((mcPts P ∩ ⋃ W ∈ S, zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) =
      ∑ W ∈ S, ptsIntegral P (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ))
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


