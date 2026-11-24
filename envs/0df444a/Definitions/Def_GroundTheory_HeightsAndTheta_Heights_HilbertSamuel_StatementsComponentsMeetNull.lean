-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentsMeetNull
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentsMeetNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:03.543796+00:00
-- url     : https://prove2.me/theorems/4402ed32-bd5e-4666-a351-bae527d9cf75
-- title:
--   Statements Components Meet Null
-- statement:
--   Definitions and structural lemmas for Statements Components Meet Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComponentsMeetNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentsAdditive
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def ComponentsMeetNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ))),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
    (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, Ψ (segre z) = Fin.cons 1 y ∧
      ∃ W ∈ S, ∃ W' ∈ S, W ≠ W' ∧ z ∈ zeroLocus ℂ W ∧ z ∈ zeroLocus ℂ W'} = 0
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


