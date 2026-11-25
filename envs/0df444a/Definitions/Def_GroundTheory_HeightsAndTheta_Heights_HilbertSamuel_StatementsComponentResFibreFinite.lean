-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:16.970926+00:00
-- url     : https://prove2.me/theorems/2a5b3214-3a0a-588c-8cbb-cb6fe56b5c54
-- title:
--   Statements Component Res Fibre Finite
-- statement:
--   Definitions and structural lemmas for Statements Component Res Fibre Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComponentResFibreFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
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
def ComponentResFibreFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    IsGoodProj P Ψ →
    ∀ y, (resProj R Ψ ⁻¹' {y} \ resBad R Ψ).Finite
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


