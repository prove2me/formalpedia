-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:41.392402+00:00
-- url     : https://prove2.me/theorems/6da25114-9142-5fa5-8b83-244fe3b02ee2
-- title:
--   Statements Component Res Bad Null
-- statement:
--   Definitions and structural lemmas for Statements Component Res Bad Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComponentResBadNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResInt
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
section Objects
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
def resProj (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M) : Fin e → ℂ :=
  fun i => Ψ (segre (R.pt x)) i.succ / Ψ (segre (R.pt x)) 0
def resBad (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.R.M :=
  {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} ∪ {x | Ψ (segre (R.pt x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.atlas.chart j).source ∧
      ¬ (AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) ∧
        LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}
end Objects
def ComponentResBadNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    IsGoodProj P Ψ →
    ∀ j, volume ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' resBad R Ψ) = 0
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


