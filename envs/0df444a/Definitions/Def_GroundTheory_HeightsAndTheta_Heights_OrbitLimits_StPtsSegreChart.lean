-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSegreChart
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSegreChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:37.170039+00:00
-- url     : https://prove2.me/theorems/d5c4e7e5-9ffe-49e1-baa2-29782cb09698
-- title:
--   St Pts Segre Chart
-- statement:
--   Definitions and structural lemmas for St Pts Segre Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsSegreChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
namespace PtsSegreChart
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def coordEquiv : (Σ k, ι k) ≃ Fin (Fintype.card (Σ k, ι k)) :=
  Fintype.equivFin _
def pt (x : Fin (Fintype.card (Σ k, ι k)) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => x (coordEquiv p)
def ideal (P : Ideal (MRing ι)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  Ideal.map ((rename (coordEquiv (ι := ι))).toRingHom.comp (map (Int.castRingHom ℂ))) P ⊔
    Ideal.span (Set.range fun k => (X (coordEquiv ⟨k, i k⟩) - 1 : MvPolynomial _ ℂ))
def chartPot {e : ℕ} (L : Fin e → HermLine ι) : Fin e → (Fin (Fintype.card (Σ k, ι k)) → ℂ) → ℝ :=
  fun j x => Real.log ((L j).h (pt x))
def weight (u : ((Σ k, ι k) → ℂ) → ℝ) (A : HermLine ι) (s : MRing ι) :
    (Fin (Fintype.card (Σ k, ι k)) → ℂ) → ℝ :=
  {x | ∀ k, ∃ j, pt x ⟨k, j⟩ ≠ 0}.indicator fun x => u (pt x) * logNorm A s (pt x)
end PtsSegreChart
def PtsSegreChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (u : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    IsDegZeroSmooth u → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → u z = 0) →
    ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y =>
        ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (fun z => u z * logNorm A s z) y w) ∧
      ptsIntegralAt P Ψ (pot L) (fun z => u z * logNorm A s z) =
        ∑ᶠ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
          varInt J e (PtsSegreChart.weight u A s) (PtsSegreChart.chartPot L)
end GroundTheory.Heights₂.Heights


