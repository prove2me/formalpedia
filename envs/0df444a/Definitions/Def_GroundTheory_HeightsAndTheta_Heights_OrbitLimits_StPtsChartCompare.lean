-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsChartCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsChartCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:19.967344+00:00
-- url     : https://prove2.me/theorems/f4299463-8142-48c3-92be-983f0305fee9
-- title:
--   St Pts Chart Compare
-- statement:
--   Definitions and structural lemmas for St Pts Chart Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsChartCompare.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSegreChart
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
def PtsChartCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (e : ℕ) (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    Measurable ({z : (Σ k, ι k) → ℂ | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}.indicator g) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) g y w|) →
      Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) g y w) →
      ptsIntegralAt P Ψ (pot L) g =
        ∑ᶠ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
          varInt J e
            ({x | ∀ k, ∃ j, PtsSegreChart.pt x ⟨k, j⟩ ≠ 0}.indicator fun x => g (PtsSegreChart.pt x))
            (PtsSegreChart.chartPot L)
end GroundTheory.Heights₂.Heights


