-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:46.483196+00:00
-- url     : https://prove2.me/theorems/416a0d8d-16c1-4d0c-a79e-806d56b442ad
-- title:
--   Statements Proj Regular
-- statement:
--   Definitions and structural lemmas for Statements Proj Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsProjRegular.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
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
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
def projRegular {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {V : Set R.X} (BV : FinHolAtlas n V) : Set V :=
  {x | Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0 ∧ ∀ j, x ∈ (BV.chart j).source →
    LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0}
def ProjRegular.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (V : Set R.X) (BV : FinHolAtlas n V),
    HoloMap BV R.A Subtype.val →
    IsOpen (projRegular R Ψ BV) ∧
    (∀ x : V, Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0 → ∀ j, x ∈ (BV.chart j).source →
      AnalyticAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x)) ∧
    (∀ x : V, Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0 →
      LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart (chartIdx BV x)).symm)
        (BV.chart (chartIdx BV x) x) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 →
      x ∈ projRegular R Ψ BV)
end GroundTheory.Heights₂.Heights.Targets


