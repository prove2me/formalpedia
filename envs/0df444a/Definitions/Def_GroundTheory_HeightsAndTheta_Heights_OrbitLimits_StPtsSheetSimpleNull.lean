-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:44.302917+00:00
-- url     : https://prove2.me/theorems/f386460d-665e-4385-bb27-715cf7dbf46f
-- title:
--   St Pts Sheet Simple Null
-- statement:
--   Definitions and structural lemmas for St Pts Sheet Simple Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StPtsSheetSimpleNull.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
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
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet PBlk)
def IsSimpleSheetPt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSheet P Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)
def PtsSheetSimpleNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      volume {y : Fin e → ℂ | ∃ w ∈ fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) ∧ ¬ IsSimpleSheetPt P Ψ w} = 0
def planeLift (y : Fin 2 → ℂ) : (Σ k, PBlk 3 k) → ℂ := fun p => (Fin.cons 1 y : Fin 3 → ℂ) p.2
end GroundTheory.Heights₂.Heights


