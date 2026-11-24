-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:13.094929+00:00
-- url     : https://prove2.me/theorems/bb7bf022-da1c-456f-ad63-8620fed7fa70
-- title:
--   St Segre Coord Good Proj
-- statement:
--   Definitions and structural lemmas for St Segre Coord Good Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegreCoordGoodProj.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre PBlk)
def SegreCoordGoodProj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (i : (k : K) → ι k),
    IsArithVar P (e + 1) → (∃ z ∈ mcPts P, segre z i ≠ 0) →
      ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ ∧ ∀ w, Ψ w 0 = w i
def planeCoordProj : (((k : Unit) → PBlk 3 k) → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) :=
  LinearMap.pi fun a : Fin 3 =>
    LinearMap.proj (R := ℂ) (φ := fun _ : ((k : Unit) → PBlk 3 k) => ℂ) (fun _ : Unit => a)
end GroundTheory.Heights₂.Heights


