-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSheetHessPSD
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StSheetHessPSD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:12.30928+00:00
-- url     : https://prove2.me/theorems/fd00d887-cb5b-4540-bc64-ed008a40d0d9
-- title:
--   St Sheet Hess PSD
-- statement:
--   Definitions and structural lemmas for St Sheet Hess PSD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StSheetHessPSD.lean

import Mathlib
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
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder
def SheetHessPSD.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (M : HermLine ι) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ),
    IsSmoothHerm M → IsSemiPosHerm M → IsSheet P Ψ y w γ →
    (cxHessian (fun y' => Real.log (M.h (γ y'))) y).PosSemidef
def lineProj : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ) :=
  LinearMap.pi fun i : Fin 2 => LinearMap.proj (R := ℂ) (φ := fun _ : ((k : Unit) → PBlk 2 k) => ℂ) (fun _ => i)
def lineSheet (y : Fin 1 → ℂ) : (Σ k, PBlk 2 k) → ℂ :=
  fun p => ![1, y 0] p.2
end GroundTheory.Heights₂.Heights.Inter


