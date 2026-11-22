-- Prove2me | Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
-- name    : Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:13.986734+00:00
-- url     : https://prove2.me/theorems/7ba6c231-dd4f-45a0-b52a-ba3f61d5aad7
-- title:
--   Lat Lift Indep
-- statement:
--   Definitions and structural lemmas for Lat Lift Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/LatLiftIndep.lean

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ThetaLiftIndependence
namespace LatticeLiftIndependence
open Formalism.HermitianLatticesTheory
section Gen
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (a * b) L = gmap a (gmap b L) := by
  unfold gmap
  rw [← Submodule.map_comp]
  rfl
theorem gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  simp [gmap]
theorem gmap_inv_gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : gmap g⁻¹ (gmap g L) = L := by
  rw [← gmap_mul, inv_mul_cancel, gmap_one]
end Gen
section Lat
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
theorem conj_mem_autL (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    {M : Submodule (NumberField.RingOfIntegers K) V} {a : V ≃ₗ[K] V} (ha : a ∈ autL h M) :
    g * a * g⁻¹ ∈ autL h (gmap g M) := by
  refine ⟨(isom h).mul_mem ((isom h).mul_mem hg ha.1) ((isom h).inv_mem hg), ?_⟩
  show gmap (g * a * g⁻¹) (gmap g M) = gmap g M
  rw [gmap_mul, gmap_inv_gmap, gmap_mul, ha.2]
def conjEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ isom h)
    (M : Submodule (NumberField.RingOfIntegers K) V) : autL h M ≃ autL h (gmap g M) where
  toFun a := ⟨g * a * g⁻¹, conj_mem_autL h hg a.2⟩
  invFun b := ⟨g⁻¹ * b * g, by
    have := conj_mem_autL h ((isom h).inv_mem hg) b.2
    rwa [gmap_inv_gmap, inv_inv] at this⟩
  left_inv a := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv b := by
    apply Subtype.ext
    simp [mul_assoc]
end Lat
end LatticeLiftIndependence
open Formalism.HermitianLatticesTheory LatticeLiftIndependence
end Formalism.ThetaLiftIndependence


