-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:05.275027+00:00
-- url     : https://prove2.me/theorems/7380ef5c-6d9a-444e-aa02-9ed71df32b59
-- title:
--   Is Multi Homog Plane Coordinate
-- statement:
--   Definitions and structural lemmas for Is Multi Homog Plane Coordinate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_isMultiHomog

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def normSq (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) ^ 2
def regLog (A : HermLine ι) (s : MRing ι) (ε : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (normSq A s z + ε) / 2
theorem normSq_smul {A : HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    normSq A s (fun p => c p.1 * z p) = normSq A s z := by
  unfold normSq
  rw [eval_smul_of_isMultiHomog hs c z, A.smul c z hc, norm_mul, norm_prod]
  have hC : (∏ k, ‖c k‖ ^ A.a k) = ∏ k, ‖c k ^ a k‖ := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, norm_pow, zpow_natCast]
  rw [hC, mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ =>
    norm_ne_zero_iff.mpr (pow_ne_zero _ (hc k)))]
def regLine (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) : HermLine ι :=
  HermLine.ofWeight (fun z => -regLog A s ε z) fun c z hc => by
    simp only [regLog, normSq_smul ha hs c z hc]
theorem isMultiHomog_planeCoordinate (i : Fin 3) : IsMultiHomog (Xc 3 i) (fun _ => 1) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  simp [Finsupp.single_apply]
def regularisedLogNormSecond : HermLine (PBlk 3) :=
  regLine (fsLine 3) (Xc 3 1) 1 (fun _ => rfl) (isMultiHomog_planeCoordinate 1)
end GroundTheory.Heights₂.Heights.Targets


