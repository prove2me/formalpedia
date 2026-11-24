-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:30.172834+00:00
-- url     : https://prove2.me/theorems/cfaf59bf-2d2e-4836-bb77-389db96a8936
-- title:
--   PChart Domain
-- statement:
--   Definitions and structural lemmas for PChart Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartDomain.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
abbrev Base : Type := Localization.Away (Ideal.Quotient.mk Q (X j))
def cx (e : ℕ) (l : Fin n) : MvPolynomial (Par e n) (Base Q j) :=
  C (algebraMap _ _ (Ideal.Quotient.mk Q (X l)))
def cinv (e : ℕ) : MvPolynomial (Par e n) (Base Q j) :=
  C (IsLocalization.Away.invSelf (Ideal.Quotient.mk Q (X j)))
theorem cx_mul_cinv : cx Q j e j * cinv Q j e = 1 := by
  rw [cx, cinv, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
def parVal : Par e n → MvPolynomial (Par e n) (Base Q j)
  | .inl (i, l) => X (.inl (i, l)) -
      if l = j then cinv Q j e * ∑ m, X (.inl (i, m)) * cx Q j e m else 0
  | .inr l => X (.inr l) -
      if l = j then cinv Q j e * (∑ m, X (.inr m) * cx Q j e m - 1) else 0
def κ (e : ℕ) : D →+* MvPolynomial (Par e n) (Base Q j) :=
  (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp ((Ideal.Quotient.mk Q).comp C))
def evalF (e : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* MvPolynomial (Par e n) (Base Q j) :=
  eval₂Hom (eval₂Hom (κ Q j e) (parVal Q j)) (cx Q j e)
theorem evalF_comp_map :
    (evalF Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)) =
      (C : Base Q j →+* _).comp ((algebraMap _ (Base Q j)).comp (Ideal.Quotient.mk Q)) := by
  apply MvPolynomial.ringHom_ext
  · intro d; simp [evalF, κ]
  · intro l; simp [evalF, cx]
theorem secIdeal_le_ker :
    secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X ≤ RingHom.ker (evalF Q j e) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, evalF_comp_map]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inl (i, m)) * cx Q j e m)) * cx_mul_cinv Q j (e := e)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_one, map_sum, map_mul]
    simp only [evalF, coe_eval₂Hom, eval₂_C, eval₂Hom_X', parVal]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linear_combination (-(∑ m, X (.inr m) * cx Q j e m - 1)) * cx_mul_cinv Q j (e := e)
abbrev secI (e : ℕ) : Ideal (MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :=
  secIdeal (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)
abbrev Sec (e : ℕ) : Type :=
  SecAlg (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D)
abbrev xj (e : ℕ) : Sec Q e :=
  secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) (X : Par e n → MvPolynomial (Par e n) D) j
abbrev Chart (e : ℕ) : Type :=
  Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (X : Par e n → MvPolynomial (Par e n) D) j)
def toChart (e : ℕ) : MvPolynomial (Fin n) (MvPolynomial (Par e n) D) →+* Chart Q j e :=
  algebraMap _ (Chart Q j e)
theorem toChart_apply (e : ℕ) (a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)) :
    toChart Q j e a =
      algebraMap (Sec Q e) (Chart Q j e) (Ideal.Quotient.mk (secI Q e) a) := rfl
def toPoly (e : ℕ) : Chart Q j e →+* MvPolynomial (Par e n) (Base Q j) :=
  IsLocalization.Away.lift (xj Q j e)
    (g := Ideal.Quotient.lift (secI Q e) (evalF Q j e) (fun _ ha => RingHom.mem_ker.mp (secIdeal_le_ker Q j ha))) (by
      simp only [xj, secCoord, Ideal.Quotient.lift_mk, evalF, coe_eval₂Hom, eval₂_X]
      exact IsUnit.of_mul_eq_one _ (cx_mul_cinv Q j (e := e)))
theorem toChart_eq_zero {e : ℕ} {a : MvPolynomial (Fin n) (MvPolynomial (Par e n) D)} (ha : a ∈ secI Q e) :
    toChart Q j e a = 0 := by
  rw [toChart_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
def quotToChart (e : ℕ) : MvPolynomial (Fin n) D ⧸ Q →+* Chart Q j e :=
  Ideal.Quotient.lift Q ((toChart Q j e).comp (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D)))
    (fun _ hq => toChart_eq_zero Q j (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))))
def baseToChart (e : ℕ) : Base Q j →+* Chart Q j e :=
  IsLocalization.Away.lift (Ideal.Quotient.mk Q (X j)) (g := quotToChart Q j e) (by
    rw [quotToChart, Ideal.Quotient.lift_mk, RingHom.comp_apply, map_X, toChart_apply]
    exact IsLocalization.Away.algebraMap_isUnit (xj Q j e))
def fromPoly (e : ℕ) : MvPolynomial (Par e n) (Base Q j) →+* Chart Q j e :=
  eval₂Hom (baseToChart Q j e) fun p => toChart Q j e (C (X p))
end ChartDomain
end
end GroundTheory.Heights₂.Heights.Vertical


