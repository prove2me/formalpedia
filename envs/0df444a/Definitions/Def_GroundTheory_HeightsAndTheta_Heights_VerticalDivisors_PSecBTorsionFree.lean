-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:42.68094+00:00
-- url     : https://prove2.me/theorems/1f9de653-4be3-427b-b7e7-c8f7dcec91d3
-- title:
--   PSec BTorsion Free
-- statement:
--   Definitions and structural lemmas for PSec BTorsion Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
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
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
section Coordinates
variable {R : Type*} [CommRing R] {n e : ℕ}
end Coordinates
section Chart
variable {D : Type*} [CommRing D] {n : ℕ}
def chartCoordinate (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) : MvPolynomial (Fin n) D ⧸ Q :=
  Ideal.Quotient.mk Q (X j)
abbrev ChartDj (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) : Type _ :=
  Localization.Away (chartCoordinate Q j)
def chartCoord (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j k : Fin n) :
    MvPolynomial (Par e n) (ChartDj Q j) :=
  C (algebraMap _ _ (Ideal.Quotient.mk Q (X k)))
def chartInvC (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    MvPolynomial (Par e n) (ChartDj Q j) :=
  C (IsLocalization.Away.invSelf (chartCoordinate Q j))
theorem chartCoord_mul_inv (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    chartCoord e Q j j * chartInvC e Q j = 1 := by
  rw [chartCoord, chartInvC, ← C_mul]
  have : algebraMap (MvPolynomial (Fin n) D ⧸ Q) (ChartDj Q j) (Ideal.Quotient.mk Q (X j)) *
      IsLocalization.Away.invSelf (chartCoordinate Q j) = 1 := IsLocalization.Away.mul_invSelf (chartCoordinate Q j)
  rw [this, C_1]
def chartSub (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    Par e n → MvPolynomial (Par e n) (ChartDj Q j) :=
  Sum.elim
    (fun ik => X (.inl ik) -
      if ik.2 = j then (∑ k, X (.inl (ik.1, k)) * chartCoord e Q j k) * chartInvC e Q j else 0)
    (fun k => X (.inr k) -
      if k = j then (∑ k', X (.inr k') * chartCoord e Q j k' - 1) * chartInvC e Q j else 0)
theorem chartSub_rel_inl (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (i : Fin e) :
    ∑ k, chartSub e Q j (.inl (i, k)) * chartCoord e Q j k = 0 := by
  simp only [chartSub, Sum.elim_inl, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_assoc, mul_comm (chartInvC e Q j) _, chartCoord_mul_inv, mul_one, sub_self]
theorem chartSub_rel_inr (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    ∑ k, chartSub e Q j (.inr k) * chartCoord e Q j k = 1 := by
  simp only [chartSub, Sum.elim_inr, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_assoc, mul_comm (chartInvC e Q j) _, chartCoord_mul_inv, mul_one, sub_sub_cancel]
  rw [one_mul, mul_comm, chartCoord_mul_inv]
def chartHomA (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    MvPolynomial (Par e n) D →+* MvPolynomial (Par e n) (ChartDj Q j) :=
  eval₂Hom (C.comp ((algebraMap _ (ChartDj Q j)).comp ((Ideal.Quotient.mk Q).comp C))) (chartSub e Q j)
variable (e : ℕ) (R : Type*) [CommRing R] [Algebra (MvPolynomial (Par e n) D) R]
def chartModel (Q : Ideal (MvPolynomial (Fin n) D)) : Ideal (MvPolynomial (Fin n) R) :=
  Q.map (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C))
variable (D) in

def chartPar : Par e n → R := fun p => algebraMap (MvPolynomial (Par e n) D) R (X p)
theorem chartModel_le (Q : Ideal (MvPolynomial (Fin n) D)) :
    chartModel e R Q ≤ secIdeal (chartModel e R Q) (chartPar D e R) :=
  le_sup_left.trans le_sup_left
abbrev ChartE' (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D)) :
    Type _ :=
  Localization (S.map (chartHomA e Q j))
variable (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D))
def chartHomR [IsLocalization S R] : R →+* ChartE' e Q j S :=
  IsLocalization.map (M := S) (ChartE' e Q j S) (chartHomA e Q j) (Submonoid.le_comap_map S)
theorem chartHomR_algebraMap [IsLocalization S R] (a : MvPolynomial (Par e n) D) :
    chartHomR e R Q j S (algebraMap _ R a) = algebraMap _ (ChartE' e Q j S) (chartHomA e Q j a) :=
  IsLocalization.map_eq _ _
def chartPhi0 [IsLocalization S R] : MvPolynomial (Fin n) R →+* ChartE' e Q j S :=
  eval₂Hom (chartHomR e R Q j S) fun k => algebraMap _ _ (chartCoord e Q j k)
theorem chartPhi0_map [IsLocalization S R] (q : MvPolynomial (Fin n) D) :
    chartPhi0 e R Q j S (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C) q) =
      algebraMap (MvPolynomial (Par e n) (ChartDj Q j)) (ChartE' e Q j S)
        (C (algebraMap _ (ChartDj Q j) (Ideal.Quotient.mk Q q))) := by
  have : (chartPhi0 e R Q j S).comp (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C)) =
      (algebraMap (MvPolynomial (Par e n) (ChartDj Q j)) (ChartE' e Q j S)).comp (C.comp ((algebraMap _ (ChartDj Q j)).comp
        (Ideal.Quotient.mk Q))) := by
    refine MvPolynomial.ringHom_ext (fun d => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, map_C, chartPhi0, eval₂Hom_C, chartHomR_algebraMap, chartHomA]
    · simp only [RingHom.comp_apply, map_X, chartPhi0, eval₂Hom_X', chartCoord]
  exact RingHom.congr_fun this q
theorem secIdeal_le_ker_chartPhi0 [IsLocalization S R] :
    secIdeal (chartModel e R Q) (chartPar D e R) ≤ RingHom.ker (chartPhi0 e R Q j S) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [chartModel, Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, chartPhi0_map, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero,
      map_zero, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h := congrArg (algebraMap _ (ChartE' e Q j S)) (chartSub_rel_inl e Q j i)
    rw [map_zero] at h
    rw [← h]
    simp only [secForm, linForm, chartPar, map_sum, map_mul, chartPhi0, eval₂Hom_C, eval₂Hom_X',
      chartHomR_algebraMap, chartHomA]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      sub_eq_zero]
    have h := congrArg (algebraMap _ (ChartE' e Q j S)) (chartSub_rel_inr e Q j)
    rw [map_one] at h
    rw [← h]
    simp only [chartForm, linForm, chartPar, map_sum, map_mul, chartPhi0, eval₂Hom_C, eval₂Hom_X',
      chartHomR_algebraMap, chartHomA]
def chartPhi [IsLocalization S R] : SecAlg (chartModel e R Q) (chartPar D e R) →+* ChartE' e Q j S :=
  Ideal.Quotient.lift _ (chartPhi0 e R Q j S) fun _ ha => secIdeal_le_ker_chartPhi0 e R Q j S ha
abbrev ChartBj : Type _ :=
  Localization.Away (secCoord (chartModel e R Q) (chartPar D e R) j)
def chartKappa : MvPolynomial (Fin n) D →+* SecAlg (chartModel e R Q) (chartPar D e R) :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C))
theorem chartKappa_eq_zero {q : MvPolynomial (Fin n) D} (hq : q ∈ Q) : chartKappa e R Q q = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (chartModel_le e R Q (Ideal.mem_map_of_mem _ hq))
theorem chartKappa_X (k : Fin n) : chartKappa e R Q (X k) = secCoord (chartModel e R Q) (chartPar D e R) k := by
  simp only [chartKappa, RingHom.comp_apply, map_X, secCoord]
def chartChi : (MvPolynomial (Fin n) D ⧸ Q) →+* ChartBj e R Q j :=
  (algebraMap _ _).comp (Ideal.Quotient.lift Q (chartKappa e R Q) fun _ hq => chartKappa_eq_zero e R Q hq)
theorem chartChi_mk (q : MvPolynomial (Fin n) D) :
    chartChi e R Q j (Ideal.Quotient.mk Q q) = algebraMap _ (ChartBj e R Q j) (chartKappa e R Q q) := by
  simp only [chartChi, RingHom.comp_apply, Ideal.Quotient.lift_mk]
theorem chartChi_isUnit : IsUnit (chartChi e R Q j (chartCoordinate Q j)) := by
  rw [chartCoordinate, chartChi_mk, chartKappa_X]
  exact IsLocalization.Away.algebraMap_isUnit _
def chartPsiD : ChartDj Q j →+* ChartBj e R Q j :=
  IsLocalization.Away.lift (chartCoordinate Q j) (chartChi_isUnit e R Q j)
theorem chartPsiD_mk (q : MvPolynomial (Fin n) D) :
    chartPsiD e R Q j (algebraMap _ _ (Ideal.Quotient.mk Q q)) =
      algebraMap _ (ChartBj e R Q j) (chartKappa e R Q q) := by
  rw [chartPsiD, IsLocalization.Away.lift_eq, chartChi_mk]
def chartPsi0 : MvPolynomial (Par e n) (ChartDj Q j) →+* ChartBj e R Q j :=
  eval₂Hom (chartPsiD e R Q j) fun p =>
    algebraMap _ _ (algebraMap R (SecAlg (chartModel e R Q) (chartPar D e R)) (chartPar D e R p))
theorem chartPsi0_coord (k : Fin n) :
    chartPsi0 e R Q j (chartCoord e Q j k) =
      algebraMap _ (ChartBj e R Q j) (secCoord (chartModel e R Q) (chartPar D e R) k) := by
  rw [chartPsi0, chartCoord, eval₂Hom_C, chartPsiD_mk, chartKappa_X]
theorem chartPsi0_rel_inl (i : Fin e) :
    chartPsi0 e R Q j (∑ k, X (.inl (i, k)) * chartCoord e Q j k) = 0 := by
  have h0 : Ideal.Quotient.mk (secIdeal (chartModel e R Q) (chartPar D e R))
      (secForm (chartPar D e R) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_sup_right
      (Ideal.subset_span ⟨i, rfl⟩)))
  have h1 := congrArg (algebraMap _ (ChartBj e R Q j)) h0
  rw [map_zero] at h1
  rw [← h1, map_sum, secForm, linForm, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_mul, chartPsi0_coord, chartPsi0, eval₂Hom_X']
  rfl
theorem chartPsi0_rel_inr :
    chartPsi0 e R Q j (∑ k, X (.inr k) * chartCoord e Q j k - 1) = 0 := by
  have h0 : Ideal.Quotient.mk (secIdeal (chartModel e R Q) (chartPar D e R))
      (chartForm (chartPar D e R) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  have h1 := congrArg (algebraMap _ (ChartBj e R Q j)) h0
  rw [map_zero] at h1
  rw [← h1]
  simp only [map_sub, map_one]
  rw [map_sum, chartForm, linForm, map_sum, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_mul, chartPsi0_coord, chartPsi0, eval₂Hom_X']
  rfl
theorem chartPsi0_comp :
    (chartPsi0 e R Q j).comp (chartHomA e Q j) =
      (algebraMap _ (ChartBj e R Q j)).comp
        ((algebraMap R (SecAlg (chartModel e R Q) (chartPar D e R))).comp
          (algebraMap (MvPolynomial (Par e n) D) R)) := by
  refine MvPolynomial.ringHom_ext (fun d => ?_) (fun p => ?_)
  · simp only [RingHom.comp_apply, chartHomA, eval₂Hom_C]
    rw [chartPsi0, eval₂Hom_C, chartPsiD_mk]
    simp only [chartKappa, RingHom.comp_apply, map_C]
    rfl
  · simp only [RingHom.comp_apply, chartHomA, eval₂Hom_X']
    rcases p with ⟨i, k⟩ | k
    · simp only [chartSub, Sum.elim_inl, map_sub]
      split_ifs
      · rw [map_mul, chartPsi0_rel_inl, zero_mul, sub_zero, chartPsi0, eval₂Hom_X']
        rfl
      · rw [map_zero, sub_zero, chartPsi0, eval₂Hom_X']
        rfl
    · simp only [chartSub, Sum.elim_inr, map_sub]
      split_ifs
      · rw [map_mul, chartPsi0_rel_inr, zero_mul, sub_zero, chartPsi0, eval₂Hom_X']
        rfl
      · rw [map_zero, sub_zero, chartPsi0, eval₂Hom_X']
        rfl
def chartPsi [IsLocalization S R] : ChartE' e Q j S →+* ChartBj e R Q j :=
  IsLocalization.lift (M := S.map (chartHomA e Q j)) (g := chartPsi0 e R Q j) (by
    rintro ⟨_, s, hs, rfl⟩
    show IsUnit (chartPsi0 e R Q j (chartHomA e Q j s))
    have h := RingHom.congr_fun (chartPsi0_comp e R Q j) s
    simp only [RingHom.comp_apply] at h
    rw [h]
    exact ((IsLocalization.map_units R (⟨s, hs⟩ : S)).map _).map _)
end Chart
end
end GroundTheory.Heights₂.Heights.Vertical


