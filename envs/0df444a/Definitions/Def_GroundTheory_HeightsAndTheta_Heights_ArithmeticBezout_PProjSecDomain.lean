-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:59.092914+00:00
-- url     : https://prove2.me/theorems/aef1966b-9e1a-4ca1-a195-a0d93f9be5dc
-- title:
--   PProj Sec Domain
-- statement:
--   Definitions and structural lemmas for PProj Sec Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDomain.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ProjSecDomain
abbrev Kf (e : ℕ) : Type := FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
variable {n e : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
abbrev S : Type :=
  Vertical.SecAlg (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A)
theorem map_linPoly (k : Fin (e + 1)) :
    MvPolynomial.map (algebraMap ℂ (Kf e)) (ComplexSets.linPoly A k) =
      linForm fun j => algebraMap ℂ (Kf e) (A k j) := by
  simp [ComplexSets.linPoly, linForm, map_sum]
theorem projVar_ne_zero (k : Fin (e + 1)) : projVar e k ≠ 0 := by
  rw [projVar, ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact X_ne_zero k
theorem chartForm_eq : Vertical.chartForm (projPar A) =
    C (projVar e 0)⁻¹ * linForm fun j => algebraMap ℂ (Kf e) (A 0 j) := by
  simp [Vertical.chartForm, linForm, projPar, Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm]
theorem secForm_eq (i : Fin e) : Vertical.secForm (projPar A) i =
    C (projVar e i.succ) * (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) -
      C (projVar e 0) * linForm fun j => algebraMap ℂ (Kf e) (A i.succ j) := by
  simp [Vertical.secForm, linForm, projPar, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_assoc]
variable {W A}
theorem mk_row (k : Fin (e + 1)) :
    Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
        (linForm fun j => algebraMap ℂ (Kf e) (A k j)) =
      algebraMap (Kf e) (S W A) (projVar e k) := by
  set q := Ideal.Quotient.mk (Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A))
  have hC : ∀ c, q (C c) = algebraMap (Kf e) (S W A) c := fun _ => rfl
  have hu : q (C (projVar e 0)) * q (C ((projVar e 0)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero 0), map_one, map_one]
  have hch : q (Vertical.chartForm (projPar A) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [map_sub, map_one, chartForm_eq, map_mul] at hch
  have ha0 : q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) = q (C (projVar e 0)) := by
    linear_combination q (C (projVar e 0)) * hch - q (linForm fun j => algebraMap ℂ (Kf e) (A 0 j)) * hu
  induction k using Fin.cases with
  | zero => rw [ha0, hC]
  | succ i =>
    have hs : q (Vertical.secForm (projPar A) i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_eq, map_sub, map_mul, map_mul, ha0] at hs
    rw [← hC]
    linear_combination (-q (C ((projVar e 0)⁻¹))) * hs +
      (q (C (projVar e i.succ)) - q (linForm fun j => algebraMap ℂ (Kf e) (A i.succ j))) * hu
variable (W A)
def psi : MvPolynomial (Fin n) ℂ ⧸ W →+* S W A :=
  Ideal.Quotient.lift W
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap ℂ (Kf e))))
    fun _ hf => Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)))
def M : Submonoid (MvPolynomial (Fin n) ℂ ⧸ W) :=
  (nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)).map (ComplexSets.projHom W A)
abbrev T : Type := Localization (M W A)
def kappa : Kf e →+* T W A :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial (Fin (e + 1)) ℂ)) (S := Kf e) (P := T W A)
    (g := (algebraMap _ (T W A)).comp (ComplexSets.projHom W A).toRingHom)
    fun y => IsLocalization.map_units (T W A) (⟨_, Submonoid.mem_map_of_mem _ y.2⟩ : M W A)
def phi : MvPolynomial (Fin n) (Kf e) →+* T W A :=
  eval₂Hom (kappa W A) fun j => algebraMap _ (T W A) (Ideal.Quotient.mk W (X j))
variable {W A}
theorem psi_mk (f : MvPolynomial (Fin n) ℂ) : psi W A (Ideal.Quotient.mk W f) =
    Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap ℂ (Kf e)) f) := rfl
theorem projHom_X (k : Fin (e + 1)) :
    ComplexSets.projHom W A (X k) = Ideal.Quotient.mk W (ComplexSets.linPoly A k) := by
  rw [ComplexSets.projHom, AlgHom.comp_apply, ComplexSets.pullback, aeval_X]; rfl
theorem psi_comp_projHom :
    (psi W A).comp (ComplexSets.projHom W A).toRingHom =
      (algebraMap (Kf e) (S W A)).comp (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · have h1 : algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Kf e) (C r) = algebraMap ℂ (Kf e) r :=
      (IsScalarTower.algebraMap_apply ℂ _ (Kf e) r).symm
    have h2 : ComplexSets.projHom W A (C r) = Ideal.Quotient.mk W (C r) := (ComplexSets.projHom W A).commutes r
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2, psi_mk,
      map_C]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, projHom_X,
      psi_mk, map_linPoly, mk_row]
    rfl
theorem kappa_alg (p : MvPolynomial (Fin (e + 1)) ℂ) :
    kappa W A (algebraMap _ (Kf e) p) = algebraMap _ (T W A) (ComplexSets.projHom W A p) := by
  unfold kappa; exact IsLocalization.lift_eq _ p
theorem phi_C (c : Kf e) : phi W A (C c) = kappa W A c := eval₂Hom_C _ _ _
theorem phi_map (f : MvPolynomial (Fin n) ℂ) :
    phi W A (MvPolynomial.map (algebraMap ℂ (Kf e)) f) = algebraMap _ (T W A) (Ideal.Quotient.mk W f) := by
  have : (phi W A).comp (MvPolynomial.map (algebraMap ℂ (Kf e))) =
      (algebraMap _ (T W A)).comp (Ideal.Quotient.mk W) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_C, phi_C,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Kf e), kappa_alg, AlgHom.commutes]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, map_X, phi, eval₂Hom_X']
  exact RingHom.congr_fun this f
theorem phi_row (k : Fin (e + 1)) :
    phi W A (linForm fun j => algebraMap ℂ (Kf e) (A k j)) = kappa W A (projVar e k) := by
  rw [← map_linPoly, phi_map, projVar, kappa_alg, projHom_X]
theorem secIdeal_le_ker :
    Vertical.secIdeal (W.map (MvPolynomial.map (algebraMap ℂ (Kf e)))) (projPar A) ≤
      RingHom.ker (phi W A) := by
  have hu : kappa W A (projVar e 0)⁻¹ * kappa W A (projVar e 0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (projVar_ne_zero 0), map_one]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]; intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, phi_map, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm_eq, map_sub, map_mul, map_mul, phi_C, phi_C, phi_row,
      phi_row]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      chartForm_eq, map_mul, phi_C, phi_row, hu, sub_self]
variable (W A)
def g : S W A →+* T W A := Ideal.Quotient.lift _ (phi W A) fun _ hf => RingHom.mem_ker.1 (secIdeal_le_ker hf)
theorem psi_unit (y : M W A) : IsUnit (psi W A y) := by
  obtain ⟨_, p, hp, rfl⟩ := y
  have h := RingHom.congr_fun (psi_comp_projHom (W := W) (A := A)) p
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  exact (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp)).map _
def chi : T W A →+* S W A :=
  IsLocalization.lift (M := M W A) (S := T W A) (P := S W A) (g := psi W A) (psi_unit W A)
variable {W A}
end ProjSecDomain
end
end GroundTheory.Heights₂.Heights


