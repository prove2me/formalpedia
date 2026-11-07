-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:37:40.850345+00:00
-- url     : https://prove2.me/theorems/f6e4d9a9-cb57-467d-a66f-49adbf196c71
-- title:
--   LPSOriginal Filled Cusps
-- statement:
--   Definitions and structural lemmas for LPSOriginal Filled Cusps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
abbrev LPSOriginalFilledCurve (N : ℕ) : Type :=
  MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ ⊕
    CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
def lpsOriginalFilledCuspSource (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    Set (LPSOriginalFilledCurve N) := fun x =>
  match x with
  | Sum.inl y => y∈Set.range (lpsOriginalCuspProjection N ρ)
  | Sum.inr c => c=lpsOriginalCuspOrbit N ρ
def lpsOriginalFilledCuspToFun (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    LPSOriginalFilledCurve N → ℂ := fun x =>
  match x with
  | Sum.inl y => if hy : y∈Set.range (lpsOriginalCuspProjection N ρ) then
      (lpsOriginalCuspNeighborhoodChart N ρ ⟨y,hy⟩).val else 0
  | Sum.inr _ => 0
def lpsOriginalFilledCuspInvFun (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) (q : ℂ) :
    LPSOriginalFilledCurve N :=
  if hq : q=0 then Sum.inr (lpsOriginalCuspOrbit N ρ)
  else if hn : ‖q‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty) then
    Sum.inl ((lpsOriginalCuspNeighborhoodChart N ρ).symm ⟨q,hq,hn⟩).val
  else Sum.inr (lpsOriginalCuspOrbit N ρ)
def lpsOriginalFilledCuspPartialEquiv (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    PartialEquiv (LPSOriginalFilledCurve N) ℂ where
  toFun := lpsOriginalFilledCuspToFun N ρ
  invFun := lpsOriginalFilledCuspInvFun N ρ
  source := lpsOriginalFilledCuspSource N ρ
  target := {q | ‖q‖<Real.exp (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty)}
  map_source' := by
    intro x hx
    cases x with
    | inl y =>
      change y∈Set.range (lpsOriginalCuspProjection N ρ) at hx
      change ‖lpsOriginalFilledCuspToFun N ρ (Sum.inl y)‖<_
      rw [lpsOriginalFilledCuspToFun,dif_pos hx]
      exact (lpsOriginalCuspNeighborhoodChart N ρ ⟨y,hx⟩).property.2
    | inr c =>
      change ‖(0:ℂ)‖<_
      simpa only [norm_zero] using Real.exp_pos
        (-2*Real.pi/(lpsOriginalCuspGroup N ρ).strictWidthInfty)
  map_target' := by
    intro q hq
    change ‖q‖<_ at hq
    by_cases hz : q=0
    · rw [lpsOriginalFilledCuspInvFun,dif_pos hz]
      rfl
    · rw [lpsOriginalFilledCuspInvFun,dif_neg hz,dif_pos hq]
      exact ((lpsOriginalCuspNeighborhoodChart N ρ).symm ⟨q,hz,hq⟩).property
  left_inv' := by
    intro x hx
    cases x with
    | inl y =>
      change y∈Set.range (lpsOriginalCuspProjection N ρ) at hx
      let q := lpsOriginalCuspNeighborhoodChart N ρ ⟨y,hx⟩
      have hz : q.val≠0 := q.property.1
      have hn := q.property.2
      rw [lpsOriginalFilledCuspToFun,dif_pos hx]
      change lpsOriginalFilledCuspInvFun N ρ q.val=Sum.inl y
      rw [lpsOriginalFilledCuspInvFun,dif_neg hz,dif_pos hn]
      exact congrArg (fun z => Sum.inl z.val)
        ((lpsOriginalCuspNeighborhoodChart N ρ).symm_apply_apply ⟨y,hx⟩)
    | inr c =>
      change c=lpsOriginalCuspOrbit N ρ at hx
      subst c
      simp [lpsOriginalFilledCuspToFun,lpsOriginalFilledCuspInvFun]
  right_inv' := by
    intro q hq
    change ‖q‖<_ at hq
    by_cases hz : q=0
    · subst q
      simp [lpsOriginalFilledCuspInvFun,lpsOriginalFilledCuspToFun]
    · let y := (lpsOriginalCuspNeighborhoodChart N ρ).symm ⟨q,hz,hq⟩
      rw [lpsOriginalFilledCuspInvFun,dif_neg hz,dif_pos hq]
      change lpsOriginalFilledCuspToFun N ρ (Sum.inl y.val)=q
      rw [lpsOriginalFilledCuspToFun,dif_pos y.property]
      exact congrArg Subtype.val
        ((lpsOriginalCuspNeighborhoodChart N ρ).apply_symm_apply ⟨q,hz,hq⟩)
def lpsOriginalFilledCuspClosedPatch (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Set (LPSOriginalFilledCurve N) :=
  lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c) ''
    Metric.closedBall (0:ℂ) (Real.exp
      (-2*Real.pi*2/(lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty))
def lpsOriginalFilledCuspParam (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target →
      LPSOriginalFilledCurve N :=
  fun q => lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c) q.val
def lpsOriginalCuspPunctToFull (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    lpsOriginalCuspDisk N ρ → (lpsOriginalFilledCuspPartialEquiv N ρ).target :=
  fun q => ⟨q.val,q.property.2⟩
def lpsOriginalCuspPunctInverse (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    lpsOriginalCuspDisk N ρ → MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
  fun q => ((lpsOriginalCuspNeighborhoodChart N ρ).symm q).val
end
end QEC.Coding.TannerLiftedProduct


