-- Prove2me | Definitions.Def_ChapterHermiteGraphApprox
-- name    : ChapterHermiteGraphApprox
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T20:28:20.625249+00:00
-- url     : https://prove2.me/theorems/41a82e88-32a9-46c1-9be5-5082c7df702c
-- title:
--   ChapterHermiteGraphApprox
-- statement:
--   ChapterHermiteGraphApprox

import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterDegEnergyEstimate
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_DegEnergy_dcoord_conj
import Theorems.Thm_BookProof_DegEnergy_integral_dcoord_mul
import Theorems.Thm_BookProof_HermiteLadder_hamPolyL_apply

import Theorems.Thm_BookProof_HermiteLadder_exists_ladderOrd_hamPolyL
import Definitions.Def_ChapterNsKoopman
import Theorems.Thm_BookProof_HermiteProductBasis_annPoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMv
import Theorems.Thm_BookProof_HermiteProductBasis_pderiv_hermiteMv
import Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn
import Theorems.Thm_BookProof_ScalaronEsa_ccEquiv_coe
import Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_dcoord
import Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_finsetSum


/-!
# The Gauss–polynomial core approximates the compactly supported core in the graph norm

`BookProof/ChapterQgOneParticleCcEsa.lean` transports essential self-adjointness *from* the
Gauss–polynomial core *to* the compactly supported smooth core, by cutting a Gauss
polynomial off outside a large ball.  The Kato theorem of `BookProof/ChapterDegKatoEsa.lean`
runs the other way: it is proved on the compactly supported core, and what is needed is the
opposite approximation — every compactly supported smooth `ψ` must be approximated, in the
graph norm of `−Δ_S + W`, by Gauss polynomials.

That is supplied here by the **Hermite expansion**.  Let `ψ_α` be the product Hermite basis
of `BookProof.HermiteProductBasis`, `c_α = ⟪ψ_α, ψ⟫`, and let `Λ = ∑_i a_i† a_i` be the
number operator, for which `Λ ψ_α = |α| ψ_α`.  Then

* integrating by parts twice against the (compactly supported!) `ψ` gives
  `|α|² c_α = ⟪ψ_α, Λ²_cl ψ⟫`, so Bessel's inequality bounds `∑_α (|α|+1)⁴ |c_α|²` by a
  multiple of `‖ψ‖² + ‖Λ_cl ψ‖² + ‖Λ²_cl ψ‖²`, which is finite;
* every operator occurring in `−Δ_S + W` with `W` a polynomial of degree `≤ k` is a finite
  combination of products of at most `max (k, 2)` ladder operators, and a product of `n`
  ladder operators maps `ψ_α` to a multiple, of size at most `(|α| + n)^{n/2}`, of a single
  basis vector; hence `‖(−Δ_S + W) v‖ ≤ C ∑_α (|α| + n)^n |c_α|²` on the core.

Together these make the Hermite truncations of `ψ` a Cauchy sequence in the graph norm; the
limit is `ψ` in `L²` and `(−Δ_S + W)ψ` in the graph coordinate, because the core is dense
and the operator is symmetric.
-/

namespace BookProof.HermiteGraphApprox

open MeasureTheory SchwartzMap MvPolynomial Filter Topology
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.DegEnergy BookProof.HermiteLadder
open BookProof.ConvolutionCalc
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The operator on compactly supported smooth functions -/

/-- `−Δ_S + W` acting on functions. -/
def Lfun (S : Finset (Fin d)) (W : Vd d → ℝ) (g : Vd d → ℂ) : Vd d → ℂ :=
  fun x => -lapCS S g x + ((W x : ℝ) : ℂ) * g x

theorem contDiff_lapCS (S : Finset (Fin d)) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lapCS S g) :=
  ContDiff.sum fun j _ => contDiff_dcoord (contDiff_dcoord hg j) j

theorem hasCompactSupport_lapCS (S : Finset (Fin d)) {g : Vd d → ℂ}
    (hgc : HasCompactSupport g) : HasCompactSupport (lapCS S g) :=
  hasCompactSupport_finsetSum S fun j _ =>
    hasCompactSupport_dcoord (hasCompactSupport_dcoord hgc j) j

theorem contDiff_Lfun (S : Finset (Fin d)) {W : Vd d → ℝ}
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Lfun S W g) :=
  (contDiff_lapCS S hg).neg.add ((Complex.ofRealCLM.contDiff.comp hW).mul hg)

theorem hasCompactSupport_Lfun (S : Finset (Fin d)) (W : Vd d → ℝ) {g : Vd d → ℂ}
    (hgc : HasCompactSupport g) : HasCompactSupport (Lfun S W g) :=
  (hasCompactSupport_lapCS S hgc).neg.add hgc.mul_left

/-! ## 2. Integration by parts between the two cores -/

theorem pgFun_add_apply (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (p + q) x = pgFun p x + pgFun q x := by
  simp [pgFun, add_mul]

theorem pgFun_smul_apply (c : ℂ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (c • p) x = c * pgFun p x := by
  simp [pgFun, smul_eq_C_mul, mul_assoc]

/-- One direction of `S`: `∫ conj(∂ⱼ²f) g = ∫ conj f ∂ⱼ²g` for `g` compactly supported. -/
theorem integral_conj_dd_mul {f g : Vd d → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) (j : Fin d) :
    ∫ x, (starRingEnd ℂ) (dcoord j (dcoord j f) x) * g x
      = ∫ x, (starRingEnd ℂ) (f x) * dcoord j (dcoord j g) x := by
  have hdf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j f) := contDiff_dcoord hf j
  have hcf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (f y)) :=
    Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.contDiff.comp hf
  have hcdf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (dcoord j f y)) :=
    Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.contDiff.comp hdf
  have h1 : ∫ x, (starRingEnd ℂ) (dcoord j (dcoord j f) x) * g x
      = ∫ x, g x * dcoord j (fun y => (starRingEnd ℂ) (dcoord j f y)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [dcoord_conj hdf j x, mul_comm]
  have h2 : ∫ x, dcoord j g x * (starRingEnd ℂ) (dcoord j f x)
      = ∫ x, dcoord j g x * dcoord j (fun y => (starRingEnd ℂ) (f y)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [dcoord_conj hf j x]
  rw [h1, integral_dcoord_mul hg hgc hcdf j, h2,
    integral_dcoord_mul (contDiff_dcoord hg j) (hasCompactSupport_dcoord hgc j) hcf j, neg_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- **Integration by parts between the Gauss–polynomial and the compactly supported cores.** -/
theorem integral_conj_pgFun_hamPolyL (S : Finset (Fin d)) {q : MvPolynomial (Fin d) ℂ}
    (hq : RealCoeff q) (p : MvPolynomial (Fin d) ℂ) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ x, (starRingEnd ℂ) (pgFun (hamPolyL S q p) x) * g x
      = ∫ x, (starRingEnd ℂ) (pgFun p x) * Lfun S (polyW q) g x := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pgFun p) := contDiff_pgFun p
  have hpt : ∀ x, pgFun (hamPolyL S q p) x = -lapCS S (pgFun p) x
      + ((polyW q x : ℝ) : ℂ) * pgFun p x := by
    intro x
    rw [hamPolyL_apply, pgFun_add_apply, pgFun_mul_polyW hq, lapCS_pgFun, neg_neg]
  have hI : ∀ j, Integrable (fun x => (starRingEnd ℂ) (dcoord j (dcoord j (pgFun p)) x) * g x)
      (volume : Measure (Vd d)) := fun j =>
    ((Complex.continuous_conj.comp (contDiff_dcoord (contDiff_dcoord hf j) j).continuous).mul
      hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hI' : ∀ j, Integrable (fun x => (starRingEnd ℂ) (pgFun p x) * dcoord j (dcoord j g) x)
      (volume : Measure (Vd d)) := fun j =>
    ((Complex.continuous_conj.comp hf.continuous).mul
      (contDiff_dcoord (contDiff_dcoord hg j) j).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_dcoord (hasCompactSupport_dcoord hgc j) j).mul_left
  have hW : Integrable (fun x => (starRingEnd ℂ) (pgFun p x) * (((polyW q x : ℝ) : ℂ) * g x))
      (volume : Measure (Vd d)) :=
    ((Complex.continuous_conj.comp hf.continuous).mul
      ((Complex.continuous_ofReal.comp (continuous_polyW q)).mul
        hg.continuous)).integrable_of_hasCompactSupport hgc.mul_left.mul_left
  have hlap : ∫ x, (starRingEnd ℂ) (lapCS S (pgFun p) x) * g x
      = ∫ x, (starRingEnd ℂ) (pgFun p x) * lapCS S g x := by
    simp only [lapCS, map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [integral_finset_sum S fun j _ => hI j, integral_finset_sum S fun j _ => hI' j]
    exact Finset.sum_congr rfl fun j _ => integral_conj_dd_mul hf hg hgc j
  have hLI : Integrable (fun x => (starRingEnd ℂ) (lapCS S (pgFun p) x) * g x)
      (volume : Measure (Vd d)) := by
    simp only [lapCS, map_sum, Finset.sum_mul]
    exact integrable_finset_sum S fun j _ => hI j
  have hRI : Integrable (fun x => (starRingEnd ℂ) (pgFun p x) * lapCS S g x)
      (volume : Measure (Vd d)) := by
    simp only [lapCS, Finset.mul_sum]
    exact integrable_finset_sum S fun j _ => hI' j
  have e1 : ∀ x, (starRingEnd ℂ) (pgFun (hamPolyL S q p) x) * g x
      = (starRingEnd ℂ) (pgFun p x) * (((polyW q x : ℝ) : ℂ) * g x)
        - (starRingEnd ℂ) (lapCS S (pgFun p) x) * g x := by
    intro x
    rw [hpt x]
    simp only [map_add, map_neg, map_mul, Complex.conj_ofReal]
    ring
  have e2 : ∀ x, (starRingEnd ℂ) (pgFun p x) * Lfun S (polyW q) g x
      = (starRingEnd ℂ) (pgFun p x) * (((polyW q x : ℝ) : ℂ) * g x)
        - (starRingEnd ℂ) (pgFun p x) * lapCS S g x := by
    intro x
    simp only [Lfun]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e1),
    integral_congr_ae (Filter.Eventually.of_forall e2), integral_sub hW hLI,
    integral_sub hW hRI, hlap]

/-! ## 3. The pairing in `L²` -/

theorem inner_pgLp_ae {h : MvPolynomial (Fin d) ℂ} {v : L2d d} {g : Vd d → ℂ}
    (hv : (v : Vd d → ℂ) =ᵐ[volume] g) :
    (inner ℂ (pgLp h) v : ℂ) = ∫ x, (starRingEnd ℂ) (pgFun h x) * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn h, hv] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

theorem inner_pgLp_hamPolyL (S : Finset (Fin d)) {q : MvPolynomial (Fin d) ℂ}
    (hq : RealCoeff q) (p : MvPolynomial (Fin d) ℂ) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) {v w : L2d d}
    (hv : (v : Vd d → ℂ) =ᵐ[volume] g) (hw : (w : Vd d → ℂ) =ᵐ[volume] Lfun S (polyW q) g) :
    (inner ℂ (pgLp (hamPolyL S q p)) v : ℂ) = inner ℂ (pgLp p) w := by
  rw [inner_pgLp_ae hv, inner_pgLp_ae hw, integral_conj_pgFun_hamPolyL S hq p hg hgc]

/-! ## 4. The number operator -/

theorem realCoeff_C_real' (c : ℝ) : RealCoeff (C ((c : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) := by
  change starP _ = _
  simp [starP]

/-- The potential of `Λ + 1 = −Δ + ‖x‖²/4 − d/2 + 1`, `Λ = ∑ᵢ aᵢ†aᵢ` the number operator. -/
def numPoly (d : ℕ) : MvPolynomial (Fin d) ℂ :=
  (∑ i, C (((1 / 4 : ℝ)) : ℂ) * (X i * X i)) + C (((1 - (d : ℝ) / 2 : ℝ)) : ℂ)

theorem realCoeff_numPoly : RealCoeff (numPoly d) :=
  (RealCoeff.sum fun i _ => (realCoeff_C_real' _).mul ((realCoeff_X i).mul (realCoeff_X i))).add
    (realCoeff_C_real' _)

theorem coreD_coreD_eq (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    -coreD i (coreD i p) + C (((1 / 4 : ℝ)) : ℂ) * (X i * X i) * p - C (1 / 2 : ℂ) * p
      = crePoly i (annPoly i p) := by
  have hX : pderiv i (X i * p) = p + X i * pderiv i p := by
    rw [Derivation.leibniz, pderiv_X_self]
    simp only [smul_eq_mul]
    ring
  have hC : pderiv i (C (1 / 2 : ℂ) * (X i * p)) = C (1 / 2 : ℂ) * (p + X i * pderiv i p) := by
    rw [pderiv_C_mul, hX]
  have h1 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) + C (1 / 2 : ℂ) = 1 := C_half_add_C_half
  have h2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * C (1 / 2 : ℂ) = C (((1 / 4 : ℝ)) : ℂ) := by
    rw [← C_mul]
    congr 1
    push_cast
    norm_num
  simp only [coreD, map_sub, hC, crePoly_apply, annPoly_apply]
  linear_combination (X i * pderiv i p) * h1 - (X i * X i * p) * h2

/-- `Λ + 1` on the polynomials: `kinPolyS univ p + numPoly · p = ∑ᵢ aᵢ†aᵢ p + p`. -/
theorem hamPolyL_numPoly (p : MvPolynomial (Fin d) ℂ) :
    hamPolyL Finset.univ (numPoly d) p = (∑ i, crePoly i (annPoly i p)) + p := by
  have hsum : (∑ _i : Fin d, (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * p)
      + C (((1 - (d : ℝ) / 2 : ℝ)) : ℂ) * p = p := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      ← add_mul]
    have hc : ((d : MvPolynomial (Fin d) ℂ)) * C (1 / 2 : ℂ) + C (((1 - (d : ℝ) / 2 : ℝ)) : ℂ)
        = 1 := by
      rw [show ((d : MvPolynomial (Fin d) ℂ)) = C (d : ℂ) from (map_natCast C d).symm, ← C_mul,
        ← C_add]
      rw [show ((d : ℂ) * (1 / 2) + (((1 - (d : ℝ) / 2 : ℝ)) : ℂ)) = 1 by push_cast; ring]
      rfl
    rw [hc, one_mul]
  rw [hamPolyL_apply, kinPolyS, numPoly, add_mul, Finset.sum_mul]
  rw [← Finset.sum_congr rfl fun i _ => coreD_coreD_eq i p]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  linear_combination hsum

/-- `aᵢ†aᵢ He_α = αᵢ He_α`. -/
theorem crePoly_annPoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (annPoly i (hermiteMv a)) = ((a i : ℕ) : ℂ) • hermiteMv a := by
  rw [annPoly_apply, pderiv_hermiteMv, map_smul, crePoly_hermiteMv]
  by_cases hai : a i = 0
  · simp [hai]
  · congr 2
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]

/-- **`(Λ + 1) He_α = (|α| + 1) He_α`.** -/
theorem hamPolyL_numPoly_hermiteMv (a : Fin d →₀ ℕ) :
    hamPolyL Finset.univ (numPoly d) (hermiteMv a) = ((a.degree : ℂ) + 1) • hermiteMv a := by
  rw [hamPolyL_numPoly, Finset.sum_congr rfl fun i _ => crePoly_annPoly_hermiteMv i a,
    ← Finset.sum_smul, add_smul, one_smul, Finsupp.degree_eq_sum]
  push_cast
  rfl

/-! ## 5. The Hermite coefficients of a compactly supported smooth function decay fast -/

theorem coef_Lfun_numPoly (a : Fin d →₀ ℕ) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) {v w : L2d d}
    (hv : (v : Vd d → ℂ) =ᵐ[volume] g)
    (hw : (w : Vd d → ℂ) =ᵐ[volume] Lfun Finset.univ (polyW (numPoly d)) g) :
    coef a w = ((a.degree : ℂ) + 1) * coef a v := by
  rw [coef_eq_inner_pgLp, coef_eq_inner_pgLp,
    ← inner_pgLp_hamPolyL Finset.univ realCoeff_numPoly (hermiteMv a) hg hgc hv hw,
    hamPolyL_numPoly_hermiteMv, pgLp_smul', inner_smul_left]
  have h : (starRingEnd ℂ) ((a.degree : ℂ) + 1) = (a.degree : ℂ) + 1 := by simp
  rw [h]
  ring

/-- `Λ + 1` acting on functions. -/
def numFun (d : ℕ) : (Vd d → ℂ) → (Vd d → ℂ) := Lfun Finset.univ (polyW (numPoly d))

theorem numFun_iterate_spec (k : ℕ) {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((numFun d)^[k] g) ∧
      HasCompactSupport ((numFun d)^[k] g) := by
  induction k with
  | zero => exact ⟨hg, hgc⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨contDiff_Lfun _ (contDiff_polyW _) ih.1, hasCompactSupport_Lfun _ _ ih.2⟩

theorem memLp_of_cc {g : Vd d → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp g 2 (volume : Measure (Vd d)) := hg.memLp_of_hasCompactSupport hgc

theorem coef_numFun_iterate (a : Fin d →₀ ℕ) (k : ℕ) {g : Vd d → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) {v w : L2d d}
    (hv : (v : Vd d → ℂ) =ᵐ[volume] g) (hw : (w : Vd d → ℂ) =ᵐ[volume] (numFun d)^[k] g) :
    coef a w = ((a.degree : ℂ) + 1) ^ k * coef a v := by
  induction k generalizing w with
  | zero =>
      have h : w = v := Lp.ext (hw.trans hv.symm)
      simp [h]
  | succ k ih =>
      obtain ⟨h1, h2⟩ := numFun_iterate_spec k hg hgc
      have hw' := (memLp_of_cc h1.continuous h2).coeFn_toLp
      rw [Function.iterate_succ_apply'] at hw
      rw [coef_Lfun_numPoly a h1 h2 hw' hw, ih hw', pow_succ]
      ring

theorem enorm_natCast_complex (m : ℕ) : ‖(m : ℂ)‖ₑ = (m : ℝ≥0∞) := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_natCast, ENNReal.ofReal_natCast]

/-- **Every Hermite–Sobolev norm of a compactly supported smooth function is finite.** -/
theorem hn_ne_top_of_cc {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) {v : L2d d} (hv : (v : Vd d → ℂ) =ᵐ[volume] g) (n : ℕ) :
    hn n v ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := numFun_iterate_spec n hg hgc
  have hw := (memLp_of_cc h1.continuous h2).coeFn_toLp
  have heq : hn (2 * n) v = hn 0 ((memLp_of_cc h1.continuous h2).toLp _) := by
    unfold hn
    refine tsum_congr fun a => ?_
    rw [coef_numFun_iterate a n hg hgc hv hw, wt_zero, one_mul, enorm_mul, enorm_pow, mul_pow,
      wt, show ((a.degree : ℂ) + 1) = ((a.degree + 1 : ℕ) : ℂ) by push_cast; ring,
      enorm_natCast_complex, ← pow_mul, mul_comm n 2]
  refine ne_top_of_le_ne_top ?_ (hn_mono (show n ≤ 2 * n by omega) v)
  rw [heq, hn_zero_eq]
  exact ENNReal.ofReal_ne_top

/-! ## 6. The operator on the Gauss–polynomial core -/

theorem potLp_polyW_eq {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q)
    (p : MvPolynomial (Fin d) ℂ) :
    potLp (polyW q) (continuous_polyW q) (expBounded_polyW q) p = pgLp (q * p) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [potLp_coeFn (polyW q) (continuous_polyW q) (expBounded_polyW q) p,
    pgLp_coeFn (q * p)] with x h1 h2
  rw [h1, h2, pgFun_mul_polyW hq]

theorem hamCoreS_eq_pgLp {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) (S : Finset (Fin d))
    (p : MvPolynomial (Fin d) ℂ) :
    hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (hamPolyL S q p) := by
  rw [hamCoreS_pgLp, hamPolyS, potLp_polyW_eq hq, hamPolyL_apply, pgLp_add']

/-- **The norm bound on the core**: `‖(−Δ_S + W) v‖² ≤ C ‖v‖²_n`. -/
theorem exists_hamCoreS_bound {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q)
    (S : Finset (Fin d)) {n : ℕ} (hT : LadderOrd (hamPolyL S q) n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ y : polyGaussCore (d := d),
      ENNReal.ofReal (‖hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S y‖ ^ 2)
        ≤ C * hn n (y : L2d d) := by
  obtain ⟨C, hC, h⟩ := hT.norm_sq_le
  refine ⟨C, hC, fun y => ?_⟩
  obtain ⟨p, hp⟩ := y.2
  have hy : y = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  rw [hy, hamCoreS_eq_pgLp hq]
  exact h p

/-- **Mixed symmetry**: `⟪(−Δ_S + W) v, ψ⟫ = ⟪v, (−Δ_S + W) ψ⟫` for `v` in the
Gauss–polynomial core and `ψ` in the compactly supported core. -/
theorem inner_hamCoreS_ccHamS {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q)
    (S : Finset (Fin d)) (y : polyGaussCore (d := d)) (ψ : ccDomain (Vd d)) :
    (inner ℂ (hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S y)
        (ψ : L2d d) : ℂ)
      = inner ℂ (y : L2d d) (ccHamS (polyW q) (contDiff_polyW q) S ψ) := by
  obtain ⟨p, hp⟩ := y.2
  have hy : y = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  obtain ⟨f, rfl⟩ := (ccEquiv (Vd d)).surjective ψ
  rw [hy, hamCoreS_eq_pgLp hq]
  exact inner_pgLp_hamPolyL S hq p ((f : 𝓢(Vd d, ℂ)).smooth ⊤) f.2
    ((f : 𝓢(Vd d, ℂ)).coeFn_toLp 2 (volume : Measure (Vd d)))
    (ccHamS_coeFn (polyW q) (contDiff_polyW q) S f)

/-! ## 7. Hermite truncations -/

/-- The Hermite truncation `∑_{α ∈ F} c_α(v) ψ_α`. -/
def htrunc (v : L2d d) (F : Finset (Fin d →₀ ℕ)) : L2d d := ∑ a ∈ F, coef a v • hermiteMvLp a

theorem htrunc_mem_core (v : L2d d) (F : Finset (Fin d →₀ ℕ)) :
    htrunc v F ∈ polyGaussCore (d := d) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hermiteMvLp_mem_core a)

theorem coef_htrunc (v : L2d d) (F : Finset (Fin d →₀ ℕ)) (b : Fin d →₀ ℕ) :
    coef b (htrunc v F) = if b ∈ F then coef b v else 0 := by
  classical
  rw [htrunc, coef, inner_sum]
  simp only [inner_smul_right, inner_hermiteMvLp, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- `hermiteMvBasis` and `hermiteMvLp` agree pointwise.

`Def_ChapterHermiteProductBasis` proves this as the `@[simp]` lemma
`hermiteMvBasis_apply`, but the PLATFORM's served copy of that bundle does not
carry it (the served text stops after the `def`), so `simp` sees
`hermiteMvBasis a` and `hermiteMvLp a` as different terms and `tendsto_htrunc`
was left with an unprovable-looking equality (measured 2026-11-08: the bundle
gated FAIL `406:88: unsolved goals` only because of this one missing simp
lemma).  Re-derive it from the definition, which both copies declare. -/
private theorem hermiteMvBasis_eq_hermiteMvLp (a : Fin d →₀ ℕ) :
    hermiteMvBasis (d := d) a = hermiteMvLp (d := d) a := by
  rw [hermiteMvBasis, HilbertBasis.coe_mk]

theorem tendsto_htrunc (v : L2d d) : Tendsto (htrunc v) atTop (𝓝 v) := by
  have h := hermiteMvBasis.hasSum_repr v
  have heq : htrunc v = fun F => ∑ a ∈ F, hermiteMvBasis.repr v a • hermiteMvBasis a := by
    funext F
    simp [htrunc, coef_eq_repr, hermiteMvBasis_eq_hermiteMvLp]
  rw [heq]
  exact h

theorem hn_htrunc_sub_le (v : L2d d) (n : ℕ) {F₀ F F' : Finset (Fin d →₀ ℕ)} (hF : F₀ ≤ F)
    (hF' : F₀ ≤ F') :
    hn n (htrunc v F - htrunc v F')
      ≤ ∑' b : {b // b ∉ F₀}, wt n (b : Fin d →₀ ℕ) * ‖coef (b : Fin d →₀ ℕ) v‖ₑ ^ 2 := by
  classical
  refine le_of_le_of_eq ?_
    (tsum_subtype ({b | b ∉ F₀} : Set (Fin d →₀ ℕ)) (fun b => wt n b * ‖coef b v‖ₑ ^ 2)).symm
  refine ENNReal.tsum_le_tsum fun b => ?_
  rw [coef_sub, coef_htrunc, coef_htrunc]
  by_cases hb : b ∈ F₀
  · have h1 : b ∈ F := hF hb
    have h2 : b ∈ F' := hF' hb
    simp [h1, h2]
  · rw [Set.indicator_of_mem (show b ∈ ({b | b ∉ F₀} : Set (Fin d →₀ ℕ)) from hb)]
    gcongr
    by_cases h1 : b ∈ F <;> by_cases h2 : b ∈ F' <;> simp [h1, h2]

theorem eq_zero_of_orth_dense {D : Submodule ℂ (L2d d)} (hD : Dense (D : Set (L2d d)))
    {y : L2d d} (h : ∀ x ∈ D, (inner ℂ x y : ℂ) = 0) : y = 0 := by
  have hc : IsClosed {x : L2d d | (inner ℂ x y : ℂ) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hall : Set.univ ⊆ {x : L2d d | (inner ℂ x y : ℂ) = 0} := by
    rw [← hD.closure_eq]
    exact hc.closure_subset_iff.2 fun x hx => h x hx
  exact inner_self_eq_zero.1 (hall (Set.mem_univ y))

/-! ## 8. The graph approximation -/

/-- The Hermite truncation, as an element of the Gauss–polynomial core. -/
def truncCore (v : L2d d) (F : Finset (Fin d →₀ ℕ)) : polyGaussCore (d := d) :=
  ⟨htrunc v F, htrunc_mem_core v F⟩

theorem truncCore_coe (v : L2d d) (F : Finset (Fin d →₀ ℕ)) :
    ((truncCore v F : polyGaussCore (d := d)) : L2d d) = htrunc v F := rfl

theorem ccDomain_ae (ψ : ccDomain (Vd d)) :
    ((ψ : L2d d) : Vd d → ℂ) =ᵐ[volume]
      (((ccEquiv (Vd d)).symm ψ : ccSchwartz (Vd d)) : 𝓢(Vd d, ℂ)) := by
  have h := (((ccEquiv (Vd d)).symm ψ : ccSchwartz (Vd d)) : 𝓢(Vd d, ℂ)).coeFn_toLp 2
    (volume : Measure (Vd d))
  rwa [← ccEquiv_coe, LinearEquiv.apply_symm_apply] at h

/-- The images of the Hermite truncations of a compactly supported smooth function form a
Cauchy net. -/
theorem cauchySeq_hamCoreS_truncCore {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q)
    (S : Finset (Fin d)) (ψ : ccDomain (Vd d)) :
    CauchySeq (fun F => hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S
      (truncCore (ψ : L2d d) F)) := by
  obtain ⟨n, hT⟩ := exists_ladderOrd_hamPolyL S q
  obtain ⟨C, hC, hbound⟩ := exists_hamCoreS_bound hq S hT
  have hfin : ∑' b, wt n b * ‖coef b (ψ : L2d d)‖ₑ ^ 2 ≠ ⊤ :=
    hn_ne_top_of_cc ((((ccEquiv (Vd d)).symm ψ : ccSchwartz (Vd d)) : 𝓢(Vd d, ℂ)).smooth ⊤)
      ((ccEquiv (Vd d)).symm ψ).2 (ccDomain_ae ψ) n
  rw [Metric.cauchySeq_iff]
  intro δ hδ
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero hfin
  have h2 : Tendsto (fun F : Finset (Fin d →₀ ℕ) =>
      C * ∑' b : {b // b ∉ F}, wt n (b : Fin d →₀ ℕ) * ‖coef (b : Fin d →₀ ℕ) (ψ : L2d d)‖ₑ ^ 2)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul htail (Or.inr hC)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ ^ 2) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.1 (h2.eventually (gt_mem_nhds hpos))
  refine ⟨F₀, fun F hF F' hF' => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  have h3 := hbound (truncCore (ψ : L2d d) F - truncCore (ψ : L2d d) F')
  have h4 : hn n ((truncCore (ψ : L2d d) F - truncCore (ψ : L2d d) F' :
        polyGaussCore (d := d)) : L2d d)
      ≤ ∑' b : {b // b ∉ F₀}, wt n (b : Fin d →₀ ℕ)
          * ‖coef (b : Fin d →₀ ℕ) (ψ : L2d d)‖ₑ ^ 2 :=
    hn_htrunc_sub_le (ψ : L2d d) n hF hF'
  have h5 := lt_of_le_of_lt (h3.trans (mul_le_mul_right h4 C)) (hF₀ F₀ le_rfl)
  have h6 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 h5
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 h6

set_option maxHeartbeats 1000000 in
-- the final assembly unfolds the core operator in several coercion-heavy limits
/-- **Graph approximation of the compactly supported core by the Gauss–polynomial core.**
For a polynomial potential every compactly supported smooth function is approximated,
together with its image under `−Δ_S + W`, by Gauss polynomials. -/
theorem exists_core_graph_approx (q : MvPolynomial (Fin d) ℂ) (hq : RealCoeff q)
    (S : Finset (Fin d)) (ψ : ccDomain (Vd d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : polyGaussCore (d := d),
      ‖(v : L2d d) - (ψ : L2d d)‖ < ε ∧
        ‖hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S v
          - ccHamS (polyW q) (contDiff_polyW q) S ψ‖ < ε := by
  obtain ⟨g₀, hg₀⟩ := cauchySeq_tendsto_of_complete (cauchySeq_hamCoreS_truncCore hq S ψ)
  have hid : g₀ = ccHamS (polyW q) (contDiff_polyW q) S ψ := by
    refine sub_eq_zero.1 (eq_zero_of_orth_dense polyGaussCore_dense fun y hy => ?_)
    have hlim1 : Tendsto (fun F => (inner ℂ y (hamCoreS (polyW q) (continuous_polyW q)
        (expBounded_polyW q) S (truncCore (ψ : L2d d) F)) : ℂ)) atTop (𝓝 (inner ℂ y g₀)) :=
      tendsto_const_nhds.inner hg₀
    have hlim2 : Tendsto (fun F => (inner ℂ y (hamCoreS (polyW q) (continuous_polyW q)
        (expBounded_polyW q) S (truncCore (ψ : L2d d) F)) : ℂ)) atTop
        (𝓝 (inner ℂ (hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S ⟨y, hy⟩)
          (ψ : L2d d))) := by
      have heq : (fun F => (inner ℂ y (hamCoreS (polyW q) (continuous_polyW q)
          (expBounded_polyW q) S (truncCore (ψ : L2d d) F)) : ℂ))
          = fun F => (inner ℂ (hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S
              ⟨y, hy⟩) (htrunc (ψ : L2d d) F) : ℂ) := by
        funext F
        exact (hamCoreS_symmetricOn _ _ _ S ⟨y, hy⟩ (truncCore (ψ : L2d d) F)).symm
      rw [heq]
      exact tendsto_const_nhds.inner (tendsto_htrunc _)
    have hval := tendsto_nhds_unique hlim1 hlim2
    have hmix := inner_hamCoreS_ccHamS hq S ⟨y, hy⟩ ψ
    rw [inner_sub_right, hval]
    exact sub_eq_zero.2 hmix
  have hev1 := Metric.tendsto_nhds.1 (tendsto_htrunc (ψ : L2d d)) ε hε
  have hev2 := Metric.tendsto_nhds.1 hg₀ ε hε
  rw [hid] at hev2
  obtain ⟨F, h1, h2⟩ := (hev1.and hev2).exists
  refine ⟨truncCore (ψ : L2d d) F, ?_, ?_⟩
  · rw [truncCore_coe, ← dist_eq_norm]
    exact h1
  · rw [← dist_eq_norm]
    exact h2

/-- **`−Δ_S + W` is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝᵈ)`** for
every polynomial potential `W ≥ 1`.  This is the Kato-type input that the Faris–Lavine
criterion cannot supply. -/
theorem hamCoreS_esa (q : MvPolynomial (Fin d) ℂ) (hq : RealCoeff q)
    (hq1 : ∀ x, 1 ≤ polyW q x) (S : Finset (Fin d)) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (hamCoreS (polyW q) (continuous_polyW q) (expBounded_polyW q) S) :=
  essentiallySelfAdjointOn_of_graphApprox _ _
    (fun ψ _ hε => exists_core_graph_approx q hq S ψ hε)
    (ccHamS_esa (polyW q) (contDiff_polyW q) hq1 S)

end

end BookProof.HermiteGraphApprox


