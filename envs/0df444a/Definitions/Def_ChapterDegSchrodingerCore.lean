-- Prove2me | Definitions.Def_ChapterDegSchrodingerCore
-- name    : ChapterDegSchrodingerCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T08:59:04.605581+00:00
-- url     : https://prove2.me/theorems/7a6266ef-cfdb-4b8a-9d67-acb4e3c8d152
-- title:
--   Chapter DegSchrodingerCore
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterDegSchrodingerCore.lean`): generated def bundle for ChapterDegSchrodingerCore. See BookProof/ChapterDegSchrodingerCore.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterDegSchrodingerCore.lean

import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_pgLp

import Theorems.Thm_BookProof_QgHermiteFriedrichs_conj_polyEval

import Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_symmetric

import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_continuous

import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_coreD

import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_neg

import Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_sum

import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_coreD

import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_coreD_raw

import Theorems.Thm_BookProof_QgHermiteFriedrichs_gaussInt_neg

import Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_potLp_symm

import Theorems.Thm_BookProof_ScalaronEsa_opCc_apply

import Theorems.Thm_BookProof_StrichartzWave_opL2_apply

import Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn

import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric

import Theorems.Thm_BookProof_ScalaronEsa_symmetricOn_inclusion


import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStrichartzWave
import Mathlib
import Theorems.Thm_BookProof_QgHermiteFriedrichs_coreEquiv_symm_pgLp
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_nonneg_const


/-!
# Degenerate Schrödinger operators `−Δ_S + W` on `L²(ℝᵈ)`

The Standard-Model Faris–Lavine comparison operator `N = 2h + Σ_m q_m² + c₀` of
`BookProof/ChapterSmFarisLavine.lean` is a Schrödinger operator on `L²(ℝ¹⁶³)` whose kinetic
term differentiates only the `40` momentum-carrying coordinates: it has the shape

`−Δ_S + W`,  `Δ_S = ∑_{j ∈ S} ∂_j²`,

with `S ⊆ {0, …, d−1}` a set of coordinates and `W ≥ 0` a (quartic) polynomial.  This module
sets up that class of operators on the two cores the project works with —

* the **Gauss–polynomial core** `polyGaussCore d`, via the polynomial realization
  `kinPolyS S` of `−Δ_S` (`hamCoreS`);
* the **compactly supported smooth core** `ccDomain (Vd d)` (`ccHamS`) —

records their pointwise formulas and their symmetry, and packages the elementary facts
about polynomial potentials (`polyW`) that the analysis in
`BookProof/ChapterDegKatoEsa.lean` and `BookProof/ChapterHermiteGraphApprox.lean` consumes.

For `S = Finset.univ` everything here specializes to the `−Δ + W` of
`BookProof.QgHermiteFriedrichs` and `BookProof.QgOneParticleCc`.
-/

namespace BookProof.DegSchrodinger

open MeasureTheory SchwartzMap MvPolynomial
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.HermiteProductBasis

noncomputable section

variable {d : ℕ}

/-! ## 1. The kinetic term of a set of coordinates -/

/-- The coefficient vector of `−Δ_S`: `−1` in the directions of `S`, `0` elsewhere. -/
def kinCoeff (S : Finset (Fin d)) (j : Fin d) : ℝ := if j ∈ S then -1 else 0

/-- `−Δ_S = −∑_{j ∈ S} ∂_j²` as an operator on Schwartz space. -/
def kinOpS (S : Finset (Fin d)) : 𝓢(Vd d, ℂ) →L[ℂ] 𝓢(Vd d, ℂ) :=
  constCoeffOp (kinCoeff S) (kinDir d) 0

/-- The partial Laplacian in coordinates. -/
def lapCS (S : Finset (Fin d)) (u : Vd d → ℂ) (x : Vd d) : ℂ :=
  ∑ j ∈ S, dcoord j (dcoord j u) x

/-- On a Schwartz map `kinOpS S` is the pointwise `−Δ_S`. -/
theorem kinOpS_apply_eq (S : Finset (Fin d)) (f : 𝓢(Vd d, ℂ)) (x : Vd d) :
    (kinOpS S f) x = -lapCS S (f : Vd d → ℂ) x := by
  have h : (kinOpS S f)
      = (∑ i : Fin d, ((kinCoeff S i : ℝ) : ℂ) • secondDeriv (kinDir d i) f)
        + ((0 : ℝ) : ℂ) • f := by
    simp [kinOpS, constCoeffOp]
  rw [h]
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul,
    Complex.ofReal_zero, zero_mul, add_zero, secondDeriv_apply_eq, lapCS, dcoord]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S)]
  have h2 : ∀ i ∈ Finset.univ.filter (fun i : Fin d => ¬ i ∈ S),
      ((kinCoeff S i : ℝ) : ℂ) *
        fderiv ℝ (fun y => fderiv ℝ (f : Vd d → ℂ) y (kinDir d i)) x (kinDir d i) = 0 := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [kinCoeff, hi.2]
  rw [Finset.sum_eq_zero h2, add_zero]
  have h3 : (Finset.univ.filter (fun i : Fin d => i ∈ S)) = S := by
    ext i; simp
  rw [h3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [kinCoeff, hi, if_pos, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]
  rfl

/-- The kinetic term on the compactly supported smooth core. -/
def kinCcS (S : Finset (Fin d)) : ccDomain (Vd d) →ₗ[ℂ] L2d d :=
  opL2 (kinOpS S) ∘ₗ Submodule.inclusion (ccDomain_le_schwartzDomain (E := Vd d))

/-- **The degenerate Schrödinger operator `−Δ_S + W` on the compactly supported smooth
core** of `L²(ℝᵈ)`, for an arbitrary smooth real potential `W`. -/
def ccHamS (W : Vd d → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (S : Finset (Fin d)) :
    ccDomain (Vd d) →ₗ[ℂ] L2d d :=
  kinCcS S + opCc W hW

theorem kinCcS_symmetricOn (S : Finset (Fin d)) : SymmetricOn (ccDomain (Vd d)) (kinCcS S) :=
  symmetricOn_inclusion _ _ (constCoeffOp_symmetric _ _ _)

theorem ccHamS_symmetricOn (W : Vd d → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (S : Finset (Fin d)) : SymmetricOn (ccDomain (Vd d)) (ccHamS W hW S) := by
  intro x y
  have h1 := kinCcS_symmetricOn S x y
  have h2 := smoothPotential_symmetric W hW x y
  simp only [ccHamS, LinearMap.add_apply, inner_add_left, inner_add_right]
  linear_combination h1 + h2

theorem kinCcS_apply (S : Finset (Fin d)) (f : ccSchwartz (Vd d)) :
    kinCcS S (ccEquiv (Vd d) f)
      = (kinOpS S (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d)) := by
  have hincl : Submodule.inclusion (ccDomain_le_schwartzDomain (E := Vd d)) (ccEquiv (Vd d) f)
      = schwartzEquiv (Vd d) ((f : 𝓢(Vd d, ℂ))) := Subtype.ext rfl
  simp only [kinCcS, LinearMap.coe_comp, Function.comp_apply, hincl, opL2_apply]

/-- The pointwise formula for the operator on the compactly supported core. -/
theorem ccHamS_coeFn (W : Vd d → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (S : Finset (Fin d)) (f : ccSchwartz (Vd d)) :
    ((ccHamS W hW S (ccEquiv (Vd d) f) : L2d d) : Vd d → ℂ)
      =ᵐ[volume] fun x => -lapCS S ((f : 𝓢(Vd d, ℂ)) : Vd d → ℂ) x
        + ((W x : ℝ) : ℂ) * (f : 𝓢(Vd d, ℂ)) x := by
  have h1 : ccHamS W hW S (ccEquiv (Vd d) f)
      = (kinOpS S (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d))
        + (mulCc W hW f).toLp 2 (volume : Measure (Vd d)) := by
    simp only [ccHamS, LinearMap.add_apply, kinCcS_apply, opCc_apply]
  rw [h1]
  filter_upwards [Lp.coeFn_add ((kinOpS S (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d)))
      ((mulCc W hW f).toLp 2 (volume : Measure (Vd d))),
    (kinOpS S (f : 𝓢(Vd d, ℂ))).coeFn_toLp 2 (volume : Measure (Vd d)),
    (mulCc W hW f).coeFn_toLp 2 (volume : Measure (Vd d))] with z hz h2 h3
  rw [hz, Pi.add_apply, h2, h3, kinOpS_apply_eq, mulCc_apply]

/-! ## 2. The kinetic term on the Gauss–polynomial core -/

/-- The polynomial realization of `−Δ_S` on the Gauss–polynomial core. -/
def kinPolyS (S : Finset (Fin d)) (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  -∑ j ∈ S, coreD j (coreD j p)

theorem kinPolyS_add (S : Finset (Fin d)) (p q : MvPolynomial (Fin d) ℂ) :
    kinPolyS S (p + q) = kinPolyS S p + kinPolyS S q := by
  simp only [kinPolyS, coreD_add, Finset.sum_add_distrib, neg_add]

theorem kinPolyS_smul (S : Finset (Fin d)) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    kinPolyS S (c • p) = c • kinPolyS S p := by
  simp only [kinPolyS, coreD_smul, ← Finset.smul_sum, smul_neg]

/-- The partial Laplacian on the core is `−kinPolyS`. -/
theorem lapCS_pgFun (S : Finset (Fin d)) (p : MvPolynomial (Fin d) ℂ) :
    lapCS S (pgFun p) = fun x => -pgFun (kinPolyS S p) x := by
  funext x
  simp only [lapCS, dcoord_pgFun]
  simp only [pgFun, kinPolyS, map_neg, map_sum, Finset.sum_mul, neg_mul, neg_neg]

/-- `H p = −Δ_S(p e^{−‖x‖²/4}) + W · (p e^{−‖x‖²/4})`, as an element of `L²(ℝᵈ)`. -/
def hamPolyS (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) (S : Finset (Fin d))
    (p : MvPolynomial (Fin d) ℂ) : L2d d :=
  pgLp (kinPolyS S p) + potLp W hWc hWb p

/-- The operator as a linear map out of the polynomials. -/
def hamPolyMapS (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) (S : Finset (Fin d)) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d where
  toFun := hamPolyS W hWc hWb S
  map_add' p q := by
    have h : pgLp (kinPolyS S p + kinPolyS S q)
        = pgLp (kinPolyS S p) + pgLp (kinPolyS S q) := by
      rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply,
        ← HermiteProductCore.pgMap_apply, map_add]
    simp only [hamPolyS, kinPolyS_add, potLp_add, h]
    abel
  map_smul' c p := by
    have h : pgLp (c • kinPolyS S p) = c • pgLp (kinPolyS S p) := by
      rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply, map_smul]
    simp only [hamPolyS, kinPolyS_smul, potLp_smul, RingHom.id_apply, h, smul_add]

/-- **The degenerate Schrödinger operator `−Δ_S + W` on the Gauss–polynomial core.** -/
def hamCoreS (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) (S : Finset (Fin d)) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (hamPolyMapS W hWc hWb S).comp (coreEquiv (d := d)).symm.toLinearMap

theorem hamCoreS_pgLp (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W)
    (S : Finset (Fin d)) (p : MvPolynomial (Fin d) ℂ) :
    hamCoreS W hWc hWb S ⟨pgLp p, pgLp_mem_core p⟩ = hamPolyS W hWc hWb S p := by
  simp only [hamCoreS, LinearMap.comp_apply, LinearEquiv.coe_coe, coreEquiv_symm_pgLp]
  rfl

theorem hamCoreS_coeFn (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W)
    (S : Finset (Fin d)) (p : MvPolynomial (Fin d) ℂ) :
    ((hamCoreS W hWc hWb S ⟨pgLp p, pgLp_mem_core p⟩ : L2d d) : Vd d → ℂ)
      =ᵐ[volume] fun z => pgFun (kinPolyS S p) z + ((W z : ℝ) : ℂ) * pgFun p z := by
  rw [hamCoreS_pgLp]
  filter_upwards [Lp.coeFn_add (pgLp (kinPolyS S p)) (potLp W hWc hWb p),
    pgLp_coeFn (kinPolyS S p), potLp_coeFn W hWc hWb p] with z h1 h2 h3
  simp only [hamPolyS]
  rw [h1, Pi.add_apply, h2, h3]

/-- The kinetic pairing over `S`, with the Laplacian on the right argument. -/
theorem gaussInt_kinPolyS (S : Finset (Fin d)) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly p * kinPolyS S q)
      = ∑ j ∈ S, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly p * kinPolyS S q = -∑ j ∈ S, cpoly p * coreD j (coreD j q) := by
    simp only [kinPolyS, Finset.mul_sum, mul_neg]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD j p (coreD j q)]

/-- The same pairing, with the Laplacian on the left argument. -/
theorem gaussInt_kinPolyS_left (S : Finset (Fin d)) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPolyS S p) * q)
      = ∑ j ∈ S, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hcp : cpoly (kinPolyS S p) = kinPolyS S (cpoly p) := by
    simp only [kinPolyS, cpoly_neg, cpoly_sum, cpoly_coreD]
  have hmul : cpoly (kinPolyS S p) * q = -∑ j ∈ S, coreD j (coreD j (cpoly p)) * q := by
    rw [hcp]
    simp only [kinPolyS, Finset.sum_mul, neg_mul]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD_raw j (coreD j (cpoly p)) q, cpoly_coreD, neg_neg]

/-- **The operator is symmetric on the Gauss–polynomial core.** -/
theorem hamCoreS_symmetricOn (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W)
    (S : Finset (Fin d)) :
    SymmetricOn (polyGaussCore (d := d)) (hamCoreS W hWc hWb S) := by
  intro x y
  obtain ⟨p, hp⟩ := x.2
  obtain ⟨q, hq⟩ := y.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨pgLp q, pgLp_mem_core q⟩ := Subtype.ext hq.symm
  rw [hx, hy, hamCoreS_pgLp, hamCoreS_pgLp]
  change (inner ℂ (hamPolyS W hWc hWb S p) (pgLp q) : ℂ)
    = inner ℂ (pgLp p) (hamPolyS W hWc hWb S q)
  simp only [hamPolyS, inner_add_left, inner_add_right]
  congr 1
  · rw [QgHermiteFriedrichs.inner_pgLp_pgLp, QgHermiteFriedrichs.inner_pgLp_pgLp,
      gaussInt_kinPolyS_left, gaussInt_kinPolyS]
  · exact inner_potLp_symm W hWc hWb p q

/-! ## 3. Polynomial potentials -/

/-- The real-valued function attached to a polynomial with real coefficients. -/
def polyW (q : MvPolynomial (Fin d) ℂ) (x : Vd d) : ℝ :=
  (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q).re

theorem contDiff_polyW (q : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (polyW q) :=
  Complex.reCLM.contDiff.comp (contDiff_polyEval q)

theorem continuous_polyW (q : MvPolynomial (Fin d) ℂ) : Continuous (polyW q) :=
  (contDiff_polyW q).continuous

theorem abs_coord_le_norm (x : Vd d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have h : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (x j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hnorm : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
  have h2 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, hnorm]; exact h
  nlinarith [abs_nonneg (x i), norm_nonneg x]

theorem expBounded_polyW (q : MvPolynomial (Fin d) ℂ) : ExpBounded (polyW q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      refine ⟨‖a‖, 0, le_rfl, fun x => ?_⟩
      have hC : polyW (C a : MvPolynomial (Fin d) ℂ) x = a.re := by simp [polyW]
      rw [hC]
      simpa using Complex.abs_re_le_norm a
  | add p q hp hq =>
      obtain ⟨C1, c1, hc1, h1⟩ := hp
      obtain ⟨C2, c2, hc2, h2⟩ := hq
      have hC1 : 0 ≤ C1 := ExpBounded.nonneg_const h1
      have hC2 : 0 ≤ C2 := ExpBounded.nonneg_const h2
      refine ⟨C1 + C2, max c1 c2, le_trans hc1 (le_max_left _ _), fun x => ?_⟩
      have hadd : polyW (p + q) x = polyW p x + polyW q x := by simp [polyW]
      have e1 : C1 * Real.exp (c1 * ‖x‖) ≤ C1 * Real.exp (max c1 c2 * ‖x‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))) hC1
      have e2 : C2 * Real.exp (c2 * ‖x‖) ≤ C2 * Real.exp (max c1 c2 * ‖x‖) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x))) hC2
      rw [hadd]
      have h1x := h1 x
      have h2x := h2 x
      have htri := abs_add_le (polyW p x) (polyW q x)
      linarith
  | mul_X p i hp =>
      obtain ⟨C1, c1, hc1, h1⟩ := hp
      have hC1 : 0 ≤ C1 := ExpBounded.nonneg_const h1
      refine ⟨C1, c1 + 1, by linarith, fun x => ?_⟩
      have hmul : polyW (p * X i) x = polyW p x * (x i) := by
        simp only [polyW, map_mul, MvPolynomial.eval_X, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      rw [hmul, abs_mul]
      have hxi : |x i| ≤ ‖x‖ := abs_coord_le_norm x i
      have hexp : ‖x‖ ≤ Real.exp ‖x‖ := (Real.add_one_le_exp ‖x‖).trans' (by linarith)
      have hstep : |polyW p x| * |x i| ≤ (C1 * Real.exp (c1 * ‖x‖)) * Real.exp ‖x‖ := by
        refine mul_le_mul (h1 x) (hxi.trans hexp) (abs_nonneg _) ?_
        positivity
      refine hstep.trans (le_of_eq ?_)
      rw [mul_assoc, ← Real.exp_add]
      ring_nf



/-- For a polynomial with real coefficients the complex evaluation is the real one. -/
theorem polyW_ofReal {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) (x : Vd d) :
    ((polyW q x : ℝ) : ℂ) = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
  have hcp : cpoly q = q := hq
  have h : (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
    rw [conj_polyEval, hcp]
  exact Complex.conj_eq_iff_re.mp h

/-- Multiplication by a real-coefficient polynomial is the potential term on the core. -/
theorem pgFun_mul_polyW {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q)
    (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (q * p) x = ((polyW q x : ℝ) : ℂ) * pgFun p x := by
  simp only [pgFun, map_mul, polyW_ofReal hq x]
  ring

end

end BookProof.DegSchrodinger


