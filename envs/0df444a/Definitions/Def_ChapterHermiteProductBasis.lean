-- Prove2me | Definitions.Def_ChapterHermiteProductBasis
-- name    : ChapterHermiteProductBasis
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:20:30.179147+00:00
-- url     : https://prove2.me/theorems/1bbebf44-7807-4279-895a-1d5b3cdfc887
-- title:
--   `BookProof.ChapterHermiteProductCore` builds the Gauss–polynomial core `polyGaussCore` of `L²(ℝᵈ)` — the polynomials tim ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteProductBasis`, source chapter `BookProof/ChapterHermiteProductBasis.lean`).
--
--   `BookProof.ChapterHermiteProductCore` builds the Gauss–polynomial core `polyGaussCore` of `L²(ℝᵈ)` — the polynomials times `e^{-‖x‖²/4}` — proves it dense, and shows it is the span of the *product Hermite functions* `ψ_α(x) = ∏ᵢ He_{αᵢ}(xᵢ) · e^{-‖x‖²/4}` (`polyGaussCore_eq_hermiteSpan`). What it does *not* do is make that family an orthonormal basis, or relate it to the ladder (creation / annihilation) operators. Both are supplied here; they are what the differential realization of the Navier–Stokes quadratic symbol (`BookProof.ChapterNavierStokesDifferentialL2`) needs.
--
--   * `eval_hermiteFactor`, `pgFun_hermiteMv` — the product Hermite function is the product of the one-dimensional Hermite functions of `BookProof.ChapterHermiteFunctions`, coordinate by coordinate; * `inner_pgLp_hermiteMv` — the `L²` inner product of two of them is the product of the one-dimensional Hermite inner products (Fubini); * `hermiteMvNorm`, `hermiteMvLp`, `orthonormal_hermiteMvLp`, `span_hermiteMvLp`, `hermiteMvBasis` — the **orthonormal (Hilbert) basis** `ψ_α / ‖ψ_α‖` of `L²(ℝᵈ)` indexed by the multi-indices `α : Fin d →₀ ℕ`, whose span is exactly the Gauss–polynomial core; * `pderiv_hermiteMv` — `∂ᵢ He_α = αᵢ He_{α−eᵢ}` for the product Hermite *polynomials*; * `annPoly`, `crePoly` and `annPoly_hermiteMvLp`, `crePoly_hermiteMvLp` — the polynomial incarnations of the ladder operators `aᵢ = xᵢ/2 + ∂ᵢ`, `aᵢ† = xᵢ/2 − ∂ᵢ` acting on the Gauss-weighted functions, and their action `aᵢψ_α = √αᵢ ψ_{α−eᵢ}`, `aᵢ†ψ_α = √(αᵢ+1) ψ_{α+eᵢ}` on the orthonormal basis.
--
--   The Gaussian factor is what turns the *polynomial* operators `p ↦ ∂ᵢp` and `p ↦ xᵢp − ∂ᵢp` into the *function* operators `f ↦ (xᵢ/2)f + f'` and `f ↦ (xᵢ/2)f − f'`: `∂ᵢ(p·e^{-‖x‖²/4}) = (∂ᵢp − (xᵢ/2)p)·e^{-‖x‖²/4}`. The analytic side of that identity is proved in `BookProof.ChapterNavierStokesDifferentialL2`; here everything is algebraic.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

import Definitions.Def_ChapterHermiteProductCore

import Mathlib

/-!
# The product Hermite basis of `L²(ℝᵈ)` and its ladder relations

`BookProof.ChapterHermiteProductCore` builds the Gauss–polynomial core
`polyGaussCore` of `L²(ℝᵈ)` — the polynomials times `e^{-‖x‖²/4}` — proves it dense, and
shows it is the span of the *product Hermite functions*
`ψ_α(x) = ∏ᵢ He_{αᵢ}(xᵢ) · e^{-‖x‖²/4}` (`polyGaussCore_eq_hermiteSpan`).  What it does
*not* do is make that family an orthonormal basis, or relate it to the ladder (creation /
annihilation) operators.  Both are supplied here; they are what the differential
realization of the Navier–Stokes quadratic symbol
(`BookProof.ChapterNavierStokesDifferentialL2`) needs.

## Contents

* `eval_hermiteFactor`, `pgFun_hermiteMv` — the product Hermite function is the product of
  the one-dimensional Hermite functions of `BookProof.ChapterHermiteFunctions`, coordinate
  by coordinate;
* `inner_pgLp_hermiteMv` — the `L²` inner product of two of them is the product of the
  one-dimensional Hermite inner products (Fubini);
* `hermiteMvNorm`, `hermiteMvLp`, `orthonormal_hermiteMvLp`, `span_hermiteMvLp`,
  `hermiteMvBasis` — the **orthonormal (Hilbert) basis** `ψ_α / ‖ψ_α‖` of `L²(ℝᵈ)` indexed
  by the multi-indices `α : Fin d →₀ ℕ`, whose span is exactly the Gauss–polynomial core;
* `pderiv_hermiteMv` — `∂ᵢ He_α = αᵢ He_{α−eᵢ}` for the product Hermite *polynomials*;
* `annPoly`, `crePoly` and `annPoly_hermiteMvLp`, `crePoly_hermiteMvLp` — the polynomial
  incarnations of the ladder operators
  `aᵢ = xᵢ/2 + ∂ᵢ`, `aᵢ† = xᵢ/2 − ∂ᵢ` acting on the Gauss-weighted functions, and their
  action `aᵢψ_α = √αᵢ ψ_{α−eᵢ}`, `aᵢ†ψ_α = √(αᵢ+1) ψ_{α+eᵢ}` on the orthonormal basis.

The Gaussian factor is what turns the *polynomial* operators `p ↦ ∂ᵢp` and
`p ↦ xᵢp − ∂ᵢp` into the *function* operators `f ↦ (xᵢ/2)f + f'` and `f ↦ (xᵢ/2)f − f'`:
`∂ᵢ(p·e^{-‖x‖²/4}) = (∂ᵢp − (xᵢ/2)p)·e^{-‖x‖²/4}`.  The analytic side of that identity is
proved in `BookProof.ChapterNavierStokesDifferentialL2`; here everything is algebraic.
-/

namespace BookProof.HermiteProductBasis

open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

/-! ## The product Hermite functions, coordinate by coordinate -/

/-- The `d`-dimensional Gaussian is the product of the one-dimensional ones. -/
theorem gaussD_eq_prod (x : Vd d) : gaussD x = ∏ i, gaussH (x i) := by
  have h : ∏ i, gaussH (x i) = Real.exp (∑ i, (-(x i) ^ 2 / 4)) := by
    rw [Real.exp_sum]; rfl
  rw [gaussD, norm_sq_eq_sum, h]
  congr 1
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The complexified Hermite polynomial evaluated at a real point is the real one. -/
theorem eval_hermiteCx (n : ℕ) (t : ℝ) :
    Polynomial.eval ((t : ℝ) : ℂ) (hermiteCx n) = (((hermiteR n).eval t : ℝ) : ℂ) := by
  have h := Polynomial.hom_eval₂ (Polynomial.hermite n) (Int.castRingHom ℝ) Complex.ofRealHom t
  have hcomp : (Complex.ofRealHom.comp (Int.castRingHom ℝ)) = Int.castRingHom ℂ := by ext1; simp
  rw [hcomp] at h
  simp only [hermiteCx, hermiteR, Polynomial.eval_map]
  exact h.symm

/-- The `i`-th Hermite factor evaluated at `x` only sees the `i`-th coordinate. -/
theorem eval_hermiteFactor (i : Fin d) (n : ℕ) (x : Vd d) :
    MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (hermiteFactor i n)
      = (((hermiteR n).eval (x i) : ℝ) : ℂ) := by
  have hdef : hermiteFactor i n
      = Polynomial.eval₂ (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ) (X i) (hermiteCx n) := by
    rw [hermiteFactor, Polynomial.aeval_def]; rfl
  rw [hdef, Polynomial.hom_eval₂]
  have h : ((MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ))).comp
      (MvPolynomial.C : ℂ →+* MvPolynomial (Fin d) ℂ)) = RingHom.id ℂ := by ext1 c; simp
  rw [h]
  simp only [MvPolynomial.eval_X, Polynomial.eval₂_id]
  exact eval_hermiteCx n (x i)

/-- **The product Hermite function is the product of the one-dimensional Hermite
functions.** -/
theorem pgFun_hermiteMv (a : Fin d →₀ ℕ) (x : Vd d) :
    pgFun (hermiteMv a) x = ((∏ i, hermiteFun (a i) (x i) : ℝ) : ℂ) := by
  rw [pgFun, hermiteMv, map_prod, gaussD_eq_prod]
  push_cast
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [eval_hermiteFactor]; simp [hermiteFun]

/-- The one-dimensional Hermite inner product, written as an integral of Hermite
functions. -/
theorem integral_hermiteFun_mul (m n : ℕ) :
    ∫ t : ℝ, hermiteFun m t * hermiteFun n t = hermiteInner m n := by
  rw [hermiteInner, gint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => hermiteFun_mul m n t)

/-- **Fubini for two product Hermite functions**: their `L²` inner product is the product
of the one-dimensional Hermite inner products. -/
theorem inner_pgLp_hermiteMv (a b : Fin d →₀ ℕ) :
    (inner ℂ (pgLp (hermiteMv a)) (pgLp (hermiteMv b)) : ℂ)
      = ((∏ i, hermiteInner (a i) (b i) : ℝ) : ℂ) := by
  rw [inner_pgLp]
  have key : (∫ x : Vd d, (starRingEnd ℂ) (pgFun (hermiteMv a) x)
        * (pgLp (hermiteMv b) : Vd d → ℂ) x)
      = ∫ x : Vd d, ∏ i, ((hermiteFun (a i) (x i) * hermiteFun (b i) (x i) : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn (hermiteMv b)] with x hx
    rw [hx, pgFun_hermiteMv, pgFun_hermiteMv, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [key, integral_prod_coord (fun i t => ((hermiteFun (a i) t * hermiteFun (b i) t : ℝ) : ℂ)),
    Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_complex_ofReal, integral_hermiteFun_mul]

/-! ## The orthonormal basis -/

/-- The `L²` norm of the product Hermite function `ψ_α`. -/
def hermiteMvNorm (a : Fin d →₀ ℕ) : ℝ := ∏ i, hermiteNorm (a i)

theorem hermiteMvNorm_pos (a : Fin d →₀ ℕ) : 0 < hermiteMvNorm a :=
  Finset.prod_pos fun i _ => hermiteNorm_pos (a i)

theorem hermiteMvNorm_ne_zero (a : Fin d →₀ ℕ) : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (hermiteMvNorm_pos a)

/-- **The normalized product Hermite function** `ψ_α / ‖ψ_α‖`. -/
def hermiteMvLp (a : Fin d →₀ ℕ) : L2d d := ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv a)

theorem pgLp_hermiteMv_eq (a : Fin d →₀ ℕ) :
    pgLp (hermiteMv a) = ((hermiteMvNorm a : ℝ) : ℂ) • hermiteMvLp a := by
  rw [hermiteMvLp, smul_smul, mul_inv_cancel₀ (hermiteMvNorm_ne_zero a), one_smul]

theorem inner_hermiteMvLp (a b : Fin d →₀ ℕ) :
    (inner ℂ (hermiteMvLp a) (hermiteMvLp b) : ℂ) = if a = b then 1 else 0 := by
  rw [hermiteMvLp, hermiteMvLp, inner_smul_left, inner_smul_right, inner_pgLp_hermiteMv]
  by_cases hab : a = b
  · subst hab
    have hprod : (∏ i, hermiteInner (a i) (a i)) = hermiteMvNorm a * hermiteMvNorm a := by
      rw [hermiteMvNorm, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [hermiteNorm_sq, hermiteInner_eq]; simp
    rw [hprod]
    have hne : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero a
    simp only [map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp
  · have hex : ∃ i, a i ≠ b i := by
      by_contra h
      push_neg at h
      exact hab (Finsupp.ext h)
    obtain ⟨i, hi⟩ := hex
    have h0 : (∏ i, hermiteInner (a i) (b i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hermiteInner_eq, if_neg hi])
    rw [h0, if_neg hab]
    simp

theorem orthonormal_hermiteMvLp : Orthonormal ℂ (hermiteMvLp (d := d)) := by
  rw [orthonormal_iff_ite]
  intro a b
  simpa using inner_hermiteMvLp a b

/-- The span of the normalized product Hermite functions is the Gauss–polynomial core. -/
theorem span_hermiteMvLp :
    Submodule.span ℂ (Set.range (hermiteMvLp (d := d))) = polyGaussCore (d := d) := by
  rw [polyGaussCore_eq_hermiteSpan]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    change pgLp (hermiteMv a) ∈ Submodule.span ℂ (Set.range (hermiteMvLp (d := d)))
    rw [pgLp_hermiteMv_eq a]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem hermiteMvLp_mem_core (a : Fin d →₀ ℕ) : hermiteMvLp a ∈ polyGaussCore (d := d) := by
  rw [← span_hermiteMvLp]
  exact Submodule.subset_span ⟨a, rfl⟩

/-- **The product Hermite functions form a Hilbert basis of `L²(ℝᵈ)`**, indexed by the
multi-indices. -/
def hermiteMvBasis : HilbertBasis (Fin d →₀ ℕ) ℂ (L2d d) :=
  HilbertBasis.mk orthonormal_hermiteMvLp
    (by
      rw [span_hermiteMvLp]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])





/-! ## The derivative of a product Hermite polynomial -/











/-! ## The ladder operators, at the level of polynomials -/

/-- The polynomial incarnation of the annihilation operator: multiplying by the Gaussian,
`p ↦ ∂ᵢp` is the function operator `f ↦ (xᵢ/2)f + ∂ᵢf`. -/
def annPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := pderiv i p
  map_add' p q := by simp
  map_smul' c p := by simp

/-- The polynomial incarnation of the creation operator: multiplying by the Gaussian,
`p ↦ xᵢp − ∂ᵢp` is the function operator `f ↦ (xᵢ/2)f − ∂ᵢf`. -/
def crePoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := X i * p - pderiv i p
  map_add' p q := by simp [mul_add]; ring
  map_smul' c p := by simp [smul_sub]







/-! ### The normalizing constants -/







/-! ### The ladder action on the orthonormal basis -/







end

end BookProof.HermiteProductBasis


