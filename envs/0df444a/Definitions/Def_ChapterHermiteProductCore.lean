-- Prove2me | Definitions.Def_ChapterHermiteProductCore
-- name    : ChapterHermiteProductCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:09:37.904677+00:00
-- url     : https://prove2.me/theorems/16f46c3c-fa0f-4da6-a8fc-5e57c6437e2b
-- title:
--   `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the *field-space* realization of the gauge-fixed Yang–Mills Hamiltoni ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteProductCore`, source chapter `BookProof/ChapterHermiteProductCore.lean`).
--
--   `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the *field-space* realization of the gauge-fixed Yang–Mills Hamiltonian: the fields must act as genuine multiplication and differentiation operators on a dense core of `L²(ℝ⁹⁹)`, rather than abstractly on the occupation-number space `ℓ²(ℕ, ℂ)`.
--
--   This module builds that core in an arbitrary finite dimension `d`:
--
--   * `gaussD x = e^{-‖x‖²/4}` is the `d`-dimensional Gaussian, and for a polynomial `p ∈ ℂ[X₀, …, X_{d-1}]` the function `pgFun p x = p(x) · e^{-‖x‖²/4}` is square integrable (`memLp_pgFun`); `pgMap` is the resulting linear map `ℂ[X] →ₗ[ℂ] L²(ℝᵈ)`, and it is **injective** (`pgMap_injective`); * `polyGaussCore = range pgMap` — the polynomials times the Gaussian. This is exactly the span of the *product Hermite functions* `ψ_α(x) = ∏ᵢ He_{αᵢ}(xᵢ) e^{-xᵢ²/4}` (`polyGaussCore_eq_hermiteSpan`), i.e. the `d`-dimensional Hermite core (the span of the product Hermite polynomials is the whole polynomial ring, `span_hermiteMv`); * the core is **dense** (`polyGaussCore_dense`), proved by the multidimensional version of the Fourier/moment argument of `BookProof.ChapterHermiteFunctions`; * the **Gaussian integration-by-parts identity** (`gaussInt_pderiv`) which makes the momentum operators symmetric on the core; * an orthonormal basis `coreBasis` of `L²(ℝᵈ)` adapted to the core, whose span — the *finite-mode domain* of the project's Friedrichs/Hashimoto theorems — is exactly the core (`span_range_coreBasis`).
--
--   The one-dimensional Hermite machinery of `BookProof.ChapterHermiteFunctions` (`hermiteR`, `gint`, `gint_ibp`) is reused throughout: the `d`-dimensional statements are reduced to it by Fubini (`integral_prod_coord`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductCore.lean

import Definitions.Def_ChapterHermiteFunctions

import Mathlib

/-!
# The Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`

`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the *field-space* realization
of the gauge-fixed Yang–Mills Hamiltonian: the fields must act as genuine
multiplication and differentiation operators on a dense core of `L²(ℝ⁹⁹)`,
rather than abstractly on the occupation-number space `ℓ²(ℕ, ℂ)`.

This module builds that core in an arbitrary finite dimension `d`:

* `gaussD x = e^{-‖x‖²/4}` is the `d`-dimensional Gaussian, and for a polynomial
  `p ∈ ℂ[X₀, …, X_{d-1}]` the function `pgFun p x = p(x) · e^{-‖x‖²/4}` is square
  integrable (`memLp_pgFun`); `pgMap` is the resulting linear map
  `ℂ[X] →ₗ[ℂ] L²(ℝᵈ)`, and it is **injective** (`pgMap_injective`);
* `polyGaussCore = range pgMap` — the polynomials times the Gaussian.  This is
  exactly the span of the *product Hermite functions*
  `ψ_α(x) = ∏ᵢ He_{αᵢ}(xᵢ) e^{-xᵢ²/4}` (`polyGaussCore_eq_hermiteSpan`), i.e. the
  `d`-dimensional Hermite core (the span of the product Hermite polynomials is
  the whole polynomial ring, `span_hermiteMv`);
* the core is **dense** (`polyGaussCore_dense`), proved by the multidimensional
  version of the Fourier/moment argument of `BookProof.ChapterHermiteFunctions`;
* the **Gaussian integration-by-parts identity** (`gaussInt_pderiv`) which makes
  the momentum operators symmetric on the core;
* an orthonormal basis `coreBasis` of `L²(ℝᵈ)` adapted to the core, whose span —
  the *finite-mode domain* of the project's Friedrichs/Hashimoto theorems — is
  exactly the core (`span_range_coreBasis`).

The one-dimensional Hermite machinery of `BookProof.ChapterHermiteFunctions`
(`hermiteR`, `gint`, `gint_ibp`) is reused throughout: the `d`-dimensional
statements are reduced to it by Fubini (`integral_prod_coord`).
-/

namespace BookProof.HermiteProductCore

open MeasureTheory Complex MvPolynomial BookProof.HermiteCore
open scoped FourierTransform
open SchwartzMap

noncomputable section

/-- The field space `ℝᵈ`, a `d`-dimensional Euclidean space. -/
abbrev Vd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `L²(ℝᵈ)`. -/
abbrev L2d (d : ℕ) := Lp ℂ 2 (volume : Measure (Vd d))

variable {d : ℕ}

/-! ## Fubini in the coordinates -/

/-- **Fubini in the coordinates of `ℝᵈ`**: the integral of a product of functions
of the separate coordinates is the product of the one-dimensional integrals. -/
theorem integral_prod_coord (f : Fin d → ℝ → ℂ) :
    ∫ x : Vd d, ∏ i, f i (x i) = ∏ i, ∫ t : ℝ, f i t := by
  rw [← ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
      (fun x : Vd d => ∏ i, f i (x i)))]
  exact MeasureTheory.integral_fintype_prod_eq_prod (fun i => f i)

/-- Each coordinate is dominated by the norm. -/
theorem coord_abs_le_norm (x : Vd d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : |x i| ^ 2 ≤ ∑ j, |x j| ^ 2 :=
    Finset.single_le_sum (f := fun j => |x j| ^ 2) (by intros; positivity) (Finset.mem_univ i)
  calc |x i| = Real.sqrt (|x i| ^ 2) := (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ _ := by
        refine Real.sqrt_le_sqrt ?_
        simpa [Real.norm_eq_abs] using h

/-! ## The Gaussian -/

/-- The `d`-dimensional Gaussian `e^{-‖x‖²/4}`, the square root of the Gaussian
weight `e^{-‖x‖²/2}`. -/
def gaussD (x : Vd d) : ℝ := Real.exp (-‖x‖ ^ 2 / 4)

theorem gaussD_pos (x : Vd d) : 0 < gaussD x := Real.exp_pos _

theorem gaussD_ne_zero (x : Vd d) : gaussD x ≠ 0 := ne_of_gt (gaussD_pos x)

theorem continuous_gaussD : Continuous (gaussD (d := d)) := by
  unfold gaussD; fun_prop

/-- The Gaussian `e^{-c‖x‖²}` is integrable on `ℝᵈ` for every `c > 0`. -/
theorem integrable_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Vd d => Real.exp (-c * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Vd d)
    (b := (c : ℂ)) (by simpa using hc) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow]

/-- A polynomial factor is absorbed by a Gaussian: `tᵏ e^{-t²/8}` is bounded. -/
theorem pow_mul_exp_bound (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ k * Real.exp (-t ^ 2 / 8) ≤ 1 + 8 ^ k * (Nat.factorial k) := by
  have hexp_le_one : Real.exp (-t ^ 2 / 8) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_; nlinarith [sq_nonneg t]
  have hexp_pos : 0 < Real.exp (-t ^ 2 / 8) := Real.exp_pos _
  have hfacpos : (0 : ℝ) < 8 ^ k * (Nat.factorial k) := by positivity
  rcases le_or_gt t 1 with h1 | h1
  · have hk : t ^ k ≤ 1 := pow_le_one₀ ht h1
    have : t ^ k * Real.exp (-t ^ 2 / 8) ≤ 1 := mul_le_one₀ hk (le_of_lt hexp_pos) hexp_le_one
    linarith
  · have hkey : (t ^ 2 / 8) ^ k / (Nat.factorial k) ≤ Real.exp (t ^ 2 / 8) :=
      Real.pow_div_factorial_le_exp _ (by positivity) k
    have hfac : (0 : ℝ) < (Nat.factorial k) := by exact_mod_cast Nat.factorial_pos k
    have h2 : (t ^ 2 / 8) ^ k ≤ (Nat.factorial k) * Real.exp (t ^ 2 / 8) := by
      rw [div_le_iff₀ hfac] at hkey; linarith [hkey]
    have hpow : t ^ k ≤ t ^ (2 * k) := by
      refine pow_le_pow_right₀ (le_of_lt h1) ?_; omega
    have hexp_eq : Real.exp (-t ^ 2 / 8) = (Real.exp (t ^ 2 / 8))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    have hE : (0 : ℝ) < Real.exp (t ^ 2 / 8) := Real.exp_pos _
    have h3 : t ^ (2 * k) * Real.exp (-t ^ 2 / 8) ≤ 8 ^ k * (Nat.factorial k) := by
      rw [hexp_eq, mul_inv_le_iff₀ hE, pow_mul]
      have hrw : (t ^ 2) ^ k = 8 ^ k * (t ^ 2 / 8) ^ k := by
        rw [← mul_pow]; ring_nf
      rw [hrw]
      have hmul := mul_le_mul_of_nonneg_left h2 (le_of_lt (pow_pos (by norm_num : (0:ℝ) < 8) k))
      calc (8 : ℝ) ^ k * (t ^ 2 / 8) ^ k ≤ 8 ^ k * ((Nat.factorial k) * Real.exp (t ^ 2 / 8)) :=
            hmul
        _ = 8 ^ k * (Nat.factorial k) * Real.exp (t ^ 2 / 8) := by ring
    nlinarith [mul_le_mul_of_nonneg_right hpow (le_of_lt hexp_pos)]

/-- `‖x‖ᵏ e^{-‖x‖²/4}` is square integrable on `ℝᵈ`. -/
theorem memLp_pow_mul_gaussD (k : ℕ) :
    MemLp (fun x : Vd d => ‖x‖ ^ k * gaussD x) 2 (volume : Measure (Vd d)) := by
  set C : ℝ := 1 + 8 ^ k * (Nat.factorial k) with hC
  have hCpos : 0 ≤ C := by positivity
  have hgmem : MemLp (fun x : Vd d => C * Real.exp (-‖x‖ ^ 2 / 8)) 2 (volume : Measure (Vd d)) := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).mpr ?_
    have hint : Integrable (fun x : Vd d => Real.exp (-(1/4 : ℝ) * ‖x‖ ^ 2)) :=
      integrable_gauss (by norm_num)
    refine (hint.const_mul (C ^ 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    ring_nf
  refine hgmem.mono (by unfold gaussD; fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have hb := pow_mul_exp_bound (t := ‖x‖) k (norm_nonneg x)
  have hgauss : gaussD x = Real.exp (-‖x‖ ^ 2 / 8) * Real.exp (-‖x‖ ^ 2 / 8) := by
    rw [← Real.exp_add]; unfold gaussD; ring_nf
  have hpos : (0 : ℝ) < Real.exp (-‖x‖ ^ 2 / 8) := Real.exp_pos _
  have hnn : 0 ≤ ‖x‖ ^ k * gaussD x := by
    have := gaussD_pos x; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ C * Real.exp (-‖x‖ ^ 2 / 8))]
  calc ‖x‖ ^ k * gaussD x
      = (‖x‖ ^ k * Real.exp (-‖x‖ ^ 2 / 8)) * Real.exp (-‖x‖ ^ 2 / 8) := by
        rw [hgauss]; ring
    _ ≤ C * Real.exp (-‖x‖ ^ 2 / 8) := by
        exact mul_le_mul_of_nonneg_right hb (le_of_lt hpos)

/-! ## Polynomials times the Gaussian -/

/-- `pgFun p x = p(x) · e^{-‖x‖²/4}`: a polynomial in the coordinates of `ℝᵈ`
times the Gaussian. -/
def pgFun (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : ℂ :=
  MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p * (gaussD x : ℂ)

theorem continuous_polyEval (p : MvPolynomial (Fin d) ℂ) :
    Continuous (fun x : Vd d => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => exact (hp.add hq).congr fun x => by rw [Pi.add_apply, MvPolynomial.eval_add]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul (by fun_prop)

theorem continuous_pgFun (p : MvPolynomial (Fin d) ℂ) : Continuous (pgFun p) := by
  unfold pgFun
  exact (continuous_polyEval p).mul (Complex.continuous_ofReal.comp continuous_gaussD)



theorem pgFun_add (p q : MvPolynomial (Fin d) ℂ) : pgFun (p + q) = pgFun p + pgFun q := by
  funext x; simp [pgFun, add_mul]

theorem pgFun_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgFun (c • p) = c • pgFun p := by
  funext x; simp [pgFun, smul_eq_mul, mul_assoc]

/-- A monomial times the Gaussian is square integrable. -/
theorem memLp_pgFun_monomial (a : Fin d →₀ ℕ) (c : ℂ) :
    MemLp (pgFun (monomial a c)) 2 (volume : Measure (Vd d)) := by
  set k : ℕ := ∑ b ∈ a.support, a b with hk
  have hmem : MemLp (fun x : Vd d => ‖c‖ * (‖x‖ ^ k * gaussD x)) 2 (volume : Measure (Vd d)) :=
    (memLp_pow_mul_gaussD (d := d) k).const_mul ‖c‖
  refine hmem.mono ((continuous_pgFun (monomial a c)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have hgauss : (0 : ℝ) < gaussD x := gaussD_pos x
  have hprod : ∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖ ≤ ‖x‖ ^ k := by
    rw [hk, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    rw [norm_pow]
    have h1 : ‖((x i : ℝ) : ℂ)‖ ≤ ‖x‖ := by simpa using coord_abs_le_norm x i
    exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  have hval : ‖pgFun (monomial a c) x‖
      = ‖c‖ * (∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖) * gaussD x := by
    rw [pgFun, MvPolynomial.eval_monomial, norm_mul, norm_mul, Finsupp.prod, norm_prod]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgauss]
  have hrhs : ‖‖c‖ * (‖x‖ ^ k * gaussD x)‖ = ‖c‖ * (‖x‖ ^ k * gaussD x) :=
    Real.norm_of_nonneg (by positivity)
  rw [hval, hrhs]
  have hstep := mul_le_mul_of_nonneg_right hprod (le_of_lt hgauss)
  calc ‖c‖ * (∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖) * gaussD x
      = ‖c‖ * ((∏ b ∈ a.support, ‖((x b : ℝ) : ℂ) ^ a b‖) * gaussD x) := by ring
    _ ≤ ‖c‖ * (‖x‖ ^ k * gaussD x) := mul_le_mul_of_nonneg_left hstep (norm_nonneg c)

/-- **A polynomial times the Gaussian is square integrable.** -/
theorem memLp_pgFun (p : MvPolynomial (Fin d) ℂ) :
    MemLp (pgFun p) 2 (volume : Measure (Vd d)) := by
  have hsum : p = ∑ v ∈ p.support, (monomial v) (MvPolynomial.coeff v p) :=
    (MvPolynomial.support_sum_monomial_coeff p).symm
  have hfun : pgFun p = fun x => ∑ v ∈ p.support, pgFun ((monomial v) (coeff v p)) x := by
    funext x
    rw [pgFun]
    nth_rewrite 1 [hsum]
    simp only [map_sum, Finset.sum_mul, pgFun]
  rw [hfun]
  exact memLp_finset_sum _ fun v _ => memLp_pgFun_monomial v _

/-! ## The core as the range of a linear map -/

/-- `p ↦ [p · e^{-‖x‖²/4}]` as an element of `L²(ℝᵈ)`. -/
def pgLp (p : MvPolynomial (Fin d) ℂ) : L2d d := (memLp_pgFun p).toLp _

theorem pgLp_coeFn (p : MvPolynomial (Fin d) ℂ) :
    (pgLp p : Vd d → ℂ) =ᵐ[volume] pgFun p := (memLp_pgFun p).coeFn_toLp

/-- **The Gauss–polynomial map** `ℂ[X₀, …, X_{d-1}] →ₗ[ℂ] L²(ℝᵈ)`. -/
def pgMap : MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d where
  toFun := pgLp
  map_add' p q := by
    have h : pgFun (p + q) = pgFun p + pgFun q := pgFun_add p q
    simp only [pgLp]
    rw [← MemLp.toLp_add (memLp_pgFun p) (memLp_pgFun q)]
    congr 1
  map_smul' c p := by
    have h : pgFun (c • p) = c • pgFun p := pgFun_smul c p
    simp only [pgLp, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_pgFun p)]
    congr 1



/-- A multivariate polynomial with complex coefficients vanishing at every *real*
point of `ℝᵈ` is the zero polynomial. -/
theorem mvpoly_eq_zero_of_eval_real : ∀ {n : ℕ} {p : MvPolynomial (Fin n) ℂ},
    (∀ x : Fin n → ℝ, eval (fun i => ((x i : ℝ) : ℂ)) p = 0) → p = 0 := by
  intro n
  induction n with
  | zero =>
      intro p h
      refine MvPolynomial.funext fun x => ?_
      have hx : x = fun i => (((fun _ : Fin 0 => (0 : ℝ)) i : ℝ) : ℂ) := by
        funext i; exact i.elim0
      rw [hx, h, map_zero]
  | succ n ih =>
      intro p h
      set P := (MvPolynomial.finSuccEquiv ℂ n) p with hP
      have hcoeff : ∀ k, P.coeff k = 0 := by
        intro k
        refine ih (p := P.coeff k) fun x => ?_
        have hQ : Polynomial.map (eval (fun i => ((x i : ℝ) : ℂ))) P = 0 := by
          refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
          refine Set.Infinite.mono (s := Set.range ((↑) : ℝ → ℂ)) ?_ ?_
          · rintro _ ⟨y, rfl⟩
            have hy := h (Fin.cons y x)
            have hcons : (fun i : Fin (n + 1) => (((Fin.cons y x : Fin (n + 1) → ℝ) i : ℝ) : ℂ))
                = Fin.cons ((y : ℝ) : ℂ) (fun i => ((x i : ℝ) : ℂ)) := by
              funext i
              refine Fin.cases ?_ ?_ i <;> simp
            rw [hcons, MvPolynomial.eval_eq_eval_mv_eval'] at hy
            simpa [Polynomial.IsRoot, hP] using hy
          · exact Set.infinite_range_of_injective Complex.ofReal_injective
        have hc := congrArg (fun q : Polynomial ℂ => q.coeff k) hQ
        simpa using hc
      have hP0 : P = 0 := Polynomial.ext fun k => by simpa using hcoeff k
      have hfin := congrArg (MvPolynomial.finSuccEquiv ℂ n).symm hP0
      simpa [hP] using hfin

/-- **The Gauss–polynomial map is injective**: distinct polynomials give distinct
elements of `L²(ℝᵈ)`.  Equivalently the monomials times the Gaussian are linearly
independent. -/
theorem pgMap_apply (p : MvPolynomial (Fin d) ℂ) : pgMap p = pgLp p := rfl

theorem pgMap_injective : Function.Injective (pgMap (d := d)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hae : pgFun p =ᵐ[volume] 0 := by
    have h0 : (pgLp p : Vd d → ℂ) =ᵐ[volume] 0 := by
      have hp0 : pgLp p = 0 := by simpa [pgMap_apply] using hp
      rw [hp0]
      exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure (Vd d)))
    exact (pgLp_coeFn p).symm.trans h0
  have hzero : pgFun p = 0 :=
    ((continuous_pgFun p).ae_eq_iff_eq volume continuous_const).mp hae
  refine mvpoly_eq_zero_of_eval_real fun x => ?_
  have hx := congrFun hzero ((WithLp.toLp 2 x : Vd d))
  simp only [pgFun, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · simpa using hx
  · exact absurd (by exact_mod_cast hx) (gaussD_ne_zero _)

/-- **The Gauss–polynomial (product Hermite) core** of `L²(ℝᵈ)`: all polynomials
times the Gaussian `e^{-‖x‖²/4}`. -/
def polyGaussCore : Submodule ℂ (L2d d) := LinearMap.range (pgMap (d := d))

theorem pgLp_mem_core (p : MvPolynomial (Fin d) ℂ) : pgLp p ∈ polyGaussCore (d := d) :=
  ⟨p, rfl⟩

/-! ## Density of the core: the multidimensional Fourier/moment argument -/

/-- `x ↦ e^{c‖x‖} e^{-‖x‖²/4}` is square integrable: the Gaussian beats every
exponential, in every dimension. -/
theorem memLp_two_exp_norm_mul_gaussD (c : ℝ) :
    MemLp (fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)) 2
      (volume : Measure (Vd d)) := by
  have hcont : Continuous fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).mul continuous_gaussD
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hdom :
      Integrable (fun x : Vd d => Real.exp (4 * c ^ 2) * Real.exp (-(1/4 : ℝ) * ‖x‖ ^ 2)) :=
    (integrable_gauss (by norm_num)).const_mul _
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  have hsq : ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ ^ 2
      = Real.exp (2 * c * ‖x‖ - ‖x‖ ^ 2 / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_pos (Real.exp_pos _) (gaussD_pos x)).le]
    rw [gaussD, mul_pow, pow_two (Real.exp _), pow_two (Real.exp _), ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hsq]
  have hb : 2 * c * ‖x‖ - ‖x‖ ^ 2 / 2 ≤ 4 * c ^ 2 + -(1/4 : ℝ) * ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ / 2 - 2 * c), norm_nonneg x]
  calc Real.exp (2 * c * ‖x‖ - ‖x‖ ^ 2 / 2)
      ≤ Real.exp (4 * c ^ 2 + -(1/4 : ℝ) * ‖x‖ ^ 2) := Real.exp_le_exp.mpr hb
    _ = Real.exp (4 * c ^ 2) * Real.exp (-(1/4 : ℝ) * ‖x‖ ^ 2) := Real.exp_add _ _

/-- The product of two square-integrable functions is integrable. -/
theorem integrable_mul_of_memLp_two {f g : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d)))
    (hg : MemLp g 2 (volume : Measure (Vd d))) : Integrable (fun x : Vd d => f x * g x) := by
  simpa [Pi.mul_def] using hf.integrable_mul hg

/-- The linear polynomial `x ↦ ⟪ x, w ⟫`. -/
def innerPoly (w : Vd d) : MvPolynomial (Fin d) ℂ := ∑ i, C ((w i : ℝ) : ℂ) * X i

theorem eval_innerPoly (w x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (innerPoly w) = ((inner ℝ x w : ℝ) : ℂ) := by
  rw [innerPoly, map_sum]
  push_cast [PiLp.inner_apply, RCLike.inner_apply]
  simp [mul_comm]

theorem pgFun_innerPoly_pow (w x : Vd d) (k : ℕ) :
    pgFun ((innerPoly w) ^ k) x = ((inner ℝ x w : ℝ) : ℂ) ^ k * (gaussD x : ℂ) := by
  rw [pgFun, map_pow, eval_innerPoly]

/-- **The multidimensional Fourier/moment lemma.**  If `u ∈ L²(ℝᵈ)` is orthogonal
to every polynomial times the Gaussian, then the Fourier transform of the `L¹`
function `e^{-‖x‖²/4} u` vanishes identically. -/
theorem fourier_gaussD_mul_eq_zero {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d)))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x = 0) (w : Vd d) :
    𝓕 (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x) w = 0 := by
  set F : ℕ → Vd d → ℂ := fun N x =>
    (∑ k ∈ Finset.range N,
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
      * (((gaussD x : ℝ) : ℂ) * u x) with hF
  have hterm : ∀ p : MvPolynomial (Fin d) ℂ, Integrable (fun x : Vd d => pgFun p x * u x) :=
    fun p => integrable_mul_of_memLp_two (memLp_pgFun p) hu
  have hFint : ∀ N, ∫ x : Vd d, F N x = 0 := by
    intro N
    have hpt : ∀ x : Vd d, F N x = ∑ k ∈ Finset.range N,
        ((Complex.I * ((-2 * Real.pi : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
          * (pgFun ((innerPoly w) ^ k) x * u x) := by
      intro x
      simp only [hF, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pgFun_innerPoly_pow]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun k _ => (hterm _).const_mul _)]
    simp [integral_const_mul, hmom]
  set c : ℝ := 2 * Real.pi * ‖w‖ with hc
  have hcnn : 0 ≤ c := by positivity
  have hbdd : Integrable (fun x : Vd d => ((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x) :=
    integrable_mul_of_memLp_two (memLp_two_exp_norm_mul_gaussD c) hu
  have hmeas : ∀ N, AEStronglyMeasurable (F N) (volume : Measure (Vd d)) := by
    intro N
    refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) ?_
    · refine continuous_finset_sum _ fun k _ => ?_
      refine Continuous.div_const ?_ _
      exact (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul (by fun_prop)))).pow k
    · exact ((Complex.continuous_ofReal.comp continuous_gaussD).aestronglyMeasurable).mul hu.1
  have hdom : ∀ N, ∀ᵐ x : Vd d, ‖F N x‖
      ≤ ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x‖ := by
    intro N
    filter_upwards with x
    have hinner : |(inner ℝ x w : ℝ)| ≤ ‖x‖ * ‖w‖ := abs_real_inner_le_norm x w
    have hsum : ‖∑ k ∈ Finset.range N,
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
        ≤ Real.exp (c * ‖x‖) := by
      have hstep : ∀ k ∈ Finset.range N,
          ‖(Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
            ≤ (c * ‖x‖) ^ k / (k.factorial : ℝ) := by
        intro k _
        rw [norm_div, norm_pow]
        have hnum : ‖Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)‖ ≤ c * ‖x‖ := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            hc]
          have h2pi : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
            rw [abs_of_nonpos (by nlinarith [Real.pi_pos] : (-2 * Real.pi : ℝ) ≤ 0)]; ring
          rw [h2pi]
          calc 2 * Real.pi * |(inner ℝ x w : ℝ)| ≤ 2 * Real.pi * (‖x‖ * ‖w‖) := by
                exact mul_le_mul_of_nonneg_left hinner (by positivity)
            _ = 2 * Real.pi * ‖w‖ * ‖x‖ := by ring
        have hden : ‖(k.factorial : ℂ)‖ = (k.factorial : ℝ) := by
          simp
        rw [hden]
        gcongr
      calc ‖∑ k ∈ Finset.range N,
            (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
          ≤ ∑ k ∈ Finset.range N,
              ‖(Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k
                / (k.factorial : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range N, (c * ‖x‖) ^ k / (k.factorial : ℝ) :=
            Finset.sum_le_sum hstep
        _ ≤ Real.exp (c * ‖x‖) := Real.sum_le_exp_of_nonneg (by positivity) N
    simp only [hF, norm_mul]
    have h1 : ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ)‖ = Real.exp (c * ‖x‖) * gaussD x := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_pos (Real.exp_pos _) (gaussD_pos x)).le]
    have h2 : ‖((gaussD x : ℝ) : ℂ)‖ = gaussD x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussD_pos x)]
    rw [h1, h2]
    have hg : (0 : ℝ) ≤ gaussD x * ‖u x‖ := mul_nonneg (gaussD_pos x).le (norm_nonneg _)
    calc ‖∑ k ∈ Finset.range N,
          (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)‖
            * (gaussD x * ‖u x‖)
        ≤ Real.exp (c * ‖x‖) * (gaussD x * ‖u x‖) := mul_le_mul_of_nonneg_right hsum hg
      _ = Real.exp (c * ‖x‖) * gaussD x * ‖u x‖ := by ring
  have hlim : ∀ᵐ x : Vd d, Filter.Tendsto (fun N => F N x) Filter.atTop
      (nhds (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
        * (((gaussD x : ℝ) : ℂ) * u x))) := by
    filter_upwards with x
    have hsum := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ)
      (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)))
    have hsum' : HasSum (fun k : ℕ =>
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
        (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))) := by
      simpa [Complex.exp_eq_exp_ℂ] using hsum
    exact hsum'.tendsto_sum_nat.mul_const _
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Vd d => ‖((Real.exp (c * ‖x‖) * gaussD x : ℝ) : ℂ) * u x‖)
    hmeas hbdd.norm hdom hlim
  have hval : ∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
      * (((gaussD x : ℝ) : ℂ) * u x) = 0 := by
    have hc0 : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
        (nhds (∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
          * (((gaussD x : ℝ) : ℂ) * u x))) := by
      simpa [hFint] using hconv
    exact tendsto_nhds_unique hc0 tendsto_const_nhds
  rw [Real.fourier_eq', ← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **Fourier uniqueness on `ℝᵈ`** (the multiplication formula). -/
theorem integral_fourier_mul_comm {f g : Vd d → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ xi : Vd d, 𝓕 f xi * g xi = ∫ x : Vd d, f x * 𝓕 g x := by
  have hflip : ((innerₗ (Vd d)) : Vd d →ₗ[ℝ] Vd d →ₗ[ℝ] ℝ).flip = innerₗ (Vd d) := by
    refine LinearMap.ext fun x : Vd d => LinearMap.ext fun y : Vd d => ?_
    simp [real_inner_comm y x]
  have hcont : Continuous fun p : Vd d × Vd d => (innerₗ (Vd d)) p.1 p.2 := by
    simpa using (continuous_inner (𝕜 := ℝ) (E := Vd d))
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (V := Vd d) (W := Vd d) (E := ℂ) (F := ℂ) (G := ℂ) (μ := volume) (ν := volume)
    (L := innerₗ (Vd d)) (e := Real.fourierChar) (f := f) (g := g)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar hcont hf hg
  show (∫ (xi : Vd d), VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ (Vd d)) f xi * g xi)
      = (∫ (x : Vd d), f x *
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (Vd d)) g x)
  simpa [hflip, ContinuousLinearMap.mul_apply'] using h

/-- An integrable function on `ℝᵈ` whose Fourier transform vanishes identically is
zero almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero {v : Vd d → ℂ} (hv : Integrable v)
    (h : ∀ w : Vd d, 𝓕 v w = 0) : ∀ᵐ x : Vd d, v x = 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hv.locallyIntegrable ?_
  intro g hg hgsupp
  set psi : 𝓢(Vd d, ℂ) := HasCompactSupport.toSchwartzMap
    (f := fun x : Vd d => ((g x : ℝ) : ℂ))
    (by exact hgsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
    (Complex.ofRealCLM.contDiff.comp hg) with hpsi
  set phi : 𝓢(Vd d, ℂ) := 𝓕⁻ psi with hphi
  have hfourier : 𝓕 (phi : Vd d → ℂ) = (psi : Vd d → ℂ) := by
    rw [← SchwartzMap.fourier_coe, hphi]
    simp
  have hkey := integral_fourier_mul_comm hv (phi : 𝓢(Vd d, ℂ)).integrable
  rw [hfourier] at hkey
  have hzero : ∫ xi : Vd d, 𝓕 v xi * (phi : Vd d → ℂ) xi = 0 := by simp [h]
  rw [hzero] at hkey
  have hrw : ∫ x : Vd d, g x • v x = ∫ x : Vd d, v x * (psi : Vd d → ℂ) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hcoe : (psi : Vd d → ℂ) x = ((g x : ℝ) : ℂ) := rfl
    simp only [Complex.real_smul, hcoe]
    ring
  rw [hrw, ← hkey]

/-- **Vanishing of all Gaussian moments forces `u = 0`** on `ℝᵈ`. -/
theorem ae_eq_zero_of_moments {u : Vd d → ℂ} (hu : MemLp u 2 (volume : Measure (Vd d)))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ, ∫ x : Vd d, pgFun p x * u x = 0) :
    ∀ᵐ x : Vd d, u x = 0 := by
  have hg : MemLp (fun x : Vd d => ((gaussD x : ℝ) : ℂ)) 2 (volume : Measure (Vd d)) := by
    have h1 : pgFun (1 : MvPolynomial (Fin d) ℂ) = fun x : Vd d => ((gaussD x : ℝ) : ℂ) := by
      funext x; simp [pgFun]
    rw [← h1]
    exact memLp_pgFun 1
  have hv : Integrable (fun x : Vd d => ((gaussD x : ℝ) : ℂ) * u x) :=
    integrable_mul_of_memLp_two hg hu
  have hzero := ae_eq_zero_of_fourier_eq_zero hv (fun w => fourier_gaussD_mul_eq_zero hu hmom w)
  filter_upwards [hzero] with x hx
  have hne : ((gaussD x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (gaussD_pos x)
  exact (mul_eq_zero.mp hx).resolve_left hne

/-! ## The core is dense -/

theorem inner_pgLp (p : MvPolynomial (Fin d) ℂ) (u : L2d d) :
    (inner ℂ (pgLp p) u : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * (u : Vd d → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn p] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

/-- A monomial with coefficient `1` is real valued on `ℝᵈ`. -/
theorem conj_pgFun_monomial_one (a : Fin d →₀ ℕ) (x : Vd d) :
    (starRingEnd ℂ) (pgFun (monomial a (1 : ℂ)) x) = pgFun (monomial a 1) x := by
  rw [pgFun, MvPolynomial.eval_monomial]
  simp [Finsupp.prod, map_prod, Complex.conj_ofReal]

/-- **The Gauss–polynomial core is dense in `L²(ℝᵈ)`.**  This is the
`d`-dimensional completeness of the Hermite functions. -/
theorem polyGaussCore_dense : Dense ((polyGaussCore : Submodule ℂ (L2d d)) : Set (L2d d)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hmon : ∀ a : Fin d →₀ ℕ,
      ∫ x : Vd d, pgFun (monomial a (1 : ℂ)) x * (u : Vd d → ℂ) x = 0 := by
    intro a
    have h0 : (inner ℂ (pgLp (monomial a (1 : ℂ))) u : ℂ) = 0 :=
      hu _ (pgLp_mem_core _)
    rw [inner_pgLp] at h0
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [conj_pgFun_monomial_one]
  have hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ x : Vd d, pgFun p x * (u : Vd d → ℂ) x = 0 := by
    intro p
    have hu2 : MemLp (u : Vd d → ℂ) 2 (volume : Measure (Vd d)) := Lp.memLp u
    have hsum : p = ∑ v ∈ p.support, (monomial v) (MvPolynomial.coeff v p) :=
      (MvPolynomial.support_sum_monomial_coeff p).symm
    have hpt : ∀ x : Vd d, pgFun p x * (u : Vd d → ℂ) x
        = ∑ v ∈ p.support, MvPolynomial.coeff v p *
            (pgFun (monomial v (1 : ℂ)) x * (u : Vd d → ℂ) x) := by
      intro x
      rw [pgFun]
      nth_rewrite 1 [hsum]
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [pgFun, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun v _ =>
      ((integrable_mul_of_memLp_two (memLp_pgFun (monomial v (1 : ℂ))) hu2)).const_mul _)]
    simp [integral_const_mul, hmon]
  have hzero := ae_eq_zero_of_moments (Lp.memLp u) hmom
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hzero

/-! ## Gaussian moments and integration by parts

The momentum operators are symmetric on the core because of the Gaussian
integration-by-parts identity `∫ (∂ⱼ r) e^{-‖x‖²/2} = ∫ xⱼ r e^{-‖x‖²/2}`, which is
proved here by reducing to the one-dimensional identity `gint_ibp` of
`BookProof.ChapterHermiteFunctions` by Fubini. -/

/-- The Gaussian weight `e^{-‖x‖²/2} = (e^{-‖x‖²/4})²`. -/
def gaussWD (x : Vd d) : ℝ := Real.exp (-‖x‖ ^ 2 / 2)

/-- The squared norm is the sum of the squared coordinates. -/
theorem norm_sq_eq_sum (x : Vd d) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

theorem gaussWD_eq_sq (x : Vd d) : gaussWD x = gaussD x * gaussD x := by
  rw [gaussWD, gaussD, ← Real.exp_add]
  ring_nf

theorem gaussWD_eq_prod (x : Vd d) : gaussWD x = ∏ i, Real.exp (-(x i) ^ 2 / 2) := by
  rw [gaussWD, norm_sq_eq_sum, ← Real.exp_sum]
  congr 1
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring







/-- `r ↦ ∫ r(x) e^{-‖x‖²/2} dx`, the Gaussian-weighted integral of a polynomial:
the `d`-dimensional analogue of `BookProof.HermiteCore.gint`. -/
def gaussInt (r : MvPolynomial (Fin d) ℂ) : ℂ :=
  ∫ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ)











/-- The one-dimensional Gaussian moments `M k = ∫ tᵏ e^{-t²/2} dt`. -/
def gaussMoment (k : ℕ) : ℝ := gint ((Polynomial.X : Polynomial ℝ) ^ k)

theorem gwFun_eq (r : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ) = pgFun r x * pgFun 1 x := by
  simp only [pgFun, gaussWD_eq_sq, map_one]
  push_cast
  ring

theorem integrable_gwFun (r : MvPolynomial (Fin d) ℂ) :
    Integrable (fun x : Vd d =>
      MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r * (gaussWD x : ℂ)) := by
  refine (integrable_mul_of_memLp_two (memLp_pgFun r) (memLp_pgFun 1)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using (gwFun_eq r x).symm

theorem gaussInt_add (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r + s) = gaussInt r + gaussInt s := by
  rw [gaussInt, gaussInt, gaussInt, ← integral_add (integrable_gwFun r) (integrable_gwFun s)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [add_mul]

theorem gaussInt_smul (c : ℂ) (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (c • r) = c * gaussInt r := by
  rw [gaussInt, gaussInt, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_assoc]

theorem gaussInt_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    gaussInt (∑ v ∈ s, f v) = ∑ v ∈ s, gaussInt (f v) := by
  classical
  induction s using Finset.induction with
  | empty => simp [gaussInt]
  | insert v s hv ih =>
      rw [Finset.sum_insert hv, Finset.sum_insert hv, gaussInt_add, ih]

/-- **The moment recurrence** `M_{k+1} = k · M_{k-1}`, one-dimensional integration
by parts against the Gaussian (`BookProof.HermiteCore.gint_ibp`).  For `k = 0` it
reads `M₁ = 0`. -/
theorem gaussMoment_succ (k : ℕ) : gaussMoment (k + 1) = (k : ℝ) * gaussMoment (k - 1) := by
  have h := gint_ibp ((Polynomial.X : Polynomial ℝ) ^ k) 1
  rw [Polynomial.derivative_X_pow, mul_one, Polynomial.derivative_one, sub_zero, mul_one] at h
  rw [gint_C_mul] at h
  rw [gaussMoment, gaussMoment, h, pow_succ]

/-- The Gaussian integral of a monomial factorizes into one-dimensional moments. -/
theorem gaussInt_monomial (a : Fin d →₀ ℕ) :
    gaussInt (monomial a (1 : ℂ)) = ∏ i, ((gaussMoment (a i) : ℝ) : ℂ) := by
  have hpt : ∀ x : Vd d,
      MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (monomial a (1 : ℂ)) * (gaussWD x : ℂ)
        = ∏ i, (((x i) ^ (a i) * Real.exp (-(x i) ^ 2 / 2) : ℝ) : ℂ) := by
    intro x
    rw [MvPolynomial.eval_monomial, one_mul, gaussWD_eq_prod,
      Finsupp.prod_of_support_subset a (Finset.subset_univ _) _ (fun i _ => by simp)]
    push_cast
    rw [← Finset.prod_mul_distrib]
  rw [gaussInt]
  simp_rw [hpt]
  rw [integral_prod_coord (fun i t => (((t ^ (a i) * Real.exp (-t ^ 2 / 2) : ℝ)) : ℂ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussMoment, gint]
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  norm_cast
  simp [gaussW]

/-- **Gaussian integration by parts in `d` dimensions**:
`∫ (∂ⱼ r) e^{-‖x‖²/2} = ∫ xⱼ r e^{-‖x‖²/2}`. -/
theorem gaussInt_pderiv (j : Fin d) (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv j r) = gaussInt (X j * r) := by
  classical
  have hmono : ∀ a : Fin d →₀ ℕ,
      gaussInt (pderiv j (monomial a (1 : ℂ))) = gaussInt (X j * monomial a (1 : ℂ)) := by
    intro a
    have hL : pderiv j (monomial a (1 : ℂ))
        = ((a j : ℂ)) • monomial (a - Finsupp.single j 1) 1 := by
      rw [MvPolynomial.pderiv_monomial, one_mul]
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hR : (X j : MvPolynomial (Fin d) ℂ) * monomial a 1
        = monomial (a + Finsupp.single j 1) 1 := by
      rw [X, monomial_mul]
      simp [add_comm]
    rw [hL, hR, gaussInt_smul, gaussInt_monomial, gaussInt_monomial]
    have hsplit : ∀ b : Fin d →₀ ℕ, ∏ i, ((gaussMoment (b i) : ℝ) : ℂ)
        = ((gaussMoment (b j) : ℝ) : ℂ)
          * ∏ i ∈ Finset.univ.erase j, ((gaussMoment (b i) : ℝ) : ℂ) := by
      intro b
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hprod_eq : ∏ i ∈ Finset.univ.erase j,
          ((gaussMoment ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i) : ℝ) : ℂ)
        = ∏ i ∈ Finset.univ.erase j,
          ((gaussMoment ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i) : ℝ) : ℂ) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      have h1 : ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i) = a i := by
        simp [Finsupp.tsub_apply, hij]
      have h2 : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i) = a i := by
        simp [hij]
      rw [h1, h2]
    rw [hsplit (a - Finsupp.single j 1), hsplit (a + Finsupp.single j 1), hprod_eq]
    have hj1 : ((a - Finsupp.single j 1 : Fin d →₀ ℕ) j) = a j - 1 := by
      simp [Finsupp.tsub_apply]
    have hj2 : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) j) = a j + 1 := by simp
    rw [hj1, hj2, gaussMoment_succ]
    push_cast
    ring
  have hsum : r = ∑ v ∈ r.support, (MvPolynomial.coeff v r) • monomial v (1 : ℂ) := by
    nth_rewrite 1 [← MvPolynomial.support_sum_monomial_coeff r]
    exact Finset.sum_congr rfl fun v _ => by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsum]
  rw [map_sum, Finset.mul_sum, gaussInt_sum, gaussInt_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Derivation.map_smul, gaussInt_smul, mul_smul_comm, gaussInt_smul, hmono v]







/-! ## An orthonormal basis of `L²(ℝᵈ)` whose finite-mode domain is the core

The abstract Friedrichs/Hashimoto theorems of the project are stated for the
*finite-mode domain* `span (range b)` of a `HilbertBasis ℕ`.  Enumerating the
monomials and orthonormalizing the resulting family of Gauss–polynomials by the
Gram–Schmidt process produces such a basis whose finite-mode domain is exactly
the core `polyGaussCore`. -/

/-- The enumerated monomial family is the monomial basis precomposed with the
enumeration. -/
theorem monomialFamily_eq (e : ℕ ≃ (Fin d →₀ ℕ)) :
    (⇑(MvPolynomial.basisMonomials (Fin d) ℂ) ∘ ⇑e)
      = fun n : ℕ => (monomial (e n) (1 : ℂ)) := rfl

/-- The monomials times the Gaussian, enumerated by `ℕ`. -/
def coreFamily (e : ℕ ≃ (Fin d →₀ ℕ)) : ℕ → L2d d := fun n => pgLp (monomial (e n) 1)

theorem coreFamily_linearIndependent (e : ℕ ≃ (Fin d →₀ ℕ)) :
    LinearIndependent ℂ (coreFamily (d := d) e) := by
  have hmon : LinearIndependent ℂ (fun n : ℕ => (monomial (e n) (1 : ℂ))) := by
    have hb := (MvPolynomial.basisMonomials (Fin d) ℂ).linearIndependent
    have hcomp := hb.comp e e.injective
    rwa [monomialFamily_eq (d := d) e] at hcomp
  exact hmon.map' (pgMap (d := d))
    (LinearMap.ker_eq_bot.mpr (pgMap_injective (d := d)))

theorem span_coreFamily (e : ℕ ≃ (Fin d →₀ ℕ)) :
    Submodule.span ℂ (Set.range (coreFamily (d := d) e)) = polyGaussCore (d := d) := by
  have hrange : Set.range (coreFamily (d := d) e)
      = (pgMap (d := d)) '' (Set.range fun n : ℕ => (monomial (e n) (1 : ℂ))) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span]
  have hspan : Submodule.span ℂ (Set.range fun n : ℕ => (monomial (e n) (1 : ℂ)))
      = (⊤ : Submodule ℂ (MvPolynomial (Fin d) ℂ)) := by
    have hb := (MvPolynomial.basisMonomials (Fin d) ℂ).span_eq
    have hrng : Set.range (fun n : ℕ => (monomial (e n) (1 : ℂ)))
        = Set.range (MvPolynomial.basisMonomials (Fin d) ℂ) := by
      rw [← monomialFamily_eq (d := d) e]
      exact e.surjective.range_comp _
    rw [hrng, hb]
  rw [hspan, Submodule.map_top, polyGaussCore]

/-- **An orthonormal basis of `L²(ℝᵈ)` adapted to the core**: the Gram–Schmidt
orthonormalization of the enumerated Gauss–polynomials. -/
def coreBasis (e : ℕ ≃ (Fin d →₀ ℕ)) : HilbertBasis ℕ ℂ (L2d d) :=
  HilbertBasis.mk
    (InnerProductSpace.gramSchmidtNormed_orthonormal (coreFamily_linearIndependent e))
    (by
      have hspan : Submodule.span ℂ
            (Set.range (InnerProductSpace.gramSchmidtNormed ℂ (coreFamily (d := d) e)))
          = polyGaussCore (d := d) := by
        rw [InnerProductSpace.span_gramSchmidtNormed_range,
          InnerProductSpace.span_gramSchmidt, span_coreFamily]
      rw [hspan]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

/-- The span of the basis vectors — the *finite-mode domain* of the abstract
theorems — is exactly the Gauss–polynomial core. -/
theorem span_range_coreBasis (e : ℕ ≃ (Fin d →₀ ℕ)) :
    Submodule.span ℂ (Set.range (coreBasis (d := d) e)) = polyGaussCore (d := d) := by
  rw [coreBasis, HilbertBasis.coe_mk, InnerProductSpace.span_gramSchmidtNormed_range,
    InnerProductSpace.span_gramSchmidt, span_coreFamily]




/-! ## The core is the span of the product Hermite functions

The core was defined as *all* polynomials times the Gaussian.  The name "product
Hermite core" is justified here: the products `∏ᵢ He_{αᵢ}(xᵢ)` of probabilists'
Hermite polynomials span the same space, because the three-term recurrence
`X · He_n = He_{n+1} + n · He_{n-1}` makes their span stable under multiplication
by each coordinate. -/





/-- The probabilists' Hermite polynomial with complex coefficients. -/
def hermiteCx (n : ℕ) : Polynomial ℂ := (Polynomial.hermite n).map (Int.castRingHom ℂ)





/-- The Hermite factor `He_n(x_i)` in the `i`-th coordinate. -/
def hermiteFactor (i : Fin d) (n : ℕ) : MvPolynomial (Fin d) ℂ :=
  Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) (hermiteCx n)





/-- The **product Hermite polynomial** `∏ᵢ He_{αᵢ}(xᵢ)`. -/
def hermiteMv (a : Fin d →₀ ℕ) : MvPolynomial (Fin d) ℂ := ∏ i, hermiteFactor i (a i)

/-- The derivative of the probabilists' Hermite polynomial, over `ℤ`. -/
theorem derivative_hermiteZ (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1))
      = Polynomial.C ((n : ℤ) + 1) * Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_zero]
  | succ n ih =>
    have key : Polynomial.derivative (Polynomial.hermite (n + 1 + 1))
        = Polynomial.hermite (n + 1) + Polynomial.C ((n : ℤ) + 1)
          * (Polynomial.X * Polynomial.hermite n
              - Polynomial.derivative (Polynomial.hermite n)) := by
      rw [Polynomial.hermite_succ (n + 1), Polynomial.derivative_sub,
        Polynomial.derivative_mul, Polynomial.derivative_X, ih, Polynomial.derivative_C_mul]
      ring
    have hC : (Polynomial.C (((n : ℕ) + 1 : ℕ) + 1 : ℤ) : Polynomial ℤ)
        = Polynomial.C ((n : ℤ) + 1) + 1 := by
      push_cast
      rw [show ((n : ℤ) + 1 + 1) = ((n : ℤ) + 1) + 1 from rfl, Polynomial.C_add, Polynomial.C_1]
    rw [key, ← Polynomial.hermite_succ n, hC, add_mul, one_mul, add_comm]

/-- The **three-term recurrence** `X · He_n = He_{n+1} + n · He_{n-1}`, over `ℤ`. -/
theorem hermiteZ_X_mul (n : ℕ) :
    (Polynomial.X : Polynomial ℤ) * Polynomial.hermite n
      = Polynomial.hermite (n + 1) + (n : ℤ) • Polynomial.hermite (n - 1) := by
  cases n with
  | zero => simp [Polynomial.hermite_succ, Polynomial.hermite_zero]
  | succ m =>
    rw [Polynomial.hermite_succ (m + 1), derivative_hermiteZ m]
    simp [Polynomial.smul_eq_C_mul]

theorem hermiteCx_zero : hermiteCx 0 = 1 := by
  simp [hermiteCx, Polynomial.hermite_zero]

theorem hermiteCx_X_mul (n : ℕ) :
    (Polynomial.X : Polynomial ℂ) * hermiteCx n
      = hermiteCx (n + 1) + (n : ℂ) • hermiteCx (n - 1) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℂ)) (hermiteZ_X_mul n)
  simpa [hermiteCx, Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_add] using h

theorem hermiteFactor_zero (i : Fin d) : hermiteFactor i 0 = 1 := by
  simp [hermiteFactor, hermiteCx_zero]

theorem hermiteFactor_X_mul (i : Fin d) (n : ℕ) :
    X i * hermiteFactor i n = hermiteFactor i (n + 1) + (n : ℂ) • hermiteFactor i (n - 1) := by
  have h := congrArg (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ)) (hermiteCx_X_mul n)
  simpa [hermiteFactor, map_add, map_smul] using h

theorem hermiteMv_zero : hermiteMv (0 : Fin d →₀ ℕ) = 1 := by
  simp [hermiteMv, hermiteFactor_zero]

theorem hermiteMv_erase (i : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMv a = hermiteFactor i (a i) * ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) := by
  rw [hermiteMv, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

/-- **The three-term recurrence in `d` variables**: multiplying a product Hermite
polynomial by a coordinate stays inside the family. -/
theorem hermiteMv_X_mul (i : Fin d) (a : Fin d →₀ ℕ) :
    X i * hermiteMv a
      = hermiteMv (a + Finsupp.single i 1) + ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by
  classical
  have hrest : ∀ b : Fin d →₀ ℕ, (∀ j : Fin d, j ≠ i → b j = a j) →
      ∏ j ∈ Finset.univ.erase i, hermiteFactor j (b j)
        = ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) := by
    intro b hb
    exact Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
  have hadd : ∀ j : Fin d, j ≠ i → (a + Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [hj]
  have hsub : ∀ j : Fin d, j ≠ i → (a - Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [Finsupp.tsub_apply, hj]
  have hai : (a + Finsupp.single i 1 : Fin d →₀ ℕ) i = a i + 1 := by simp
  have hsi : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]
  rw [hermiteMv_erase i a, hermiteMv_erase i (a + Finsupp.single i 1),
    hermiteMv_erase i (a - Finsupp.single i 1), hrest _ hadd, hrest _ hsub, hai, hsi,
    ← mul_assoc, hermiteFactor_X_mul i (a i)]
  rw [add_mul, smul_mul_assoc]

/-- The span of the product Hermite polynomials is stable under multiplication by
each coordinate. -/
theorem mul_X_mem_span_hermiteMv (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ Submodule.span ℂ (Set.range (hermiteMv (d := d)))) :
    X i * p ∈ Submodule.span ℂ (Set.range (hermiteMv (d := d))) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [hermiteMv_X_mul]
    exact add_mem (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- **The product Hermite polynomials span all polynomials.** -/
theorem span_hermiteMv :
    Submodule.span ℂ (Set.range (hermiteMv (d := d))) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : (C a : MvPolynomial (Fin d) ℂ) = a • hermiteMv (0 : Fin d →₀ ℕ) := by
      rw [hermiteMv_zero, MvPolynomial.smul_eq_C_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => rw [mul_comm]; exact mul_X_mem_span_hermiteMv i hp

/-- **The Gauss–polynomial core is exactly the span of the product Hermite
functions** `∏ᵢ He_{αᵢ}(xᵢ) · e^{-‖x‖²/4}` — the `d`-dimensional Hermite core. -/
theorem polyGaussCore_eq_hermiteSpan :
    polyGaussCore (d := d)
      = Submodule.span ℂ (Set.range fun a : Fin d →₀ ℕ => pgLp (hermiteMv a)) := by
  have hrange : (Set.range fun a : Fin d →₀ ℕ => pgLp (hermiteMv a))
      = (pgMap (d := d)) '' (Set.range (hermiteMv (d := d))) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span, span_hermiteMv, Submodule.map_top, polyGaussCore]













end

end BookProof.HermiteProductCore


