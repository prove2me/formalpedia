-- Prove2me | Definitions.Def_ChapterQuadratureEsa
-- name    : ChapterQuadratureEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-24T08:49:20.003344+00:00
-- url     : https://prove2.me/theorems/a14fae3b-6b1e-48a5-965c-1a3733a18515
-- title:
--   Chapter QuadratureEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuadratureEsa.lean`): generated def bundle for ChapterQuadratureEsa. See BookProof/ChapterQuadratureEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadratureEsa.lean

import Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvBasis_apply

import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreEquiv_coe
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coe
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coreEquiv

import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_pgLp_smul
-- §2.67 partial-bundle fix: these lemmas live in published theorem modules,
-- not in the partial def bundles they were generated alongside.
import Theorems.Thm_BookProof_HermiteRelative_foOp_linear_apply_eq_mul
import Theorems.Thm_BookProof_HermiteRelative_foOp_apply
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_momPoly_apply
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_mulXPoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_annPoly_apply
import Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMvLp
import Theorems.Thm_BookProof_HermiteProductBasis_annPoly_hermiteMvLp
import Theorems.Thm_BookProof_HermiteRelative_foOp_symmetric
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa

import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The quadrature operator `∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` on the Hermite core

`BookProof.ChapterHermiteRelativeBound` proves that the first-order operator
`B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` (`foOp b b'`) is symmetric on the Gauss–polynomial
(product Hermite) core of `L²(ℝᵈ)`, and that `H_c + B` is essentially self-adjoint
whenever the quadratic part `H_c` is *elliptic*.  The shifted-core modules
(`ChapterShiftedQuadraticEsa`, `ChapterShiftedQuadraticMatrixEsa`,
`ChapterShiftedQuadraticDegenerate`) remove the sign and the invertibility
conditions by completing the square, but need a classical equilibrium — which does
not exist in a kernel direction carrying both a linear potential `bᵢxᵢ` and a
momentum term `b'ᵢπᵢ`.  There the operator has no quadratic part at all, and the
two routes used elsewhere both fail: it has no `L²` eigenvector (so the
Hermite-eigenbasis argument does not see it) and it is not constant-coefficient
(so the Fourier-multiplier argument does not see it either).
`BookProof.ChapterMixedLinearEsa` settles that operator on the **Schwartz** core, by
a quadratic gauge.  This module settles it on the **Gauss–polynomial core** — the
core the whole quadratic family lives on — by the metaplectic rotation, which on
that core is nothing but a phase.

## What is proved

* `fourier_eq_zero_of_moments`, `ae_eq_zero_of_moments'` — **a moment lemma without
  an `L²` hypothesis**: a function all of whose exponentially weighted moments are
  finite and all of whose polynomial moments vanish is zero almost everywhere.
  This strengthens `BookProof.HermiteProductCore.ae_eq_zero_of_moments`, which
  needs the function to be a Gaussian times an `L²` function, and is what lets the
  deficiency equation of a *multiplication* operator be treated on the
  Gauss–polynomial core (there the natural function is `e^{-‖x‖²/4}(ℓ − z)u`, which
  is not of that shape);
* `foOp_pos_deficiencyTrivialAt`, `foOp_pos_essentiallySelfAdjoint` — multiplication
  by the real linear function `x ↦ ⟪x, b⟫` is essentially self-adjoint on the core;
* `phaseBasis`, `phaseU`, `phaseU_hermiteMvLp` — **the instrument**: a unimodular
  multiplier on a Hilbert basis is a unitary of the space, sending each basis vector
  to its phase multiple;
* `posL_hermiteCore`, `momL_hermiteCore`, `foOp_hermiteCore` — the ladder form of the
  canonical pair on the product Hermite basis: the quadrature raises the `i`-th
  excitation number with amplitude `wᵢ = bᵢ + ib'ᵢ/2` and lowers it with `conj wᵢ`;
* `phaseU_foOp_hermiteCore` — the phase unitary rotates the canonical pair: it carries
  `foOp r 0` onto `foOp b b'` when `ζᵢ = wᵢ/|wᵢ|`, `rᵢ = |wᵢ|`.  This is the metaplectic
  rotation `e^{iθ·N}`, realized diagonally on the Hermite basis;
* HEADLINE `foOp_essentiallySelfAdjoint` — for **arbitrary** real coefficients
  `b, b'` the quadrature `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝᵈ)`, and `foOp_stone_flow` turns that into a
  complete unitary flow.

A reusable by-product is `linearMap_ext_of_span`: two linear maps out of a submodule
spanned by a family agree as soon as they agree on that family.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.QuadratureEsa

open MeasureTheory MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

variable {d : ℕ}

/-! ## 1. A moment lemma without an `L²` hypothesis -/

/-- The `k`-th term of the exponential series is dominated by the exponential. -/
private theorem integrable_inner_pow_mul {v : Vd d → ℂ}
    (hmeas : AEStronglyMeasurable v (volume : Measure (Vd d)))
    (hexp : ∀ c : ℝ, Integrable (fun x : Vd d => Real.exp (c * ‖x‖) * ‖v x‖))
    (w : Vd d) (k : ℕ) :
    Integrable (fun x : Vd d => ((inner ℝ x w : ℝ) : ℂ) ^ k * v x) := by
  have hmeas' : AEStronglyMeasurable (fun x : Vd d => ((inner ℝ x w : ℝ) : ℂ) ^ k * v x)
      (volume : Measure (Vd d)) := by
    refine AEStronglyMeasurable.mul ?_ hmeas
    exact ((Complex.continuous_ofReal.comp (by fun_prop)).pow k).aestronglyMeasurable
  refine Integrable.mono' (((hexp ‖w‖).const_mul (k.factorial : ℝ))) hmeas' ?_
  filter_upwards with x
  have hinner : |(inner ℝ x w : ℝ)| ≤ ‖x‖ * ‖w‖ := abs_real_inner_le_norm x w
  have h1 : ‖((inner ℝ x w : ℝ) : ℂ) ^ k‖ ≤ (‖w‖ * ‖x‖) ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [mul_comm]; exact hinner) k
  have h2 : (‖w‖ * ‖x‖) ^ k ≤ (k.factorial : ℝ) * Real.exp (‖w‖ * ‖x‖) := by
    have hpos : (0 : ℝ) ≤ ‖w‖ * ‖x‖ := by positivity
    have hle : (‖w‖ * ‖x‖) ^ k / (k.factorial : ℝ) ≤ Real.exp (‖w‖ * ‖x‖) := by
      have := Real.sum_le_exp_of_nonneg hpos (k + 1)
      have hmem : (‖w‖ * ‖x‖) ^ k / (k.factorial : ℝ)
          ≤ ∑ j ∈ Finset.range (k + 1), (‖w‖ * ‖x‖) ^ j / (j.factorial : ℝ) := by
        refine Finset.single_le_sum (f := fun j => (‖w‖ * ‖x‖) ^ j / (j.factorial : ℝ))
          (fun j _ => by positivity) (Finset.self_mem_range_succ k)
      linarith
    have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
    calc (‖w‖ * ‖x‖) ^ k = (k.factorial : ℝ) * ((‖w‖ * ‖x‖) ^ k / (k.factorial : ℝ)) := by
          field_simp
      _ ≤ (k.factorial : ℝ) * Real.exp (‖w‖ * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left hle hfac.le
  calc ‖((inner ℝ x w : ℝ) : ℂ) ^ k * v x‖
      = ‖((inner ℝ x w : ℝ) : ℂ) ^ k‖ * ‖v x‖ := norm_mul _ _
    _ ≤ ((k.factorial : ℝ) * Real.exp (‖w‖ * ‖x‖)) * ‖v x‖ := by
        exact mul_le_mul_of_nonneg_right (h1.trans h2) (norm_nonneg _)
    _ = (k.factorial : ℝ) * (Real.exp (‖w‖ * ‖x‖) * ‖v x‖) := by ring

/-- **The Fourier/moment lemma, with exponential-moment hypotheses.**  If every
exponentially weighted moment of `v` is finite and every polynomial moment of `v`
vanishes, then the Fourier transform of `v` vanishes identically.

This is `BookProof.HermiteProductCore.fourier_gaussD_mul_eq_zero` with the special
shape `v = e^{-‖x‖²/4}u`, `u ∈ L²`, replaced by the integrability that shape
provides. -/
theorem fourier_eq_zero_of_moments {v : Vd d → ℂ}
    (hmeas : AEStronglyMeasurable v (volume : Measure (Vd d)))
    (hexp : ∀ c : ℝ, Integrable (fun x : Vd d => Real.exp (c * ‖x‖) * ‖v x‖))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p * v x = 0)
    (w : Vd d) : 𝓕 v w = 0 := by
  set c : ℝ := 2 * Real.pi * ‖w‖ with hc
  set F : ℕ → Vd d → ℂ := fun N x =>
    (∑ k ∈ Finset.range N,
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
      * v x with hF
  have hmomk : ∀ k : ℕ, ∫ x : Vd d, ((inner ℝ x w : ℝ) : ℂ) ^ k * v x = 0 := by
    intro k
    have h := hmom ((innerPoly w) ^ k)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ((inner ℝ x w : ℝ) : ℂ) ^ k * v x
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) ((innerPoly w) ^ k) * v x
    rw [map_pow, eval_innerPoly]
  have hFint : ∀ N, ∫ x : Vd d, F N x = 0 := by
    intro N
    have hpt : ∀ x : Vd d, F N x = ∑ k ∈ Finset.range N,
        ((Complex.I * ((-2 * Real.pi : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
          * (((inner ℝ x w : ℝ) : ℂ) ^ k * v x) := by
      intro x
      simp only [hF, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun k _ =>
      ((integrable_inner_pow_mul hmeas hexp w k)).const_mul _)]
    simp [integral_const_mul, hmomk]
  have hmeasF : ∀ N, AEStronglyMeasurable (F N) (volume : Measure (Vd d)) := by
    intro N
    refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) hmeas
    refine continuous_finset_sum _ fun k _ => ?_
    refine Continuous.div_const ?_ _
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul (by fun_prop)))).pow k
  have hdom : ∀ N, ∀ᵐ x : Vd d, ‖F N x‖ ≤ Real.exp (c * ‖x‖) * ‖v x‖ := by
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
        have hden : ‖(k.factorial : ℂ)‖ = (k.factorial : ℝ) := by simp
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
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hlim : ∀ᵐ x : Vd d, Filter.Tendsto (fun N => F N x) Filter.atTop
      (nhds (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) * v x)) := by
    filter_upwards with x
    have hsum := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ)
      (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)))
    have hsum' : HasSum (fun k : ℕ =>
        (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ)) ^ k / (k.factorial : ℂ))
        (Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))) := by
      simpa [Complex.exp_eq_exp_ℂ] using hsum
    exact hsum'.tendsto_sum_nat.mul_const _
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Vd d => Real.exp (c * ‖x‖) * ‖v x‖) hmeasF (hexp c) hdom hlim
  have hval : ∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
      * v x = 0 := by
    have hc0 : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
        (nhds (∫ x : Vd d, Complex.exp (Complex.I * ((-2 * Real.pi * (inner ℝ x w : ℝ) : ℝ) : ℂ))
          * v x)) := by
      simpa [hFint] using hconv
    exact tendsto_nhds_unique hc0 tendsto_const_nhds
  rw [Real.fourier_eq', ← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **Vanishing of all polynomial moments forces `v = 0`**, under exponential
integrability alone. -/
theorem ae_eq_zero_of_moments' {v : Vd d → ℂ}
    (hmeas : AEStronglyMeasurable v (volume : Measure (Vd d)))
    (hexp : ∀ c : ℝ, Integrable (fun x : Vd d => Real.exp (c * ‖x‖) * ‖v x‖))
    (hmom : ∀ p : MvPolynomial (Fin d) ℂ,
      ∫ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p * v x = 0) :
    ∀ᵐ x : Vd d, v x = 0 := by
  have hint : Integrable v (volume : Measure (Vd d)) := by
    have h := hexp 0
    simp only [zero_mul, Real.exp_zero, one_mul] at h
    exact (integrable_norm_iff hmeas).mp h
  exact ae_eq_zero_of_fourier_eq_zero hint (fun w => fourier_eq_zero_of_moments hmeas hexp hmom w)

/-! ## 2. Multiplication by a real linear function on the Hermite core -/

/-- The real linear symbol `x ↦ ∑ᵢ bᵢxᵢ` — the multiplier of `foOp b 0`. -/
def linSymb (b : Fin d → ℝ) (x : Vd d) : ℝ := ∑ i, b i * x i

/-- The linear symbol as a polynomial. -/
noncomputable def linPoly (b : Fin d → ℝ) : MvPolynomial (Fin d) ℂ := ∑ i, C ((b i : ℝ) : ℂ) * X i

theorem eval_linPoly (b : Fin d → ℝ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (linPoly b) = ((linSymb b x : ℝ) : ℂ) := by
  rw [linPoly, map_sum, linSymb]
  push_cast
  simp

theorem abs_linSymb_le (b : Fin d → ℝ) (x : Vd d) :
    |linSymb b x| ≤ (∑ i, |b i|) * ‖x‖ := by
  calc |linSymb b x| ≤ ∑ i, |b i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |b i| * ‖x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (coord_abs_le_norm x i) (abs_nonneg _)
    _ = (∑ i, |b i|) * ‖x‖ := by rw [Finset.sum_mul]

theorem foOp_coe (b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    (foOp b b' (coreEquiv p)) = pgLp (foPoly b b' p) := coreOp_coe _ p

/-- Conjugation of the coefficients is conjugation of the values at real points.
(Inlined from the chapter source: the bundle must not import a provider bundle that
collides with this file's own `BookProof.NavierStokesFlow` declarations.) -/
private theorem eval_starP_qe (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  rw [starP, eval_map]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

set_option maxHeartbeats 1600000 in
-- a single long computation: the exponential domination bound, the moment identity and
-- the pointwise factorisation are all elaborated inside one declaration
/-- **The deficiency spaces of the linear potential are trivial.**  A vector `w`
satisfying the deficiency identity of multiplication by `x ↦ ∑ᵢ bᵢxᵢ` at a non-real
point vanishes: the moment lemma above applies to `e^{-‖x‖²/4}(ℓ − z)w`, which is not
of the Gaussian-times-`L²` shape covered by the moment lemma of
`ChapterHermiteProductCore`. -/
theorem foOp_pos_deficiencyTrivialAt (b : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (foOp b 0) z := by
  intro w hw
  set W : Vd d → ℂ := fun x => (w : Vd d → ℂ) x with hW
  have hWmem : MemLp W 2 (volume : Measure (Vd d)) := Lp.memLp w
  set v : Vd d → ℂ :=
    fun x => ((gaussD x : ℝ) : ℂ) * ((((linSymb b x : ℝ) : ℂ) - z) * W x) with hv
  -- measurability
  have hmeas : AEStronglyMeasurable v (volume : Measure (Vd d)) := by
    refine AEStronglyMeasurable.mul ?_ (AEStronglyMeasurable.mul ?_ hWmem.1)
    · exact (Complex.continuous_ofReal.comp continuous_gaussD).aestronglyMeasurable
    · refine AEStronglyMeasurable.sub ?_ aestronglyMeasurable_const
      refine (Complex.continuous_ofReal.comp ?_).aestronglyMeasurable
      exact continuous_finset_sum _ fun i _ => continuous_const.mul (by fun_prop)
  -- exponential integrability
  have hexp : ∀ c : ℝ, Integrable (fun x : Vd d => Real.exp (c * ‖x‖) * ‖v x‖) := by
    intro c
    set B : ℝ := (∑ i, |b i|) + ‖z‖ + 1 with hB
    have hBpos : 0 < B := by
      have : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      positivity
    have hdom : Integrable
        (fun x : Vd d => B * ‖((Real.exp ((c + 1) * ‖x‖) * gaussD x : ℝ) : ℂ) * W x‖) := by
      refine Integrable.const_mul ?_ B
      exact (integrable_mul_of_memLp_two (memLp_two_exp_norm_mul_gaussD (c + 1)) hWmem).norm
    refine Integrable.mono' hdom ?_ ?_
    · exact ((Real.continuous_exp.comp
        (continuous_const.mul continuous_norm)).aestronglyMeasurable).mul hmeas.norm
    · filter_upwards with x
      have hgpos : 0 < gaussD x := gaussD_pos x
      have hnv : ‖v x‖ = gaussD x * (‖((linSymb b x : ℝ) : ℂ) - z‖ * ‖W x‖) := by
        rw [hv]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos]
      have hlin : ‖((linSymb b x : ℝ) : ℂ) - z‖ ≤ B * Real.exp ‖x‖ := by
        have h1 : ‖((linSymb b x : ℝ) : ℂ) - z‖ ≤ |linSymb b x| + ‖z‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
        have h2 : |linSymb b x| + ‖z‖ ≤ ((∑ i, |b i|) + ‖z‖ + 1) * (1 + ‖x‖) := by
          have := abs_linSymb_le b x
          have hnn : (0 : ℝ) ≤ ∑ i, |b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
          nlinarith [norm_nonneg x, norm_nonneg z]
        have h3 : (1 : ℝ) + ‖x‖ ≤ Real.exp ‖x‖ := by
          have := Real.add_one_le_exp ‖x‖
          linarith
        calc ‖((linSymb b x : ℝ) : ℂ) - z‖ ≤ ((∑ i, |b i|) + ‖z‖ + 1) * (1 + ‖x‖) := h1.trans h2
          _ ≤ B * Real.exp ‖x‖ := by rw [hB]; exact mul_le_mul_of_nonneg_left h3 hBpos.le
      have hrhs : ‖((Real.exp ((c + 1) * ‖x‖) * gaussD x : ℝ) : ℂ) * W x‖
          = Real.exp ((c + 1) * ‖x‖) * gaussD x * ‖W x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp ((c + 1) * ‖x‖) * gaussD x)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hnv, hrhs]
      have hexpadd : Real.exp ((c + 1) * ‖x‖) = Real.exp (c * ‖x‖) * Real.exp ‖x‖ := by
        rw [← Real.exp_add]; ring_nf
      rw [hexpadd]
      have hWnn : (0 : ℝ) ≤ ‖W x‖ := norm_nonneg _
      have hstep : gaussD x * (‖((linSymb b x : ℝ) : ℂ) - z‖ * ‖W x‖)
          ≤ gaussD x * ((B * Real.exp ‖x‖) * ‖W x‖) := by
        gcongr
      calc Real.exp (c * ‖x‖) * (gaussD x * (‖((linSymb b x : ℝ) : ℂ) - z‖ * ‖W x‖))
          ≤ Real.exp (c * ‖x‖) * (gaussD x * ((B * Real.exp ‖x‖) * ‖W x‖)) := by
            exact mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
        _ = B * (Real.exp (c * ‖x‖) * Real.exp ‖x‖ * gaussD x * ‖W x‖) := by ring
  -- all polynomial moments vanish
  have hmom : ∀ q : MvPolynomial (Fin d) ℂ,
      ∫ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q * v x = 0 := by
    intro q
    set p : MvPolynomial (Fin d) ℂ := starP q with hp
    have hconj : ∀ x : Vd d, (starRingEnd ℂ) (pgFun p x) = pgFun q x := by
      intro x
      rw [pgFun, pgFun, map_mul, Complex.conj_ofReal, hp, eval_starP_qe, Complex.conj_conj]
    -- the two integrals occurring in the deficiency identity
    have hint1 : Integrable (fun x : Vd d => pgFun q x * W x) :=
      integrable_mul_of_memLp_two (memLp_pgFun q) hWmem
    have hint2 : Integrable (fun x : Vd d => pgFun (linPoly b * q) x * W x) :=
      integrable_mul_of_memLp_two (memLp_pgFun (linPoly b * q)) hWmem
    have hpt2 : ∀ x : Vd d, pgFun (linPoly b * q) x * W x
        = ((linSymb b x : ℝ) : ℂ) * (pgFun q x * W x) := by
      intro x
      rw [pgFun, pgFun, map_mul, eval_linPoly]
      ring
    have h := hw (coreEquiv p)
    rw [foOp_coe, coreEquiv_coe, inner_pgLp, inner_pgLp] at h
    replace h : ∫ x : Vd d, (starRingEnd ℂ) (pgFun (foPoly b 0 p) x) * W x
        = z * ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * W x := h
    have hL : ∫ x : Vd d, (starRingEnd ℂ) (pgFun (foPoly b 0 p) x) * W x
        = ∫ x : Vd d, ((linSymb b x : ℝ) : ℂ) * (pgFun q x * W x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change (starRingEnd ℂ) (pgFun (foPoly b 0 p) x) * W x
        = ((linSymb b x : ℝ) : ℂ) * (pgFun q x * W x)
      rw [foOp_linear_apply_eq_mul, map_mul, Complex.conj_ofReal, hconj]
      simp only [linSymb]
      ring
    have hR : ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * W x = ∫ x : Vd d, pgFun q x * W x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change (starRingEnd ℂ) (pgFun p x) * W x = pgFun q x * W x
      rw [hconj]
    rw [hL, hR] at h
    have hsplit : ∫ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q * v x
        = (∫ x : Vd d, ((linSymb b x : ℝ) : ℂ) * (pgFun q x * W x))
          - z * ∫ x : Vd d, pgFun q x * W x := by
      have hpt : ∀ x : Vd d, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q * v x
          = ((linSymb b x : ℝ) : ℂ) * (pgFun q x * W x) - z * (pgFun q x * W x) := by
        intro x
        rw [hv, pgFun]
        ring
      simp_rw [hpt]
      rw [integral_sub ?_ (hint1.const_mul z), integral_const_mul]
      · exact hint2.congr (Filter.Eventually.of_forall fun x => hpt2 x)
    rw [hsplit, h]
    ring
  -- conclude
  have hzero := ae_eq_zero_of_moments' hmeas hexp hmom
  have hWzero : ∀ᵐ x : Vd d, W x = 0 := by
    filter_upwards [hzero] with x hx
    have hg : ((gaussD x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (gaussD_pos x)
    have hlz : ((linSymb b x : ℝ) : ℂ) - z ≠ 0 := by
      intro h0
      apply hz
      have := congrArg Complex.im h0
      simpa using this.symm
    have h1 : (((linSymb b x : ℝ) : ℂ) - z) * W x = 0 := (mul_eq_zero.mp hx).resolve_left hg
    exact (mul_eq_zero.mp h1).resolve_left hlz
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hWzero

/-- **Multiplication by a real linear function is essentially self-adjoint on the
Gauss–polynomial core.** -/
theorem foOp_pos_essentiallySelfAdjoint (b : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (foOp b 0) :=
  ⟨foOp_pos_deficiencyTrivialAt b (by simp), foOp_pos_deficiencyTrivialAt b (by simp)⟩

/-! ## 3. The metaplectic phase rotation on the product Hermite basis -/

/-- **Linear maps out of a spanned submodule are determined on the spanning family.** -/
theorem linearMap_ext_of_span {E M ι : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup M] [Module ℂ M] (v : ι → E) {D : Submodule ℂ E}
    (hD : Submodule.span ℂ (Set.range v) = D) (hvD : ∀ i, v i ∈ D)
    (F G : D →ₗ[ℂ] M) (h : ∀ i, F ⟨v i, hvD i⟩ = G ⟨v i, hvD i⟩) : F = G := by
  have main : ∀ y : E, y ∈ Submodule.span ℂ (Set.range v) → ∀ hy : y ∈ D,
      F ⟨y, hy⟩ = G ⟨y, hy⟩ := by
    intro y hy0
    induction hy0 using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        intro _
        exact h j
    | zero =>
        intro hy
        have h0 : (⟨(0 : E), hy⟩ : D) = 0 := Subtype.ext rfl
        rw [h0, map_zero, map_zero]
    | add z w hz hw ihz ihw =>
        intro hy
        have hzD : z ∈ D := hD ▸ hz
        have hwD : w ∈ D := hD ▸ hw
        have hadd : (⟨z + w, hy⟩ : D) = ⟨z, hzD⟩ + ⟨w, hwD⟩ := Subtype.ext rfl
        rw [hadd, map_add, map_add, ihz hzD, ihw hwD]
    | smul r z hz ih =>
        intro hy
        have hzD : z ∈ D := hD ▸ hz
        have hsm : (⟨r • z, hy⟩ : D) = r • ⟨z, hzD⟩ := Subtype.ext rfl
        rw [hsm, map_smul, map_smul, ih hzD]
  refine LinearMap.ext ?_
  rintro ⟨x, hx⟩
  exact main x (hD ▸ hx) hx

theorem conj_mul_self_of_norm_one {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [Complex.conj_mul']
  norm_cast
  simp [h]

/-! ### The core vector carried by a product Hermite function -/

/-- The normalized product Hermite function `ψ_α`, as an element of the core. -/
noncomputable def hermiteCore (a : Fin d →₀ ℕ) : polyGaussCore (d := d) :=
  coreEquiv (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a)

@[simp] theorem hermiteCore_coe (a : Fin d →₀ ℕ) :
    ((hermiteCore a : polyGaussCore (d := d)) : L2d d) = hermiteMvLp a := by
  rw [hermiteCore, coreEquiv_coe, pgLp_smul, hermiteMvLp]

theorem hermiteCore_eq (a : Fin d →₀ ℕ) (h : hermiteMvLp (d := d) a ∈ polyGaussCore (d := d)) :
    (⟨hermiteMvLp a, h⟩ : polyGaussCore (d := d)) = hermiteCore a :=
  Subtype.ext (hermiteCore_coe a).symm

/-! ### The canonical pair in terms of the ladder operators -/

theorem pgLp_add' (p q : MvPolynomial (Fin d) ℂ) : pgLp (p + q) = pgLp p + pgLp q :=
  map_add (pgMap (d := d)) p q

theorem pgLp_sub' (p q : MvPolynomial (Fin d) ℂ) : pgLp (p - q) = pgLp p - pgLp q :=
  map_sub (pgMap (d := d)) p q

/-- `xᵢ = aᵢ + a†ᵢ`, on polynomial coordinates. -/
theorem mulXPoly_eq_cre_add_ann (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXPoly i p = crePoly i p + annPoly i p := by
  simp [mulXPoly_apply, crePoly_apply, annPoly_apply]

/-- `πᵢ = (i/2)(a†ᵢ − aᵢ)`, on polynomial coordinates. -/
theorem momPoly_eq_cre_sub_ann (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = (Complex.I / 2) • (crePoly i p - annPoly i p) := by
  simp only [momPoly_apply, crePoly_apply, annPoly_apply, ← MvPolynomial.smul_eq_C_mul]
  module

theorem posL_coe (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    posL i (coreEquiv p) = pgLp (mulXPoly i p) := coreOp_coe _ p

theorem momL_coe (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momL i (coreEquiv p) = pgLp (momPoly i p) := coreOp_coe _ p

/-- **The position operator on a product Hermite function**: `xᵢψ_α = √(αᵢ+1)ψ_{α+eᵢ} +
√αᵢ ψ_{α−eᵢ}`. -/
theorem posL_hermiteCore (i : Fin d) (a : Fin d →₀ ℕ) :
    posL i (hermiteCore a)
      = ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1)
        + ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1) := by
  rw [hermiteCore, posL_coe, map_smul, mulXPoly_eq_cre_add_ann, smul_add, pgLp_add', pgLp_smul,
    pgLp_smul, crePoly_hermiteMvLp, annPoly_hermiteMvLp]

/-- **The momentum operator on a product Hermite function**: `πᵢψ_α =
(i/2)(√(αᵢ+1)ψ_{α+eᵢ} − √αᵢ ψ_{α−eᵢ})`. -/
theorem momL_hermiteCore (i : Fin d) (a : Fin d →₀ ℕ) :
    momL i (hermiteCore a)
      = (Complex.I / 2) •
          (((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1)
            - ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1)) := by
  rw [hermiteCore, momL_coe, map_smul, momPoly_eq_cre_sub_ann, smul_comm, smul_sub, pgLp_smul,
    pgLp_sub', pgLp_smul, pgLp_smul, crePoly_hermiteMvLp, annPoly_hermiteMvLp]

/-! ### The complex amplitude of a quadrature -/

/-- The complex amplitude `wᵢ = bᵢ + i b'ᵢ/2` of the quadrature `bᵢxᵢ + b'ᵢπᵢ`: it is the
coefficient with which the quadrature raises the `i`-th excitation number. -/
noncomputable def foAmp (b b' : Fin d → ℝ) (i : Fin d) : ℂ :=
  ((b i : ℝ) : ℂ) + Complex.I * ((b' i : ℝ) : ℂ) / 2

theorem foAmp_real (r : Fin d → ℝ) (i : Fin d) : foAmp r 0 i = ((r i : ℝ) : ℂ) := by
  simp [foAmp]

theorem conj_foAmp (b b' : Fin d → ℝ) (i : Fin d) :
    (starRingEnd ℂ) (foAmp b b' i) = ((b i : ℝ) : ℂ) - Complex.I * ((b' i : ℝ) : ℂ) / 2 := by
  simp only [foAmp, map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- **The quadrature on a product Hermite function.** -/
theorem foOp_hermiteCore (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    foOp b b' (hermiteCore a)
      = ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
                • hermiteMvLp (a + Finsupp.single i 1)
              + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
                • hermiteMvLp (a - Finsupp.single i 1)) := by
  rw [foOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [posL_hermiteCore, momL_hermiteCore, conj_foAmp, foAmp]
  module

/-- The modulus of the amplitude: the coefficient of the rotated, purely positional,
quadrature. -/
noncomputable def foMod (b b' : Fin d → ℝ) (i : Fin d) : ℝ := ‖foAmp b b' i‖

/-- The phase of the amplitude (set to `1` in a direction where the quadrature is absent). -/
noncomputable def foPhase (b b' : Fin d → ℝ) (i : Fin d) : ℂ :=
  if foAmp b b' i = 0 then 1 else foAmp b b' i / ((foMod b b' i : ℝ) : ℂ)

theorem norm_foPhase (b b' : Fin d → ℝ) (i : Fin d) : ‖foPhase b b' i‖ = 1 := by
  rw [foPhase]
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, foMod, abs_norm,
      div_self (norm_ne_zero_iff.mpr h)]

/-- **Polar decomposition of the amplitude**: `wᵢ = |wᵢ| ζᵢ`. -/
theorem foMod_mul_foPhase (b b' : Fin d → ℝ) (i : Fin d) :
    ((foMod b b' i : ℝ) : ℂ) * foPhase b b' i = foAmp b b' i := by
  rw [foPhase]
  split_ifs with h
  · rw [h, mul_one]
    simp [foMod, h]
  · have hne : ((foMod b b' i : ℝ) : ℂ) ≠ 0 := by
      simpa [foMod, Complex.ofReal_eq_zero] using h
    field_simp

/-- The conjugate polar identity `|wᵢ| = conj(wᵢ) ζᵢ`, which is what makes the *lowering*
coefficient rotate the right way. -/
theorem foMod_eq_conj_mul_foPhase (b b' : Fin d → ℝ) (i : Fin d) :
    ((foMod b b' i : ℝ) : ℂ) = (starRingEnd ℂ) (foAmp b b' i) * foPhase b b' i := by
  have hpolar := foMod_mul_foPhase b b' i
  have hconj := congrArg (starRingEnd ℂ) hpolar
  rw [map_mul, Complex.conj_ofReal] at hconj
  calc ((foMod b b' i : ℝ) : ℂ)
      = ((foMod b b' i : ℝ) : ℂ) * ((starRingEnd ℂ) (foPhase b b' i) * foPhase b b' i) := by
        rw [conj_mul_self_of_norm_one (norm_foPhase b b' i), mul_one]
    _ = (starRingEnd ℂ) (foAmp b b' i) * foPhase b b' i := by
        rw [← mul_assoc, hconj]

/-! ### The diagonal phase unitary -/

/-- The multi-index power `ζ^α = ∏ᵢ ζᵢ^{αᵢ}`. -/
noncomputable def phasePow (zeta : Fin d → ℂ) (a : Fin d →₀ ℕ) : ℂ := ∏ i, zeta i ^ (a i)

theorem norm_phasePow (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) (a : Fin d →₀ ℕ) :
    ‖phasePow zeta a‖ = 1 := by
  rw [phasePow, norm_prod]
  exact Finset.prod_eq_one fun i _ => by rw [norm_pow, hzn i, one_pow]

theorem phasePow_ne_zero (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) (a : Fin d →₀ ℕ) :
    phasePow zeta a ≠ 0 := by
  intro h
  have := norm_phasePow zeta hzn a
  rw [h] at this
  simp at this

theorem phasePow_add_single (zeta : Fin d → ℂ) (i : Fin d) (a : Fin d →₀ ℕ) :
    phasePow zeta (a + Finsupp.single i 1) = phasePow zeta a * zeta i := by
  classical
  have h : ∀ j : Fin d, zeta j ^ ((a + Finsupp.single i 1 : Fin d →₀ ℕ) j)
      = zeta j ^ (a j) * (if j = i then zeta i else 1) := by
    intro j
    have hj : ((a + Finsupp.single i 1 : Fin d →₀ ℕ) j) = a j + (if j = i then 1 else 0) := by
      simp [Finsupp.single_apply, eq_comm]
    rw [hj, pow_add]
    split_ifs with hji
    · rw [hji, pow_one]
    · rw [pow_zero]
  rw [phasePow, phasePow, Finset.prod_congr rfl fun j _ => h j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i (fun _ => zeta i)]
  simp

theorem phasePow_sub_single (zeta : Fin d → ℂ) {i : Fin d} {a : Fin d →₀ ℕ} (ha : 0 < a i) :
    phasePow zeta (a - Finsupp.single i 1) * zeta i = phasePow zeta a := by
  classical
  have h : ∀ j : Fin d, zeta j ^ ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j)
      * (if j = i then zeta i else 1) = zeta j ^ (a j) := by
    intro j
    have hj : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j) = a j - (if j = i then 1 else 0) := by
      simp [Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
    rw [hj]
    split_ifs with hji
    · subst hji
      rw [← pow_succ]
      congr 1
      omega
    · rw [mul_one, Nat.sub_zero]
  rw [phasePow, phasePow, ← Finset.prod_congr rfl fun j _ => h j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i (fun _ => zeta i)]
  simp

/-- The phase-rotated product Hermite family `ζ^α ψ_α`. -/
noncomputable def phaseFamily (zeta : Fin d → ℂ) (a : Fin d →₀ ℕ) : L2d d :=
  phasePow zeta a • hermiteMvLp a

theorem orthonormal_phaseFamily (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    Orthonormal ℂ (phaseFamily (d := d) zeta) := by
  classical
  rw [orthonormal_iff_ite]
  intro a c
  rw [phaseFamily, phaseFamily, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (orthonormal_hermiteMvLp (d := d)) a c]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, mul_one, conj_mul_self_of_norm_one (norm_phasePow zeta hzn a)]
  · rw [if_neg hac, mul_zero, mul_zero]

theorem span_phaseFamily (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    Submodule.span ℂ (Set.range (phaseFamily (d := d) zeta)) = polyGaussCore (d := d) := by
  rw [← span_hermiteMvLp]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hrw : hermiteMvLp (d := d) a = (phasePow zeta a)⁻¹ • phaseFamily zeta a := by
      rw [phaseFamily, smul_smul, inv_mul_cancel₀ (phasePow_ne_zero zeta hzn a), one_smul]
    change hermiteMvLp (d := d) a ∈ Submodule.span ℂ (Set.range (phaseFamily (d := d) zeta))
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- The phase-rotated product Hermite functions are again a Hilbert basis. -/
noncomputable def phaseBasis (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    HilbertBasis (Fin d →₀ ℕ) ℂ (L2d d) :=
  HilbertBasis.mk (orthonormal_phaseFamily zeta hzn)
    (by
      rw [span_phaseFamily zeta hzn]
      have hd := polyGaussCore_dense (d := d)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

/-- **The phase unitary**: the unitary of `L²(ℝᵈ)` which multiplies the `α`-th product
Hermite function by `ζ^α`.  For `ζᵢ = e^{iθᵢ}` this is the metaplectic rotation
`e^{iθ·N}` generated by the number operators. -/
noncomputable def phaseU (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) : L2d d ≃ₗᵢ[ℂ] L2d d :=
  (hermiteMvBasis (d := d)).repr.trans (phaseBasis zeta hzn).repr.symm

theorem phaseU_hermiteMvLp (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) (a : Fin d →₀ ℕ) :
    phaseU zeta hzn (hermiteMvLp (d := d) a) = phasePow zeta a • hermiteMvLp a := by
  classical
  have h1 : (hermiteMvBasis (d := d)).repr (hermiteMvLp a) = lp.single 2 a 1 := by
    rw [← hermiteMvBasis_apply]
    exact HilbertBasis.repr_self _ a
  have h2 : (phaseBasis (d := d) zeta hzn).repr.symm (lp.single 2 a 1)
      = phaseFamily (d := d) zeta a := by
    rw [HilbertBasis.repr_symm_single, phaseBasis, HilbertBasis.coe_mk]
  rw [phaseU, LinearIsometryEquiv.trans_apply, h1, h2, phaseFamily]

theorem phaseU_mem_core (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1)
    (v : polyGaussCore (d := d)) :
    phaseU zeta hzn (v : L2d d) ∈ polyGaussCore (d := d) := by
  have main : ∀ y : L2d d, y ∈ Submodule.span ℂ (Set.range (hermiteMvLp (d := d))) →
      phaseU zeta hzn y ∈ polyGaussCore (d := d) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        rw [phaseU_hermiteMvLp]
        exact Submodule.smul_mem _ _ (hermiteMvLp_mem_core a)
    | zero => simp
    | add z w _ _ ihz ihw =>
        rw [map_add]
        exact Submodule.add_mem _ ihz ihw
    | smul r z _ ih =>
        rw [map_smul]
        exact Submodule.smul_mem _ _ ih
  exact main (v : L2d d) (by rw [span_hermiteMvLp]; exact v.2)

/-- The phase unitary, as an operator of the core. -/
noncomputable def phaseCore (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1) :
    polyGaussCore (d := d) →ₗ[ℂ] polyGaussCore (d := d) where
  toFun v := ⟨phaseU zeta hzn (v : L2d d), phaseU_mem_core zeta hzn v⟩
  map_add' u v := Subtype.ext (by simp)
  map_smul' c v := Subtype.ext (by simp)

@[simp] theorem phaseCore_coe (zeta : Fin d → ℂ) (hzn : ∀ i, ‖zeta i‖ = 1)
    (v : polyGaussCore (d := d)) :
    ((phaseCore zeta hzn v : polyGaussCore (d := d)) : L2d d) = phaseU zeta hzn (v : L2d d) := rfl

/-! ### The rotation of the quadrature -/

set_option maxHeartbeats 1600000 in
-- the core coercions make the elaboration of this one identity expensive
/-- **The phase unitary rotates the quadrature**: on a product Hermite function it carries
the positional quadrature `∑ᵢ|wᵢ|xᵢ` onto `∑ᵢ(bᵢxᵢ + b'ᵢπᵢ)`. -/
theorem phaseU_foOp_hermiteCore (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    phaseU (foPhase b b') (norm_foPhase b b') (foOp (foMod b b') 0 (hermiteCore a))
      = foOp b b' (phaseCore (foPhase b b') (norm_foPhase b b') (hermiteCore a)) := by
  classical
  have hpc : phaseCore (foPhase b b') (norm_foPhase b b') (hermiteCore a)
      = phasePow (foPhase b b') a • hermiteCore a := by
    refine Subtype.ext ?_
    rw [phaseCore_coe, hermiteCore_coe, phaseU_hermiteMvLp, Submodule.coe_smul, hermiteCore_coe]
  rw [hpc, map_smul, foOp_hermiteCore, foOp_hermiteCore, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_smul, map_smul, phaseU_hermiteMvLp, phaseU_hermiteMvLp, smul_add,
    smul_smul, smul_smul, smul_smul, smul_smul, foAmp_real, Complex.conj_ofReal]
  have hup : ((foMod b b' i : ℝ) : ℂ) * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)
      * phasePow (foPhase b b') (a + Finsupp.single i 1)
      = phasePow (foPhase b b') a * (foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)) := by
    rw [phasePow_add_single, ← foMod_mul_foPhase b b' i]
    ring
  have hdown : ((foMod b b' i : ℝ) : ℂ) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ)
      * phasePow (foPhase b b') (a - Finsupp.single i 1)
      = phasePow (foPhase b b') a
        * ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ)) := by
    rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
    · have hs : ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) = 0 := by
        rw [h0]
        simp
      rw [hs]
      ring
    · rw [← phasePow_sub_single (foPhase b b') hpos]
      rw [foMod_eq_conj_mul_foPhase b b' i]
      ring
  rw [hup, hdown]

/-- **HEADLINE.**  For arbitrary real coefficients `b, b'` the quadrature
`∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint on the Gauss–polynomial (product Hermite)
core of `L²(ℝᵈ)`. -/
theorem foOp_essentiallySelfAdjoint (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (foOp b b') := by
  refine BookProof.NavierStokesFlow.SignFlip.essentiallySelfAdjointOn_of_intertwine
    (phaseU (foPhase b b') (norm_foPhase b b')) (foOp (foMod b b') 0) (foOp b b')
    (phaseU_mem_core _ _) ?_ (foOp_pos_essentiallySelfAdjoint (foMod b b'))
  have hEq :
      ((phaseU (foPhase b b') (norm_foPhase b b')).toLinearEquiv.toLinearMap
          ∘ₗ foOp (foMod b b') 0)
        = (foOp b b' ∘ₗ phaseCore (foPhase b b') (norm_foPhase b b')) := by
    refine linearMap_ext_of_span (hermiteMvLp (d := d)) span_hermiteMvLp hermiteMvLp_mem_core
      _ _ fun a => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hermiteCore_eq]
    exact phaseU_foOp_hermiteCore b b' a
  intro v
  exact congrArg (fun F : polyGaussCore (d := d) →ₗ[ℂ] L2d d => F v) hEq

/-- **The quadrature generates a complete unitary flow.**  Stone's theorem applied to the
closure of `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`. -/
theorem foOp_stone_flow (b b' : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (foOp b b') T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense (foOp_symmetric b b')
    (foOp_essentiallySelfAdjoint b b')

end BookProof.QuadratureEsa


