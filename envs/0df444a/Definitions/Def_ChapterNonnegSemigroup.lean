-- Prove2me | Definitions.Def_ChapterNonnegSemigroup
-- name    : ChapterNonnegSemigroup
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T14:29:48.063372+00:00
-- url     : https://prove2.me/theorems/09a6eaba-421c-4011-add0-867c546e314b
-- title:
--   The Lean 4 theorem `commute_expNeg` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNonnegSemigroup.lean`): generated def bundle for ChapterNonnegSemigroup. See BookProof/ChapterNonnegSemigroup.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNonnegSemigroup.lean

import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Mathlib

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The contraction semigroup `e^{-tT}` of a non-negative self-adjoint linear relation

`BookProof.ChapterNonnegResolvent` produced, for a non-negative self-adjoint linear
relation `T` on a complex Hilbert space `F`, the resolvent family `R a = (T + a)⁻¹` and
the **Yosida approximation** `T_a = a (1 − a R a)`: bounded, self-adjoint, non-negative
operators with `T_a h → k` for `(h, k) ∈ T`.  `BookProof.ChapterNonnegUnitaryGroup` turned
that approximation into the *unitary group* `e^{-itT}`.  This chapter runs the same
machine on the *real* exponential and produces the **heat semigroup** `e^{-tT}`: the
object that turns a spectral lower bound into a decay rate, and the analytic input the
consolidated plan asks for on the operator thread.

## The exponential of a bounded non-negative operator

`expNeg A t = e^{-tA}` for a bounded `A`.  It satisfies `expNeg A 0 = 1`
(`expNeg_zero`), the semigroup law (`expNeg_add`), the differential equation
`d/dt e^{-tA}x = -A e^{-tA}x` (`hasDerivAt_expNeg`), and — this is where non-negativity
enters — the **contraction bound** `‖e^{-tA}x‖ ≤ ‖x‖` for `t ≥ 0` (`norm_expNeg_le`),
obtained by showing that `s ↦ ‖e^{-sA}x‖²` has non-positive derivative
`-2 Re⟪A e^{-sA}x, e^{-sA}x⟫`.

The quantitative comparison of two generators is the **Cauchy estimate**
`‖e^{-tA}x − e^{-tB}x‖ ≤ t ‖Ax − Bx‖` for commuting non-negative `A, B`
(`norm_expNeg_sub_expNeg_le`), proved by differentiating the interpolating path
`s ↦ e^{-sA} e^{-(t-s)B} x` along `[0, t]` (`hasDerivAt_interp`).

## The limit semigroup

The Yosida approximations commute, so the approximating semigroups
`approxS hT n t = e^{-tT_{n+1}}` are Cauchy at every point of the domain
(`approxS_cauchy_of_mem`) and — the domain being dense for single-valued `T` — at every
vector (`approxS_cauchy`).  Its limit is

* **`semigroupS hT hsv t = e^{-tT}`** (`tendsto_semigroupS`), a contraction
  (`norm_semigroupS_apply_le`), self-adjoint (`isSelfAdjoint_semigroupS`), equal to `1`
  at `t = 0` (`semigroupS_zero`) and satisfying the **semigroup law**
  `S (s + t) = S s ∘ S t` for `s, t ≥ 0` (`semigroupS_add`).

Its rate of convergence on the domain is `‖e^{-tT}h − e^{-tT_m}h‖ ≤ t ‖k − T_m h‖`
(`norm_semigroupS_sub_approxS_le`), which gives `‖e^{-tT}h − h‖ ≤ t‖k‖` on the domain
(`norm_semigroupS_sub_self_le_of_mem`) and hence **strong continuity at `0`**
(`tendsto_semigroupS_zero`).
-/

namespace BookProof.NonnegSemigroup

open BookProof.ClosureUniqueness BookProof.PositiveSquareRoot BookProof.NonnegResolvent
open BookProof.NonnegUnitaryGroup
open Filter Topology NormedSpace
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

noncomputable local instance ratNormedAlgebra' : NormedAlgebra ℚ (F →L[ℂ] F) :=
  NormedAlgebra.restrictScalars ℚ ℂ (F →L[ℂ] F)

/-! ## The exponential of a bounded operator -/

/-- `e^{-tA}` for a bounded operator `A`. -/
noncomputable def expNeg (A : F →L[ℂ] F) (t : ℝ) : F →L[ℂ] F :=
  NormedSpace.exp ((-t : ℝ) • A)

@[simp] theorem expNeg_zero (A : F →L[ℂ] F) : expNeg A 0 = 1 := by
  simp [expNeg]

@[simp] theorem expNeg_zero_op (t : ℝ) : expNeg (0 : F →L[ℂ] F) t = 1 := by
  simp [expNeg]



/-- `A` commutes with `e^{-sA}`. -/
theorem commute_expNeg (A : F →L[ℂ] F) (s : ℝ) (x : F) :
    expNeg A s (A x) = A (expNeg A s x) := by
  have hc : Commute A (NormedSpace.exp ((-s : ℝ) • A)) :=
    ((Commute.refl A).smul_right _).exp_right
  have h := congrArg (fun S : F →L[ℂ] F => S x) hc
  simpa [expNeg, ContinuousLinearMap.mul_apply] using h.symm



/-- **The differential equation** `d/dt e^{-tA}x = -A e^{-tA}x`. -/
theorem hasDerivAt_expNeg (A : F →L[ℂ] F) (s : ℝ) (x : F) :
    HasDerivAt (fun u : ℝ => expNeg A u x) (-(expNeg A s (A x))) s := by
  have h1 := hasDerivAt_exp_smul_const A (-s)
  have h2 : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) s := (hasDerivAt_id s).neg
  have h3 := h1.scomp s h2
  set E : (F →L[ℂ] F) →L[ℝ] F := (ContinuousLinearMap.apply ℂ F x).restrictScalars ℝ with hE
  have h4 := (E.hasFDerivAt (x := NormedSpace.exp ((-s : ℝ) • A))).comp_hasDerivAt s h3
  simpa [hE, expNeg, Function.comp_def, ContinuousLinearMap.mul_apply] using h4

/-- The operator-valued derivative `d/ds e^{-sA} = -e^{-sA}A`. -/
theorem hasDerivAt_expNegOp (A : F →L[ℂ] F) (s : ℝ) :
    HasDerivAt (fun u : ℝ => expNeg A u) (-(expNeg A s * A)) s := by
  have h1 := hasDerivAt_exp_smul_const A (-s)
  have h2 : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) s := (hasDerivAt_id s).neg
  simpa [expNeg, Function.comp_def] using h1.scomp s h2

/-- The operator-valued derivative `d/ds e^{-(t-s)B} = e^{-(t-s)B}B`. -/
theorem hasDerivAt_expNegOp_sub (B : F →L[ℂ] F) (t s : ℝ) :
    HasDerivAt (fun u : ℝ => expNeg B (t - u)) (expNeg B (t - s) * B) s := by
  have h1 := hasDerivAt_exp_smul_const B (-(t - s))
  have h2 : HasDerivAt (fun u : ℝ => -(t - u)) (1 : ℝ) s := by
    simpa [neg_sub] using (hasDerivAt_id s).sub_const t
  simpa [expNeg, Function.comp_def] using h1.scomp s h2

/-! ## Contraction -/

/-- `d/dt ‖e^{-tA}x‖² = -2 Re⟪A e^{-tA}x, e^{-tA}x⟫`. -/
theorem hasDerivAt_normSq_expNeg (A : F →L[ℂ] F) (x : F) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ‖expNeg A t x‖ ^ 2)
      (-2 * (inner ℂ (A (expNeg A s x)) (expNeg A s x) : ℂ).re) s := by
  have h1 : HasDerivAt (fun t : ℝ => expNeg A t x) (-(A (expNeg A s x))) s := by
    simpa [commute_expNeg] using hasDerivAt_expNeg A s x
  have h2 := h1.inner ℂ h1
  have h3 := (Complex.reCLM.hasFDerivAt
    (x := (inner ℂ (expNeg A s x) (expNeg A s x) : ℂ))).comp_hasDerivAt s h2
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.add_re, inner_neg_right,
    inner_neg_left, Complex.neg_re] at h3
  have hrw : ∀ t : ℝ, ((inner ℂ (expNeg A t x) (expNeg A t x) : ℂ)).re = ‖expNeg A t x‖ ^ 2 :=
    fun t => inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hcs : (starRingEnd ℂ) (inner ℂ (A (expNeg A s x)) (expNeg A s x) : ℂ)
      = (inner ℂ (expNeg A s x) (A (expNeg A s x)) : ℂ) := inner_conj_symm _ _
  have hconj : (inner ℂ (expNeg A s x) (A (expNeg A s x)) : ℂ).re
      = (inner ℂ (A (expNeg A s x)) (expNeg A s x) : ℂ).re := by
    rw [← hcs]; exact Complex.conj_re _
  simp only [hrw] at h3
  convert h3 using 1 <;> (first | rfl | (rw [hconj]; ring))

/-- For `A ≥ 0` the squared norm along the orbit is antitone. -/
theorem antitone_normSq_expNeg (A : F →L[ℂ] F) (hA : 0 ≤ A) (x : F) :
    Antitone (fun s : ℝ => ‖expNeg A s x‖ ^ 2) := by
  have hpos := (ContinuousLinearMap.isPositive_iff_complex A).1
    ((ContinuousLinearMap.nonneg_iff_isPositive A).1 hA)
  refine antitone_of_deriv_nonpos
    (fun s => (hasDerivAt_normSq_expNeg A x s).differentiableAt) (fun s => ?_)
  rw [(hasDerivAt_normSq_expNeg A x s).deriv]
  have hs := (hpos (expNeg A s x)).2
  simp only [RCLike.re_to_complex] at hs
  nlinarith

/-- **The contraction bound** `‖e^{-tA}x‖ ≤ ‖x‖` for `t ≥ 0` and `A ≥ 0`. -/
theorem norm_expNeg_le (A : F →L[ℂ] F) (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖expNeg A t x‖ ≤ ‖x‖ := by
  have h := antitone_normSq_expNeg A hA x ht
  simp only [expNeg_zero, ContinuousLinearMap.one_apply] at h
  nlinarith [norm_nonneg (expNeg A t x), norm_nonneg x]

/-! ## The Cauchy estimate -/

/-- The interpolating path `s ↦ e^{-sA}e^{-(t-s)B}x` and its derivative. -/
theorem hasDerivAt_interp (A B : F →L[ℂ] F) (hcomm : Commute A B) (t s : ℝ) (x : F) :
    HasDerivAt (fun u : ℝ => (expNeg A u * expNeg B (t - u)) x)
      (expNeg A s (expNeg B (t - s) (B x - A x))) s := by
  have hprod := (hasDerivAt_expNegOp A s).mul (hasDerivAt_expNegOp_sub B t s)
  set E : (F →L[ℂ] F) →L[ℝ] F := (ContinuousLinearMap.apply ℂ F x).restrictScalars ℝ with hE
  have h4 := (E.hasFDerivAt (x := expNeg A s * expNeg B (t - s))).comp_hasDerivAt s hprod
  have hAB : (A : F →L[ℂ] F) * expNeg B (t - s) = expNeg B (t - s) * A :=
    (hcomm.smul_right (-(t - s) : ℝ)).exp_right
  simp only [hE, Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.apply_apply] at h4
  have hx := congrArg (fun S : F →L[ℂ] F => S x) hAB
  simp only [ContinuousLinearMap.mul_apply] at hx
  convert h4 using 1 <;>
    first
    | (funext u; rfl)
    | (simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.neg_apply, map_sub, hx]; abel)

/-- **The Cauchy estimate**: for commuting non-negative bounded operators,
`‖e^{-tA}x − e^{-tB}x‖ ≤ t ‖Ax − Bx‖`. -/
theorem norm_expNeg_sub_expNeg_le (A B : F →L[ℂ] F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcomm : Commute A B) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖expNeg A t x - expNeg B t x‖ ≤ t * ‖A x - B x‖ := by
  set g : ℝ → F := fun u => (expNeg A u * expNeg B (t - u)) x with hg
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt g (expNeg A u (expNeg B (t - u) (B x - A x))) (Set.Icc (0 : ℝ) t) u :=
    fun u _ => (hasDerivAt_interp A B hcomm t u x).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) t,
      ‖expNeg A u (expNeg B (t - u) (B x - A x))‖ ≤ ‖A x - B x‖ := by
    intro u hu
    have h1 : ‖expNeg A u (expNeg B (t - u) (B x - A x))‖
        ≤ ‖expNeg B (t - u) (B x - A x)‖ := norm_expNeg_le A hA hu.1 _
    have h2 : ‖expNeg B (t - u) (B x - A x)‖ ≤ ‖B x - A x‖ :=
      norm_expNeg_le B hB (by linarith [hu.2]) _
    have h3 : ‖B x - A x‖ = ‖A x - B x‖ := norm_sub_rev _ _
    linarith [h1.trans h2, h3.le, h3.symm.le]
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) hderiv hbound
    (convex_Icc (0 : ℝ) t) (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht)
  have hgt : g t = expNeg A t x := by simp [hg, ContinuousLinearMap.mul_apply]
  have hg0 : g 0 = expNeg B t x := by simp [hg, ContinuousLinearMap.mul_apply]
  rw [hgt, hg0] at hmain
  calc ‖expNeg A t x - expNeg B t x‖ ≤ ‖A x - B x‖ * ‖t - (0 : ℝ)‖ := hmain
    _ = t * ‖A x - B x‖ := by rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht]; ring



/-! ## The approximating semigroups `e^{-tT_a}` -/

variable {T : Submodule ℂ (F × F)}

/-- The Yosida approximations are non-negative. -/
theorem yosidaAt_nonneg (hT : IsNonnegSelfAdjoint T) (n : ℕ) : 0 ≤ yosidaAt hT n :=
  yosidaCLM_nonneg hT _

/-- The approximating semigroup `e^{-tT_{n+1}}` built from the Yosida approximation. -/
noncomputable def approxS (hT : IsNonnegSelfAdjoint T) (n : ℕ) (t : ℝ) : F →L[ℂ] F :=
  expNeg (yosidaAt hT n) t

@[simp] theorem approxS_zero (hT : IsNonnegSelfAdjoint T) (n : ℕ) : approxS hT n 0 = 1 :=
  expNeg_zero _



theorem norm_approxS_apply_le (hT : IsNonnegSelfAdjoint T) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖approxS hT n t x‖ ≤ ‖x‖ :=
  norm_expNeg_le _ (yosidaAt_nonneg hT n) ht x



/-- The Cauchy estimate for the approximating semigroups. -/
theorem norm_approxS_sub_apply_le (hT : IsNonnegSelfAdjoint T) (n m : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (x : F) :
    ‖approxS hT n t x - approxS hT m t x‖ ≤ t * ‖yosidaAt hT n x - yosidaAt hT m x‖ :=
  norm_expNeg_sub_expNeg_le _ _ (yosidaAt_nonneg hT n) (yosidaAt_nonneg hT m)
    (commute_yosidaAt hT n m) ht x

/-! ## The limit semigroup -/

omit [CompleteSpace F] in
/-- A sequence of contractions converging pointwise on a dense set converges pointwise
everywhere (Cauchy version). -/
theorem cauchySeq_of_dense_of_contraction {G : ℕ → F →L[ℂ] F} (hc : ∀ n y, ‖G n y‖ ≤ ‖y‖)
    {D : Set F} (hD : Dense D) (hCauchy : ∀ y ∈ D, CauchySeq (fun n => G n y)) (y : F) :
    CauchySeq (fun n => G n y) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨z, hz, hyz⟩ := hD.exists_dist_lt y (ε := ε / 4) (by linarith)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hCauchy z hz) (ε / 4) (by linarith)
  refine ⟨N, fun k hk l hl => ?_⟩
  have hkz : dist (G k y) (G k z) ≤ dist y z := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact hc k _
  have hlz : dist (G l z) (G l y) ≤ dist y z := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_sub_rev]; exact hc l _
  calc dist (G k y) (G l y)
      ≤ dist (G k y) (G k z) + dist (G k z) (G l z) + dist (G l z) (G l y) :=
        dist_triangle4 _ _ _ _
    _ < ε := by
        have := hN k hk l hl
        have hd : dist y z < ε / 4 := hyz
        linarith

theorem approxS_cauchy_of_mem (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {t : ℝ} (ht : 0 ≤ t) :
    CauchySeq (fun n : ℕ => approxS hT n t h) := by
  have hy : CauchySeq (fun n : ℕ => yosidaAt hT n h) := (tendsto_yosidaAt hT hsv hk).cauchySeq
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hpos : (0 : ℝ) < ε / (t + 1) := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hy _ hpos
  refine ⟨N, fun n hn m hm => ?_⟩
  have hnm := hN n hn m hm
  rw [dist_eq_norm] at hnm ⊢
  calc ‖approxS hT n t h - approxS hT m t h‖
      ≤ t * ‖yosidaAt hT n h - yosidaAt hT m h‖ := norm_approxS_sub_apply_le hT n m ht h
    _ ≤ t * (ε / (t + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

theorem approxS_cauchy (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    CauchySeq (fun n : ℕ => approxS hT n t x) := by
  refine cauchySeq_of_dense_of_contraction (G := fun n => approxS hT n t)
    (fun n y => norm_approxS_apply_le hT n ht y) (dense_domain hT hsv) ?_ x
  intro y hy
  obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hy
  have hpy : (y, p.2) ∈ T := by
    have hpe : p = (y, p.2) := by rw [← hp1]; simp
    rwa [← hpe]
  exact approxS_cauchy_of_mem hT hsv hpy ht

/-- The semigroup `e^{-tT}` generated by a non-negative self-adjoint linear relation,
as a function. -/
noncomputable def semigroupFun (hT : IsNonnegSelfAdjoint T) (t : ℝ) (x : F) : F :=
  limUnder atTop (fun n : ℕ => approxS hT n t x)

theorem tendsto_semigroupFun (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    Tendsto (fun n : ℕ => approxS hT n t x) atTop (𝓝 (semigroupFun hT t x)) := by
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (approxS_cauchy hT hsv ht x)
  rw [semigroupFun, hz.limUnder_eq]
  exact hz

theorem norm_semigroupFun_le (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖semigroupFun hT t x‖ ≤ ‖x‖ := by
  have h1 : Tendsto (fun n : ℕ => ‖approxS hT n t x‖) atTop (𝓝 ‖semigroupFun hT t x‖) :=
    (tendsto_semigroupFun hT hsv ht x).norm
  exact le_of_tendsto' h1 (fun n => norm_approxS_apply_le hT n ht x)

/-- `e^{-tT}` as a linear map. -/
noncomputable def semigroupLinear (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) : F →ₗ[ℂ] F where
  toFun x := semigroupFun hT t x
  map_add' x y := by
    refine tendsto_nhds_unique (tendsto_semigroupFun hT hsv ht (x + y)) ?_
    have h : (fun n : ℕ => approxS hT n t (x + y))
        = fun n : ℕ => approxS hT n t x + approxS hT n t y := by
      funext n; rw [map_add]
    rw [h]
    exact (tendsto_semigroupFun hT hsv ht x).add (tendsto_semigroupFun hT hsv ht y)
  map_smul' c x := by
    refine tendsto_nhds_unique (tendsto_semigroupFun hT hsv ht (c • x)) ?_
    have h : (fun n : ℕ => approxS hT n t (c • x))
        = fun n : ℕ => c • approxS hT n t x := by
      funext n; rw [map_smul]
    rw [h]
    exact (tendsto_semigroupFun hT hsv ht x).const_smul c

/-- **The contraction semigroup `e^{-tT}`** generated by a non-negative self-adjoint
linear relation. -/
noncomputable def semigroupS (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) : F →L[ℂ] F :=
  (semigroupLinear hT hsv ht).mkContinuous 1 (fun x => by
    simp only [semigroupLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    exact norm_semigroupFun_le hT hsv ht x)

@[simp] theorem semigroupS_apply (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    semigroupS hT hsv ht x = semigroupFun hT t x := rfl

theorem tendsto_semigroupS (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    Tendsto (fun n : ℕ => approxS hT n t x) atTop (𝓝 (semigroupS hT hsv ht x)) :=
  tendsto_semigroupFun hT hsv ht x



@[simp] theorem semigroupS_zero (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) : semigroupS hT hsv (le_refl (0 : ℝ)) = 1 := by
  ext x
  refine tendsto_nhds_unique (tendsto_semigroupS hT hsv (le_refl (0 : ℝ)) x) ?_
  have h : (fun n : ℕ => approxS hT n 0 x) = fun _ : ℕ => x := by
    funext n; simp
  rw [h]
  simp





/-! ## Rate of convergence and strong continuity -/







end BookProof.NonnegSemigroup


