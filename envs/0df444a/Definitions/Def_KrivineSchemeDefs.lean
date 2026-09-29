-- Prove2me | Definitions.Def_KrivineSchemeDefs
-- name    : KrivineSchemeDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T18:22:00.244094+00:00
-- url     : https://prove2.me/theorems/ba2f4c52-cbaf-4f11-8520-2c8d0bc987bb
-- title:
--   Krivine schemes and the normalized correlation function $H(t)$
-- statement:
--   This file formalizes the rounding schemes through which upper bounds on the Grothendieck constant are obtained, together with the analytic object that measures their quality.
--
--   A **Krivine scheme** of dimension $k$ is a pair of partitions of $\mathbb R^k$ into a $+1$ region and a $-1$ region, encoded by two measurable odd functions $f,g:\mathbb R^k\to\{\pm1\}$. To round a semidefinite solution one maps each vector to a Gaussian point of $\mathbb R^k$, correlated according to the inner products, and labels it by the region its point falls in; the choice $f=g=\operatorname{sgn}(z_1)$ is random hyperplane rounding.
--
--   The quality of a scheme is carried by its **normalized correlation function**
--
--   $$H(t)=\frac{\pi}{2}\,\mathbb E\bigl[f(X)\,g(Y)\bigr],$$
--
--   where $X,Y$ are standard Gaussian vectors of $\mathbb R^k$ whose coordinates are pairwise correlated, $\mathbb E[X_iY_i]=t$. For the half-space partition one has $H(t)=\arcsin t$, the classical identity behind Krivine's bound. Writing the odd expansion $H(t)=b_1t+b_3t^3+\cdots$, the hyperplane scheme sits at $(b_1,b_3)=(1,\tfrac16)$.
--
--   These coefficients are the quantities constrained by the lower-bound theorem of the source paper, and they are linear functionals of the scheme, which is what lets a constraint on them survive mixing and limits of schemes.
--
--   **Formalization Note** The expectation is written as an explicit double integral against the density of a correlated Gaussian pair, namely the product over coordinates of $\frac{1}{2\pi\sqrt{1-t^2}}\exp\bigl(-\frac{a^2-2tab+b^2}{2(1-t^2)}\bigr)$; the density is meaningful for $|t|<1$. The coefficients $b_1$ and $b_3$ are read off as $H'(0)$ and $H'''(0)/6$. Oddness is imposed almost everywhere rather than at every point: no $\pm1$-valued function can satisfy $f(-0)=-f(0)$ at the origin, and the quantity that matters, the Gaussian expectation, is insensitive to null sets. With that convention the half-space partition is a scheme in every dimension $k\ge1$, and the file exhibits it, so the notion is not vacuous; dimension $k=0$ carries no scheme.
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, pp. 4-5 ("Rounding schemes as partitions" and "The normalized correlation function"); Figure 2.

import Mathlib

namespace GrothendieckConstant

open MeasureTheory Real

/-- Joint density on `ℝ^k × ℝ^k` of two standard Gaussian vectors whose
coordinates are pairwise correlated with correlation `t`. -/
noncomputable def gaussianPairDensity (k : ℕ) (t : ℝ) (x y : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, (1 / (2 * π * Real.sqrt (1 - t ^ 2))) *
    Real.exp (-(x i ^ 2 - 2 * t * x i * y i + y i ^ 2) / (2 * (1 - t ^ 2)))

/-- A Krivine scheme in dimension `k`: a pair of measurable, odd, ±1-valued
functions on `ℝ^k`, i.e. a pair of partitions of `ℝ^k` into a `+1` and a `-1` region.
Oddness is required almost everywhere: a `±1`-valued function cannot be odd at the
origin, and only the null-set-invariant Gaussian expectation of the pair matters. -/
structure KrivineScheme (k : ℕ) where
  f : (Fin k → ℝ) → ℝ
  g : (Fin k → ℝ) → ℝ
  measurable_f : Measurable f
  measurable_g : Measurable g
  f_sign : ∀ z, f z = 1 ∨ f z = -1
  g_sign : ∀ z, g z = 1 ∨ g z = -1
  f_odd : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), f (-z) = -f z
  g_odd : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), g (-z) = -g z

/-- The half-space scheme underlying random hyperplane rounding, which exists in
every dimension `k ≥ 1`; in particular `KrivineScheme k` is inhabited for `k ≥ 1`. -/
noncomputable def halfspaceScheme (k : ℕ) (hk : 0 < k) : KrivineScheme k where
  f := fun z => if 0 < z ⟨0, hk⟩ then 1 else -1
  g := fun z => if 0 < z ⟨0, hk⟩ then 1 else -1
  measurable_f := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const (measurable_pi_apply _)
  measurable_g := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const (measurable_pi_apply _)
  f_sign := by intro z; by_cases h : 0 < z ⟨0, hk⟩ <;> simp [h]
  g_sign := by intro z; by_cases h : 0 < z ⟨0, hk⟩ <;> simp [h]
  f_odd := by
    have h0 : (volume : Measure (Fin k → ℝ)) {z : Fin k → ℝ | z ⟨0, hk⟩ = 0} = 0 :=
      Measure.pi_hyperplane _ _ _
    have hae : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), z ⟨0, hk⟩ ≠ 0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [hae] with z hz
    rcases lt_or_gt_of_ne hz with h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos (by simpa using neg_pos.mpr h)]; norm_num
    · rw [if_pos h, if_neg (by simpa using not_lt.mpr (neg_nonpos.mpr h.le))]
  g_odd := by
    have h0 : (volume : Measure (Fin k → ℝ)) {z : Fin k → ℝ | z ⟨0, hk⟩ = 0} = 0 :=
      Measure.pi_hyperplane _ _ _
    have hae : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), z ⟨0, hk⟩ ≠ 0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [hae] with z hz
    rcases lt_or_gt_of_ne hz with h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos (by simpa using neg_pos.mpr h)]; norm_num
    · rw [if_pos h, if_neg (by simpa using not_lt.mpr (neg_nonpos.mpr h.le))]

/-- The normalized correlation function `H(t) = (π/2) * E[f(X) g(Y)]`, where `X, Y`
are standard Gaussian vectors in `ℝ^k` with `E[X i * Y i] = t` coordinatewise. -/
noncomputable def correlationFunction {k : ℕ} (S : KrivineScheme k) (t : ℝ) : ℝ :=
  (π / 2) * ∫ x : Fin k → ℝ, ∫ y : Fin k → ℝ,
    S.f x * S.g y * gaussianPairDensity k t x y

/-- The linear coefficient `b₁` of `H(t) = b₁ t + b₃ t³ + ⋯`, as `H'(0)`. -/
noncomputable def coeffLinear {k : ℕ} (S : KrivineScheme k) : ℝ :=
  deriv (correlationFunction S) 0

/-- The cubic coefficient `b₃` of `H(t) = b₁ t + b₃ t³ + ⋯`, as `H'''(0)/6`. -/
noncomputable def coeffCubic {k : ℕ} (S : KrivineScheme k) : ℝ :=
  iteratedDeriv 3 (correlationFunction S) 0 / 6

end GrothendieckConstant


