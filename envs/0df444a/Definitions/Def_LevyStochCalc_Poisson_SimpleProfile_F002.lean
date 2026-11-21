-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F002
-- name    : LevyStochCalc_Poisson_SimpleProfile_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:13:07.552572+00:00
-- url     : https://prove2.me/theorems/8027669f-aa8a-4258-ab3b-d59978831103
-- title:
--   Source declarations: LevyStochCalc.Poisson.SimpleProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SimpleProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F001
import Definitions.Def_SourceProof_dc0655f17321fa2fa8890ee8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple mark profiles and their compensated step integrals

A *simple mark profile* for an intensity `ν` on the mark space is a finite family of pairwise
disjoint mark sets of finite intensity carrying constant coefficients, `∑ₖ cₖ 𝟙_{Bₖ}`. Every
square-integrable mark profile is the `L²(ν)` limit of simple profiles, obtained from the nonzero
level sets of square-integrable simple functions approximating it in `L²(ν)`; a bounded one is
the limit of simple profiles obeying the same bound, obtained from the simple functions
approximating it inside the interval the bound cuts out.

The compensated integral of a simple profile over the step `(a, b]` is
`∑ₖ cₖ Ñ((a, b] × Bₖ)`. The `L²(P)` pairing of two such integrals over a common step is
`(b − a) ∫ f g dν`, so profiles converging in `L²(ν)` have compensated integrals converging in
`L²(P)`.

## Main definitions

* `LevyStochCalc.Poisson.SimpleProfile` — a simple mark profile.
* `LevyStochCalc.Poisson.SimpleProfile.toFun` — the function it carries.
* `LevyStochCalc.Poisson.SimpleProfile.stepIntegral` — its compensated integral over a step.

## Main statements

* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2_of_memLp` — approximation of a
  square-integrable mark profile by simple profiles.
* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` — approximation of a bounded
  square-integrable mark profile by simple profiles obeying the same bound.
* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` — the `L²(P)` pairing of two
  compensated step integrals.
* `LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub` — the isometry
  `‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`.
* `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` — convergence of the compensated
  integrals in `L²(P)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

/-! ### The compensated integral of a simple profile over a step -/

variable (N : PoissonRandomMeasure P ν)

/-- Expansion of the integral of the square of a difference. -/
private theorem integral_sub_sq_aux {α : Type*} [MeasurableSpace α] (m : Measure α)
    (F F' : α → ℝ) (h11 : Integrable (fun x => F x * F x) m)
    (h12 : Integrable (fun x => F x * F' x) m) (h21 : Integrable (fun x => F' x * F x) m)
    (h22 : Integrable (fun x => F' x * F' x) m) :
    ∫ x, (F x - F' x) ^ 2 ∂m
      = ∫ x, F x * F x ∂m - ∫ x, F x * F' x ∂m - ∫ x, F' x * F x ∂m + ∫ x, F' x * F' x ∂m := by
  have h2 : Integrable (fun x => F x * F x - F x * F' x) m := h11.sub h12
  have h1 : Integrable (fun x => F x * F x - F x * F' x - F' x * F x) m := h2.sub h21
  rw [show (fun x => (F x - F' x) ^ 2)
      = fun x => F x * F x - F x * F' x - F' x * F x + F' x * F' x from by funext x; ring,
    integral_add h1 h22, integral_sub h2 h21, integral_sub h11 h12]
/-- **The isometry at a step, in second-moment form.** The second moment of the difference of
the compensated step integrals of two simple mark profiles is the step length times the
`L²(ν)` distance of their functions, squared. -/
theorem integral_stepIntegral_sub_sq (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ ω, (G.stepIntegral N a b ω - G'.stepIntegral N a b ω) ^ 2 ∂P
      = (b - a) * ∫ e, (G.toFun e - G'.toFun e) ^ 2 ∂ν := by
  have hP : ∀ H H' : SimpleProfile E ν, Integrable (fun ω =>
      H.stepIntegral N a b ω * H'.stepIntegral N a b ω) P :=
    fun H H' => (H.memLp_stepIntegral N ha b).integrable_mul (H'.memLp_stepIntegral N ha b)
  have hν : ∀ H H' : SimpleProfile E ν, Integrable (fun e => H.toFun e * H'.toFun e) ν :=
    fun H H' => H.memLp_toFun.integrable_mul H'.memLp_toFun
  rw [integral_sub_sq_aux P _ _ (hP G G) (hP G G') (hP G' G) (hP G' G'),
    integral_sub_sq_aux ν _ _ (hν G G) (hν G G') (hν G' G) (hν G' G'),
    _root_.Prove2MeSourceProof.h_dc0655f17321fa2fa8890ee8 N G G ha hab, _root_.Prove2MeSourceProof.h_dc0655f17321fa2fa8890ee8 N G G' ha hab,
    _root_.Prove2MeSourceProof.h_dc0655f17321fa2fa8890ee8 N G' G ha hab, _root_.Prove2MeSourceProof.h_dc0655f17321fa2fa8890ee8 N G' G' ha hab]
  ring
/-- The `L²` seminorm of a square-integrable real function through its second moment. -/
private theorem eLpNorm_two_eq_ofReal {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F : α → ℝ} (hF : MemLp F 2 m) :
    eLpNorm F 2 m = (ENNReal.ofReal (∫ x, F x ^ 2 ∂m)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞).toReal = 2 from by norm_num,
    ← Compensated.lintegral_sq_eq_ofReal_integral hF]
  refine congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (lintegral_congr fun x => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl
/-- **The isometry at a step.** The `L²(P)` distance of the compensated step integrals of two
simple mark profiles is the square root of the step length times their `L²(ν)` distance. -/
theorem eLpNorm_stepIntegral_sub (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    eLpNorm (fun ω => G.stepIntegral N a b ω - G'.stepIntegral N a b ω) 2 P
      = ENNReal.ofReal (Real.sqrt (b - a))
        * eLpNorm (fun e => G.toFun e - G'.toFun e) 2 ν := by
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hPsub : MemLp (fun ω => G.stepIntegral N a b ω - G'.stepIntegral N a b ω) 2 P :=
    (G.memLp_stepIntegral N ha b).sub (G'.memLp_stepIntegral N ha b)
  have hνsub : MemLp (fun e => G.toFun e - G'.toFun e) 2 ν := G.memLp_toFun.sub G'.memLp_toFun
  rw [eLpNorm_two_eq_ofReal hPsub, eLpNorm_two_eq_ofReal hνsub,
    integral_stepIntegral_sub_sq N G G' ha hab,
    ENNReal.ofReal_mul hba, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hba (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sqrt_eq_rpow]
/-! ### Simple profiles from simple functions -/

/-- The nonzero values of a simple function on the mark space, indexed by a finite type. -/
private noncomputable def nzValue (g : SimpleFunc E ℝ) : Fin (g.range.erase 0).card → ℝ :=
  fun k => (((g.range.erase 0).equivFin.symm k : {x // x ∈ g.range.erase 0}) : ℝ)
private theorem nzValue_injective (g : SimpleFunc E ℝ) : Function.Injective (nzValue g) :=
  fun _ _ hkl => (g.range.erase 0).equivFin.symm.injective (Subtype.ext hkl)
private theorem nzValue_ne_zero (g : SimpleFunc E ℝ) (k : Fin (g.range.erase 0).card) :
    nzValue g k ≠ 0 :=
  Finset.ne_of_mem_erase ((g.range.erase 0).equivFin.symm k).2
private theorem sum_nzValue_indicator (g : SimpleFunc E ℝ) (e : E) :
    ∑ k, nzValue g k * (g ⁻¹' {nzValue g k}).indicator (fun _ => (1 : ℝ)) e = g e := by
  classical
  by_cases h0 : g e = 0
  · refine (Finset.sum_eq_zero fun k _ => ?_).trans h0.symm
    rw [Set.indicator_of_notMem (by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, h0]
      exact fun hc => nzValue_ne_zero g k hc.symm), mul_zero]
  · have hmem : g e ∈ g.range.erase 0 := Finset.mem_erase.2 ⟨h0, g.mem_range_self e⟩
    have hvk : nzValue g ((g.range.erase 0).equivFin ⟨g e, hmem⟩) = g e := by
      simp [nzValue]
    refine (Finset.sum_eq_single ((g.range.erase 0).equivFin ⟨g e, hmem⟩)
      (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · rw [Set.indicator_of_notMem (by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact fun hc => hk (nzValue_injective g (hvk.trans hc)).symm), mul_zero]
    · rw [Set.indicator_of_mem (by simp [hvk]), mul_one, hvk]
/-- The simple mark profile carried by the nonzero level sets of a square-integrable simple
function on the mark space. -/
noncomputable def ofSimpleFunc {g : SimpleFunc E ℝ} (hg : MemLp g 2 ν) : SimpleProfile E ν where
  K := (g.range.erase 0).card
  B := fun k => g ⁻¹' {nzValue g k}
  B_measurable := fun k => g.measurableSet_fiber _
  B_disjoint := fun k l hkl => Set.disjoint_left.2 fun e he he' => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at he he'
    exact hkl (nzValue_injective g (he.symm.trans he'))
  B_finite := fun k => (SimpleFunc.measure_preimage_lt_top_of_memLp (by norm_num) (by norm_num)
    g hg _ (nzValue_ne_zero g k)).ne
  c := nzValue g
omit [SigmaFinite ν] in
@[simp] theorem toFun_ofSimpleFunc {g : SimpleFunc E ℝ} (hg : MemLp g 2 ν) (e : E) :
    (ofSimpleFunc hg).toFun e = g e :=
  sum_nzValue_indicator g e
end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

/-! ### Convergence of the compensated step integrals -/

end LevyStochCalc.Poisson


