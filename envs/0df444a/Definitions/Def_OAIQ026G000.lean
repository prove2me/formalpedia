-- Prove2me | Definitions.Def_OAIQ026G000
-- name    : OAIQ026G000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:30:52.942175+00:00
-- url     : https://prove2.me/theorems/a636c614-756c-4bba-be54-5ead1d740c71
-- title:
--   Definitions bundle OAIQ026G000 of the split of OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 698 declarations of OpenAI's Lean: 318 definitions, 11 inductive types or structures, 19 instances and 350 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.GeneralMahler.Body`, `OAI.GeneralMahler.Body.P`, `OAI.GeneralMahler.Body.cone`, `OAI.GeneralMahler.Body.off`, `OAI.GeneralMahler.Body.polarSlice`, `OAI.GeneralMahler.Body.polarVol`, `OAI.GeneralMahler.Body.productAt`, `OAI.GeneralMahler.Body.santalo`, `OAI.GeneralMahler.Body.shear`, `OAI.GeneralMahler.Bwt`, `OAI.GeneralMahler.Cert.IV`, `OAI.GeneralMahler.Cert.IV.Duo`, `OAI.GeneralMahler.Cert.IV.Has`, `OAI.GeneralMahler.Cert.IV.LeB`, `OAI.GeneralMahler.Cert.IV.Less`, `OAI.GeneralMahler.Cert.IV.Radius`, `OAI.GeneralMahler.Cert.IV.SubB`, `OAI.GeneralMahler.Cert.IV.Zabs`, `OAI.GeneralMahler.Cert.IV.Zmax`, `OAI.GeneralMahler.Cert.IV.add0`, `OAI.GeneralMahler.Cert.IV.bcChord`, `OAI.GeneralMahler.Cert.IV.c`, `OAI.GeneralMahler.Cert.IV.clampNN`, `OAI.GeneralMahler.Cert.IV.covers`, `OAI.GeneralMahler.Cert.IV.den`, `OAI.GeneralMahler.Cert.IV.eSeries`, `OAI.GeneralMahler.Cert.IV.ebox`, `OAI.GeneralMahler.Cert.IV.errLog`, `OAI.GeneralMahler.Cert.IV.esmall`, `OAI.GeneralMahler.Cert.IV.getR`, `OAI.GeneralMahler.Cert.IV.inv0`, `OAI.GeneralMahler.Cert.IV.isrt`, `OAI.GeneralMahler.Cert.IV.isum`, `OAI.GeneralMahler.Cert.IV.lbox`, `OAI.GeneralMahler.Cert.IV.lbox0`, `OAI.GeneralMahler.Cert.IV.limK`, `OAI.GeneralMahler.Cert.IV.lob` and 289 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Convex_GeneralMahler_BiWeight`, `Convex_GeneralMahler_Bias`, `Convex_GeneralMahler_BoundField`, `Convex_GeneralMahler_Budget_Blocks`, `Convex_GeneralMahler_Budget_Extract`, `Convex_GeneralMahler_Budget_Klimit`, `Convex_GeneralMahler_Budget_Tbound`, `Convex_GeneralMahler_CDF`, `Convex_GeneralMahler_Cone`, `Convex_GeneralMahler_CovHerm`, `Convex_GeneralMahler_Cutoff`, `Convex_GeneralMahler_DefectLayer`, `Convex_GeneralMahler_Density`, `Convex_GeneralMahler_Edge`, `Convex_GeneralMahler_EdgeBand`, `Convex_GeneralMahler_Entropy`, `Convex_GeneralMahler_EvalGap`, `Convex_GeneralMahler_Field`, `Convex_GeneralMahler_Frame_Diagonal`, `Convex_GeneralMahler_Frame_Sec`, `Convex_GeneralMahler_Frame_Selector`, `Convex_GeneralMahler_GainFinal`, `Convex_GeneralMahler_GainIndent`, `Convex_GeneralMahler_GaussianTail`, `Convex_GeneralMahler_Growth`, `Convex_GeneralMahler_HLayer`, `Convex_GeneralMahler_HMatrix`, `Convex_GeneralMahler_Hermite_Dense`, `Convex_GeneralMahler_Hermite_Gradient`, `Convex_GeneralMahler_Hermite_H`, `Convex_GeneralMahler_Hermite_L2`, `Convex_GeneralMahler_Hermite_Multi`, `Convex_GeneralMahler_Hermite_Pair`, `Convex_GeneralMahler_Indicator`, `Convex_GeneralMahler_Intervals_Basic`, `Convex_GeneralMahler_Intervals_Chord`, `Convex_GeneralMahler_Intervals_Elem`, `Convex_GeneralMahler_Intervals_JCalc`, `Convex_GeneralMahler_Intervals_Jet`, `Convex_GeneralMahler_Intervals_Log`, `Convex_GeneralMahler_Intervals_Trig`, `Convex_GeneralMahler_LFun`, `Convex_GeneralMahler_Laplace`, `Convex_GeneralMahler_Lift`, `Convex_GeneralMahler_Linear_Gram`, `Convex_GeneralMahler_Linear_Nu`, `Convex_GeneralMahler_Linear_Segments`, `Convex_GeneralMahler_LogDet`, `Convex_GeneralMahler_LogPath`, `Convex_GeneralMahler_Matrix`, `Convex_GeneralMahler_MatrixBox`, `Convex_GeneralMahler_MatrixDeriv`, `Convex_GeneralMahler_Middle_Bound2`, `Convex_GeneralMahler_Mills`, `Convex_GeneralMahler_MillsLog`, `Convex_GeneralMahler_MixedField`, `Convex_GeneralMahler_NtLayer`, `Convex_GeneralMahler_Orthant`, `Convex_GeneralMahler_Packet`, `Convex_GeneralMahler_Parameter`, `Convex_GeneralMahler_Polar`, `Convex_GeneralMahler_Prim`, `Convex_GeneralMahler_Profiles`, `Convex_GeneralMahler_Proj`, `Convex_GeneralMahler_ProjMean`, `Convex_GeneralMahler_Rapid`, `Convex_GeneralMahler_Reduction`, `Convex_GeneralMahler_Santalo`, `Convex_GeneralMahler_Scalar_Data`, `Convex_GeneralMahler_SimplexCone`, `Convex_GeneralMahler_Smoothing`, `Convex_GeneralMahler_Spectral`, `Convex_GeneralMahler_TestFun`, `Convex_GeneralMahler_Threshold`, `Convex_GeneralMahler_TraceOrder`, `Convex_GeneralMahler_Transform`, `Convex_GeneralMahler_Update`, `Convex_GeneralMahler_Variation`, `Convex_GeneralMahler_pRapid`.
--
--   **Imports.** It imports the published bundle `Def_GeneralMahler`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ026G002`; the statement `OAI.GeneralMahler.Complete_profile_input`.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_GeneralMahler

section
-- module Solutions.OAIQ026_GM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Cone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive dual cones and their Laplace integrals (paper Piece 2, §01)

The measure is ordinary Lebesgue (statements proved for any compatible
Lebesgue normalization where useful). "ProperCone" here is Mathlib's
closed cone containing zero; the extra paper hypotheses (solid and
contains no line) are imposed as needed. In the main application both
C and its positive dual have specified interior points.
-/

noncomputable section

open Filter Set MeasureTheory MeasureTheory.Measure Metric Real
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace

namespace GeneralMahler

section Cone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Paper C* = D. -/
abbrev posDual (C : ProperCone ℝ E) : ProperCone ℝ E :=
  ProperCone.innerDual (C : Set E)

@[simp]
theorem mem_posDual {C : ProperCone ℝ E} {x : E} :
    x ∈ posDual C ↔ (∀ ⦃y⦄, y ∈ C → 0 ≤ ⟪y, x⟫) := Iff.rfl

theorem interior_dual_bound {C : ProperCone ℝ E} {V : E}
    (hv : V ∈ interior (posDual C : Set E)) :
    ∃ c > 0, ∀ x ∈ C, c * ‖x‖ ≤ ⟪V, x⟫ := by
  obtain ⟨r, hr, hb⟩ := nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hv)
  refine ⟨r, hr, fun x hx => ?_⟩
  by_cases h : x = 0
  · simp [h]
  have hxp := norm_pos_iff.mpr h
  have hm : V - (r / ‖x‖) • x ∈ closedBall V r := by
    rw [mem_closedBall, dist_eq_norm, sub_right_comm, sub_self, zero_sub,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hxp)]
    exact le_of_eq (div_mul_cancel₀ _ hxp.ne')
  have hi := mem_posDual.mp (hb hm) hx
  rwa [real_inner_comm, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, pow_two, ← mul_assoc, div_mul_cancel₀ _ hxp.ne',
    sub_nonneg] at hi

theorem interior_dual_of_bound {C : ProperCone ℝ E} {V : E}
    {c : ℝ} (hc : 0 < c) (hf : ∀ x ∈ C, c * ‖x‖ ≤ ⟪V, x⟫) :
    V ∈ interior (posDual C : Set E) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply nhds_basis_closedBall.mem_iff.mpr
  refine ⟨c, hc, ?_⟩
  intro y hy
  apply mem_posDual.mpr
  intro x hx
  have h₁ := hf x hx
  have h₂ := real_inner_le_norm (V - y) x
  rw [inner_sub_left] at h₂
  rw [real_inner_comm]
  have hle : ‖V - y‖ ≤ c := by rwa [mem_closedBall, dist_comm, dist_eq_norm] at hy
  have h₃ := mul_le_mul_of_nonneg_right hle (norm_nonneg x)
  linarith

/-- If y is not interior to the dual, then there is a nonzero bad
direction in the cone. -/
theorem exists_ray_of_not_interior_dual {C : ProperCone ℝ E} {y : E}
    (h : y ∉ interior (posDual C : Set E)) :
    ∃ x ∈ C, ‖x‖ = 1 ∧ ⟪y, x⟫ ≤ 0 := by
  let s := (C : Set E) ∩ sphere 0 1
  by_contra! hn
  have hc : ∃ c > 0, ∀ x ∈ s, c ≤ ⟪y, x⟫ := by
    rcases s.eq_empty_or_nonempty with hs|hs
    · exact ⟨1, by norm_num, by simp [hs]⟩
    · have hk : IsCompact s :=
        (isCompact_sphere (0 : E) 1).inter_left C.isClosed
      obtain ⟨x, hx, hf⟩ := hk.exists_isMinOn hs
        (by fun_prop : ContinuousOn (fun z => ⟪y, z⟫) s)
      exact ⟨⟪y, x⟫, hn _ hx.1 (by simpa using hx.2), fun _ hb => hf hb⟩
  obtain ⟨c,hc,hb⟩ := hc
  apply h
  apply interior_dual_of_bound hc
  intro x hx
  by_cases hz : x = 0
  · simp [hz]
  have hp := norm_pos_iff.mpr hz
  have hm : ‖x‖⁻¹ • x ∈ s := by
    refine ⟨C.smul_mem hx (inv_nonneg.mpr hp.le), ?_⟩
    simp [norm_smul, hp.ne']
  specialize hb _ hm
  rwa [real_inner_smul_right, ← div_eq_inv_mul, le_div_iff₀ hp] at hb

variable [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]

/-- Paper §01 χ_C(V). Used with V interior to the dual. -/
def chi (C : ProperCone ℝ E) (V : E) : ℝ :=
  ∫ x in C, Real.exp (-⟪V,x⟫)

/-- For limiting arguments keep track of infinity. -/
def chiExt (C : ProperCone ℝ E) (V : E) : ℝ≥0∞ :=
  ∫⁻ x in C, ENNReal.ofReal (Real.exp (-⟪V,x⟫))

/-- Exponential tail with polynomial factors, finiteness.
This elementary proof uses the integrable comparison (1+‖x‖)^(-r)
above dimension r>n. -/
theorem integrable_polynomial_exp_tail {c : ℝ} (hc : 0 < c) (p : ℕ) :
    Integrable (fun x : E => (1 + ‖x‖)^p * Real.exp (-(c * ‖x‖))) := by
  let r : ℝ := (Module.finrank ℝ E : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let a := c / ((p:ℝ)+r)
  have har : 0 < (p:ℝ)+r := by positivity
  have ha : 0 < a := div_pos hc har
  let k := ((p:ℝ)+r) * (a - 1 - Real.log a)
  refine ((integrable_one_add_norm (show (Module.finrank ℝ E:ℝ) < r by
    dsimp [r]; linarith)).const_mul (Real.exp k)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  set b := (1 + ‖x‖)
  have hb : 0 < b := by dsimp [b]; positivity
  have H : Real.log b ≤ a*b - 1 - Real.log a := by
    have he := Real.log_le_sub_one_of_pos (mul_pos ha hb)
    rwa [Real.log_mul ha.ne' hb.ne', add_comm, ← le_sub_iff_add_le] at he
  have eqc : ((p:ℝ)+r)*a = c := by
    rw [mul_comm]; exact div_mul_cancel₀ _ har.ne'
  have H₂ : Real.log b * p - c * ‖x‖ ≤ k + Real.log b * (-r) := by
    calc
      _ = ((p:ℝ)+r) * Real.log b + Real.log b * (-r) - c * ‖x‖ := by ring
      _ ≤ ((p:ℝ)+r) * (a*b - 1 - Real.log a) + Real.log b * (-r) - c * ‖x‖ := by gcongr
      _ = k + Real.log b * (-r) := by
        dsimp [k,b]
        rw [← eqc]
        ring
  change ‖b^p * Real.exp _‖ ≤ Real.exp k * b ^ (-r)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.rpow_natCast, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, ← sub_eq_add_neg]
  exact H₂

theorem chi_integrable {C : ProperCone ℝ E} {V : E}
    (hV : V ∈ interior (posDual C : Set E)) :
    IntegrableOn (fun x => Real.exp (-⟪V,x⟫)) C := by
  obtain ⟨c,hc,hb⟩ := interior_dual_bound hV
  have htail : Integrable (fun x : E => Real.exp (-(c*‖x‖))) := by
    simpa using (integrable_polynomial_exp_tail (E := E) hc 0)
  apply htail.integrableOn.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem C.isClosed.measurableSet] with x hx
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp,
    neg_le_neg_iff] using hb x hx

theorem chiExt_eq {C : ProperCone ℝ E} {V : E}
    (hV : V ∈ interior (posDual C : Set E)) :
    chiExt C V = ENNReal.ofReal (chi C V) :=
  (ofReal_integral_eq_lintegral_ofReal (chi_integrable hV)
    (ae_of_all _ fun _x => (Real.exp_pos _).le)).symm

omit [IsAddHaarMeasure (volume : Measure E)] in
theorem chiExt_lsc (C : ProperCone ℝ E) : LowerSemicontinuous (chiExt C) := by
  intro V b hlt
  let g (u x : E) := ENNReal.ofReal (Real.exp (-⟪u,x⟫))
  refine eventually_lt_of_lt_liminf ?_
  refine hlt.trans_le (le_trans ?_ (lintegral_liminf_le
    (u := 𝓝 V) (μ := volume.restrict (C : Set E)) (f := g) (by intro i; dsimp [g]; fun_prop)))
  apply lintegral_mono
  intro x
  have hf : Continuous (fun i => g i x) := ENNReal.continuous_ofReal.comp (show Continuous (fun i => Real.exp (-⟪i,x⟫)) by fun_prop)
  exact (Tendsto.liminf_eq (hf.tendsto V)).symm.le

/-- If w has a bad direction in C, then the Laplace integral
is infinite: translate C along that ray. The translated copy
does not decrease the integral but misses a relatively low layer
of positive volume measured in any interior-dual direction. -/
theorem chiExt_top {C : ProperCone ℝ E}
    (hs : (interior (C : Set E)).Nonempty)
    (hd : (interior (posDual C : Set E)).Nonempty)
    {V : E} (hV : V ∉ interior (posDual C : Set E)) :
    chiExt C V = ∞ := by
  obtain ⟨q,hq,hq1,hq2⟩ := exists_ray_of_not_interior_dual hV
  obtain ⟨a,ha⟩ := hs
  obtain ⟨W,hW⟩ := hd
  obtain ⟨c,hc,hcw⟩ := interior_dual_bound hW
  have hq3 : 0 < ⟪W,q⟫ := by simpa only [hq1,mul_one] using (lt_of_lt_of_le
    (mul_pos hc (by rw [hq1]; norm_num)) (hcw q hq))
  let r := max 0 ⟪W,a⟫ / ⟪W,q⟫ + 1
  have hrp : 0 ≤ (max 0 ⟪W,a⟫) / ⟪W,q⟫ := div_nonneg (le_max_left ..) hq3.le
  have hr : 0 < r := by dsimp [r]; linarith
  let p := r • q
  have hp : p ∈ C := C.smul_mem hq hr.le
  have hpa : ⟪W,a⟫ < ⟪W,p⟫ := by
    dsimp [p, r]
    rw [real_inner_smul_right, add_mul, div_mul_cancel₀ _ hq3.ne', one_mul]
    exact lt_of_le_of_lt (le_max_right ..) (by linarith)
  let D : Set E := {x | x - p ∈ C}
  let B := interior (C : Set E) ∩ {x | ⟪W,x⟫ < ⟪W,p⟫}
  have hm : MeasurableSet D :=
    ((C.isClosed).preimage (continuous_id.sub continuous_const)).measurableSet
  have hbo : IsOpen B := isOpen_interior.inter
    (isOpen_lt (by fun_prop) continuous_const)
  have hdis : Disjoint D B := Set.disjoint_left.mpr (by
    intro x hx hy
    have hxu := hcw (x - p) hx
    rw [inner_sub_right] at hxu
    have hh : ⟪W,x⟫ < ⟪W,p⟫ := hy.2
    have hh' : 0 ≤ c * ‖x - p‖ := by positivity
    linarith)
  have hsub : D ∪ B ⊆ C := union_subset (fun x hx => by
    have hh := C.add_mem hx hp
    rwa [sub_add_cancel] at hh) (inter_subset_left.trans interior_subset)
  let g (x : E) := ENNReal.ofReal (Real.exp (-⟪V,x⟫))
  have gm : Measurable g := by fun_prop (disch := aesop)
  have hpos : 0 < ∫⁻ x in B, g x := by
    apply (lintegral_pos_iff_support gm).mpr
    have hh : Function.support g = univ := eq_univ_of_forall (fun x =>
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    rw [hh, Measure.restrict_apply_univ]
    exact hbo.measure_pos volume ⟨a,ha,hpa⟩
  have hle : chiExt C V ≤ ∫⁻ x in D, g x := by
    have hme := measurePreserving_add_right volume p
    rw [← hme.map_eq, setLIntegral_map hm gm hme.measurable]
    -- The preimage is exactly C
    have heq : (fun x => x + p) ⁻¹' D = C := by ext; simp [D]
    rw [heq]
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [inner_add_right]
    have hu : ⟪V,p⟫ ≤ 0 := by
      dsimp [p]
      rw [real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos hr.le hq2
    linarith
  by_contra hh
  have halt : chiExt C V + (∫⁻ x in B, g x) ≤ chiExt C V := calc
    _ ≤ (∫⁻ x in D, g x) + (∫⁻ x in B, g x) := add_le_add_left hle _
    _ = ∫⁻ x in D ∪ B, g x := (lintegral_union hbo.measurableSet hdis).symm
    _ ≤ _ := lintegral_mono_set hsub
  exact (not_lt_of_ge halt) (ENNReal.lt_add_right hh hpos.ne')

/-- Strict convexity on dual interior for a solid cone. -/
theorem chi_strictConvex {C : ProperCone ℝ E}
    (hs : (interior (C : Set E)).Nonempty) :
    StrictConvexOn ℝ (interior (posDual C : Set E)) (chi C) := by
  have cv := (posDual C).convex.interior
  refine ⟨cv, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let z := a • x + b • y
  have hz := cv hx hy ha.le hb.le hab
  let f (u t : E) := Real.exp (-⟪u,t⟫)
  let g (t : E) := a * f x t + b * f y t - f z t
  have hi : IntegrableOn g C :=
    (((chi_integrable hx).const_mul _).add ((chi_integrable hy).const_mul _)).sub (chi_integrable hz)
  have hn : ∀ t, 0 ≤ g t := by
    intro t
    have H := strictConvexOn_exp.convexOn.2
      (show -⟪x,t⟫ ∈ univ from mem_univ _) (show -⟪y,t⟫ ∈ univ from mem_univ _)
      ha.le hb.le hab
    apply sub_nonneg.mpr
    simpa [f,z, inner_add_left, real_inner_smul_left, neg_add, add_comm] using H
  let B : Set E := interior (C : Set E) ∩ {t | ⟪x-y,t⟫ ≠ 0}
  have hbo : IsOpen B := isOpen_interior.inter (isOpen_ne_fun (by fun_prop) continuous_const)
  obtain ⟨u,hu⟩ := hs
  have hu₁ : 0 < ⟪x-y,x-y⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hxy)
  have hbne : B.Nonempty := by
    by_cases h : ⟪x-y,u⟫ = 0
    · let w : ℝ → E := fun s => u + s • (x-y)
      have hw : Continuous w := by fun_prop (disch := aesop)
      obtain ⟨s,hs,hh⟩ : ∃ s, 0 < s ∧ w s ∈ interior (C : Set E) := by
        have hne : w ⁻¹' interior (C : Set E) ∈ 𝓝 (0:ℝ) :=
          (hw.tendsto 0) (isOpen_interior.mem_nhds (by simpa [w] using hu))
        exact ((show ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s from self_mem_nhdsWithin).and
          ((nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) hne)).exists
      refine ⟨w s, hh, ?_⟩
      change ⟪x-y,u+s • (x-y)⟫ ≠ 0
      simp [inner_add_right, real_inner_smul_right, h, hs.ne', sub_ne_zero.mpr hxy]
    · exact ⟨u, hu, h⟩
  have hpos : 0 < ∫ t in C, g t := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hn) hi).mpr
    refine lt_of_lt_of_le (hbo.measure_pos volume hbne) (measure_mono (fun t ht => ?_))
    refine ⟨?_, interior_subset ht.1⟩
    apply ne_of_gt
    have HH : -⟪x,t⟫ ≠ -⟪y,t⟫ := by
      have h : ⟪x-y,t⟫ ≠ 0 := ht.2
      simpa [sub_ne_zero,inner_sub_left] using h
    have H := strictConvexOn_exp.2 (mem_univ _) (mem_univ _) HH ha hb hab
    apply sub_pos.mpr
    simpa [f,z, inner_add_left, real_inner_smul_left, neg_add, add_comm] using H
  change 0 < ∫ t in C, (a * f x t + b * f y t - f z t) at hpos
  rw [integral_sub, integral_add, integral_const_mul, integral_const_mul] at hpos
  · exact sub_pos.mp hpos
  all_goals
    first
    | exact chi_integrable hz
    | exact (chi_integrable hx).const_mul _
    | exact (chi_integrable hy).const_mul _
    | exact ((chi_integrable hx).const_mul _).add ((chi_integrable hy).const_mul _)

end Cone
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Elementary bounds used throughout the Gaussian and layer integrations.
We keep pointwise growth and measurability hypotheses separate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Real
open scoped Topology ENNReal RealInnerProductSpace NNReal
namespace GeneralMahler
section
variable {X Y E F : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

def PolyBound (f : X → E) : Prop :=
  ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n

namespace PolyBound

theorem of_bound {f : X → E} (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C) : PolyBound f :=
  ⟨C,0, le_trans (norm_nonneg (f 0)) (h 0), by simpa⟩

theorem const (v : E) : PolyBound (fun _ : X => v) := of_bound _ (fun _ => le_rfl)

theorem id : PolyBound (fun x : X => x) :=
  ⟨1,1,zero_le_one,by simp⟩

theorem clm [NormedSpace ℝ X] [NormedSpace ℝ E] (f : X →L[ℝ] E) :
    PolyBound f :=
  ⟨‖f‖, 1,norm_nonneg _, fun x => (f.le_opNorm x).trans (by
    gcongr; simp)⟩

variable {f g : X → E}
theorem mono {h : X → F} (hf : PolyBound f) (H : ∀ x, ‖h x‖ ≤ ‖f x‖) :
    PolyBound h := by
  obtain ⟨C,n,hc,hb⟩ := hf
  exact ⟨C,n,hc,fun x => (H x).trans (hb x)⟩

lemma common {h : X → F} (hf : PolyBound f) (hg : PolyBound h) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C*(1+‖x‖)^n ∧ ‖h x‖ ≤ C*(1+‖x‖)^n := by
  obtain ⟨C,n,hc,hn⟩ := hf
  obtain ⟨D,m,hd,hm⟩ := hg
  refine ⟨C+D, n+m, by positivity, fun x => ?_⟩
  constructor
  · apply le_trans (hn x); gcongr <;> simp_all
  · apply le_trans (hm x); gcongr <;> simp_all

theorem add (hf : PolyBound f) (hg : PolyBound g) : PolyBound fun x => f x + g x := by
  obtain ⟨C,n,hc,hb⟩ := common hf hg
  refine ⟨2*C,n,by positivity, fun x => (norm_add_le ..).trans ?_⟩
  obtain ⟨h,h'⟩ := hb x; linarith
theorem neg (hf : PolyBound f) : PolyBound fun x => -f x := hf.mono (by simp)
theorem sub (hf : PolyBound f) (hg : PolyBound g) : PolyBound fun x => f x - g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
theorem norm (hf : PolyBound f) : PolyBound fun x => ‖f x‖ :=
  hf.mono (fun _ => (Real.norm_of_nonneg (norm_nonneg _)).le)
lemma of_prod_le {K : Type*} [SeminormedAddCommGroup K] {h : X → F}
    {l : X → K} (hf : PolyBound f) (hh : PolyBound h) (hl : ∀ x, ‖l x‖ ≤ ‖f x‖*‖h x‖) :
    PolyBound l := by
  obtain ⟨C,n,hc,hn⟩ := common hf hh
  refine ⟨C*C,n+n,by positivity,fun x => (hl x).trans ?_⟩
  obtain ⟨h₁,h₂⟩ := hn x
  calc
    _ ≤ (C*(1+‖x‖)^n)*(C*(1+‖x‖)^n) := mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring
theorem smul [NormedSpace ℝ E] {a : X → ℝ} (ha : PolyBound a) (hf : PolyBound f) :
    PolyBound fun x => a x • f x :=
  of_prod_le ha hf (fun _x => (norm_smul _ _).le)
theorem mul {R : Type*} [NormedRing R] {b d : X → R} (hb : PolyBound b) (hd : PolyBound d) :
    PolyBound fun x => b x * d x :=
  of_prod_le hb hd fun _ => norm_mul_le _ _
theorem pow {R : Type*} [NormedRing R] {b : X → R} (hb : PolyBound b) (n : ℕ) :
    PolyBound fun x => b x ^ n := by
  induction n with
  | zero => simpa using (const (X := X) (1 : R))
  | succ n ih => simpa [pow_succ] using ih.mul hb
theorem fst : PolyBound (Prod.fst (α := X) (β := E)) := id.mono fun _x => le_max_left ..
theorem snd : PolyBound (Prod.snd (α := X) (β := E)) := id.mono fun _x => le_max_right ..
theorem comp {b : E → F} (hb : PolyBound b) (hf : PolyBound f) :
    PolyBound fun x => b (f x) := by
  obtain ⟨C,n,hc,h⟩ := hb
  obtain ⟨D,m,hd,h'⟩ := hf
  refine ⟨C*(1+D)^n, m*n, by positivity, fun x => (h _).trans ?_⟩
  calc
    _ ≤ C*((1+D)*(1+‖x‖)^m)^n := by
      have hv : (1:ℝ) ≤ (1+‖x‖)^m := one_le_pow₀ (by simp)
      gcongr; linarith [h' x]
    _ = _ := by rw [mul_pow,pow_mul,mul_assoc]

theorem linear_growth {K : ℝ≥0} (h : LipschitzWith K f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C*(1+‖x‖) := by
  refine ⟨K+‖f 0‖,by positivity, fun x => ?_⟩
  have hi : ‖f x - f 0‖ ≤ K*‖x‖ := by simpa [dist_eq_norm] using h.dist_le_mul x 0
  have hh := norm_add_le (f x - f 0) (f 0)
  rw [sub_add_cancel] at hh
  nlinarith [norm_nonneg (f 0),norm_nonneg x]

theorem lipschitz {K : ℝ≥0} (hf : LipschitzWith K f) : PolyBound f := by
  obtain ⟨C,hc,h⟩ := linear_growth hf
  exact ⟨C,1,hc,by simpa using h⟩

end PolyBound
end

section Integrability
open ProbabilityTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]
  {μ : Measure E} [IsGaussian μ]

lemma integrable_envelope (n : ℕ) :
    Integrable (fun x:E => (1+‖x‖)^n) μ := by
  cases n with
  | zero => simp
  | succ n =>
    let p : ℝ≥0∞ := ↑(n+1 : ℕ)
    have hI := IsGaussian.memLp_id μ p (by simp [p])
    have hW : MemLp (fun _ : E => (1:ℝ)) p μ := memLp_const _
    have hf : MemLp (fun x:E => (1+‖x‖)) (↑(n+1 : ℕ)) μ := hW.add hI.norm
    have he := hf.integrable_norm_rpow (by simp) (by simp)
    have hnorm (x:E) : ‖1+‖x‖‖ = 1+‖x‖ := Real.norm_of_nonneg (by positivity)
    simpa only [hnorm, ENNReal.toReal_natCast, Real.rpow_natCast] using he

theorem PolyBound.gaussian_integrable {f : E → F}
    (h : PolyBound f) (hm : AEStronglyMeasurable f μ) : Integrable f μ := by
  obtain ⟨C,n,hc,he⟩ := h
  exact ((integrable_envelope n).const_mul C).mono' hm (ae_of_all _ he)
end Integrability
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! The Gaussian integrations in §§02--06: Lebesgue density and
translation/scaling dictionary. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace GeneralMahler

abbrev normal (n : ℕ) := stdGaussian (Rn n)

abbrev gamma : Measure ℝ := gaussianReal 0 1
def phi := gaussianPDFReal 0 1
variable {n : ℕ}

lemma phi_apply (t : ℝ) : phi t = (√(2 * π))⁻¹ * Real.exp (-(t ^ 2)/2) := by
  simp [phi, gaussianPDFReal]

lemma phi_pos (t : ℝ) : 0 < phi t := gaussianPDFReal_pos _ _ _ one_ne_zero

def nDensity (x : Rn n) := (√(2 * π))⁻¹ ^ n * Real.exp (-(‖x‖^2)/2)
lemma nDensity_pos (x : Rn n) : 0 < nDensity x := by
  unfold nDensity; positivity

@[fun_prop] lemma continuous_nDensity : Continuous (@nDensity n) := by
  unfold nDensity; fun_prop

lemma nDensity_prod (x : Fin n → ℝ) :
    nDensity (WithLp.toLp 2 x) = ∏ i, phi (x i) := by
  simp_rw [phi_apply, Finset.prod_mul_distrib, ← Real.exp_sum]
  simp only [nDensity, EuclideanSpace.real_norm_sq_eq, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.sum_div, Finset.sum_neg_distrib]

lemma gaussian_pi_density :
    Measure.pi (fun _ : Fin n => gamma) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, phi (x i))) := by
  have hf : Integrable phi := integrable_gaussianPDFReal _ _
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  let u := fun (i : Fin n) => (volume : Measure ℝ).restrict (s i)
  change (∫⁻ x in _, _ ∂Measure.pi _) = _
  rw [Measure.restrict_pi_pi]
  have h : Integrable (fun x : Fin n → ℝ => ∏ i, phi (x i)) (Measure.pi u) :=
    Integrable.fintype_prod (E := ℝ) (fun _ => hf.integrableOn)
  let v := fun i : Fin n => ∫ x, phi x ∂u i
  have Hv (i : Fin n) : 0 ≤ v i := integral_nonneg fun x => (phi_pos _).le
  change (∫⁻ x, _ ∂Measure.pi u) = _
  rw [← ofReal_integral_eq_lintegral_ofReal h (ae_of_all _ fun x =>
      Finset.prod_nonneg (fun i _ => (phi_pos _).le)), integral_fintype_prod_eq_prod]
  change ENNReal.ofReal (∏ i, v i) = _
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    exact (gaussianReal_apply_eq_integral _ one_ne_zero _).symm
  · exact fun i _ => Hv i

theorem normal_density :
    normal n = volume.withDensity (fun x => ENNReal.ofReal (nDensity x)) := by
  let T := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have hT : MeasurePreserving T := PiLp.volume_preserving_toLp _
  have he : normal n = (Measure.pi (fun _ : Fin n => gamma)).map T :=
    ProbabilityTheory.map_pi_eq_stdGaussian.symm
  rw [he, gaussian_pi_density]
  ext s hs
  rw [Measure.map_apply T.measurable hs, withDensity_apply _ hs, withDensity_apply _ (T.measurable hs)]

  have hsd := setLIntegral_map (μ := volume) (g := (T : _ → Rn n)) hs
    (show Measurable (fun x:Rn n => ENNReal.ofReal (nDensity x)) by fun_prop) T.measurable
  rw [hT.map_eq] at hsd
  rw [hsd]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal _ = ENNReal.ofReal (nDensity (WithLp.toLp 2 x))
  rw [nDensity_prod]

theorem normal_ac : normal n ≪ (volume : Measure (Rn n)) := by
  rw [normal_density]; exact withDensity_absolutelyContinuous _ _

theorem ac_normal : (volume : Measure (Rn n)) ≪ normal n := by
  rw [normal_density]
  apply withDensity_absolutelyContinuous' (by fun_prop)
  exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (nDensity_pos x)).ne'

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normal_integral (f : Rn n → F) : ∫ x, f x ∂(normal n) = ∫ x, nDensity x • f x := by
  rw [normal_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (nDensity_pos _).le]

lemma normal_integrable_iff {f : Rn n → F} :
    Integrable f (normal n) ↔ Integrable (fun x => nDensity x • f x) := by
  rw [normal_density, integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (nDensity_pos _).le]
end
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Gaussian smoothing and an integration by parts formula. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

theorem hasDeriv_nDensity_shift (x a : Rn m) :
    HasFDerivAt (fun y => nDensity (x-y))
      (nDensity (x-a) • (innerSL ℝ (x-a))) a := by
  let c : ℝ := (√(2 * π))⁻¹ ^ m
  have hf := ((hasFDerivAt_const (𝕜 := ℝ) x a).sub (hasFDerivAt_id a))
  have hg := ((hf.norm_sq.neg.mul_const ((2:ℝ)⁻¹)).exp).const_mul c
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  all_goals ext v; simp [nDensity,c,div_eq_mul_inv, two_smul]; ring

theorem nDensity_shift_bound (a B : ℝ) (ha : 0 < a) (_hb : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Rn m, ‖y‖ ≤ B →
      nDensity (x-y) ≤ C * exp (-(a * ‖x‖)) := by
  let c : ℝ := (√(2 * π))⁻¹ ^ m
  refine ⟨c*exp (a*B+a^2/2),by dsimp [c]; positivity,?_⟩
  intro x y hy
  rw [mul_assoc, ← exp_add]
  change c*_ ≤ c*_
  gcongr
  have hh : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa using (norm_add_le (x-y) y)
  nlinarith [sq_nonneg (‖x-y‖-a)]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def smoothG (f : Rn m → F) (a : Rn m) := ∫ x, f (x+a) ∂(normal m)

lemma smoothG_eq (f : Rn m → F) (a : Rn m) :
    smoothG f a = ∫ x, nDensity (x-a) • f x := by
  rw [smoothG, normal_integral]
  rw [← integral_add_right_eq_self (μ := volume) (fun x => nDensity (x-a) • f x) a]
  simp

abbrev G' (f : Rn m → F) (a x : Rn m) : Rn m →L[ℝ] F :=
  (nDensity (x-a) • innerSL ℝ (x-a)).smulRight (f x)

lemma continuous_pair_G' (x : Rn m) :
    Continuous (fun p : Rn m × F =>
      (nDensity (x-p.1) • innerSL ℝ (x-p.1)).smulRight p.2) := by
  change Continuous (fun p : Rn m × F => ContinuousLinearMap.smulRightL ℝ _ _
    (nDensity (x-p.1) • innerSL ℝ (x-p.1)) p.2)
  fun_prop

theorem smooth_domination {f : Rn m → F}
    (hf : PolyBound f) {B : ℝ} (hb : 0 ≤ B) :
    ∃ g : Rn m → ℝ, Integrable g ∧ ∀ a x, ‖a‖ ≤ B →
      ‖nDensity (x-a) • f x‖ ≤ g x ∧ ‖G' f a x‖ ≤ g x := by
  obtain ⟨C,n,hc,h⟩ := hf
  obtain ⟨K,hk,hg⟩ := nDensity_shift_bound (m := m) 1 B zero_lt_one hb
  let g := fun x:Rn m => (K*C)*(1+B) * ((1+‖x‖)^(n+1) * exp (-(1*‖x‖)))
  refine ⟨g,(integrable_polynomial_exp_tail zero_lt_one _).const_mul _ ,?_⟩
  intro a x ha
  have h₁ := h x
  have h₂ := hg x a ha
  have he : 1 ≤ (1+B)*(1+‖x‖) := one_le_mul_of_one_le_of_one_le (by linarith) (by simp)
  have hr : ‖x-a‖ ≤ (1+B)*(1+‖x‖) := by
    apply (norm_sub_le ..).trans
    nlinarith [norm_nonneg x]
  have h₄ : nDensity (x-a) * ‖f x‖ ≤ K * exp (-(1*‖x‖))*(C*(1+‖x‖)^n) :=
    mul_le_mul h₂ h₁ (norm_nonneg _) (by positivity)
  have ge : g x = (K * exp (-(1*‖x‖))*(C*(1+‖x‖)^n))*((1+B)*(1+‖x‖)) := by
    dsimp [g]; rw [pow_succ]; ring
  rw [ge]
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (nDensity_pos _).le]
    exact h₄.trans (le_mul_of_one_le_right (by positivity) he)
  · rw [G',ContinuousLinearMap.norm_smulRight_apply,norm_smul, innerSL_apply_norm,
      Real.norm_of_nonneg (nDensity_pos _).le,mul_right_comm]
    exact mul_le_mul h₄ hr (norm_nonneg _) (by positivity)

theorem strongly_G' {f : Rn m → F} (hm : StronglyMeasurable f) (a : Rn m) :
    StronglyMeasurable (G' f a) := by
  let g (p : Rn m × F) : Rn m →L[ℝ] F :=
    ContinuousLinearMap.smulRightL ℝ _ _
      (nDensity (p.1-a) • innerSL ℝ (p.1-a)) p.2
  have hc : Continuous g := by dsimp only [g]; fun_prop
  have hu : StronglyMeasurable (fun x => (id x,f x)) :=
    (continuous_id (X := Rn m)).stronglyMeasurable.prodMk hm
  have H : StronglyMeasurable (g ∘ (fun x => (id x,f x))) := hc.comp_stronglyMeasurable hu
  let f' := G' f a
  have he : G' f a = g ∘ (fun x => (id x,f x)) := by rfl
  rw [he]
  exact H

theorem smoothG_hasFDeriv {f : Rn m → F} (hf : PolyBound f)
    (hm : StronglyMeasurable f) (a : Rn m) :
    Integrable (G' f a) ∧ HasFDerivAt (smoothG f) (∫ x, G' f a x) a := by
  obtain ⟨g,hg,h⟩ := smooth_domination hf (show 0 ≤ ‖a‖+1 by positivity)
  let s := closedBall a 1
  have hs : s ∈ 𝓝 a := closedBall_mem_nhds _ zero_lt_one
  have h₁ : ‖a‖ ≤ ‖a‖+1 := by linarith
  have h₂ (y) (hy : y ∈ s) : ‖y‖ ≤ ‖a‖+1 := by
    have hh : ‖y‖ ≤ ‖y-a‖+‖a‖ := by simpa using (norm_add_le (y-a) a)
    change dist _ _ ≤ _ at hy
    rw [dist_eq_norm] at hy
    linarith
  have hmeas (y : Rn m) :
      StronglyMeasurable (fun x : Rn m => nDensity (x-y) • f x) :=
    (by fun_prop : Continuous (fun x : Rn m => nDensity (x-y))).stronglyMeasurable.smul hm
  refine ⟨hg.mono' (strongly_G' hm a).aestronglyMeasurable
    (ae_of_all _ fun x => (h _ _ h₁).2), ?_⟩
  rw [funext (smoothG_eq f)]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (Eventually.of_forall fun y => (hmeas y).aestronglyMeasurable)
    (hg.mono' (hmeas a).aestronglyMeasurable (ae_of_all _ fun x => (h _ _ h₁).1))
    ((strongly_G' hm a).aestronglyMeasurable)
    (ae_of_all _ fun x y hy => (h y x (h₂ y hy)).2) hg (ae_of_all _ ?_)
  intro x y _
  exact (hasDeriv_nDensity_shift x y).smul_const _

theorem smoothG_deriv_cont {f : Rn m → F} (hf : PolyBound f)
    (hm : StronglyMeasurable f) : Continuous (fun a => ∫ x, G' f a x) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨g,hg,h⟩ := smooth_domination hf (show 0 ≤ ‖a‖+1 by positivity)
  have hv : ∀ᶠ y in 𝓝 a, ‖y‖ ≤ ‖a‖+1 :=
    continuous_norm.continuousAt (Iic_mem_nhds (by linarith))
  apply continuousAt_of_dominated
    (Eventually.of_forall fun y => ((strongly_G' hm y).aestronglyMeasurable))
    (hv.mono fun y hy => (ae_of_all _ fun x => (h y x hy).2)) hg
    (ae_of_all _ ?_)
  intro x
  exact ((continuous_pair_G' x).comp (continuous_id.prodMk continuous_const)).continuousAt
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Matrix notation and ordered Euclidean operators used in §§02--06. -/

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace ENNReal NNReal
namespace GeneralMahler
variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev op : Mat n ≃⋆ₐ[ℝ] (Rn n →L[ℝ] Rn n) := Matrix.toEuclideanCLM

def opCLE : Mat n ≃L[ℝ] (Rn n →L[ℝ] Rn n) :=
  (op (n := n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

@[simp] lemma opCLE_apply (A : Mat n) : opCLE A = op A := rfl
@[simp] lemma opCLE_symm_apply (A : Rn n →L[ℝ] Rn n) : opCLE.symm A = op.symm A := rfl

theorem op_norm (A : Mat n) : ‖op A‖ = ‖A‖ := rfl

@[fun_prop] theorem continuous_op : Continuous (@op n) :=
  opCLE.continuous

@[fun_prop] theorem continuous_op_symm : Continuous (@op n).symm :=
  opCLE.symm.continuous

lemma op_inner_adjoint (A : Mat n) (x y : Rn n) :
    ⟪op A x,y⟫ = ⟪x,op (star A) y⟫ := by
  rw [map_star]
  exact (adjoint_inner_right ..).symm

lemma op_iff_hermitian {A : Mat n} :
    A.IsHermitian ↔ ∀ x y : Rn n, ⟪op A x,y⟫ = ⟪x,op A y⟫ := by
  change star A = A ↔ _
  constructor
  · intro h x y
    rw [op_inner_adjoint, h]
  · intro h
    apply op.injective
    ext y : 1
    apply ext_inner_left ℝ
    intro x
    exact (op_inner_adjoint A x y).symm.trans (h x y)

lemma op_posSemidef_iff {A : Mat n} :
    A.PosSemidef ↔ A.IsHermitian ∧ (∀ x, 0 ≤ ⟪x,op A x⟫) := by
  rw [posSemidef_iff_dotProduct_mulVec]
  apply and_congr_right; intro hh
  constructor
  · intro h x
    rw [inner_toEuclideanCLM]
    simpa using h (WithLp.ofLp x)
  · intro h x
    specialize h (WithLp.toLp 2 x)
    rw [inner_toEuclideanCLM] at h
    simpa using h

lemma op_posDef_iff {A : Mat n} :
    A.PosDef ↔ A.IsHermitian ∧ (∀ x ≠ (0:Rn n), 0 < ⟪x,op A x⟫) := by
  rw [posDef_iff_dotProduct_mulVec]
  apply and_congr_right; intro hh
  constructor
  · intro h x hx
    rw [inner_toEuclideanCLM]
    have hn : WithLp.ofLp x ≠ 0 := by simpa
    simpa using h hn
  · intro h x hx
    specialize h (WithLp.toLp 2 x) (by simpa using hx)
    rw [inner_toEuclideanCLM] at h
    simpa using h

lemma op_order_iff {A B : Mat n} (ha : A.IsHermitian) (hb : B.IsHermitian) :
    A ≤ B ↔ ∀ x : Rn n, ⟪x,op A x⟫ ≤ ⟪x,op B x⟫ := by
  rw [Matrix.le_iff,op_posSemidef_iff]
  simp only [hb.sub ha, true_and,_root_.map_sub, _root_.sub_apply,inner_sub_right,sub_nonneg]

lemma le_one_norm (A : Mat n) (hA : A.IsHermitian) (h : ‖A‖ ≤ 1) :
    A ≤ 1 := by
  refine (op_order_iff hA (isHermitian_one)).mpr (fun x => ?_)
  have he : ‖op A x‖ ≤ ‖x‖ :=
    ((op A).le_opNorm _).trans (by
      rw [op_norm]; exact mul_le_of_le_one_left (norm_nonneg _) h)
  rw [_root_.map_one]
  change ⟪x,op A x⟫ ≤ ⟪x,x⟫
  rw [real_inner_self_eq_norm_sq]
  have hf := real_inner_le_norm x (op A x)
  nlinarith [norm_nonneg x]

/-- Realized paper expressions via clm evaluations. -/
def opPair (x y : Rn n) : Mat n →L[ℝ] ℝ :=
  (innerSL ℝ x).comp ((ContinuousLinearMap.apply ℝ (Rn n) y).comp
    opCLE.toContinuousLinearMap)
@[simp] theorem opPair_apply (A : Mat n) (x y : Rn n) :
    opPair x y A = ⟪x,op A y⟫ := rfl

theorem op_inner_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (x y : Rn n) :
    ⟪x,op (∫ t, A t ∂μ) y⟫ = ∫ t, ⟪x,op (A t) y⟫ ∂μ :=
  ((opPair x y).integral_comp_comm ha).symm

theorem integral_opPair {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (x y : Rn n) :
    Integrable (fun t => ⟪x,op (A t) y⟫) μ :=
  by
    change Integrable (⇑(opPair x y) ∘ A) μ
    exact (opPair x y).integrable_comp ha

theorem hermitian_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (hh : ∀ᵐ x ∂μ, (A x).IsHermitian) :
    (∫ x, A x ∂μ).IsHermitian := by
  apply op_iff_hermitian.mpr
  intro x y
  rw [real_inner_comm, op_inner_integral ha,op_inner_integral ha]
  apply integral_congr_ae
  filter_upwards [hh] with i hi
  rw [real_inner_comm]
  exact op_iff_hermitian.mp hi x y

theorem psd_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (hh : ∀ᵐ x ∂μ, (A x).PosSemidef) :
    (∫ x, A x ∂μ).PosSemidef := by
  apply op_posSemidef_iff.mpr
  refine ⟨hermitian_integral ha (hh.mono fun x hx => hx.1), fun v => ?_⟩
  rw [op_inner_integral ha]
  apply integral_nonneg_of_ae
  exact hh.mono fun x hx => (op_posSemidef_iff.mp hx).2 v

/-- Normalized trace over coordinates. -/
def trN (A : Mat n) := trace A / (n:ℝ)

def trL : Mat n →L[ℝ] ℝ := ((n:ℝ)⁻¹ • (Matrix.traceLinearMap _ _ _)).toContinuousLinearMap
@[simp] theorem trL_apply (A : Mat n) : trL A = trN A := by simp [trL,trN,div_eq_inv_mul]

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Euclidean projection onto a closed convex cone and Moreau decomposition. -/
noncomputable section
open Set Filter Topology Real Metric InnerProductSpace Asymptotics
open scoped RealInnerProductSpace
namespace GeneralMahler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def coneProj (C : ProperCone ℝ E) (u : E) : E :=
  (exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex u).choose

variable (C : ProperCone ℝ E)
local notation "f" => coneProj C

theorem proj_mem (x:E) : f x ∈ C :=
  (exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex x).choose_spec.1

theorem proj_vi (x:E) {v : E} (hv : v ∈ C) :
    ⟪x-f x,v-f x⟫ ≤ 0 := by
  exact ((norm_eq_iInf_iff_real_inner_le_zero C.convex (proj_mem C _)).mp
    ((exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex x).choose_spec.2))
    _ hv

theorem proj_unique {x v:E} (hv : v ∈ C) (he : ∀ y ∈ C, ⟪x-v,y-v⟫ ≤ 0) :
    f x = v := by
  have h₁ := proj_vi C x hv
  have h₂ := he _ (proj_mem C x)
  rw [show x-v = (x-f x)+(f x-v) by abel, inner_add_left,
    real_inner_self_eq_norm_sq, show f x-v = -(v-f x) by abel, inner_neg_right] at h₂
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [norm_neg] at h₂
  rw [norm_sub_rev]
  nlinarith

theorem proj_of_mem {x:E} (hx : x ∈ C) : f x = x :=
  proj_unique C hx (by simp)

theorem proj_orthogonal (x:E) : ⟪x-f x,f x⟫ = 0 := by
  have h₁ := proj_vi C x C.zero_mem
  have h₂ := proj_vi C x (C.add_mem (proj_mem C x) (proj_mem C x))
  rw [zero_sub,inner_neg_right] at h₁
  rw [add_sub_cancel_right] at h₂
  linarith

theorem proj_residual_dual (x:E) : f x - x ∈ posDual C := by
  rw [mem_posDual]
  intro y hy
  have h := proj_vi C x (C.add_mem hy (proj_mem C x))
  rw [add_sub_cancel_right] at h
  rw [real_inner_comm, show f x-x = -(x-f x) by abel, inner_neg_left]
  linarith

theorem proj_moreau (x:E) :
    coneProj (posDual C) (-x) = coneProj C x - x := by
  apply proj_unique (posDual C) (proj_residual_dual C x)
  intro y hy
  rw [show -x-(f x-x) = -f x by abel, inner_neg_left,inner_sub_right,
    show f x-x = -(x-f x) by abel, inner_neg_right, real_inner_comm (x-f x),
    proj_orthogonal]
  have he := (mem_posDual).mp hy (proj_mem C x)
  linarith

lemma proj_zero_of_dual (x : E) (hx : -x ∈ posDual C) :
    coneProj C x = 0 := by
  have h := proj_moreau C x
  rw [proj_of_mem _ hx] at h
  exact (by rw [← add_left_inj (-x)]; simpa [sub_eq_add_neg] using h.symm)

theorem proj_firm (x y:E) :
    ‖f x-f y‖^2 ≤ ⟪x-y,f x-f y⟫ := by
  have hx := proj_vi C x (proj_mem C y)
  have hy := proj_vi C y (proj_mem C x)
  rw [show f y-f x = -(f x-f y) by abel, inner_neg_right] at hx
  rw [show x-y = (x-f x)-(y-f y)+(f x-f y) by abel, inner_add_left,
    inner_sub_left,real_inner_self_eq_norm_sq]
  linarith

theorem coneProj_lip : LipschitzWith 1 f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one,one_mul]
  have h := (proj_firm C x y).trans (real_inner_le_norm ..)
  nlinarith [norm_nonneg (x-y),norm_nonneg (f x-f y)]

def energy (u:E) := ‖coneProj C u‖^2 /2

lemma energy_lower (x:E) {y:E} (hy : y ∈ C) :
    ⟪y,x⟫ - ‖y‖^2/2 ≤ energy C x := by
  have he : 0 ≤ ⟪y,f x - x⟫ := mem_posDual.mp (proj_residual_dual C x) hy
  rw [inner_sub_right] at he
  have hh := real_inner_le_norm y (f x)
  unfold energy; nlinarith [sq_nonneg (‖y‖-‖coneProj C x‖)]

theorem energy_eq (x:E) :
    energy C x = ⟪f x,x⟫ - ‖f x‖^2/2 := by
  have he := proj_orthogonal C x
  rw [inner_sub_left, real_inner_self_eq_norm_sq,real_inner_comm] at he
  unfold energy; nlinarith

theorem energy_minorant (x y:E) :
    ⟪f x,y-x⟫ ≤ energy C y-energy C x := by
  have h := energy_lower C y (proj_mem C x)
  rw [energy_eq C x, inner_sub_right]
  linarith

theorem energy_hasFDeriv (x:E) :
    HasFDerivAt (energy C) (innerSL ℝ (f x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro c hc
  have hh := ball_mem_nhds (0:E) hc
  filter_upwards [hh] with v hv
  have h₁ := energy_minorant C x (x+v)
  have h₂ := energy_minorant C (x+v) x
  have h₃ := real_inner_le_norm (f (x+v)-f x) v
  have h₄ := coneProj_lip C |>.dist_le_mul (x+v) x
  simp only [add_sub_cancel_left] at h₁
  rw [show x-(x+v) = -v by abel, inner_neg_right] at h₂
  rw [inner_sub_left] at h₃
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,add_sub_cancel_left] at h₄
  have hv' := mem_ball_zero_iff.mp hv
  change ‖energy C (x+v) - energy C x - ⟪f x,v⟫‖ ≤ c*‖v‖
  rw [Real.norm_eq_abs]
  rw [abs_le]; constructor <;> nlinarith [norm_nonneg v]

theorem coneProj_fderiv_symmetric (x:E) (v w:E) :
    ⟪fderiv ℝ f x v,w⟫ = ⟪v,fderiv ℝ f x w⟫ := by
  by_cases h : DifferentiableAt ℝ f x
  · have hc : HasFDerivAt (fun y => innerSL ℝ (f y)) _ x :=
      (innerSL (E := E) ℝ).hasFDerivAt.comp x h.hasFDerivAt
    have he := second_derivative_symmetric_of_eventually_of_real
      (Filter.Eventually.of_forall (energy_hasFDeriv C)) hc v w
    change ⟪fderiv ℝ f x v,w⟫ = ⟪fderiv ℝ f x w,v⟫ at he
    rw [he,real_inner_comm]
  · simp [fderiv_zero_of_not_differentiableAt h]

theorem coneProj_fderiv_pos (x:E) (v : E) :
    0 ≤ ⟪v, fderiv ℝ f x v⟫ := by
  by_cases hx : DifferentiableAt ℝ f x
  · let line := fun t:ℝ => x+t • v
    let g := fun t => ⟪v,f (line t)⟫
    have hm : Monotone g := by
      intro a b hab
      rcases hab.eq_or_lt with h|h
      · simp [h]
      have hh := proj_firm C (line b) (line a)
      have he : line b-line a = (b-a) • v := by dsimp [line]; rw [sub_smul]; abel
      rw [he,real_inner_smul_left,inner_sub_right] at hh
      dsimp only [g]; nlinarith [sq_nonneg ‖f (line b)-f (line a)‖]
    have hd : HasDerivAt line v 0 := by
      change HasDerivAt ((fun _ : ℝ => x) + fun t : ℝ => t • v) v 0
      simpa only [line, Pi.add_apply, zero_add,one_smul] using ((hasDerivAt_const (x := (0:ℝ)) x).add
        ((hasDerivAt_id' (0:ℝ)).smul_const v))
    have ha : HasDerivAt g (⟪v,fderiv ℝ f x v⟫) 0 := by
      change HasDerivAt ((innerSL ℝ v) ∘ f ∘ line) _ _
      have he : line 0 = x := by simp [line]
      have Hx : HasFDerivAt f (fderiv ℝ f x) (line 0) := he ▸ hx.hasFDerivAt
      exact (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt _ (Hx.comp_hasDerivAt _ hd)
    rw [← ha.deriv]; exact hm.deriv_nonneg
  · simp [fderiv_zero_of_not_differentiableAt hx]
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_ProjMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Biased projection lemma §02: mean derivative -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ} (C : ProperCone ℝ (Rn m))

/-- Projection Jacobian, zero at undefined points. -/
def projJac (x : (Rn m)) : Mat m := op.symm (fderiv ℝ (coneProj C) x)

@[simp] lemma projJac_op (x : (Rn m)) :
    op (projJac C x) = fderiv ℝ (coneProj C) x := by simp [projJac]

lemma projJac_sym (x : (Rn m)) : (projJac C x).IsHermitian :=
  op_iff_hermitian.mpr fun v w => by
    simp only [projJac_op]; exact coneProj_fderiv_symmetric C x v w
lemma projJac_pos (x : (Rn m)) : (projJac C x).PosSemidef :=
  op_posSemidef_iff.mpr ⟨projJac_sym C x,fun v => by
    simp only [projJac_op]; exact coneProj_fderiv_pos C x v⟩

lemma projJac_norm (x:(Rn m)) : ‖projJac C x‖ ≤ 1 := by
  rw [← op_norm,projJac_op]
  exact norm_fderiv_le_of_lipschitz ℝ (coneProj_lip C)

lemma projJac_le_one (x:(Rn m)) : projJac C x ≤ 1 :=
  le_one_norm _ (projJac_sym C x) (projJac_norm C x)

lemma projJac_id {x : (Rn m)} (hx : x ∈ interior (C:Set (Rn m))) :
    projJac C x = 1 := by
  have h : coneProj C =ᶠ[𝓝 x] id := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact proj_of_mem C hy
  rw [projJac,h.fderiv_eq,fderiv_id]
  change op.symm 1 = 1
  exact _root_.map_one _

lemma projJac_zero {x : (Rn m)} (hx : -x ∈ interior (posDual C:Set (Rn m))) :
    projJac C x = 0 := by
  have h : coneProj C =ᶠ[𝓝 x] (fun _ => 0) := by
    have ht : ∀ᶠ y in 𝓝 x, -y ∈ (posDual C:Set (Rn m)) :=
      (continuous_neg.tendsto x) (mem_interior_iff_mem_nhds.mp hx)
    exact ht.mono fun y hy => proj_zero_of_dual C y hy
  simp [projJac,h.fderiv_eq]

lemma strongly_projJac : StronglyMeasurable (projJac C) := by
  let g := fderiv ℝ (coneProj C)
  have he : projJac C = op.symm ∘ g := rfl
  have hm := (measurable_fderiv ℝ (coneProj C)).stronglyMeasurable
  rw [he]; exact continuous_op_symm.comp_stronglyMeasurable hm

variable (B : (Rn m) ≃L[ℝ] (Rn m))
def affineN (a g : (Rn m)) : (Rn m) := B g + a
@[fun_prop] lemma continuous_affineN (a : (Rn m)) : Continuous (affineN B a) := by
  unfold affineN; fun_prop

lemma tendsto_ae_affineN (a : (Rn m)) :
    Tendsto (affineN B a) (ae (normal m)) (ae volume) := by
  have he := (measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae
  have hn : LinearMap.det (B : (Rn m) →ₗ[ℝ] (Rn m)) ≠ 0 := by

    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  have hy := LinearMap.quasiMeasurePreserving volume (B : (Rn m) →ₗ[ℝ] (Rn m)) hn
  exact (he.comp hy.tendsto_ae).mono_left normal_ac.ae_le

lemma affineN_integrable (a : (Rn m)) : Integrable (affineN B a) (normal m) :=
  (((PolyBound.clm B.toContinuousLinearMap).add (PolyBound.const a))).gaussian_integrable
    (continuous_affineN B a).aestronglyMeasurable

lemma affineN_mean (a:(Rn m)) : ∫ x, affineN B a x ∂normal m = a := by
  change ∫ x, B x + a ∂normal m = _
  have hi : Integrable id (normal m) := ProbabilityTheory.IsGaussian.integrable_id
  let b := B.toContinuousLinearMap
  have hb : Integrable (fun x => b x) (normal m) := b.integrable_comp hi
  change ∫ x, b x + a ∂normal m = a
  rw [integral_add hb (integrable_const _)]
  have he : (∫ x, b x ∂normal m) = 0 := by
    rw [show (∫ x, b x ∂normal m) = _ from b.integral_comp_comm (φ := id) hi]
    simp [normal]
  change (∫ x, b x ∂normal m) + _ = _
  simp [he]

def sample (a x : (Rn m)) := coneProj C (affineN B a x)

lemma continuous_sample (a:(Rn m)) : Continuous (sample C B a) :=
  (coneProj_lip C).continuous.comp (continuous_affineN B a)

lemma poly_sample (a : (Rn m)) : PolyBound (sample C B a) :=
  (PolyBound.lipschitz (coneProj_lip C)).comp
    ((PolyBound.clm B.toContinuousLinearMap).add (PolyBound.const a))

lemma sample_integrable (a : (Rn m)) : Integrable (sample C B a) (normal m) :=
  (poly_sample ..).gaussian_integrable (continuous_sample ..).aestronglyMeasurable

def mean (a : (Rn m)) : (Rn m) := ∫ x, sample C B a x ∂normal m
def meanJac (a : (Rn m)) : Mat m := ∫ x, projJac C (affineN B a x) ∂normal m

lemma meanJac_integrable (a : (Rn m)) :
    Integrable (fun x => projJac C (affineN B a x)) (normal m) := by
  have hm := (strongly_projJac C).comp_measurable (continuous_affineN B a).measurable
  apply PolyBound.gaussian_integrable _ hm.aestronglyMeasurable
  exact PolyBound.of_bound 1 (fun x => projJac_norm C _)

theorem hasFDerivAt_mean (a : (Rn m)) :
    HasFDerivAt (mean C B) (op (meanJac C B a)) a := by
  let : CompleteSpace (Rn m →L[ℝ] Rn m) := ContinuousLinearMap.instCompleteSpace
  let d := fun x => fderiv ℝ (coneProj C) (affineN B a x)
  have he : op (meanJac C B a) = ∫ x, d x ∂normal m := by
    have h := opCLE.toContinuousLinearMap.integral_comp_comm (meanJac_integrable C B a)
    symm
    change (∫ x, d x ∂_) = op _
    simpa only [ContinuousLinearEquiv.coe_coe, meanJac, opCLE_apply,projJac_op] using h
  rw [he]
  have hl : ∀ᵐ g ∂normal m, ∀ y ∈ Set.univ,
      ‖sample C B y g - sample C B a g‖ ≤ 1 * ‖y-a‖ := by
    apply ae_of_all; intro g y _
    simpa only [sample, affineN,NNReal.coe_one, ← dist_eq_norm, dist_add_left] using
      (coneProj_lip C).dist_le_mul (B g + y) (B g + a)
  have hm : AEStronglyMeasurable d (normal m) :=
    ((measurable_fderiv ..).comp (continuous_affineN B a).measurable).aestronglyMeasurable
  have hd := hasFDerivAt_integral_of_dominated_loc_of_lip' univ_mem
    (fun y _ => (continuous_sample C B y).aestronglyMeasurable)
    (sample_integrable C B a) hm hl (integrable_const _) (show
    ∀ᵐ g ∂normal m, HasFDerivAt (fun y => sample C B y g) (d g) a from ?_)
  exact hd.2
  have hh := (coneProj_lip C).ae_differentiableAt (μ := volume)
  filter_upwards [(tendsto_ae_affineN B a).eventually hh] with g hg
  have ha := hg.hasFDerivAt
  simpa only [sample,affineN,d,Function.comp_def,zero_add,ContinuousLinearMap.comp_id] using
    ha.comp a ((hasFDerivAt_const (B g) a).add (hasFDerivAt_id a))

theorem mean_C_one : ContDiff ℝ 1 (mean C B) := by
  let F := coneProj C ∘ B
  have hc : Continuous F := (coneProj_lip C).continuous.comp B.continuous
  have hp : PolyBound F :=
    (PolyBound.lipschitz (coneProj_lip C)).comp (PolyBound.clm B.toContinuousLinearMap)
  have hd := smoothG_hasFDeriv hp hc.stronglyMeasurable
  have hsf : ContDiff ℝ 1 (smoothG F) := by
    refine contDiff_one_iff_fderiv.mpr ⟨fun x => (hd x).2.differentiableAt,?_⟩
    have he := funext fun x => (hd x).2.fderiv
    rw [he]
    exact smoothG_deriv_cont hp hc.stronglyMeasurable
  have he : mean C B = smoothG F ∘ B.symm := by
    ext a

    simp only [mean,smoothG,F,sample,affineN,Function.comp_def,map_add,B.apply_symm_apply]
  rw [he]; exact hsf.comp B.symm.contDiff

-- strict inequalities for the average derivative
lemma prob_open (a : (Rn m)) (s : Set (Rn m)) (hs : IsOpen s) (he : s.Nonempty) :
    0 < normal m ((affineN B a) ⁻¹' s) := by
  let : (normal m).IsOpenPosMeasure := ac_normal.isOpenPosMeasure
  apply (hs.preimage (continuous_affineN B a)).measure_pos (normal m)
  rcases he with ⟨x,hx⟩
  use B.symm (x-a)
  simpa [affineN]

lemma strict_pos_of_layer {μ : Measure (Rn m)} {A : (Rn m) → Mat m} (hi : Integrable A μ)
    (hh : ∀ x, (A x).PosSemidef) {s : Set (Rn m)} (hp : 0 < μ s)
    (he : ∀ x ∈ s, A x = 1) :
    (∫ x, A x ∂μ).PosDef := by
  apply op_posDef_iff.mpr
  refine ⟨(psd_integral hi (ae_of_all _ hh)).1, fun v hv => ?_⟩
  rw [op_inner_integral hi]
  refine (integral_pos_iff_support_of_nonneg (fun x => (op_posSemidef_iff.mp (hh x)).2 v)
    (integral_opPair hi _ _)).mpr (lt_of_lt_of_le hp (measure_mono ?_))
  intro x hx
  have hh : 0 < ⟪v, op (A x) v⟫ := by
    rw [he x hx, _root_.map_one]; exact real_inner_self_pos.mpr hv
  exact hh.ne'

theorem mean_pos (hc : (interior (C : Set (Rn m))).Nonempty) (x : (Rn m)) :
    (meanJac C B x).PosDef :=
  strict_pos_of_layer (meanJac_integrable ..) (fun _ => projJac_pos ..)
    (prob_open B x _ isOpen_interior hc) (fun _ hx => projJac_id C hx)

theorem mean_lt_one (hd : (interior (posDual C : Set (Rn m))).Nonempty) (x : (Rn m)) :
    ((1 : Mat m)-meanJac C B x).PosDef := by
  let A := fun y => (1:Mat m) - projJac C (affineN B x y)
  have hi := meanJac_integrable C B x
  have hx : 1 - meanJac C B x = ∫ y, A y ∂normal m := by
    rw [meanJac,show (∫ y, A y ∂normal m)=_ from integral_sub (integrable_const _) hi]
    simp
  rw [hx]
  let s := (fun y : (Rn m) => -y) ⁻¹' interior (posDual C : Set (Rn m))
  have hp := prob_open B x s (isOpen_interior.preimage continuous_neg) (by
    rcases hd with ⟨y,hy⟩; exact ⟨-y,by simpa [s]⟩)
  apply strict_pos_of_layer ((integrable_const _).sub hi) _ hp _
  · intro y; exact Matrix.le_iff.mp (projJac_le_one ..)
  · intro y hy
    change (1:Mat m)-projJac C (affineN B x y) = _
    rw [projJac_zero C hy,sub_zero]
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Bias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Unique mean-bias choice (§02, biased projection lemma). We solve
for arbitrary interior means w, later inserting the bias curve. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ} (C : ProperCone ℝ (Rn m)) (B : Rn m ≃L[ℝ] Rn m)

def meanEnergy (a : Rn m) := ∫ x, energy C (affineN B a x) ∂normal m

lemma energy_integrable (a : Rn m) :
    Integrable (fun x => energy C (affineN B a x)) (normal m) := by
  change Integrable (fun x => ‖sample C B a x‖^2 / 2) (normal m)
  apply Integrable.div_const _ 2
  exact ((poly_sample C B a).norm.pow 2).gaussian_integrable
    (((continuous_sample C B a).norm.pow 2).aestronglyMeasurable)

theorem meanEnergy_derivative (a : Rn m) :
    HasFDerivAt (meanEnergy C B) (innerSL ℝ (mean C B a)) a := by
  let F := fun (b x : Rn m) => energy C (affineN B b x)
  have hm (b : Rn m) : Continuous (F b) := by
    exact ((continuous_sample C B b).norm.pow 2).div_const 2
  let D := fun (b x : Rn m) => innerSL ℝ (sample C B b x)
  have hD : Continuous (D a) :=
    (innerSL ℝ).continuous.comp (continuous_sample C B a)
  have he : innerSL ℝ (mean C B a) = ∫ x, D a x ∂normal m :=
    ((show (Rn m) →L[ℝ] (Rn m) →L[ℝ] ℝ from innerSL ℝ).integral_comp_comm
      (sample_integrable ..)).symm
  rw [he]
  let g := fun (x:Rn m) => ‖sample C B a x‖+1
  have hi : Integrable g (normal m) := (sample_integrable ..).norm.add (integrable_const _)
  change HasFDerivAt (fun b => ∫ x, F b x ∂_) _ a
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds a zero_lt_one)
    (Eventually.of_forall fun y => (hm y).aestronglyMeasurable)
    (energy_integrable ..) hD.aestronglyMeasurable _ hi _
  · apply ae_of_all
    intro x b hb
    change ‖innerSL ℝ _‖ ≤ g x
    rw [innerSL_apply_norm]
    have HH : ‖sample C B b x - sample C B a x‖ < 1 := lt_of_le_of_lt (by
      simpa only [sample, affineN, ← dist_eq_norm, dist_add_left,NNReal.coe_one,one_mul] using
        (coneProj_lip C).dist_le_mul (B x + b) (B x + a)) (show dist b a < 1 from hb)
    have hh := norm_add_le (sample C B b x-sample C B a x) (sample C B a x)
    rw [sub_add_cancel] at hh
    dsimp only [g]; linarith
  · apply ae_of_all
    intro x b _
    have h := energy_hasFDeriv C (B x + b)
    simpa only [F,D,sample,affineN,Function.comp_def,zero_add,ContinuousLinearMap.comp_id] using
      h.comp b ((hasFDerivAt_const (B x) b).add (hasFDerivAt_id b))

def dualEnergy (w a : Rn m) := meanEnergy C B a - ⟪w,a⟫

theorem dualEnergy_derivative (w a : Rn m) :
    HasFDerivAt (dualEnergy C B w) (innerSL ℝ (mean C B a-w)) a := by
  rw [map_sub]
  exact (meanEnergy_derivative C B a).sub (innerSL ℝ w).hasFDerivAt

lemma meanEnergy_lower (a y : Rn m) (hy : y ∈ C) :
    ⟪y,a⟫-‖y‖^2/2 ≤ meanEnergy C B a := by
  let f := affineN B a
  have hi := affineN_integrable B a
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ y
  have H : ∫ x, (l (f x)-‖y‖^2/2) ∂normal m ≤ meanEnergy C B a :=
    integral_mono ((l.integrable_comp hi).sub (integrable_const _))
      (energy_integrable ..) (fun x => energy_lower C _ hy)
  rw [integral_sub (l.integrable_comp hi) (integrable_const _), integral_const,
    l.integral_comp_comm hi,affineN_mean B a] at H
  simpa [l] using H

-- explicit bound also useful for uniform estimates
theorem dualEnergy_lower (w a : Rn m)
    {r : ℝ} (hr : 0 < r) (hu : closedBall w r ⊆ C) :
    r*‖a‖-(‖w‖+r)^2/2 ≤ dualEnergy C B w a := by
  by_cases ha : a = 0
  · subst a
    rw [dualEnergy]
    have h := meanEnergy_lower C B (0 : Rn m) 0 C.zero_mem
    simp only [inner_zero_right,norm_zero] at *
    nlinarith
  let d := (r/‖a‖) • a
  have hap : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hh : ‖d‖ = r := by
    simp only [d,norm_smul, Real.norm_eq_abs,abs_of_pos (div_pos hr hap)]
    field_simp
  have h : w+d ∈ C := hu (by rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,hh])
  have he : ⟪d,a⟫ = r * ‖a‖ := by
    simp only [d,real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have hx : ‖w+d‖ ≤ ‖w‖+r := by simpa only [← hh] using norm_add_le w d
  have H := meanEnergy_lower C B a (w+d) h
  rw [inner_add_left,he] at H
  rw [dualEnergy]
  nlinarith [norm_nonneg (w+d)]

theorem bias_exists (w : Rn m) (hw : w ∈ interior (C : Set (Rn m))) :
    ∃ a, mean C B a = w := by
  obtain ⟨r,hr,hu⟩ := nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hw)
  have h := dualEnergy_lower C B w (r := r)
  have hf : Continuous (dualEnergy C B w) := continuous_iff_continuousAt.mpr
    fun x => (dualEnergy_derivative C B w x).continuousAt
  have ht : Tendsto (dualEnergy C B w) (cocompact (Rn m)) atTop := by
    apply tendsto_atTop_mono _ ((tendsto_norm_cocompact_atTop.const_mul_atTop hr).atTop_add
      (g := fun _ => -((‖w‖+r)^2/2)) tendsto_const_nhds)
    intro x; simpa only [← sub_eq_add_neg] using h x hr hu
  obtain ⟨x,hx⟩ := hf.exists_forall_le ht
  have he := IsLocalMin.hasFDerivAt_eq_zero (f := dualEnergy C B w)
    (a := x) (Eventually.of_forall hx) (dualEnergy_derivative C B w x)
  refine ⟨x, sub_eq_zero.mp ?_⟩
  have hp := congrFun (congrArg DFunLike.coe he) (mean C B x - w)
  change ⟪mean C B x-w,mean C B x-w⟫ = 0 at hp
  simpa using hp

lemma pd_equiv {A : Mat m} (h : A.PosDef) :
    ∃ e : Rn m ≃L[ℝ] Rn m, (e:Rn m →L[ℝ] Rn m) = op A := by
  let a : Rn m →ₗ[ℝ] Rn m := (op A).toLinearMap
  have hh : Function.Injective a := by
    intro x y hxy
    by_contra hn
    have hu := (op_posDef_iff.mp h).2 (x-y) (sub_ne_zero.mpr hn)
    have hb : op A (x-y) = 0 := by change a _ = 0; rw [_root_.map_sub,hxy,sub_self]
    rw [hb, inner_zero_right] at hu
    exact (lt_irrefl _ hu)
  let e := LinearEquiv.ofBijective a ⟨hh,LinearMap.injective_iff_surjective.mp hh⟩
  exact ⟨e.toContinuousLinearEquiv, by rfl⟩

theorem mean_injective (hc : (interior (C:Set (Rn m))).Nonempty) :
    Function.Injective (mean C B) := by
  intro x y h
  by_contra hn
  let v := y-x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  let L := fun r:ℝ => x+r • v
  let g := fun r => ⟪v,mean C B (L r)⟫
  have he : StrictMono g := by
    apply strictMono_of_deriv_pos
    intro r
    have hd : HasDerivAt L v r := by
      change HasDerivAt ((fun _:ℝ=>x) + (fun t:ℝ=>t • v)) v r
      simpa only [one_smul,zero_add] using
        ((hasDerivAt_const r x).add ((hasDerivAt_id' r).smul_const v))
    have hg : HasDerivAt g ⟪v,op (meanJac C B (L r)) v⟫ r :=
      (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt r
        ((hasFDerivAt_mean C B _).comp_hasDerivAt r hd)
    rw [hg.deriv]
    exact (op_posDef_iff.mp (mean_pos C B hc _)).2 v hv
  have hh := he zero_lt_one
  simp only [g,L,zero_smul,one_smul,add_zero,v,add_sub_cancel] at hh
  rw [h] at hh
  exact lt_irrefl _ hh

/-- Unique bias at an interior mean; arbitrary value outside interior. -/
def bias (w : Rn m) : Rn m :=
  open Classical in if hw : w ∈ interior (C:Set (Rn m)) then
    (bias_exists C B w hw).choose else 0

theorem bias_mean (w : Rn m) (hw : w ∈ interior (C:Set (Rn m))) :
    mean C B (bias C B w) = w := by
  unfold bias; rw [dite_eq_left hw]
  exact (bias_exists C B w hw).choose_spec

theorem bias_C_one (w : Rn m) (hw : w ∈ interior (C:Set (Rn m))) :
    ContDiffAt ℝ 1 (bias C B) w := by
  let a := bias C B w
  have ha := bias_mean C B w hw
  obtain ⟨e,he⟩ := pd_equiv (mean_pos C B ⟨w,hw⟩ a)
  have h' : HasStrictFDerivAt (mean C B) (e : Rn m →L[ℝ] Rn m) a := by
    rw [he, ← (hasFDerivAt_mean C B a).fderiv]
    exact (mean_C_one C B).hasStrictFDerivAt (by simp)
  let f := h'.localInverse (mean C B) e a
  have hi : f =ᶠ[𝓝 w] bias C B := by
    have ht : mean C B a = w := ha
    have hy := h'.eventually_right_inverse
    rw [ht] at hy
    filter_upwards [hy,isOpen_interior.mem_nhds hw] with y hf hy
    exact mean_injective C B ⟨w,hw⟩ (hf.trans (bias_mean C B y hy).symm)
  have hr : ContDiffAt ℝ 1 f (mean C B a) :=
    (mean_C_one C B).contDiffAt.to_localInverse h'.hasFDerivAt (by norm_num)
  rw [show mean C B a = w from ha] at hr
  exact hr.congr_of_eventuallyEq hi.symm

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_CDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! One-dimensional Gaussian layers, preliminary identities and bounds (§§01--02). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Real Metric Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal
namespace GeneralMahler
namespace Layers

def p (z : ℝ) := ∫ x in Iic z, phi x
def a (z : ℝ) := phi z + z*p z

lemma d_phi (z : ℝ) : HasDerivAt phi (-z*phi z) z := by
  simp_rw [funext phi_apply]
  have he := ((hasDerivAt_id' z).pow 2).neg.div_const 2
  convert he.exp.const_mul (√(2 * π))⁻¹ using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp; ring)

lemma c_phi : Continuous phi :=
  continuous_iff_continuousAt.mpr fun x => (d_phi x).continuousAt
lemma i_phi : Integrable phi := integrable_gaussianPDFReal _ _
lemma e_phi : ∫ x, phi x = 1 := integral_gaussianPDFReal_eq_one _ one_ne_zero

lemma int_Ioi (z : ℝ) : ∫ x in Ioi z, phi x = 1-p z := by
  have h := integral_add_compl measurableSet_Iic (μ := volume) i_phi (s := Iic z)
  rw [compl_Iic,e_phi] at h
  dsimp [p]
  linarith

lemma neg_phi (x : ℝ) : phi (-x) = phi x := by simp [phi_apply]

lemma neg_p (z : ℝ) : p (-z) = 1-p z := by
  rw [← int_Ioi, ← integral_Ici_eq_integral_Ioi]
  unfold p
  let e := (Homeomorph.neg ℝ).toMeasurableEquiv
  have he := setIntegral_map_equiv (μ := volume) e phi (Iic (-z))
  have hm : Measure.map e volume = volume := measurePreserving_neg _ |>.map_eq
  rw [hm] at he
  rw [he]
  have he' : e ⁻¹' Iic (-z) = Ici z := by ext; change (-_ ≤ -z) ↔ _; simp
  rw [he']
  exact integral_congr_ae (ae_of_all _ fun x => neg_phi x)

lemma p_half : p 0 = 1/2 := by
  have he := neg_p 0
  rw [neg_zero] at he; linarith

lemma d_p (z : ℝ) : HasDerivAt p (phi z) z := by
  have H : p = fun x => p 0 + ∫ t in (0:ℝ)..x, phi t := by
    ext x
    rw [p,p, ← intervalIntegral.integral_Iic_sub_Iic i_phi.integrableOn i_phi.integrableOn]
    ring
  rw [H]
  exact ((intervalIntegral.integral_hasDerivAt_right (c_phi.intervalIntegrable ..)
    (c_phi.stronglyMeasurableAtFilter _ _) c_phi.continuousAt).const_add _)

lemma d_a (z : ℝ) : HasDerivAt a (p z) z := by
  have he := (d_phi z).add ((hasDerivAt_id' z).mul (d_p z))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | simp

lemma cp : Continuous p := continuous_iff_continuousAt.mpr fun x => (d_p x).continuousAt
lemma ca : Continuous a := continuous_iff_continuousAt.mpr fun x => (d_a x).continuousAt
lemma p_pos (z : ℝ) : 0 < p z := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun x => (phi_pos _).le) i_phi.integrableOn).mpr
  apply lt_of_lt_of_le (isOpen_Iio.measure_pos volume (Set.nonempty_Iio (a := z)))
  apply measure_mono
  exact fun x hx => ⟨(phi_pos x).ne',show x ≤ z from le_of_lt hx⟩

lemma p_lt_one (z : ℝ) : p z < 1 := by
  have h := p_pos (-z)
  rw [neg_p] at h; linarith

lemma p_mono : StrictMono p := strictMono_of_deriv_pos fun z => by
  rw [(d_p _).deriv]; apply p_pos_phi
where p_pos_phi := phi_pos
lemma a_mono : StrictMono a := strictMono_of_deriv_pos fun z => by
  rw [(d_a _).deriv]; apply p_pos

lemma phi_bdd (z : ℝ) : phi z ≤ (√(2*π))⁻¹ := by
  rw [phi_apply]
  apply mul_le_of_le_one_right (by positivity)
  exact exp_le_one_iff.mpr (by nlinarith)

lemma int_moment1 : Integrable (fun z => z * phi z) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1/2) (by norm_num)).const_mul (√(2*π))⁻¹
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rw [phi_apply]
  ring_nf

lemma moment1 (z : ℝ) : ∫ x in Iic z, -(x * phi x) = phi z := by
  have hlim : Tendsto phi atBot (𝓝 0) := by
    rw [funext phi_apply]
    have he : Tendsto (fun x:ℝ => -(x ^ 2)/2) atBot atBot := by
      refine tendsto_atBot.mpr fun a => ?_
      filter_upwards [eventually_le_atBot (-|2*a|-1)] with x hx
      nlinarith [neg_abs_le (2*a), abs_nonneg (2*a)]
    convert (Real.tendsto_exp_atBot.comp he).const_mul ((√(2*π))⁻¹) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  refine Eq.trans (integral_Iic_of_hasDerivAt_of_tendsto' ?_ int_moment1.neg.integrableOn hlim) (sub_zero _)
  exact fun x hx => by simpa using d_phi x

lemma int_gap (z:ℝ) : Integrable (fun x => (z-x)*phi x) := by
  simp_rw [sub_mul]
  exact (i_phi.const_mul z).sub int_moment1

lemma a_eq (z : ℝ) : a z = ∫ x in Iic z, (z-x)*phi x := by
  simp_rw [sub_mul]
  rw [integral_sub (i_phi.const_mul _).integrableOn int_moment1.integrableOn, integral_const_mul]
  have hh := moment1 z
  rw [integral_neg] at hh
  dsimp [a,p]; rw [← hh]; ring

lemma a_pos (z : ℝ) : 0 < a z := by
  rw [a_eq]
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (int_gap z).integrableOn).mpr
  · apply lt_of_lt_of_le (isOpen_Iio.measure_pos volume (Set.nonempty_Iio (a := z)))
    apply measure_mono
    intro x hx
    exact ⟨ne_of_gt (mul_pos (sub_pos.mpr hx) (phi_pos x)),show x ≤ z from le_of_lt hx⟩
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  exact mul_nonneg (sub_nonneg.mpr hx) (phi_pos x).le

-- Two-sided estimates, exact constants unimportant here.
lemma a_high (s : ℝ) (hs : 0 ≤ s) : a (-s) ≤ phi s := by
  rw [a, neg_phi]
  have h := p_pos (-s); nlinarith

lemma a_low (s : ℝ) (hs : 0 ≤ s) :
    phi s * exp (-4) / (1+s)^2 ≤ a (-s) := by
  let b : ℝ := (1+s)⁻¹
  have hp : 0 < 1+s := by linarith
  have hb : 0 < b := inv_pos.mpr hp
  have hbr : b * (1+s) = 1 := inv_mul_cancel₀ hp.ne'
  have hbs : b*s ≤ 1 := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  let S := Ioc (-s-2*b) (-s-b)
  have hm : MeasurableSet S := measurableSet_Ioc
  have hsub : S ⊆ Iic (-s) := fun x hx => by
    change x ≤ -s; exact hx.2.trans (by linarith)
  have hlow (x) (hx : x ∈ S) : phi s*exp (-4)*b ≤ (-s-x)*phi x := by
    have hh : -s-2*b < x ∧ x ≤ -s-b := hx
    have heQ : x ^ 2 ≤ s ^ 2 + 8 := by
      have h1 : x ^ 2 ≤ (-s-2*b)^2 := by nlinarith
      nlinarith
    have hf : phi s * exp (-4) ≤ phi x := by
      rw [phi_apply,phi_apply,mul_assoc,← Real.exp_add]
      gcongr
      linarith
    rw [mul_comm _ (phi x)]
    exact mul_le_mul hf (by linarith) hb.le (phi_pos x).le
  calc
    _ = ∫ x in S, phi s*exp (-4)*b := by
      rw [setIntegral_const]
      have he : volume.real S = b := by
        rw [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal]
        · ring
        linarith
      rw [he,smul_eq_mul]
      dsimp [b]; field_simp
    _ ≤ ∫ x in S, (-s-x)*phi x := setIntegral_mono_on
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)) ((int_gap _).integrableOn) hm hlow
    _ ≤ a (-s) := by
      rw [a_eq]
      apply setIntegral_mono_set (int_gap _).integrableOn _ (Filter.Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact mul_nonneg (sub_nonneg.mpr hx) (phi_pos _).le

end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Field
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02, Gaussian field notation and mean equations. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Real Set Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers

structure ProjField (m : ℕ) where
  C : ProperCone ℝ (Rn m)
  U : Rn m
  V : Rn m
  U_in : U ∈ interior (C : Set (Rn m))
  V_in : V ∈ interior (posDual C : Set (Rn m))
  ip : ⟪U,V⟫ = (m:ℝ)
  S : Mat m
  pos : S.PosDef
  root : Rn m ≃L[ℝ] Rn m
  matrix_eq : root.toContinuousLinearMap = op S

variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)
abbrev D := posDual q.C
def covMat := q.S * q.S
def shift (z : ℝ) := bias q.C q.root (a z • q.U)
def XT (z : ℝ) := sample q.C q.root (q.shift z)
def Z (g : Rn m) := q.root g
def YT (z : ℝ) (g : Rn m) := coneProj q.D (-(q.Z g+q.shift z))
def Pmat (z : ℝ) (g : Rn m) := projJac q.C (q.Z g + q.shift z)

lemma scaled_interior (z : ℝ) : a z • q.U ∈ interior (q.C:Set (Rn m)) := by
  have he : posDual q.D = q.C := ProperCone.innerDual_innerDual _
  rw [← he]
  obtain ⟨c,hc,h⟩ := interior_dual_bound (show q.U ∈ interior (posDual q.D:Set (Rn m))
    by rw [he]; exact q.U_in)
  apply interior_dual_of_bound (mul_pos (a_pos z) hc)
  intro x hx
  rw [real_inner_smul_left, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x hx) (a_pos z).le

lemma contDiff_a : ContDiff ℝ 1 Layers.a := contDiff_one_iff_deriv.mpr
    ⟨fun x => (d_a x).differentiableAt, by rw [show deriv a = p from funext fun x => (d_a x).deriv]; exact cp⟩

theorem shift_cd : ContDiff ℝ 1 q.shift := by
  rw [contDiff_iff_contDiffAt]
  intro z
  exact (bias_C_one q.C q.root _ (q.scaled_interior z)).comp z
    (contDiff_a.smul contDiff_const).contDiffAt

lemma XT_mean (z : ℝ) : ∫ x, q.XT z x ∂normal m = a z • q.U :=
  bias_mean q.C q.root _ (q.scaled_interior z)

lemma YT_sub (z x) : q.YT z x = q.XT z x - (q.Z x + q.shift z) :=
  proj_moreau q.C _

lemma Y_mean (z : ℝ) : ∫ x, q.YT z x ∂normal m = a z • q.U - q.shift z := by
  simp_rw [q.YT_sub]
  change ∫ x, sample q.C q.root (q.shift z) x-affineN q.root (q.shift z) x ∂normal m = _
  rw [integral_sub (sample_integrable ..) (affineN_integrable ..), affineN_mean]
  rw [← q.XT_mean z]; rfl

lemma XP (z x) : ⟪q.XT z x,q.YT z x⟫ = 0 := by
  rw [YT_sub]
  rw [real_inner_comm,show q.XT z x-(q.Z x+q.shift z) = -((q.Z x+q.shift z)-q.XT z x) by abel]
  rw [inner_neg_left]; exact neg_eq_zero.mpr (proj_orthogonal ..)

def Bt (z : ℝ) := (⟪q.U, ∫ g, q.YT z g ∂normal m⟫)/(m:ℝ)
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_HLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Equation (6): projection integration by parts; derivative
of the cumulative scalar layer kernel. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ}

local notation "std" => EuclideanSpace.basisFun (Fin m) ℝ

lemma trace_op (A : Mat m) :
    trace A = ∑ i, ⟪std i,op A (std i)⟫ := by
  simp_rw [inner_toEuclideanCLM]
  unfold trace
  apply Finset.sum_congr rfl; intro i _
  simp [dotProduct,mulVec,EuclideanSpace.basisFun_apply,EuclideanSpace.single]

namespace ProjField
variable (q : ProjField m)

def avH (z : ℝ) : ℝ := trN (q.covMat * meanJac q.C q.root (q.shift z))
def s0 := trN q.covMat

lemma Z_def (x) : q.Z x = op q.S x := congrFun (congrArg DFunLike.coe q.matrix_eq) x

lemma integrable_pair (z : ℝ) (u v : Rn m) :
    Integrable (fun g => ⟪g,u⟫ * ⟪v,q.XT z g⟫) (normal m) := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ u
  let l' : Rn m →L[ℝ] ℝ := innerSL ℝ v
  have hi : Integrable (fun g => l g * l' (q.XT z g)) (normal m) := by
    apply PolyBound.gaussian_integrable
      ((PolyBound.clm l).mul ((PolyBound.clm l').comp (poly_sample ..)))
      ((l.continuous.mul (l'.continuous.comp (continuous_sample ..))).aestronglyMeasurable)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext
  rw [real_inner_comm u]
  rfl

lemma trace_SPS (A : Mat m) :
    trace (q.covMat * A) = ∑ i, ⟪op q.S (std i),op A (op q.S (std i))⟫ := by
  change trace (q.S*q.S*A) = _
  rw [Matrix.mul_assoc,trace_mul_comm,trace_op]
  apply Finset.sum_congr rfl
  intro i _
  have H := op_iff_hermitian.mp q.pos.1 (std i) (op A (op q.S (std i)))
  simpa only [_root_.map_mul,mul_apply_eq_comp] using H.symm

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_BoundField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform cone hypotheses for the full-real-line estimates.
The extra constants are not inputs to main theorems: for every field
such bounds exist. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m : ℕ}
namespace ProjField

structure Bound (q : ProjField m) (K : ℝ) : Prop where
  one_le : 1 ≤ K
  Ub : ‖q.U‖ ≤ K
  Vb : ‖q.V‖ ≤ K
  S_le : ‖q.S‖ ≤ K
  iS_le : ‖q.root.symm.toContinuousLinearMap‖ ≤ K
  inC : ∀ x ∈ q.D, ‖x‖ ≤ K*⟪q.U,x⟫
  inD : ∀ x ∈ q.C, ‖x‖ ≤ K*⟪q.V,x⟫

variable {q : ProjField m} {K : ℝ} (hK : q.Bound K)

include hK in
lemma Bound.positive : 0 < K := lt_of_lt_of_le zero_lt_one hK.one_le

variable (q) in
theorem Field_isBound : ∃ K, q.Bound K := by
  obtain ⟨c,hc,h₁⟩ := interior_dual_bound q.V_in
  obtain ⟨d,hd,h₂⟩ := interior_dual_bound (C := q.D)
    (V := q.U) (by rw [show posDual q.D = q.C from ProperCone.innerDual_innerDual _]; exact q.U_in)
  let K := (1+‖q.U‖+‖q.V‖+‖q.S‖+‖q.root.symm.toContinuousLinearMap‖) + c⁻¹ + d⁻¹
  have hnorm (n : ℝ) (hn : n ≤ 1+‖q.U‖+‖q.V‖+‖q.S‖+‖q.root.symm.toContinuousLinearMap‖) :
      n ≤ K := by
    dsimp [K]; have h : 0 ≤ c⁻¹+d⁻¹ := by positivity
    linarith
  have he : c⁻¹ ≤ K ∧ d⁻¹ ≤ K := by
    dsimp [K]
    constructor <;> rw [← sub_nonneg] <;> ring_nf <;> positivity
  have hu := norm_nonneg q.U
  have hv := norm_nonneg q.V
  have hh := norm_nonneg q.S
  have ha := norm_nonneg q.root.symm.toContinuousLinearMap
  refine ⟨K, hnorm _ (by linarith),hnorm _ (by linarith), hnorm _ (by linarith),
    hnorm _ (by linarith), hnorm _ (by linarith),fun x hx => ?_,fun x hx => ?_⟩
  · have hb := h₂ x hx
    have hp : 0 ≤ ⟪q.U,x⟫ := le_trans (by positivity) hb
    apply le_trans _ (mul_le_mul_of_nonneg_right he.2 hp)
    rw [le_inv_mul_iff₀ hd]; exact hb
  · have hb := h₁ x hx
    have hp : 0 ≤ ⟪q.V,x⟫ := le_trans (by positivity) hb
    apply le_trans _ (mul_le_mul_of_nonneg_right he.1 hp)
    rw [le_inv_mul_iff₀ hc]; exact hb

include hK in
lemma Bound.normZ (x : Rn m) : ‖q.Z x‖ ≤ K * ‖x‖ := calc
  _ ≤ ‖q.S‖*‖x‖ := by rw [q.Z_def]; exact (op q.S).le_opNorm _
  _ ≤ _ := mul_le_mul_of_nonneg_right hK.S_le (norm_nonneg _)

section
variable (q)

lemma X_int (z : ℝ) : Integrable (q.XT z) (normal m) := sample_integrable ..
lemma Y_int (z : ℝ) : Integrable (q.YT z) (normal m) := by
  rw [funext (q.YT_sub z)]
  exact (q.X_int z).sub (affineN_integrable ..)

lemma avH_le_s (z : ℝ) : q.avH z ≤ q.s0 := by
  unfold avH s0 trN
  have hi := mean_lt_one q.C q.root ⟨_,q.V_in⟩ (q.shift z)
  gcongr
  have hh := Matrix.le_iff.mpr hi.posSemidef
  conv_rhs => rw [← mul_one q.covMat]
  rw [q.trace_SPS,q.trace_SPS]
  exact Finset.sum_le_sum fun i _ =>
    op_order_iff (mean_pos q.C q.root ⟨_,q.U_in⟩ _).1 Matrix.isHermitian_one |>.mp hh _

end
section
variable [NeZero m]
lemma m_pos : 0 < (m:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))

include hK in
lemma Bound.s0_le : q.s0 ≤ K^2 := by
  unfold s0 trN
  rw [div_le_iff₀ m_pos,← mul_one q.covMat,q.trace_SPS]
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  apply le_trans (Finset.sum_le_sum (g := fun i => K^2) ?_)
  · simp; rw [mul_comm]
  intro i hi
  rw [_root_.map_one]
  change ⟪op q.S (b i), op q.S (b i)⟫ ≤ _
  have hn : ‖b i‖ = 1 := b.orthonormal.1 i
  rw [← Z_def,real_inner_self_eq_norm_sq]
  have hh := hK.normZ (b i)
  rw [hn,mul_one] at hh
  gcongr

include hK in
omit [NeZero m] in
lemma Bound.X_mean (z : ℝ) :
    (∫ x, ‖q.XT z x‖ ∂normal m) ≤ K*m*a z := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ q.V
  have hi := q.X_int z
  calc
    _ ≤ ∫ x, K*l (q.XT z x) ∂normal m :=
      integral_mono hi.norm ((l.integrable_comp hi).const_mul K)
        (fun x => hK.inD (q.XT z x) (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi,q.XT_mean]
      change K*⟪q.V,a z • q.U⟫=_
      rw [real_inner_smul_right,real_inner_comm,q.ip]
      ring

include hK in
lemma Bound.Y_mean (z : ℝ) :
    (∫ x, ‖q.YT z x‖ ∂normal m) ≤ K*m*q.Bt z := by
  let l : Rn m →L[ℝ] ℝ := innerSL ℝ q.U
  have hi := q.Y_int z
  calc
    _ ≤ ∫ x, K*l (q.YT z x) ∂normal m :=
      integral_mono hi.norm ((l.integrable_comp hi).const_mul K)
        (fun x => hK.inC (q.YT z x) (proj_mem ..))
    _ = _ := by
      rw [integral_const_mul,l.integral_comp_comm hi]
      dsimp [l,Bt]; have H := m_pos (m := m); field_simp

end

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GaussianTail
attribute [-simp] _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Explicit exponential tail and ball estimates for standard Gaussian.
Constants depend only on the ambient dimension (and polynomial degree). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped Topology ENNReal NNReal
namespace GeneralMahler
variable {m : ℕ}

/-- Uniform lower estimate for the Gaussian mass of a ball measured in
standard coordinates. -/
theorem normal_ball_lower (m : ℕ) {r:ℝ} (hr : 0 < r) :
    ∃ c > (0:ℝ), ∀ (x:Rn m),
      c * exp (-((‖x‖+r)^2)/2) ≤ (normal m).real (closedBall x r) := by
  classical
  let c := (√(2 * π))⁻¹ ^ m
  let v := volume.real (closedBall (0:Rn m) r)
  have hp : 0 < v := ENNReal.toReal_pos (measure_closedBall_pos _ _ hr).ne'
    measure_closedBall_lt_top.ne
  have hc : 0 < c := by dsimp [c]; positivity
  use v*c
  refine ⟨by positivity,?_⟩
  intro x
  let S := closedBall x r
  have hm : MeasurableSet S := measurableSet_closedBall
  let a := c*exp (-((‖x‖+r)^2)/2)
  have HE (t:Rn m) (ht : t ∈ S) : a ≤ nDensity t := by
    change c*_ ≤ c*_
    have h1 : ‖t‖ ≤ ‖x‖+r := by
      rw [show ‖x‖ + r = r + ‖x‖ by ring]
      apply le_trans (show ‖t‖ ≤ ‖t-x‖ + ‖x‖ by simpa using norm_add_le (t-x) x)
      gcongr
      change dist t x ≤ r at ht; simpa [dist_eq_norm] using ht
    gcongr
  change _ ≤ (normal m).real S
  rw [← integral_indicator_one hm,normal_integral]
  have hi : Integrable (S.indicator (1 : Rn m → ℝ)) (normal m) :=
    (integrable_const _).indicator hm
  have hu : Integrable (S.indicator fun _ : Rn m => a) := by
    apply (integrable_indicator_iff hm).mpr
    exact integrableOn_const (hs := measure_closedBall_lt_top.ne)
  have hv : (∫ t, S.indicator (fun _ : Rn m => a) t) = v*a := by
    rw [integral_indicator hm, setIntegral_const]
    change volume.real _ * a = _
    have hb : volume.real S = v := by
      change (volume (closedBall x r)).toReal = (volume (closedBall 0 r) : ℝ≥0∞).toReal
      rw [Measure.addHaar_closedBall_center]
    rw [hb]
  rw [mul_assoc]
  change v*a ≤ _
  rw [← hv]
  apply integral_mono hu (normal_integrable_iff.mp hi)
  intro t
  by_cases ht : t ∈ S
  · simpa [indicator_of_mem ht] using HE t ht
  · simp [indicator_of_notMem ht]

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Cutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform cutoffs for the biased projections.
We strengthen the negative-tail estimate of the manuscript to an exact
cutoff (in z, depending linearly on |g|); this makes mixed-integrability
statements for the Jacobian fields simpler. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable (m : ℕ) [NeZero m] {K : ℝ}
namespace ProjField

def cutoffC (m : ℕ) (K : ℝ) := 1+2*K*(K+K*m*K^2/a 0)

theorem negative_cutoff (hk : 1 ≤ K) :
    ∃ C ≥ (1:ℝ), ∀ q : ProjField m, q.Bound K → ∀ (s:ℝ) x, C*(1+‖x‖) < s →
      -(q.Z x + q.shift (-s)) ∈ interior (q.D : Set (Rn m)) := by
  have hp : 0 < K := lt_of_lt_of_le zero_lt_one hk
  have hm : 0 < (m:ℝ) := m_pos
  let r := K⁻¹ -- shift center by 2
  have hr : 0 < r := inv_pos.mpr hp
  obtain ⟨c,hc,h₁⟩ := normal_ball_lower m hr
  let d := K*m*(√(2*π))⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  let L := |log c-log d|
  have hL : 0 ≤ L := abs_nonneg _
  let C := 2 + r + 2*K + L
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC, fun q hq s x hs => ?_⟩
  have hu : 0 ≤ s := by nlinarith [norm_nonneg x]
  by_contra hh
  obtain ⟨v,hv,hvn,hx⟩ := exists_ray_of_not_interior_dual hh
  rw [inner_neg_left] at hx
  let g := x+q.root.symm ((2:ℝ) • v)
  let S := closedBall g r
  have hgn : ‖g‖ ≤ ‖x‖+K*2 := by
    apply (norm_add_le ..).trans
    have hb : ‖(2:ℝ) • v‖ = 2 := by rw [norm_smul,hvn]; norm_num
    have he := q.root.symm.toContinuousLinearMap.le_opNorm ((2:ℝ) • v)
    rw [hb] at he
    apply add_le_add_right
    exact he.trans (mul_le_mul_of_nonneg_right hq.iS_le (by norm_num))
  have hnorm (y) (hy : y ∈ S) : 1 ≤ ‖q.XT (-s) y‖ := by
    have h₁ : ‖q.Z g - q.Z y‖ ≤ 1 := calc
      _ = ‖q.Z (g-y)‖ := by unfold Z; rw [_root_.map_sub]
      _ ≤ K*‖g-y‖ := hq.normZ _
      _ ≤ K*r := mul_le_mul_of_nonneg_left (by
          change dist y g ≤ r at hy; rwa [dist_comm, dist_eq_norm] at hy) hp.le
      _ = _ := mul_inv_cancel₀ hp.ne'
    have h₂ := real_inner_le_norm (q.Z g-q.Z y) v
    have he : q.Z g = q.Z x + (2:ℝ) • v := by simp only [g,Z,_root_.map_add,
      ContinuousLinearEquiv.apply_symm_apply]
    have hp : 0 ≤ ⟪v,q.XT (-s) y - (q.Z y + q.shift (-s))⟫ :=
      mem_posDual.mp (proj_residual_dual q.C _) hv
    rw [inner_sub_left, he, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq,hvn] at h₂
    have h₃ := real_inner_le_norm (q.XT (-s) y) v
    rw [real_inner_comm,inner_sub_left,inner_add_left] at hp
    rw [inner_add_left] at hx; rw [hvn] at h₃
    rw [he] at h₁
    nlinarith
  have hprob : (normal m).real S ≤ ∫ y, ‖q.XT (-s) y‖ ∂normal m := calc
    _ = ∫ y in S, (1:ℝ) ∂normal m := by simp
    _ ≤ ∫ y in S, ‖q.XT (-s) y‖ ∂normal m :=
      setIntegral_mono_on (integrable_const _).integrableOn (q.X_int _).norm.integrableOn
        measurableSet_closedBall hnorm
    _ ≤ _ := setIntegral_le_integral (q.X_int _).norm (ae_of_all _ fun y => norm_nonneg _)
  have hlt : c * Real.exp (-((‖g‖+r)^2)/2) ≤ d * Real.exp (-(s^2)/2) := calc
    _ ≤ _ := h₁ g
    _ ≤ _ := hprob
    _ ≤ K*m*a (-s) := hq.X_mean _
    _ ≤ K*m*phi s := mul_le_mul_of_nonneg_left (a_high s hu) (by positivity)
    _ = _ := by unfold d; rw [phi_apply]; ring
  have hll : log c - (‖g‖+r)^2/2 ≤ log d - s^2/2 := by
    have he : log (c * Real.exp (-((‖g‖+r)^2)/2)) ≤ log (d * Real.exp (-(s^2)/2)) :=
      Real.log_le_log (by positivity) hlt
    rw [Real.log_mul hc.ne' (by positivity),Real.log_mul hd.ne' (by positivity),
      Real.log_exp,Real.log_exp] at he
    linarith
  have he : ‖g‖+r+L+2 ≤ s := by
    have hi : C+‖x‖ ≤ s := by nlinarith [norm_nonneg x]
    unfold C at hi; linarith
  have ht := neg_abs_le (log c-log d)
  change -L ≤ _ at ht
  have hi : (‖g‖+r+L+2)^2 ≤ s^2 := by gcongr
  nlinarith [mul_nonneg hL (add_nonneg (norm_nonneg g) hr.le),norm_nonneg g]

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Rapid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polynomial growth and rapid layer decay with polynomial loss in
the Gaussian variables. Fubini and moment estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise
namespace GeneralMahler
section
variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
def rapid (f:X→E) := ∀ n:ℕ, ∃ C : ℝ, 0≤C ∧ ∀ x, ‖f x‖*(1+‖x‖)^n ≤ C
/-- First variable rapid (the tail layer), second moderate (Gaussian). -/
def mixed (f:X → Y → E) := ∀ n:ℕ, ∃ (C : ℝ) (m : ℕ), 0≤C ∧ ∀ x y,
    ‖f x y‖*(1+‖x‖)^n ≤ C*(1+‖y‖)^m

namespace mixed
variable {f g : X → Y → E}

lemma mono {g : X→Y→F} (hf : mixed f) (h : ∀ x y, ‖g x y‖ ≤ ‖f x y‖) :
    mixed g := by
  intro n
  obtain ⟨C,m,hc,h'⟩ := hf n
  exact ⟨C,m,hc,fun x y=>le_trans (mul_le_mul_of_nonneg_right (h x y) (by positivity)) (h' x y)⟩

lemma neg (hf : mixed f) : mixed fun x y => -(f x y) := hf.mono (by simp)

lemma of_rapid {f : X → E} (h : rapid f) : mixed (fun x (_ : Y) => f x) :=
  fun n => by
    obtain ⟨C,hc,H⟩ := h n
    exact ⟨C,0,hc,fun x _=>by simpa using H x⟩
end mixed

section Integrals
variable [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsAddHaarMeasure μ]

lemma envelope_inv_int :
    Integrable (fun x:X => ((1+‖x‖)^(Module.finrank ℝ X+1))⁻¹) μ := by
  have H := (integrable_one_add_norm (μ := μ)
    (r := ((Module.finrank ℝ X+1:ℕ):ℝ)) (by exact_mod_cast Nat.lt_succ_self _))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext x; rw [Real.rpow_neg (by positivity),Real.rpow_natCast]

lemma mixed_integrable_left {f : X → Y → E}
    (h : mixed f) (y : Y) (hf : AEStronglyMeasurable (fun x => f x y) μ) :
    Integrable (fun x => f x y) μ := by
  obtain ⟨C,l,hc,H⟩ := h (Module.finrank ℝ X+1)
  refine ((envelope_inv_int (X := X)).const_mul (C*(1+‖y‖)^l)).mono' hf (ae_of_all _ fun x => ?_)
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]; apply H

end Integrals
end
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_pRapid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar tail estimates near §02. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped ENNReal NNReal Topology
namespace GeneralMahler

lemma rapid_exp_sq {c : ℝ} (hc : 0 < c) :
    rapid (fun t:ℝ => Real.exp (-(c*t^2))) := by
  intro n
  have Hb : ∀ y:ℝ, -c*y^2 + n*y ≤ (n:ℝ)^2/(4*c) := by
    intro y
    apply (le_div_iff₀ (by positivity : 0 < 4*c)).mpr
    nlinarith [sq_nonneg ((n:ℝ)-2*c*y)]
  use Real.exp ((n:ℝ)^2/(4*c)), exp_nonneg _
  intro t
  rw [Real.norm_eq_abs,abs_of_pos (exp_pos _),Real.norm_eq_abs]
  have ht : 1+|t| ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
  apply le_trans (mul_le_mul_of_nonneg_left (show (1+|t|)^n ≤ _ from pow_le_pow_left₀ (by positivity) ht _) (exp_nonneg _))
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa [sq_abs] using Hb |t|

namespace rapid
variable {E : Type*} [NormedAddCommGroup E] {f g : E → ℝ}
lemma product (hf : rapid f) (hg : PolyBound g) : rapid (fun x => f x*g x) :=
  fun n => by
    obtain ⟨C,m,hc,h₁⟩ := hg
    obtain ⟨D,hd,h₂⟩ := hf (m+n)
    use D*C, by positivity
    intro x
    calc
      _ ≤ ‖f x‖*(C*(1+‖x‖)^m)*(1+‖x‖)^n := by rw [norm_mul]; gcongr; apply h₁
      _ = ‖f x‖*(1+‖x‖)^(m+n)*C := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (h₂ _) hc
lemma mono (hf : rapid f) (h : ∀ x, ‖g x‖ ≤ ‖f x‖) : rapid g := by
  intro n
  obtain ⟨c,hc,h₁⟩ := hf n
  exact ⟨c,hc,fun x => le_trans (mul_le_mul_of_nonneg_right (h x) (by positivity)) (h₁ x)⟩
lemma tail_limit {f : ℝ → ℝ} (h : rapid f) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨c,hc,h₁⟩ := h 1
  simp only [pow_one] at h₁
  apply squeeze_zero_norm'
    (a := fun t => c*(1+t)⁻¹) ?_
  · have htop : Tendsto (fun t : ℝ => 1+t) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    have he : Tendsto (fun t => c*(1+t)⁻¹) atTop (𝓝 (c*(0:ℝ))) := tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp htop)
    simpa using he
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    simpa [Real.norm_of_nonneg hx.le] using h₁ x
lemma integrable_real {f : ℝ → ℝ} (h : rapid f)
    (hm : Measurable f) : Integrable f :=
  mixed_integrable_left (mixed.of_rapid h) (0:ℝ) hm.aestronglyMeasurable
end rapid

namespace Layers
lemma rapid_phi : rapid phi := by
  have hp := (rapid_exp_sq (show 0<(1/2:ℝ) by norm_num)).product
    (PolyBound.const (X := ℝ) (√(2*π))⁻¹)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext x; rw [phi_apply]; ring_nf

lemma p_small :
    ∃ C > (0:ℝ), ∀ s ≥ (0 : ℝ), p (-s) ≤ phi s * C := by
  have H := phi_pos 1
  use 1+(phi 1)⁻¹, by positivity
  intro s hs
  rcases le_total s 1 with h|h
  · have h₁ : phi 1 ≤ phi s := by
      simp_rw [phi_apply]; gcongr
    have h₂ : 1 ≤ phi s / phi 1 := (le_div_iff₀ H).mpr (by simpa using h₁)
    have h₃ := p_lt_one (-s)
    rw [div_eq_mul_inv] at h₂
    nlinarith [phi_pos s]
  · have h' := a_pos (-s)
    rw [a, neg_phi] at h'
    nlinarith [p_pos (-s),phi_pos s, inv_pos.mpr H]

def st (s : ℝ) := if 0 ≤ s then (1:ℝ) else 0
@[fun_prop] lemma measurable_st : Measurable st :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma rapid_p : rapid (fun s => p s-st s) := by
  obtain ⟨C,hc,h⟩ := p_small
  have he : rapid (fun x => phi x*C) := rapid_phi.product (PolyBound.const C)
  apply he.mono
  intro s
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (by apply mul_nonneg (phi_pos s).le hc.le)]
  unfold st; split_ifs with hh
  · rw [abs_of_nonpos (by linarith [p_lt_one s])]
    linarith [neg_p s,h s hh]
  · rw [sub_zero,abs_of_pos (p_pos s)]
    simpa only [neg_neg, neg_phi] using h (-s) (by linarith)
lemma poly_a : PolyBound a := by
  have h₁ : PolyBound phi := PolyBound.of_bound (√(2*π))⁻¹ (fun x => by
    rw [Real.norm_of_nonneg (phi_pos _).le]; exact phi_bdd _)
  have h₂ : PolyBound p := PolyBound.of_bound 1 (fun x => by
    rw [Real.norm_of_nonneg (p_pos _).le]; exact (p_lt_one _).le)
  exact h₁.add (PolyBound.id.mul h₂)

end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MixedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer integrals and error estimates. -/
noncomputable section
open Filter Set Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)
def Gstep (z : ℝ) : Mat m := st z • (1:Mat m)
def Pstep (z : ℝ) (g : Rn m) : Mat m := q.Pmat z g - Gstep z
def PD (z : ℝ) (g : Rn m) : Mat m := p z • (1:Mat m) - q.Pmat z g

lemma PD_sm : StronglyMeasurable q.PD.uncurry := by
  apply StronglyMeasurable.sub
  · exact (cp.stronglyMeasurable.comp_measurable measurable_fst).smul stronglyMeasurable_const
  · apply (strongly_projJac q.C).comp_measurable
    exact ((q.root.continuous.comp continuous_snd).add (q.shift_cd.continuous.comp continuous_fst)).measurable

section
variable [NeZero m]
omit [NeZero m] in
lemma one_op_le : ‖(1:Mat m)‖ ≤ 1 := by
  rw [← op_norm,_root_.map_one]
  exact ContinuousLinearMap.norm_id_le

omit [NeZero m] in
lemma Pstep_norm (s g) : ‖q.Pstep s g‖ ≤ 2 := by
  have h : ‖Gstep s (m := m)‖ ≤ 1 := by
    unfold Gstep st; split_ifs <;> simp only [one_smul,zero_smul]
    · exact one_op_le
    simp
  exact (norm_sub_le ..).trans (by linarith [show ‖q.Pmat s g‖ ≤ 1 from projJac_norm ..])

end
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Mills
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §03 scalar log-Jacobian weights. Antitonicity of W via an
elementary argument that integration from -∞ preserves log concavity. -/
noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler
namespace rapid
lemma tail_limit_bot {f:ℝ→ℝ} (hf:rapid f) :
    Tendsto f atBot (𝓝 0) := by
  have h : rapid fun x:ℝ=>f (-x) := by
    intro n
    obtain ⟨C,hc,he⟩ := hf n
    exact ⟨C,hc,fun x=>by simpa using he (-x)⟩
  simpa [Function.comp_def] using h.tail_limit.comp tendsto_neg_atBot_atTop
end rapid
namespace Layers

def MillsC (x : ℝ) := phi x/p x
def MillsJ (x : ℝ) := x+MillsC x
def MillsW (x : ℝ) := MillsJ x*MillsC x

end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MillsLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polynomial bounds and primitive integrations for log profiles. -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler

lemma poly_of_d {f g:ℝ→ℝ} (h:∀ x, HasDerivAt f (g x) x)
    (hg:PolyBound g) : PolyBound f := by
  obtain ⟨C,n,hC,hg⟩ := hg
  have HE (a b:ℝ) (hh:a<b) :
      ∃ t∈Ioo a b,f b - f a = g t*(b-a) := by
    have hi : Differentiable ℝ f := fun x=>(h x).differentiableAt
    obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope f hh hi.continuous.continuousOn hi.differentiableOn
    rw [(h t).deriv, eq_div_iff (sub_pos.mpr hh).ne'] at he
    exact ⟨t,ht,he.symm⟩
  have he (x:ℝ) : ‖f x-f 0‖ ≤ C*(1+‖x‖)^n*‖x‖ := by
    have hb (t:ℝ) (ht:‖t‖≤‖x‖) (hh:f x-f 0=g t*x) :
        ‖f x-f 0‖≤C*(1+‖x‖)^n*‖x‖ := by rw [hh,norm_mul]; gcongr; apply le_trans (hg t); gcongr
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · obtain ⟨t,ht,h⟩ := HE x 0 hx
      apply hb t
      · rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_neg hx,abs_of_neg ht.2]; linarith [ht.1]
      linarith
    · simp
    obtain ⟨t,ht,h⟩ := HE 0 x hx
    apply hb t
    · rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hx,abs_of_pos ht.1]; exact ht.2.le
    rwa [sub_zero] at h
  refine ⟨‖f 0‖+C,n+1,add_nonneg (by positivity) hC,fun x=>?_⟩
  have h₀ : ‖f x‖ ≤ ‖f x-f 0‖+‖f 0‖ := by simpa using norm_add_le (f x-f 0) (f 0)
  apply le_trans h₀
  rw [add_mul,pow_succ]
  have hp : (1:ℝ) ≤ (1+‖x‖)^n := one_le_pow₀ (by simp)
  have he' := he x
  have h₁ := mul_le_mul_of_nonneg_left (show 1≤(1+‖x‖)^n * (1+‖x‖) by nlinarith [norm_nonneg x]) (norm_nonneg (f 0))
  have h₂ : C*(1+‖x‖)^n*‖x‖ ≤ C*((1+‖x‖)^n * (1+‖x‖)) := by rw [← mul_assoc]; gcongr; simp
  linarith

namespace Layers
def LC (x:ℝ) := Real.log (MillsC x)
def LP (x:ℝ) := Real.log (p x)
end Layers
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §01 the primary profiles and their identities. -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler.Profile
open Layers

def X (x:ℝ) := p x/phi x
def Y (x:ℝ) := (1-p x)/phi x
def f (x:ℝ) := -(1-p x)-Real.log (p x)
def j (x:ℝ) := -p x-Real.log (1-p x)
def Xd (x:ℝ) := 1+x*X x
def Yd (x:ℝ) := x*Y x-1
def g (x:ℝ) := (1-X x^2*f x-Y x^2*j x)/2
def d (x:ℝ) := Xd x^2*f x+Yd x^2*j x
def v (x:ℝ) := Real.log (X x*Y x)
def N (g:ℝ→ℝ) := fun x:ℝ=> x*deriv g x - deriv (deriv g) x
def N2 (g:ℝ→ℝ) := fun x=>N g x+2*g x

def fd (x:ℝ) := -(phi x)*(1-p x)/p x
def jd (x:ℝ) := phi x * p x/(1-p x)

def gd (x:ℝ) := -(X x*Xd x*f x+Y x*Yd x*j x)

end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_TestFun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Real test functions, all orders of polynomial growth used in the proof. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
namespace GeneralMahler

def Moderate : ℕ→(ℝ→ℝ)→Prop
  | 0,f=> PolyBound f ∧ Continuous f
  | n+1,f => PolyBound f ∧ Differentiable ℝ f ∧ Moderate n (deriv f)
def TestF (f:ℝ→ℝ) := ∀ n, Moderate n f
variable {f g:ℝ→ℝ} {n : ℕ}
namespace Moderate
lemma poly (hf:Moderate n f) : PolyBound f := by cases n <;> apply hf.1
lemma diff (hf:Moderate (n+1) f) : Differentiable ℝ f := hf.2.1
lemma dc (hf:Moderate n f) : Continuous f := by
  cases n
  · exact hf.2
  exact hf.diff.continuous
lemma der (hf:Moderate (n+1) f) : Moderate n (deriv f) := hf.2.2
lemma mk (hh:∀ x, HasDerivAt f (g x) x) (hb:PolyBound f) (hc:Moderate n g) :
    Moderate (n+1) f := by
  have h : deriv f=g := funext fun x=>(hh x).deriv
  exact ⟨hb,fun x=>(hh x).differentiableAt,h.symm ▸ hc⟩
lemma mk' (hh:∀ x, HasDerivAt f (g x) x) (hc:Moderate n g) :
    Moderate (n+1) f := mk hh (poly_of_d hh hc.poly) hc
lemma mono (hf:Moderate (n+1) f) : Moderate n f := by
  induction n generalizing f with
  | zero=> exact ⟨hf.poly,hf.dc⟩
  | succ n ih=> exact ⟨hf.poly,hf.diff,ih hf.der⟩
lemma add (hf:Moderate n f) (hg:Moderate n g) : Moderate n fun x=>f x+g x := by
  induction n generalizing f g with
  | zero=> exact ⟨hf.poly.add hg.poly,hf.dc.add hg.dc⟩
  | succ n ih=>
    exact mk' (fun x=> (hf.diff x).hasDerivAt.fun_add (hg.diff x).hasDerivAt)
      (ih hf.der hg.der)
lemma neg (hf:Moderate n f) : Moderate n fun x=> -(f x) := by
  induction n generalizing f with
  | zero=> exact ⟨hf.poly.neg,hf.dc.neg⟩
  | succ n ih=>
    exact mk' (fun x=> (hf.diff x).hasDerivAt.neg) (ih hf.der)
lemma sub (hf:Moderate n f) (hg:Moderate n g) : Moderate n fun x=>f x-g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma mul (hf:Moderate n f) (hg:Moderate n g) : Moderate n fun x=> f x*g x := by
  induction n generalizing f g with
  | zero=> exact ⟨hf.poly.mul hg.poly,hf.dc.mul hg.dc⟩
  | succ n ih=>
    exact mk' (fun x=>(hf.diff x).hasDerivAt.fun_mul (hg.diff x).hasDerivAt)
      ((ih hf.der hg.mono).add (ih hf.mono hg.der))
lemma const (c:ℝ) (n:ℕ) : Moderate n fun _=> c := by
  induction n generalizing c with
  | zero=> exact ⟨PolyBound.const _, continuous_const⟩
  | succ n ih=> exact mk' (fun x=>hasDerivAt_const x c) (ih 0)
lemma id (n : ℕ) : Moderate n fun x=> x := by
  cases n with
  | zero=> exact ⟨PolyBound.id,continuous_id⟩
  | succ n=> exact mk' (fun x=>hasDerivAt_id' x) (const 1 n)
end Moderate

namespace TestF
variable (hf:TestF f)
include hf in lemma poly : PolyBound f := (hf 0).1
include hf in lemma cont : Continuous f := (hf 0).2
include hf in lemma diff : Differentiable ℝ f := Moderate.diff (hf 1)
include hf in lemma der : TestF (deriv f) := fun n=> Moderate.der (hf (n+1))
include hf in lemma sub (hg:TestF g) : TestF fun x=> f x-g x := fun n=>(hf n).sub (hg n)
include hf in lemma mul (hg:TestF g) : TestF fun x=> f x*g x := fun n=>(hf n).mul (hg n)
lemma const (c:ℝ) : TestF fun _=> c := Moderate.const c
lemma id : TestF fun x=>x := Moderate.id
end TestF

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_HMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
### H_f, A, L from Equation (7) and their growth bounds
-/
noncomputable section
open Set Filter Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)

def kerH (f : ℝ → ℝ) (z : ℝ) (x : Rn m) := deriv f z • q.PD z x
def Hmat (f : ℝ → ℝ) (x : Rn m) := ∫ z, q.kerH f z x
def Amat := q.Hmat id
def avgA := ∫ x, q.Amat x ∂normal m

variable [NeZero m] {f : ℝ→ℝ} (h : PolyBound (deriv f))

omit [NeZero m] in
lemma H_sm : StronglyMeasurable (q.kerH f).uncurry :=
  ((measurable_deriv f).stronglyMeasurable.comp_measurable measurable_fst).smul q.PD_sm

omit [NeZero m] in
lemma H_ams (y : Rn m) :
    AEStronglyMeasurable (fun x => q.kerH f x y) :=
  ((q.H_sm (f := f)).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable

omit [NeZero m] in
lemma H_SM : StronglyMeasurable (q.Hmat f) := (q.H_sm).integral_prod_left

lemma poly_id_der : PolyBound (deriv (id : ℝ → ℝ)) := by
  rw [show deriv (id : ℝ → ℝ) = (fun _ => (1:ℝ)) from funext fun x => deriv_id x] ; exact PolyBound.const 1

omit [NeZero m] in
lemma A_SM : StronglyMeasurable q.Amat := q.H_SM

def coord (i : Fin m) : Rn m →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).toContinuousLinearMap
omit [NeZero m] in
@[simp] lemma coord_apply (i : Fin m) (x) : coord i x = x i := rfl

end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Order and functional calculus for real symmetric matrices. -/
noncomputable section
open Set Filter Matrix Real
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
variable {m : ℕ} {A B : Mat m}

lemma op_eigen (h : A.IsHermitian) (i : Fin m) :
    op A (h.eigenvectorBasis i) = h.eigenvalues i • (h.eigenvectorBasis i) := by
  apply WithLp.ofLp_injective
  rw [show op = _ from (rfl : op = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)),
    Matrix.ofLp_toEuclideanCLM]
  exact h.mulVec_eigenvectorBasis i

lemma neg_eigen {A : Mat m} (h : A.IsHermitian) (hn : ¬ 0 ≤ A) :
    ∃ v : Rn m, ∃ c : ℝ, c < 0 ∧ ‖v‖ = 1 ∧ op A v = c • v := by
  by_contra! hu
  apply hn; apply Matrix.PosSemidef.nonneg
  apply h.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  by_contra! he
  exact hu _ _ he (h.eigenvectorBasis.orthonormal.1 i) (op_eigen h i)

/-- Square root order, by testing an eigenvector of A-B. -/
lemma sq_order_cancel (ha : 0 ≤ A) (hb : 0 ≤ B)
    (hh : A*A ≤ B*B) : A ≤ B := by
  have ha' := ha.posSemidef
  have hb' := hb.posSemidef
  by_contra hn
  have hv : ¬ 0 ≤ B-A := by rwa [sub_nonneg]
  obtain ⟨v,c,hc,hv,he⟩ := neg_eigen (hb'.1.sub ha'.1) hv
  have hf (D : Mat m) (hd : D.IsHermitian) :
      (D*D).IsHermitian ∧ ⟪v,op (D*D) v⟫ = ‖op D v‖^2 := by
    constructor
    · change IsSelfAdjoint (D*D)
      show star (D*D)=D*D
      simp only [star_mul, (show star D = D from hd)]
    rw [_root_.map_mul,mul_apply_eq_comp, ← op_iff_hermitian.mp hd,
      real_inner_self_eq_norm_sq]
  obtain ⟨H,H'⟩ := hf _ ha'.1
  obtain ⟨G,G'⟩ := hf _ hb'.1
  have hm := (op_order_iff H G).mp hh v
  rw [H',G'] at hm
  rw [_root_.map_sub,_root_.sub_apply] at he
  have hh := (op_posSemidef_iff.mp hb').2 v
  have he : op A v = op B v + (-c) • v := by rw [neg_smul, ← he]; abel
  rw [he,norm_add_sq_real,real_inner_smul_right,real_inner_comm v,
    norm_smul,hv,Real.norm_eq_abs,abs_of_pos (neg_pos.mpr hc)] at hm
  nlinarith

variable {l r : ℝ}

abbrev scalar (m : ℕ) (l : ℝ) : Mat m := l • (1:Mat m)
lemma scalar_eq (m : ℕ) (l : ℝ) : scalar m l = algebraMap ℝ _ l := by rw [Algebra.algebraMap_eq_smul_one]
lemma scalar_sym (m : ℕ) (l : ℝ) : (scalar m l).IsHermitian :=
  isHermitian_one.smul (show IsSelfAdjoint l by simp [IsSelfAdjoint])

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MatrixBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Spectral boxes and clipping; normalization preparation. -/
noncomputable section
open Set Filter Real Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

def specBox (m : ℕ) (a b : ℝ) : Set (Mat m) :=
  {A | A.IsHermitian ∧ scalar m a ≤ A ∧ A ≤ scalar m b}

lemma op_scalar (a : ℝ) (v:Rn m) : op (scalar m a) v = a • v := by
  simp only [scalar,_root_.map_smul,_root_.map_one,_root_.smul_apply]
  rfl

lemma form_scalar (a : ℝ) (v:Rn m) : ⟪v,op (scalar m a) v⟫ = a * ‖v‖^2 := by
  rw [op_scalar,real_inner_smul_right,real_inner_self_eq_norm_sq]

lemma scalar_le' (a b : ℝ) (hab:a ≤ b) : scalar m a ≤ scalar m b := by
  refine (op_order_iff (scalar_sym ..) (scalar_sym ..)).mpr fun v=>?_
  rw [form_scalar,form_scalar]; gcongr

lemma mem_box_form {A : Mat m} {a b:ℝ} :
    A∈specBox m a b ↔ A.IsHermitian ∧
      (∀ v, a * ‖v‖^2 ≤ ⟪v,op A v⟫) ∧ ∀ v, ⟪v,op A v⟫ ≤ b * ‖v‖^2 := by
  change (_ ∧ _) ↔ _
  apply and_congr_right; intro h
  rw [op_order_iff (scalar_sym ..) h, op_order_iff h (scalar_sym ..)]
  simp only [form_scalar]

lemma form_posDef {a b : ℝ} (ha:0<a) {A:Mat m} (hm : A∈specBox m a b) :
    A.PosDef := by
  rw [op_posDef_iff]
  rw [mem_box_form] at hm
  exact ⟨hm.1,fun x hx => (mul_pos ha (pow_pos (norm_pos_iff.mpr hx) _)).trans_le (hm.2.1 x)⟩

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Transform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Linear transformations in the paper's Cone reduction lemma. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure Real
open scoped ENNReal RealInnerProductSpace
namespace GeneralMahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Linear image, using the inverse so the cone is obviously closed. -/
def pushCone (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) : ProperCone ℝ E :=
  ProperCone.comap (B.symm.toContinuousLinearEquiv : E →L[ℝ] E) C

@[simp] lemma mem_pushCone {C : ProperCone ℝ E} {B : E ≃ₗ[ℝ] E} {x : E} :
    x ∈ pushCone B C ↔ B.symm x ∈ C := Iff.rfl

lemma pushCone_carrier (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) :
    (pushCone B C : Set E) = B '' (C : Set E) := by
  ext x
  obtain ⟨x,rfl⟩ := B.surjective x
  simp [B.injective.eq_iff]

@[simp] lemma apply_mem_interior_pushCone {C : ProperCone ℝ E} {B : E ≃ₗ[ℝ] E} {x : E} :
    B x ∈ interior (pushCone B C : Set E) ↔ x ∈ interior (C : Set E) := by
  let e := B.toContinuousLinearEquiv.toHomeomorph
  rw [pushCone_carrier]
  change e x ∈ interior (e '' (C : Set E)) ↔ _
  rw [← e.image_interior]
  simp

/-- Inverse transpose in Euclidean metric. -/
def contra (B : E ≃ₗ[ℝ] E) : E ≃ₗ[ℝ] E :=
  { LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) with
    invFun := LinearMap.adjoint (B : E →ₗ[ℝ] E)
    left_inv := by
      intro x
      apply ext_inner_left ℝ
      intro y
      change ⟪y, LinearMap.adjoint (B : E →ₗ[ℝ] E) (LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) x)⟫ = _
      rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
      simp
    right_inv := by
      intro x
      apply ext_inner_left ℝ
      intro y
      change ⟪y, LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) (LinearMap.adjoint (B : E →ₗ[ℝ] E) x)⟫ = _
      rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
      simp }

lemma pair_contra (B : E ≃ₗ[ℝ] E) (x y : E) :
    ⟪B x, contra B y⟫ = ⟪x,y⟫ := by
  change ⟪B x, LinearMap.adjoint (B.symm : E →ₗ[ℝ] E) y⟫ = _
  rw [LinearMap.adjoint_inner_right]
  simp

lemma dual_pushCone (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) :
    posDual (pushCone B C) = pushCone (contra B) (posDual C) := by
  ext x
  obtain ⟨q,rfl⟩ := (contra B).surjective x
  rw [mem_pushCone, LinearEquiv.symm_apply_apply, mem_posDual, mem_posDual]
  constructor
  · intro hx y hy
    rw [← pair_contra B]
    exact hx (by simpa using hy)
  · intro hx y hy
    obtain ⟨v,rfl⟩ := B.surjective y
    rw [pair_contra B]
    apply hx (by simpa using hy)

def jac (B : E ≃ₗ[ℝ] E) : ℝ := LinearMap.det (B : E →ₗ[ℝ] E)

omit [FiniteDimensional ℝ E] in
@[simp] lemma jac_ne_zero (B : E ≃ₗ[ℝ] E) : jac B ≠ 0 := by
  rw [jac, ← LinearEquiv.coe_det]
  exact Units.ne_zero _

lemma jac_mul_contra (B : E ≃ₗ[ℝ] E) :
    jac B * jac (contra B) = 1 := by
  let b := stdOrthonormalBasis ℝ E
  have he : jac (contra B) = jac B.symm := by
    change LinearMap.det (LinearMap.adjoint _) = _
    rw [jac, ← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis]
    rw [LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    rfl
  rw [he]; exact LinearEquiv.det_mul_det_symm B

variable [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]

lemma chi_transform' (B D : E ≃ₗ[ℝ] E) (h : ∀ x y, ⟪B x, D y⟫ = ⟪x,y⟫)
    (C : ProperCone ℝ E) (y : E) :
    chi (pushCone B C) (D y) = |jac B| * chi C y := by
  let e := B.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he := setIntegral_map_equiv (μ := volume) e
    (fun x => exp (-⟪x,D y⟫)) (pushCone B C)
  change (∫ x in pushCone B C, exp (-⟪x,D y⟫) ∂ Measure.map (B : E →ₗ[ℝ] E) volume) =
    ∫ x in (⇑B) ⁻¹' (pushCone B C : Set E), exp (-⟪B x,D y⟫) at he
  rw [map_linearMap_addHaar_eq_smul_addHaar _ (jac_ne_zero B), Measure.restrict_smul,
    integral_smul_measure] at he
  have hp : ⇑B ⁻¹' (pushCone B C : Set E) = C := by ext; simp
  rw [hp] at he
  simp_rw [h] at he
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at he
  have hz : chi C y = |jac B|⁻¹ * chi (pushCone B C) (D y) := by
    -- reorder one remaining inner product
    unfold chi
    simpa only [real_inner_comm (D y), real_inner_comm y, jac, abs_inv, smul_eq_mul] using he.symm
  rw [hz, ← mul_assoc, mul_inv_cancel₀ (abs_pos.mpr (jac_ne_zero _)).ne', one_mul]

theorem chi_transform (B : E ≃ₗ[ℝ] E) (C : ProperCone ℝ E) (U V : E) :
    chi (pushCone B C) (contra B V) * chi (posDual (pushCone B C)) (B U) =
      chi C V * chi (posDual C) U := by
  have h : ∀ y x, ⟪contra B y, B x⟫ = ⟪y,x⟫ := by
    intro y x
    rw [real_inner_comm, pair_contra, real_inner_comm]
  rw [dual_pushCone, chi_transform' B _ (pair_contra B), chi_transform' _ B h]
  calc
    _ = |jac B * jac (contra B)| * (chi C V * chi (posDual C) U) := by rw [abs_mul]; ring
    _ = _ := by rw [jac_mul_contra]; simp

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Parameter
attribute [-simp] _root_.OAI.GeneralMahler.ProjField.coord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Coordinate and covariance parameters in compact boxes. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

-- Exact finite decimals of the paper as rationals cast to ℝ
def tmin : ℝ := -22/1000
def tmax : ℝ := 64/1000

-- Use S bounded coarsely between I/2 and 2I; precise equation maintained.
lemma add_cov_box {T : Mat m} (ht : T∈specBox m tmin tmax) :
    1+T∈specBox m (1/4:ℝ) 4 := by
  refine ⟨Matrix.isHermitian_one.add ht.1,?_,?_⟩
  · calc
      _ ≤ scalar m (1+tmin) := scalar_le' _ _ (by norm_num [tmin])
      _ = 1+scalar m tmin := by unfold scalar; rw [add_smul,one_smul]
      _ ≤ _ := add_le_add le_rfl ht.2.1
  · calc
      _ ≤ 1+scalar m tmax := add_le_add le_rfl ht.2.2
      _ = scalar m (1+tmax) := by unfold scalar; rw [add_smul,one_smul]
      _ ≤ _ := scalar_le' _ _ (by norm_num [tmax])

lemma scalar_mul (a b : ℝ) :
    scalar m a * scalar m b = scalar m (a*b) := by simp [scalar_eq]

lemma scalar_psd {a:ℝ} (h:0 ≤ a) : 0 ≤ scalar m a := by
  simpa [scalar] using (scalar_le' (m:=m) 0 a h)

lemma root_box {T : Mat m} (ht : T∈specBox m tmin tmax) :
    CFC.sqrt (1+T)∈specBox m (1/2:ℝ) 2 := by
  have hh := add_cov_box ht
  have he := (form_posDef (by norm_num) hh).posSemidef.nonneg
  have hpos := (CFC.sqrt_nonneg (1+T))
  have heq := CFC.sqrt_mul_sqrt_self _ he
  refine ⟨hpos.posSemidef.1,sq_order_cancel (scalar_psd (by norm_num)) hpos ?_,
    sq_order_cancel hpos (scalar_psd (by norm_num)) ?_⟩
  · rw [scalar_mul,heq]; convert hh.2.1 using 1; norm_num
  rw [heq, scalar_mul]; convert hh.2.2 using 1; norm_num

def equivPD {A : Mat m} (h:A.PosDef) : Rn m ≃L[ℝ] Rn m :=
  (pd_equiv h).choose
@[simp] lemma equivPD_spec {A : Mat m} (h:A.PosDef) : (equivPD h).toContinuousLinearMap=op A :=
  (pd_equiv h).choose_spec

def params (m : ℕ) (R : ℝ) : Set (Mat m × Mat m) :=
  (specBox m R⁻¹ R) ×ˢ (specBox m tmin tmax)

abbrev Param (m : ℕ) (R:ℝ) := ↥(params m R)

variable {R : ℝ}

namespace Param
def B (x : Param m R) := x.val.1
def T (x : Param m R) := x.val.2
lemma in_box (x : Param m R) :
    x.B∈specBox m R⁻¹ R ∧ x.T∈specBox m tmin tmax := x.property

def S (x : Param m R) := CFC.sqrt (1+x.T)
lemma S_box (x : Param m R) : x.S ∈ specBox m (1/2:ℝ) 2 := root_box x.in_box.2
lemma S_pos (x : Param m R) : x.S.PosDef := form_posDef (by norm_num) x.S_box

def transE (x : Param m R) (hr : 0<R) :=
  equivPD (form_posDef (inv_pos.mpr hr) x.in_box.1)

def instanceQ (x : Param m R) (hr : 0<R) (q : ProjField m) :
    ProjField m where
  C := pushCone (x.transE hr).toLinearEquiv q.C
  U := x.transE hr q.U
  V := contra (x.transE hr).toLinearEquiv q.V
  U_in := apply_mem_interior_pushCone.mpr q.U_in
  V_in := by rw [dual_pushCone]; exact apply_mem_interior_pushCone.mpr q.V_in
  ip := (pair_contra (x.transE hr).toLinearEquiv ..).trans q.ip
  S := x.S
  pos := x.S_pos
  root := equivPD x.S_pos
  matrix_eq := equivPD_spec _

end Param
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Update
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §02 covariance equation from scalar inequalities of §01. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

def lam : ℝ := 65/100
def mstar : ℝ := 352/1000
def ell0 : ℝ := -37/100
def cupper : ℝ := -341/1000

/-- Regularity and scalar bounds for the covariance update. -/
structure UpdatesOK (C K : ℝ → ℝ) : Prop where
  Cp : PolyBound C
  Kp : PolyBound K
  Cc : Continuous C
  Kc : Continuous K
  lo : ∀ x, 0 ≤ lam*tmin^2+tmin*C x + K x
  hi : ∀ x, lam*tmax^2+tmax*C x+K x ≤ 0
  tan : ∀ x, mstar^2 ≤ 2*ell0*C x-ell0^2-4*lam*K x
  C_hi : ∀ x, C x ≤ cupper

variable {m : ℕ}

def jprod (A B : Mat m) := (1/2:ℝ) • (A*B+B*A)
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_TraceOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Matrix trace order calculus for layer inequalities. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}
-- Use actual Borel measurable structure
instance mat_meas (m:ℕ) : MeasurableSpace (Mat m) := borel _
instance mat_borel (m:ℕ) : BorelSpace (Mat m) := ⟨rfl⟩

def thresh (A:Mat m) := 1-(1+A)⁻¹
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Edge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Deterministic-endcut layer of PSD contractions. Carries the
precise data needed for log-Jacobian estimate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ}
structure Edge (m:ℕ) where
  P : ℝ → Rn m → Mat m
  psd : ∀ z x, 0 ≤ P z x
  le_one : ∀ z x,P z x≤1
  meas : Measurable P.uncurry
  C : ℝ
  hp : 1 ≤ C
  tend_pos : ∀ z x,C*(1+‖x‖)<z → P z x=1
  tend_neg : ∀ z x,C*(1+‖x‖)< -z → P z x=0

variable [NeZero m]
namespace Edge
variable (e:Edge m)
def ref : Edge m where
  P := fun z x=>1-e.P (-z) x
  psd := fun z x=> sub_nonneg.mpr (e.le_one ..)
  le_one := fun z x=> sub_le_self _ (e.psd ..)
  meas := measurable_const.sub (e.meas.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd))
  C := e.C
  hp := e.hp
  tend_pos := fun z x hx=> by rw [e.tend_neg _ _ (by simpa using hx),sub_zero]
  tend_neg := fun z x hx=> by rw [e.tend_pos _ _ hx,sub_self]

def radius (x:Rn m) := e.C*(1+‖x‖)

def EP (z:ℝ) (x:Rn m) := e.P z x-st z • (1:Mat m)

def WP (z:ℝ) (x:Rn m) := MillsW z • e.P z x

def Jedge (x:Rn m) := ∫ z,e.WP z x

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LogDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Normalized log determinant; derivative and simple growth estimates. -/
noncomputable section
open Finset MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m:ℕ}

def logD (A:Mat m) := Real.log A.det/(m:ℝ)
def coeffMap (i j:Fin m) : Mat m →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
    toFun := fun A : Mat m => A i j
    map_add' := fun _ _=>rfl
    map_smul' := fun _ _=>rfl }

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_DefectLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! μ functionals and integrable density algebra for Section §03-04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Metric Real
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile

-- integrable densities with polynomial weights
def MomentF (f:ℝ→ℝ) :=
  ∀ g : ℝ→ℝ, Measurable g→PolyBound g→Integrable fun x=>f x*g x
namespace MomentF
variable {f g:ℝ→ℝ}
lemma of_rapid (hf:rapid f) (hm:Measurable f) : MomentF f :=
  fun _g hg h=> (hf.product h).integrable_real (hm.mul hg)
end MomentF
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LogPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Path z↦c(z)I+∫_{-∞}^z WP, for fixed standard input. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
namespace Edge
variable (e:Edge m) (x:Rn m)
def H (z:ℝ) := ∫ y in Iic z,e.WP y x

def path (z:ℝ) := scalar m (MillsC z)+e.H x z

def Fedge (z:ℝ) := logD (e.path x z)

def Sh (z:ℝ) := (MillsC z)⁻¹ • e.H x z
def beta (z:ℝ) := MillsJ z * trN (thresh (e.Sh x z)*(1-e.P z x))
def h1 (z:ℝ) := trN (e.P z x)

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GainIndent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Exact linear and nonnegative surplus terms in the log identity. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

namespace Edge
variable (e:Edge m)

def LinearT (z:ℝ) (x:Rn m) := MillsJ z*(e.h1 x z-st z)

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EdgeBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Lower bound for beta on the band l∈[-z,z] for z≥0, using
integration by parts against 1/W; equivalent to the subprobability
argument in the paper. -/
noncomputable section
open MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]

namespace Edge
variable (e:Edge m) (x:Rn m) (z:ℝ)
def BH (l:ℝ) := e.H x z - e.H x l

def FF (l:ℝ) := trN (e.BH x z l*(1-e.P z x))
def ntb (l:ℝ) := trN (e.P l x*(1-e.P z x))

def trC : Mat m→L[ℝ]ℝ :=
  trL.comp ((ContinuousLinearMap.mul ℝ (Mat m)).flip (1-e.P z x))

def Wi (t:ℝ) := (MillsW t)⁻¹
end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_NtLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Nonthreshold kernel and integration over the ordered halves.
We use (l,z) as pair of variables and ordinary product volume. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers
abbrev Plane := ℝ × ℝ
variable {m:ℕ}

namespace Edge
variable (e:Edge m)
def NTm (u:Plane) (x:Rn m) :=
  jprod (e.P (min u.1 u.2) x) (1-e.P (max u.1 u.2) x)
def nt0 (u:Plane) (x:Rn m) := trN (e.NTm u x)

def BandS : Set Plane := {u|0 ≤ u.2 ∧ u.1∈Icc (-u.2) u.2}

variable [NeZero m]

-- measure transformations preserving volume
def rs (u:Plane) := -u.swap

end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_GainFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Combine the log-gains of the two matrices. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]
namespace Edge
def Plin (e:Edge m) (z:ℝ) (x:Rn m) := MillsJ z*(e.h1 x z-p z)
end Edge
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Entropy bound (10), in normalized trace notation. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]

def etL (B:Mat m) : Mat m →L[ℝ]ℝ :=
  trL.comp (ContinuousLinearMap.mul ℝ (Mat m) B)
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_H
attribute [-instance] _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Hermite modes and Gaussian averages via TestF. Probabilists'
convention, orthonormal scaling. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Layers
def ga (f:ℝ→ℝ) := ∫ x,phi x*f x
lemma ga_i {f:ℝ→ℝ} (hf:TestF f) : Integrable (fun x=>phi x*f x) :=
  (rapid_phi.product hf.poly).integrable_real (c_phi.mul hf.cont).measurable
lemma ga_add {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=>f x+g x)=ga f+ga g := by
  unfold ga; simp_rw [mul_add]; exact integral_add (ga_i hf) (ga_i hg)
lemma ga_sub {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=>f x-g x)=ga f-ga g := by
  unfold ga; simp_rw [mul_sub]; exact integral_sub (ga_i hf) (ga_i hg)
lemma ga_mul (f:ℝ→ℝ) (a:ℝ) : ga (fun x=>a*f x)=a*ga f := by
  unfold ga
  rw [← integral_const_mul]
  congr 1; ext; ring
lemma ga_parts {f:ℝ→ℝ} (hf:TestF f) :
    ga (fun x=>x*f x) = ga (deriv f) := by
  let g := fun x=>phi x*f x
  have he := rapid_phi.product hf.poly
  have hd (x:ℝ) : HasDerivAt g (phi x*deriv f x-phi x*(x*f x)) x := by
    convert (d_phi x).fun_mul (hf.diff x).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | ring
  have hi := ga_i hf.der
  have h₁ := ga_i (TestF.id.mul hf)
  have hh := integral_of_hasDerivAt_of_tendsto hd (hi.sub h₁) he.tail_limit_bot he.tail_limit
  rw [integral_sub hi h₁] at hh
  unfold ga; linarith
lemma ga_pair {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    ga (fun x=>(x*f x-deriv f x)*g x) = ga (fun x=>f x*deriv g x) := by
  have h := ga_parts (hf.mul hg)
  rw [funext (show ∀ x,deriv (fun x=>f x*g x) x=_ from
    fun x=> ((hf.diff x).hasDerivAt.fun_mul (hg.diff x).hasDerivAt).deriv)] at h
  have he : (fun x=>(x*f x-deriv f x)*g x)=
      fun x=>x*(f x*g x)-deriv f x*g x := by ext; ring
  have hi := hf.der.mul hg
  have hj := hf.mul hg.der
  rw [ga_add hi hj] at h
  rw [he,ga_sub (TestF.id.mul (hf.mul hg)) hi,h]; ring

lemma gamma_area (f : ℝ→ℝ) :
    (∫ x,f x ∂GeneralMahler.gamma)=ga f := by
  unfold gamma
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]; rfl

namespace HMode
def sn (n:ℕ) := √((n:ℝ))
lemma snsq (n:ℕ) : sn n^2=n := Real.sq_sqrt (Nat.cast_nonneg _)
lemma sn_succ (n:ℕ) : 0 < sn (n+1) := by unfold sn; positivity

def H : ℕ→ℝ→ℝ
 | 0=>fun _=>1
 | n+1=>fun x=>(sn (n+1))⁻¹*(x*H n x - deriv (H n) x)
lemma ht (n:ℕ) : TestF (H n) := by
  induction n with
  | zero=>exact TestF.const _
  | succ n ih=> exact (TestF.const _).mul ((TestF.id.mul ih).sub ih.der)
lemma raise (x:ℝ) (n:ℕ) : sn (n+1)*H (n+1) x=x*H n x-deriv (H n) x := by
  rw [H,← mul_assoc,mul_inv_cancel₀ (sn_succ n).ne',one_mul]
lemma lower (n:ℕ) :
    deriv (H (n+1)) = fun x=>sn (n+1)*H n x := by
  induction n with
  | zero=>
    have h : H 1=fun x=> x := by ext; simp [H,sn]
    rw [h]
    ext; simp [H,sn]
  | succ n ih=>
    ext x
    have hi := sn_succ n
    have hp := sn_succ (n+1)
    have hh : H (n+2)=fun x=>(sn (n+2))⁻¹*(x*H (n+1) x-sn (n+1)*H n x) := by
      funext x; rw [H,ih]
    have he := ((((hasDerivAt_id' x).fun_mul ((ht (n+1)).diff x).hasDerivAt).fun_sub
      (((ht n).diff x).hasDerivAt.const_mul (sn (n+1)))).const_mul ((sn (n+2))⁻¹)).deriv
    rw [hh,he,ih]
    rw [one_mul]
    rw [show (H (n+1) x+x*(sn (n+1)*H n x)-sn (n+1)*deriv (H n) x) =
      sn (n+2)^2*H (n+1) x from ?_]
    field_simp
    calc
      _ = H (n+1) x+sn (n+1)*(x*H n x-deriv (H n) x) := by ring
      _ = _ := by rw [← raise,← mul_assoc,← pow_two,snsq,snsq]; push_cast; ring

lemma Hder (n:ℕ) (x:ℝ) : deriv (H n) x=sn n*H (n-1) x := by
  cases n
  · simp [H,sn]
  rw [lower]; rfl

lemma avg_succ (f:ℝ→ℝ) (hf:TestF f) (n:ℕ) :
    ga (fun x=>H (n+1) x*f x)=(sn (n+1))⁻¹*ga (fun x=>H n x*deriv f x) := by
  have he : (fun x=>H (n+1) x*f x)=fun x=>(sn (n+1))⁻¹*((x*H n x-deriv (H n) x)*f x) := by
    ext; rw [H,mul_assoc]
  rw [he,ga_mul,ga_pair (ht n) hf]

lemma avg_z (n:ℕ) : ga (H (n+1))=0 := by
  simpa [H,ga] using avg_succ (fun _=>1) (TestF.const 1) n
lemma avg_o (n k:ℕ) : ga (fun x=>H n x*H k x)=(if n=k then 1 else 0) := by
  induction n generalizing k with
  | zero=>
    cases k with
    | zero=>simp [H,ga,e_phi]
    | succ k=> simpa only [H,one_mul,Nat.zero_ne_add_one,↓reduceIte] using avg_z k
  | succ n ih=>
    cases k with
    | zero=> simpa only [H,mul_one,Nat.add_one_ne_zero,↓reduceIte] using avg_z n
    | succ k=>
      rw [avg_succ _ (ht _) n,lower k]
      simp_rw [mul_left_comm (H n _),ga_mul,ih]
      split_ifs with h h' <;> first | omega | skip
      · subst k
        rw [mul_one,inv_mul_cancel₀ (sn_succ n).ne']
      · ring
end HMode
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Multi
attribute [-instance] _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.OAI.GeneralMahler.equivPD_spec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Tensor Hermite modes, Gaussian multivariate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
open Layers
variable {m:ℕ}
abbrev MI (m:ℕ) := Fin m→ℕ
abbrev e (i:Fin m) : Rn m := EuclideanSpace.basisFun (Fin m) ℝ i
def MM (a:MI m) (x:Rn m) := ∏ i,H (a i) (x i)
def inc (a:MI m) (i:Fin m) := Function.update a i (a i+1)
def decM (a:MI m) (i:Fin m) := Function.update a i (a i-1)

lemma p_finprod {I X:Type*} [SeminormedAddCommGroup X] {f:I→X→ℝ} (h:∀ i,PolyBound (f i)) (s:Finset I) :
    PolyBound fun x=> ∏ i ∈ s,f i x := by
  classical
  induction s using Finset.induction with
  | empty=>simpa using PolyBound.const (X:=X) (1:ℝ)
  | insert i s hi ih=>simpa [hi] using (h i).mul ih
lemma M_poly (a:MI m) : PolyBound (MM a) :=
  p_finprod (f:=fun i (x:Rn m)=> H (a i) (x i)) (fun i=>((ht _).poly).comp (PolyBound.clm (ProjField.coord i))) _
lemma M_diff (a:MI m) : Differentiable ℝ (MM a) := by
  classical
  have h (u:Finset (Fin m)) : Differentiable ℝ (fun x:Rn m=> ∏ i∈u,H (a i) (x i)) := by
    induction u using Finset.induction with
    | empty=> simp
    | insert i u hi ih=>
      have he : Differentiable ℝ (fun x:Rn m=>H (a i) (x i)) :=
        (ht (a i)).diff.comp (ProjField.coord i).differentiable
      simpa only [Finset.prod_insert hi] using he.fun_mul ih
  exact h _
lemma M_cont (a:MI m) : Continuous (MM a) := (M_diff a).continuous

lemma M_inner (a b:MI m) :
    (∫ x,MM a x*MM b x ∂normal m) = if a=b then 1 else 0 := by
  classical
  let f := fun i:Fin m=>fun x:ℝ=> H (a i) x*H (b i) x
  let T := MeasurableEquiv.toLp 2 (Fin m→ℝ)
  have he : normal m=(Measure.pi fun _ : Fin m=>GeneralMahler.gamma).map T :=
    ProbabilityTheory.map_pi_eq_stdGaussian.symm
  have hf (i:Fin m) := avg_o (a i) (b i)
  rw [he,integral_map_equiv]
  have hx (x:Fin m→ℝ) : MM a (T x)*MM b (T x) = ∏ i, f i (x i) := by
    unfold MM f T; rw [Finset.prod_mul_distrib]; rfl
  simp_rw [hx]; rw [integral_fintype_prod_eq_prod]; simp_rw [gamma_area]
  simp_rw [show ∀ i,ga (f i)=_ from hf]
  by_cases h:a=b
  · subst b; simp
  rw [ite_eq_right h]; push Not at h
  have h' : ∃ i,a i≠b i := by by_contra! hh; exact h (funext hh)
  obtain ⟨i,hi⟩ := h'
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma factor (a:MI m) (x:Rn m) (i:Fin m) :
    MM a x=H (a i) (x i)*∏ j∈Finset.univ.erase i,H (a j) (x j) :=
  (Finset.mul_prod_erase (s:=Finset.univ) _ (Finset.mem_univ i)).symm

lemma factor_upd (a:MI m) (x:Rn m) (i:Fin m) (n:ℕ) :
    MM (Function.update a i n) x=
      H n (x i)*∏ j∈Finset.univ.erase i,H (a j) (x j) := by
  rw [factor _ _ i,Function.update_self]
  congr 1
  apply Finset.prod_congr rfl; intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma ladder (a:MI m) (i) (x:Rn m) :
    x i*MM a x=sn (a i+1)*MM (inc a i) x + sn (a i)*MM (decM a i) x := by
  unfold inc decM
  rw [factor_upd,factor_upd,factor a x i,← mul_assoc,← mul_assoc,← mul_assoc,raise,Hder]
  ring
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Dense
attribute [-instance] _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.OAI.GeneralMahler.equivPD_spec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Vanishing of all chaos coefficients implies vanishing a.e.; proof via
an exponential integrability and characteristic function argument. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ}
lemma lp_poly {f:Rn m→ℝ} (hf:PolyBound f) (hm:AEStronglyMeasurable f (normal m)) :
    MemLp f 2 (normal m) := by
  apply (memLp_two_iff_integrable_sq hm).mpr
  exact (hf.pow _).gaussian_integrable (hm.pow _)

lemma lp_EXP (t:Rn m) : MemLp (fun x:Rn m=>Real.exp |⟪x,t⟫|) 2 (normal m) := by
  obtain ⟨C,hc,h⟩ := ProbabilityTheory.IsGaussian.exists_integrable_exp_sq (normal m)
  let f := fun x:Rn m=>Real.exp |⟪x,t⟫|
  have hm : Continuous f := by unfold f; fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (h.const_mul (Real.exp (‖t‖^2/C))).mono' (hm.pow 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖f x^2‖≤_
  unfold f
  rw [Real.norm_of_nonneg (sq_nonneg _),pow_two,← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht := abs_real_inner_le_norm x t
  have he : 2*‖x‖*‖t‖-C*‖x‖^2≤‖t‖^2/C := by
    rw [le_div_iff₀ hc]
    nlinarith [sq_nonneg (C*‖x‖-‖t‖)]
  linarith

variable {f:Rn m→ℝ} (hf:MemLp f 2 (normal m))
include hf

lemma momentPower (hz : ∀ a, (∫ x,f x*MM a x ∂normal m)=0) (t:Rn m) :
    ∀ n:ℕ,(∫ x,f x*⟪x,t⟫^n ∂normal m)=0 := by
  have hi : PolyBound (fun x:Rn m=>⟪x,t⟫) := by
    simp_rw [real_inner_comm t]; exact PolyBound.clm (innerSL ℝ t)
  let W (n:ℕ) (a) (x:Rn m) := f x*⟪x,t⟫^n*MM a x
  have iw (n a) : Integrable (W n a) (normal m) := by
    unfold W; simp_rw [mul_assoc]
    exact hf.integrable_mul (lp_poly ((hi.pow _).mul (M_poly a))
      ((((continuous_id.inner continuous_const).pow _).mul (M_cont a)).aestronglyMeasurable))
  have h (n:ℕ) : ∀ a,(∫ x,W n a x ∂normal m)=0 := by
    induction n with
    | zero=>
      intro a; simpa [W] using hz a
    | succ n ih=>
      intro a
      let g (i:Fin m) (x:Rn m) := (t i*sn (a i+1))*W n (inc a i) x+(t i*sn (a i))*W n (decM a i) x
      have he (x) : W (n+1) a x= ∑ i,g i x := by
        have hu (i:Fin m) : g i x=(f x*⟪x,t⟫^n*MM a x)*(t i*x i) := by
          have hh := ladder a i x
          unfold g W
          calc
            _ = t i*(f x*⟪x,t⟫^n)*(sn (a i+1)*MM (inc a i) x+sn (a i)*MM (decM a i) x) := by ring
            _ = _ := by rw [← hh]; ring
        simp_rw [hu]; rw [← Finset.mul_sum]
        have hv : (∑ i,t i*x i)= ⟪x,t⟫ := by simp [PiLp.inner_apply]
        rw [hv]; unfold W; rw [pow_succ]; ring
      simp_rw [he]; rw [integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro i _
        unfold g; rw [integral_add]
        · simp_rw [integral_const_mul,ih]; ring
        all_goals exact (iw ..).const_mul _
      exact fun i _ => ((iw n (inc a i)).const_mul _).add ((iw n (decM a i)).const_mul _)
  intro n
  simpa [W,MM,H] using h n (fun _=>0)

local notation "ii" => Complex.I
lemma wave_zero (hm:Measurable f) (hz:∀ a, (∫ x,f x*MM a x ∂normal m)=0) (t:Rn m) :
    (∫ x, (f x:ℂ)* Complex.exp ((⟪x,t⟫:ℝ)*ii) ∂normal m)=0 := by
  let w (x:Rn m) := (⟪x,t⟫:ℂ)*ii
  let A (n:ℕ) (x:Rn m) := w x^n/(n.factorial:ℂ)
  let P (n:ℕ) (x:Rn m) := (f x:ℂ)*∑ i∈Finset.range n,A i x
  have ha : Continuous w := by unfold w; fun_prop
  have hmul (x:Rn m) : HasSum (fun i=>A i x) (Complex.exp (w x)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (w x)
  have he (n:ℕ) : (∫ x,P n x ∂normal m)=0 := by
    have hA (i:ℕ) (x:Rn m) :
        (f x:ℂ)*A i x= ii^i/(i.factorial:ℂ)*((f x*⟪x,t⟫^i:ℝ):ℂ) := by
      unfold A w; push_cast; rw [mul_pow]; ring
    have ih : PolyBound (fun x:Rn m=>⟪x,t⟫) := by
      simp_rw [real_inner_comm t]; exact PolyBound.clm (innerSL ℝ t)
    have hi (n:ℕ) : Integrable (fun x=>f x*⟪x,t⟫^n) (normal m) :=
      hf.integrable_mul (lp_poly (ih.pow _) (((continuous_id.inner continuous_const).pow _).aestronglyMeasurable))
    unfold P; simp_rw [Finset.mul_sum,hA]; rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro i _
      rw [integral_const_mul,integral_complex_ofReal,momentPower hf hz]
      simp
    intro i _
    exact (hi _).ofReal.const_mul _
  let g := fun x:Rn m=> ‖f x‖*Real.exp |⟪x,t⟫|
  have ih : Integrable g (normal m) := hf.norm.integrable_mul (lp_EXP t)
  have hb (x:Rn m) :
      HasSum (fun i=>‖A i x‖) (Real.exp |⟪x,t⟫|) := by
    rw [Real.exp_eq_exp_ℝ]
    convert NormedSpace.expSeries_div_hasSum_exp (|⟪x,t⟫|) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (funext i; unfold A w; simp)
  have hh := tendsto_integral_of_dominated_convergence
    (μ:=normal m) g (fun n=> (by unfold P A; fun_prop : Measurable (P n)).aestronglyMeasurable) (F:=P)
    ih (fun n=>ae_of_all _ fun x=> ?_) (ae_of_all _ fun x=> ?_)
    (f:=fun x=>(f x:ℂ)*Complex.exp (w x))
  · simp_rw [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · unfold P; rw [norm_mul,Complex.norm_real]
    unfold g; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_sum_le ..).trans (sum_le_hasSum _ (fun i _=> norm_nonneg _) (hb x))
  exact ((hmul x).tendsto_sum_nat).const_mul _

lemma pospart_char (hm:Measurable f) (hp:∀ x,0≤f x) :
    let μ := (normal m).withDensity (fun x=>ENNReal.ofReal (f x))
    IsFiniteMeasure μ ∧ ∀ t:Rn m,charFun μ t=∫ x,(f x:ℂ)*Complex.exp ((⟪x,t⟫:ℝ)*ii) ∂normal m := by
  intro μ
  have hi : Integrable f (normal m) := hf.integrable (by norm_num)
  have HH : Measurable fun x=>ENNReal.ofReal (f x) := hm.ennreal_ofReal
  constructor
  · constructor
    unfold μ; rw [withDensity_apply _ (by simp),restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ hp)]
    exact ENNReal.ofReal_lt_top
  intro t
  unfold charFun μ
  rw [integral_withDensity_eq_integral_toReal_smul HH (by simp)]
  simp_rw [ENNReal.toReal_ofReal (hp _),Complex.real_smul]

lemma measurable_zero (hm:Measurable f) (hz:∀ a,(∫ x,f x*MM a x ∂normal m)=0) :
    ∀ᵐ x∂normal m,f x=0 := by
  let l := fun x=> (‖f x‖+f x)
  let k := fun x=> (‖f x‖-f x)
  have hp (x):0≤l x := by unfold l; rw [Real.norm_eq_abs]; grind
  have hq (x):0≤k x := by unfold k; exact sub_nonneg.mpr (le_abs_self _)
  have i₁ : MemLp l 2 (normal m) := hf.norm.add hf
  have i₂ : MemLp k 2 (normal m) := hf.norm.sub hf
  have hl : Measurable l := hm.norm.add hm
  have hk : Measurable k := hm.norm.sub hm
  let F := fun x=>ENNReal.ofReal (l x)
  let G := fun x=>ENNReal.ofReal (k x)
  let μ := normal m; let L := μ.withDensity F; let K := μ.withDensity G
  have ha := pospart_char i₁ hl hp
  have hb := pospart_char i₂ hk hq
  have : IsFiniteMeasure L := ha.1
  have : IsFiniteMeasure K := hb.1
  have he : L=K := by
    apply Measure.ext_of_charFun
    funext t
    rw [ha.2,hb.2]
    let w := fun x:Rn m=> Complex.exp ((⟪x,t⟫:ℝ)*ii)
    have iw (f:Rn m→ℝ) (hi:MemLp f 2 μ) :
        Integrable (fun x=>(f x:ℂ)*w x) μ := by
      have hF : Integrable (fun x=>(f x:ℂ)) μ := (hi.integrable (by norm_num)).ofReal
      apply hF.mono (hF.aestronglyMeasurable.mul (by
        unfold w; exact (by fun_prop : Continuous _).aestronglyMeasurable))
      apply ae_of_all
      intro x; change ‖_*w x‖≤ _
      unfold w; simp
    have hu : (∫ x,((l x:ℂ)*w x-(k x:ℂ)*w x) ∂μ)=0 := by
      have he (x:Rn m) : (l x:ℂ)*w x-(k x:ℂ)*w x=2*((f x:ℂ)*w x) := by
        unfold l k; push_cast; ring
      simp_rw [he]
      rw [integral_const_mul]
      have hi := wave_zero hf hm hz t
      change _*(∫ x, (f x:ℂ)*Complex.exp _ ∂normal m)=_; rw [hi,mul_zero]
    rw [integral_sub (iw l i₁) (iw k i₂)] at hu
    exact sub_eq_zero.mp hu
  have h : F=ᵐ[μ] G := (withDensity_eq_iff_of_sigmaFinite (by unfold F; fun_prop)
    (by unfold G; fun_prop)).mp he
  filter_upwards [h] with x hx
  have hi := congrArg ENNReal.toReal hx
  rw [show F x= _ from (rfl : F x=ENNReal.ofReal (l x)), show G x=_ from
    (rfl : G x=ENNReal.ofReal (k x)),ENNReal.toReal_ofReal (hp _),ENNReal.toReal_ofReal (hq _)] at hi
  unfold l k at hi; linarith

theorem ae_zero (hz:∀ a,(∫ x,f x*MM a x ∂normal m)=0) : ∀ᵐ x∂normal m,f x=0 := by
  obtain ⟨g,hg,he⟩ := hf.aemeasurable
  have hi := measurable_zero (hf.ae_eq he) hg (fun a=> (integral_congr_ae (he.symm.mul (ae_eq_refl _))).trans (hz a))
  filter_upwards [hi,he] with x hx he; exact he.trans hx
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_L2
attribute [-instance] _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.OAI.GeneralMahler.equivPD_spec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar coefficient calculus. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
abbrev G2 (m:ℕ) := Lp ℝ 2 (normal m)
def ModL (a:MI m) : G2 m :=
  MemLp.toLp (MM a) (lp_poly (M_poly a) (M_cont a).aestronglyMeasurable)
omit [NeZero m] in
lemma ModL_ae (a:MI m) : ModL a=ᵐ[normal m] MM a := MemLp.coeFn_toLp ..
def qcf (f:Rn m→ℝ) (a:MI m) := ∫ x,f x*MM a x ∂normal m

omit [NeZero m] in
lemma qcf_ip (f:G2 m) (a) : qcf f a = ⟪ModL a,f⟫ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ModL_ae a] with x hx
  rw [hx]; rfl

omit [NeZero m] in
lemma qcf_congr {f g:Rn m→ℝ} (h:f=ᵐ[normal m]g) (a:MI m) :
    qcf f a=qcf g a := by
  apply integral_congr_ae
  filter_upwards [h] with x hx; rw [hx]

omit [NeZero m] in
lemma Mod_o : Orthonormal ℝ (@ModL m) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [← qcf_ip,qcf_congr (ModL_ae _)]
  simpa [qcf,eq_comm] using M_inner b a

def HB (m:ℕ) [NeZero m] : HilbertBasis (MI m) ℝ (G2 m) :=
  HilbertBasis.mkOfOrthogonalEqBot Mod_o (by
    rw [eq_bot_iff]
    intro f hf
    have hz (a:MI m) : qcf f a=0 := by
      rw [qcf_ip]; exact hf (ModL a) (Submodule.subset_span ⟨a,rfl⟩)
    have hh := ae_zero (Lp.memLp f) hz
    change f=0
    apply Lp.ext
    filter_upwards [hh,Lp.coeFn_zero ℝ 2 (normal m)] with x hx he
    rw [hx,he]; rfl)
@[simp] lemma HB_eq (a:MI m) : HB m a=ModL a := by simp [HB]

end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Gradient
attribute [-instance] _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Hermite coefficient recurrence for functions with suitable local
Lipschitz bounds. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ}
variable {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def PLip (f:Rn m→F) := ∃ g:Rn m→ℝ, PolyBound g ∧ Continuous g ∧
    ∀ x b:Rn m, ‖b‖ < 1 → ‖f (x+b)-f x‖ ≤ g x*‖b‖

def cof (f:Rn m→F) (a:MI m) : F := ∫ x,MM a x • f x ∂normal m
end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Hermite_Pair
attribute [-instance] _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Parseval identities for finite-dimensional Gaussian fields and bilinear pairings. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ} [NeZero m]
variable {F E:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A measurable field with polynomial growth. -/
structure regular (f:Rn m→F) : Prop where
  p : PolyBound f
  meas : AEStronglyMeasurable f (normal m)

variable {f:Rn m→E} {g:Rn m→F}

-- degree/shift arithmetic
def deg (a:MI m) := ∑ i,a i
omit [NeZero m] in
lemma dec_inc (a:MI m) (i:Fin m) : decM (inc a i) i=a := by
  ext j
  by_cases h:i=j
  · subst j; simp [inc, decM]
  simp [inc,decM,Ne.symm h]
omit [NeZero m] in
lemma inc_dec (a:MI m) (i:Fin m) (hi:a i≠0) : inc (decM a i) i=a := by
  ext j
  by_cases h:i=j
  · subst j; simp [inc, decM]; omega
  simp [inc,decM,Ne.symm h]
def userS (i:Fin m) := {a:MI m| a i≠0}
def incE (i:Fin m) : MI m ≃ userS i where
  toFun a := ⟨inc a i, by unfold userS inc; simp⟩
  invFun a := decM a.val i
  left_inv a := dec_inc a i
  right_inv a := Subtype.ext (inc_dec _ _ a.property)

end GeneralMahler.HMode

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_CovHerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Eq13 coefficient-pair (weighted K multiplier via coefficients). -/
noncomputable section
open Set Filter Metric MeasureTheory MeasureTheory.Measure Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

def Pj (B A C:Mat m) := trN (B*jprod A C)

def PJ (B:Mat m) : Mat m→L[ℝ]Mat m→L[ℝ]ℝ :=
  let u := (1/2:ℝ) • ((ContinuousLinearMap.mul ℝ (Mat m))+
    (ContinuousLinearMap.mul ℝ (Mat m)).flip)
  (ContinuousLinearMap.compL ℝ _ _ _ (etL B)).comp u

def CpPair (B:Mat m) (A C:Rn m→Mat m) (a:MI m) := Pj B (cof A a) (cof C a)
def kMode (a:MI m) : ℝ := (1+(deg a:ℝ))⁻¹
def KP (B:Mat m) (A C:Rn m→Mat m) := ∑' a,CpPair B A C a*kMode a

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Frame_Selector
attribute [-instance] _root_.OAI.GeneralMahler.mat_meas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Borel selection for a closed relation into a compact metric space. -/
noncomputable section
open Set Filter Metric Real MeasureTheory
open scoped Topology NNReal ENNReal
namespace GeneralMahler.Select
section
variable {X Y:Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [Nonempty Y]
variable (F:Set (X×Y))
def near (x:X) (y:Y) (r:ℝ) := ∃ v,(x,v)∈F∧dist v y ≤ r
omit [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y] in
lemma near_m (h:IsClosed F) (y:Y) (r:ℝ) : MeasurableSet {x|near F x y r} := by
  let S := F ∩ Prod.snd ⁻¹' (closedBall y r)
  have hs := isClosedMap_fst_of_compactSpace S (h.inter (isClosed_closedBall.preimage continuous_snd))
  have he : {x|near F x y r}= Prod.fst '' S := by
    ext x
    constructor
    · rintro ⟨v,hv,h⟩; exact ⟨(x,v),⟨hv,h⟩,rfl⟩
    rintro ⟨⟨x,v⟩,h,rfl⟩; exact ⟨v,h.1,h.2⟩
  rw [he]; exact hs.measurableSet
def eps (n:ℕ):ℝ := (1/2)^n
omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma dense_approx (y:Y) {r:ℝ} (hr:0 < r) :
    ∃ n:ℕ,dist y (TopologicalSpace.denseSeq Y n) < r :=
  (TopologicalSpace.denseRange_denseSeq Y).exists_dist_lt y hr
omit [TopologicalSpace X] [OpensMeasurableSpace X] [BorelSpace Y] in
lemma choose_m {p:X→Y→Prop} (h:∀ x,∃ n:ℕ,p x (TopologicalSpace.denseSeq Y n))
    (hm:∀ n:ℕ,MeasurableSet {x|p x (TopologicalSpace.denseSeq Y n)}) :
    ∃ f:X→Y,Measurable f∧∀ x,p x (f x) := by
  classical
  let f := fun x:X=> Nat.find (h x)
  exact ⟨TopologicalSpace.denseSeq Y ∘ f,(measurable_of_countable _).comp
    (measurable_find h hm),fun x=> Nat.find_spec (h x)⟩

abbrev tag (n:ℕ) := {f:X→Y // Measurable f∧∀ x, near F x (f x) (eps n)}
omit [BorelSpace Y] in
lemma start (he:∀ x:X,∃ y:Y,(x,y)∈F) (hc:IsClosed F) :
    Nonempty (tag F 0) := by
  have h (x:X) : ∃ n:ℕ,near F x (TopologicalSpace.denseSeq Y n) (eps 0) := by
    obtain ⟨y,hy⟩ := he x
    obtain ⟨n,hn⟩ := dense_approx y (r:=eps 0) (by norm_num [eps])
    exact ⟨n,y,hy,hn.le⟩
  obtain ⟨f,hf,hf'⟩ := choose_m (p:=fun x y=> near F x y (eps 0)) h (fun _=> near_m _ hc _ _)
  exact ⟨⟨f,hf,hf'⟩⟩
lemma next (hc:IsClosed F) (n:ℕ) (x:tag F n) :
    ∃ y: tag F (n+1),∀ a,dist (x.val a) (y.val a)≤2*eps n := by
  let p := fun (a:X) (y:Y)=> near F a y (eps (n+1)) ∧ dist (x.val a) y≤2*eps n
  have h (a:X) : ∃ n,p a (TopologicalSpace.denseSeq Y n) := by
    obtain ⟨v,hv,hh⟩ := x.property.2 a
    obtain ⟨w,hw⟩ := dense_approx v (r:=eps (n+1)) (by unfold eps; positivity)
    refine ⟨w,⟨v,hv,hw.le⟩,?_⟩
    apply le_trans (dist_triangle _ v _)
    have hp : 0≤eps n := by unfold eps; positivity
    have he : eps (n+1)=eps n/2 := by unfold eps; rw [pow_succ]; ring
    rw [dist_comm (x.val a)]; linarith
  have hm (i) : MeasurableSet {a|p a (TopologicalSpace.denseSeq Y i)} :=
    (near_m _ hc _ _).inter (measurableSet_le (x.property.1.dist measurable_const) measurable_const)
  obtain ⟨f,hf,h₁⟩ := choose_m h hm
  exact ⟨⟨f,hf,fun x=>(h₁ x).1⟩,fun x=>(h₁ x).2⟩

theorem selector (he:∀ x:X,∃ y:Y,(x,y)∈F) (hc:IsClosed F) :
    ∃ f:X→Y, Measurable f ∧ ∀ x,(x,f x)∈F := by
  classical
  let s (n:ℕ) := Nat.rec (motive:=fun n=> tag F n) (Classical.choice (start F he hc))
    (fun n x=> (next F hc n x).choose) n
  have hn (n a) : dist ((s n).val a) ((s (n+1)).val a) ≤ 2*eps n := (next F hc n (s n)).choose_spec a
  let g := fun n=>(s n).val
  have hh (x:X) : CauchySeq fun n=>g n x :=
    cauchySeq_of_le_geometric _ _ (show (1/2:ℝ)<1 by norm_num) (fun n=>hn n x)
  choose f hf using fun x:X=> cauchySeq_tendsto_of_complete (hh x)
  refine ⟨f,measurable_of_tendsto_metrizable (fun n=>(s n).property.1) (tendsto_pi_nhds.mpr hf),?_⟩
  intro x
  choose y hy h using fun n=> (s n).property.2 x
  have he : Tendsto y atTop (𝓝 (f x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
    have h₂ := tendsto_iff_dist_tendsto_zero.mp (hf x)
    refine squeeze_zero (g:=fun n=>eps n+dist (g n x) (f x)) (fun _=>dist_nonneg) (fun n=> ?_) ?_
    · exact le_trans (dist_triangle (y n) (g n x) (f x)) (add_le_add (h n) le_rfl)
    simpa [eps] using h₁.add h₂
  exact hc.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds he) (Eventually.of_forall hy)
end
end GeneralMahler.Select

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Frame_Diagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Borel choice of diagonalizing frame. Everything computed in a
diagonalization is defined on a full orthogonal matrix and its entries. -/
noncomputable section
open Set Filter MeasureTheory Metric Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m:ℕ}
abbrev Frm (m:ℕ) := ↥(unitary (Mat m))
namespace Frm
variable (u v:Frm m)
def loc (A:Mat m) := star u.val*A*u.val
def fixMat (A:Mat m) := u.val*A*star u.val
def eig (A:Mat m) := Matrix.diag (u.loc A)
def Dgn (A:Mat m) := u.loc A = Matrix.diagonal (u.eig A)
lemma m₁ : star u.val*u.val=1 := u.property.1

lemma loc_fix (A:Mat m) : u.loc (u.fixMat A)=A := by
  unfold loc fixMat
  simp only [mul_assoc]
  rw [u.m₁,mul_one,← mul_assoc,u.m₁,one_mul]

lemma loc_one : u.loc 1=1 := by unfold loc; rw [mul_one,u.m₁]
lemma loc_sub (A B:Mat m) : u.loc (A-B)=u.loc A-u.loc B := by simp [loc,mul_sub,sub_mul]
lemma loc_add (A B:Mat m) : u.loc (A+B)=u.loc A+u.loc B := by simp [loc,mul_add,add_mul]
lemma loc_smul (a:ℝ) (A:Mat m) : u.loc (a• A)=a•u.loc A := by simp only [loc,mul_smul_comm,smul_mul_assoc]

def specEval (A:Mat m) (f:ℝ→ℝ) := u.fixMat (Matrix.diagonal (fun i=> f (u.eig A i)))

def eu {A:Mat m} (h:A.IsHermitian) : Frm m := h.eigenvectorUnitary
lemma eu_loc {A:Mat m} (h:A.IsHermitian) :
    (eu h).loc A= Matrix.diagonal h.eigenvalues := by
  open Unitary in
    have he := h.spectral_theorem
    simp only [conjStarAlgAut_apply,RCLike.ofReal_real_eq_id,Function.id_comp] at he
    exact (congrArg (eu h).loc he).trans ((eu h).loc_fix _)
lemma eu_eig {A:Mat m} (h:A.IsHermitian) : (eu h).eig A=h.eigenvalues := by rw [eig,eu_loc,Matrix.diag_diagonal]
lemma eu_d {A:Mat m} (h:A.IsHermitian) : (eu h).Dgn A := by rw [Dgn,eu_loc,eu_eig]

lemma cont_loc : Continuous (fun x:Mat m × Frm m=> x.2.loc x.1) := by
  let f := fun x:Mat m × Frm m=> x.2.val
  have hf : Continuous f := continuous_subtype_val.comp continuous_snd
  exact (hf.star.mul continuous_fst).mul hf
lemma cdiag : Continuous (Matrix.diag:Mat m→Fin m→ℝ) :=
  continuous_pi fun i=> (coeffMap i i).continuous
lemma cdiagonal : Continuous (Matrix.diagonal:(Fin m→ℝ)→Mat m) := by
  exact (Matrix.diagonalLinearMap (Fin m) ℝ ℝ).continuous_of_finiteDimensional
lemma Dgn_closed : IsClosed {p:Mat m×Frm m|p.2.Dgn p.1} :=
  isClosed_eq cont_loc (cdiagonal.comp (cdiag.comp cont_loc))

instance frame_cmp : CompactSpace (Frm m) := by
  change CompactSpace (↥((unitary (Mat m)):Set (Mat m)))
  rw [← isCompact_iff_compactSpace]
  let s : Set (Mat m) := unitary (Mat m)
  have hc : IsClosed s := (isClosed_eq (continuous_id.star.mul continuous_id)
    continuous_const).inter (isClosed_eq (continuous_id.mul continuous_id.star)
    continuous_const)
  exact (isCompact_closedBall 0 1).of_isClosed_subset hc
    (fun x hx=> by
      rw [mem_closedBall,dist_zero_right]
      rcases subsingleton_or_nontrivial (Mat m) with h | h
      · have h0 : x = 0 := @Subsingleton.elim _ h x 0
        rw [h0,norm_zero]
        exact zero_le_one
      · let : Nontrivial (Mat m) := h
        rw [CStarRing.norm_of_mem_unitary hx])

abbrev SH (m:ℕ) := {A:Mat m // A.IsHermitian}
lemma selectU :
    ∃ f:SH m→Frm m,Measurable f∧∀ A,(f A).Dgn A.val := by
  let F : Set (SH m × Frm m) := {x|x.2.Dgn x.1.val}
  have hs : IsClosed F :=
    (@Dgn_closed m).preimage ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have he (x:SH m) : ∃ y:Frm m,(x,y) ∈ F := ⟨eu x.property,eu_d x.property⟩
  exact Select.selector F he hs

def fr (A:SH m) : Frm m := selectU.choose A
end Frm
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Indicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! p-to-indicator score and layer integration formulas. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
def jump (z y:ℝ) := if y≤z then (1:ℝ) else 0
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Thresholds of arbitrary moderate-growth random Hermitian fields
(in particular A and L) §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}
structure FieldMat (m:ℕ) where
  A : Rn m→Mat m
  sym : ∀ x,(A x).IsHermitian
  hM : StronglyMeasurable A
  poly : PolyBound A

namespace FieldMat
variable (B:FieldMat m)

def Fr (x:Rn m) := Frm.fr (⟨B.A x,B.sym x⟩:Frm.SH m)
def ev (x:Rn m) := (B.Fr x).eig (B.A x)

def eval (f:ℝ→ℝ) (x:Rn m) := cfc f (B.A x)

def Θ (z:ℝ) (x:Rn m) := B.eval (jump z) x

def QP (z:ℝ) (x:Rn m) := B.Θ z x-st z • (1:Mat m)
end FieldMat
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EvalGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Primitive identities and notation for layer to spectral comparisons. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ}

namespace FieldMat
variable (B:FieldMat m)
def eVal (f:ℝ→ℝ) (z:ℝ) (x:Rn m) := B.eval f x-scalar m (f z)

def EC (v:Plane) (x:Rn m) := scalar m (jump v.2 v.1) - B.Θ v.2 x

def LL (u:Frm m) : Mat m →L[ℝ] Mat m :=
  LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
    toFun := u.loc
    map_add' := u.loc_add
    map_smul' := u.loc_smul }
end FieldMat
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Frame_Sec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Divided difference evaluated on two possibly different frames. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ}

-- averages on segment
def along (u:Plane) (t:ℝ) := (1-t)*u.1+t*u.2
def bav (f:ℝ→ℝ) (u:Plane) := ∫ t in (0:ℝ)..1,f (along u t)

namespace Frm
variable (u v w:Frm m)
def showM (A:Mat m) := star u.val*A*v.val
def hideM (A:Mat m) := u.val*A*star v.val

def secDiag (A B:Mat m) (g:Plane→ℝ) (C:Mat m) : Mat m :=
  Matrix.of (fun i j=> g (u.eig A i,v.eig B j)*u.showM v C i j)
def sec (A B:Mat m) (g:Plane→ℝ) (C:Mat m) :=
  u.hideM v (u.secDiag v A B g C)

lemma sec_add (A B:Mat m) (g:Plane→ℝ) (C D:Mat m) :
    u.sec v A B g (C+D)=u.sec v A B g C+u.sec v A B g D := by
  have he : u.secDiag v A B g (C+D) = u.secDiag v A B g C+u.secDiag v A B g D := by
    ext i j; simp [secDiag,showM,mul_add,add_mul]
  unfold sec; rw [he]; simp only [hideM,mul_add,add_mul]
lemma sec_smul (A B:Mat m) (g:Plane→ℝ) (a:ℝ) (C:Mat m) :
    u.sec v A B g (a•C)=a•u.sec v A B g C := by
  unfold sec
  have he : u.secDiag v A B g (a•C)=a•u.secDiag v A B g C := by
    ext i j; simp [secDiag,showM,mul_left_comm]
  rw [he]
  simp only [hideM,smul_mul_assoc,mul_smul_comm]

end Frm
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_MatrixDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Derivative of spectral function of linear field. Avoid polynomial
approximation by exact secant identity and Borel frame compactness. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Asymptotics
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace Frm
def DL (u v:Frm m) (A B:Mat m) (g:Plane→ℝ) : Mat m →L[ℝ] Mat m :=
  LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
    toFun := u.sec v A B g
    map_add' := u.sec_add v A B g
    map_smul' := u.sec_smul v A B g }
end Frm

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Packet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Fixed profiles supplementing Profile.d,v,g, exact constants
and layered profiles. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.Profile
def bb : ℝ := 602/1000
def cc : ℝ := 365/1000
def r : ℝ := 22/100
def omegaP : ℝ := 46/10
def sb : ℝ := 36/10
def eta : ℝ := 22/1000
def kk : ℝ := √(bb-cc)
def kar : ℝ := 116/100
def ar : ℝ := 75/10
def tc : ℝ := 21/1000
def tr : ℝ := 43/1000
def bm : ℝ := (1+tmax)*(bb-3*eta)/(3*(3*(bb+eta)-4*cc))
def e₀ : ℝ := 256/1000
def alpha : ℝ := 226/100
def h₀ : ℝ := 5/10

def rad (x:ℝ) := bb-r^2-d x
def qu (x:ℝ) := kk-√(rad x)
def angle (x:ℝ) := omegaP*Real.arsinh (x/sb)
def uc (x:ℝ) := r*Real.cos (angle x)
def us (x:ℝ) := r*Real.sin (angle x)
def FF (x:ℝ) := cc+2*kk*qu x
def Cp (x:ℝ) := -d x+(ar-1)*deriv (deriv g) x
def Kp (x:ℝ) := d x-2*g x

def HH (w:Plane) := 4*cc+4*kk*qu w.2+2*(kk-qu w.2)*N2 qu w.1 -
    2*(N2 uc w.1*uc w.2+N2 us w.1*us w.2)
def Hh (w:Plane) := HH w+deriv (deriv v) w.2-2*kar

-- Properties proved later in the scalar estimates and used in abstract layer lemmas
structure LayerOK : Prop where
  rp : ∀ x, 0 < rad x
  q_test : TestF qu
  c_test : TestF uc
  s_test : TestF us
  q_even : Function.Even qu
  sq_p : ∀ x,0<N2 qu x
  v_bound : ∀ x,|deriv v x-x|≤319/1000
  bh_contact : ∀ x y,0<4*cc+2*kk*(N2 qu x+N2 qu y)-
    N2 qu x*N2 qu y - (N2 uc x*N2 uc y+N2 us x*N2 us y)
  bh_layer : ∀ w:Plane, HH w + tc*Hh w-1/2*tr*(h₀+Hh w^2/h₀)>
    2*(bb+eta+(bb+eta-kar)*tmin)+2*bm*N2 qu w.1*N2 qu w.2+2*e₀*(2*tr)^2+Hh w^2/alpha

end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_BiWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Layer functional ℒ and polynomial-growth calculus. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers

structure Bwt (l:Plane→ℝ) : Prop where
  c : Continuous l
  p : PolyBound l

def bAv (g:Plane→ℝ) (u:Plane) := ∫ t in (0:ℝ)..1,g (u.1,along u t)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_LFun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! ℒ evaluation; linearity and spectral form. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace FieldMat
variable (B:FieldMat m)
def bmat (f:Plane→ℝ) (z:ℝ) (x:Rn m) := B.eval (fun y=>f (z,y)) x
end FieldMat

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Algebra of the positive layer blocks (with no commutation
assumptions). All entries here are in a fixed spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ}
def hsN (A:Mat m) := trN (A*star A)
def cmu (A B:Mat m) := A*B-B*A
def mats (f:Fin m→ℝ) := (∑ i,f i)/(m:ℝ)
lemma Frm.loc_psd (u:Frm m) {A:Mat m} (ha:0≤A):0≤u.loc A := by
  have he := ha.posSemidef.conjTranspose_mul_mul_same u.val
  exact he.nonneg
lemma Frm.loc_le (u:Frm m) {A B:Mat m} (ha:A ≤ B):u.loc A ≤ u.loc B := by
  rw [← sub_nonneg,← u.loc_sub]
  apply u.loc_psd (sub_nonneg.mpr ha)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Extract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Frame decomposition of layer functionals. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

-- densities of β integrals at a fixed x,z
def linW (f:Plane→ℝ) (u:Plane):=(u.2-u.1)*f u
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Klimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Pointwise Young estimate assembled before integrating; common
lemma for the two kernel estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]

def Hcomm (A:Rn m→Mat m) (T:Mat m) := ∫ x,hsN (cmu (A x) T) ∂normal m

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Variation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Inverse-kernel and variation identity Eq14. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler
open Profile Layers
def Nr (g:ℝ→ℝ) := fun x=> g x+N g x
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Prim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar primitive conventions and calculus for §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Profile
open Layers
def prim (l:ℝ→ℝ) (x:ℝ) := ∫ t in (0:ℝ)..x,l t

def pl (l:ℝ→ℝ) (x) := prim l x-ga (prim l)

def fl (l:ℝ→ℝ) := Nr (pl l)
def ps (l:ℝ→ℝ) := prim fun x=> N (pl l) x-pl l x
end GeneralMahler.Profile

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Tbound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §05 the two layer estimates, retained penalties. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers

namespace Profile
def ap := bb+eta+(bb+eta-kar)*tmin
def lm := bb+eta+kar*tmin+1/8
def P0 (x:Plane) := 2*ap+2*bm*N2 qu x.1*N2 qu x.2+2*e₀*(2*tr)^2
def wwR (w:Plane) := tc*bAv Hh w - tr/2*(h₀+bAv Hh w^2/h₀)
def ww (w:Plane) := bAv (fun w=> HH w-P0 w) w+wwR w
def ww0 (w:Plane) := bAv (fun w=>Hh w^2) w / alpha
end Profile
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
Fixed-denominator rational interval certificates (§07–08).
Unknown intervals admit all real values.
-/
namespace GeneralMahler.Cert
inductive IV
  | unk
  | box (lo hi:Int)
deriving DecidableEq, Repr

namespace IV
def den : Int := 1000000000000000000000000000000
noncomputable def w (a:Int) := (a:ℝ)/(den:ℝ)
def Has (x:ℝ): IV → Prop
  | unk => True
  | box l h=> w l ≤ x ∧ x ≤ w h

instance instMembershipReal : Membership ℝ IV := ⟨fun v x=>Has x v⟩

def c (n:Int):IV := box (n*den) (n*den)
instance instOfNat (n:Nat) : OfNat IV n := ⟨c n⟩

protected def add0 : IV→IV→IV
  | box a b,box c d=> box (a+c) (b+d)
  | _,_=> unk
instance instAdd : Add IV := ⟨IV.add0⟩
protected def n0 : IV → IV
  | box a b=> box (-b) (-a)
  | _=> unk
instance instNeg : Neg IV := ⟨IV.n0⟩
instance instSub : Sub IV := ⟨fun a b=> a+ -b⟩

-- upward round division
def ud (a b : Int) : Int := -((-a)/b)
protected def mul0 : IV → IV → IV
  | box a b,box c d =>
    let l:=min (min (a*c) (a*d)) (min (b*c) (b*d))
    let h:=max (max (a*c) (a*d)) (max (b*c) (b*d))
    box (l/den) (ud h den)
  | _,_=> unk
instance instMul : Mul IV := ⟨IV.mul0⟩

def posInv (a b:Int) : IV := box (den*den/b) (ud (den*den) a)
protected def inv0 : IV→IV
  | box a b=> if a>0 then posInv a b else if b<0 then -posInv (-b) (-a) else unk
  | unk=> unk
instance instInv : Inv IV := ⟨IV.inv0⟩
instance instDiv : Div IV := ⟨fun a b=>a*b⁻¹⟩

protected def pow0 (A:IV) : ℕ→IV
  | 0=>1
  | n+1=> (A.pow0 n)*A
instance instPowNat : Pow IV ℕ := ⟨IV.pow0⟩

def clampNN : IV→IV
  | box a b=> box (max 0 a) b
  | unk=> unk

def Zmax : IV→IV→IV
  | box a b,box c d=> box (max a c) (max b d)
  | _,_ =>unk
def Zabs (x:IV) : IV := clampNN (Zmax x (-x))
def sq (x:IV) : IV := (Zabs x)*(Zabs x)
def span : IV→IV→IV
  | box a b,box c d=> box (min a c) (max b d)
  | _,_=>unk
def Less : IV→IV→Bool
  | box _ b,box c _=> decide (b < c)
  | _,_=>false
def LeB : IV→IV→Bool
  | box _ b,box c _=> decide (b ≤ c)
  | _,_=>false
def SubB : IV→IV→Bool
  | _,unk=>true
  | box a b,box c d=> decide (c≤a) && decide (b≤d)
  | _,_=>false

end IV
end GeneralMahler.Cert

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Jet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Real and interval towers of higher derivatives. -/
open Set Filter
open scoped Topology
namespace GeneralMahler.Jet
abbrev J (α:Type*) := ℕ → α
def tail {α} (x:J α): J α:=fun n=>x (n+1)
def ray {α} [Zero α] (x:α):J α
  | 0=>x
  | _+1=>0
def plusJ {α} [Add α] (x y:J α):J α:=fun n=>x n+y n
def subJ {α} [Sub α] (x y:J α):J α:=fun n=>x n-y n
def negJ {α} [Neg α] (x:J α):J α:=fun n=> -x n

def mulJ0 {α} [Add α] [Mul α] : ℕ→ J α→J α→α
  | 0,x,y=> x 0*y 0
  | n+1,x,y=> mulJ0 n (tail x) y+mulJ0 n x (tail y)
def mulJ {α} [Add α] [Mul α] (x y:J α):J α := fun n=> mulJ0 n x y

-- returns derivative of f(x)*y with f derivatives supplied by w
def cpM {α} [Add α] [Mul α]: ℕ→J α→J α→J α→α
  | 0,w,_,y=> w 0*y 0
  | n+1,w,x,y=> cpM n (tail w) x (mulJ (tail x) y) + cpM n w x (tail y)
def compJ {α} [Add α] [Mul α] (w x:J α):J α
  | 0=> w 0
  | n+1=> cpM n (tail w) x (tail x)

-- pointwise tower of derivative functions on S
abbrev RF:=ℝ→J ℝ
def TW (S:Set ℝ) (X:RF) : Prop :=
  ∀ n:ℕ,∀ x∈S, HasDerivAt (fun x=>X x n) (X x (n+1)) x
variable {S T:Set ℝ} {X Y W:RF}

noncomputable def dV (f:ℝ→ℝ): ℕ → ℝ →ℝ
  | 0=>f
  | n+1=>deriv (dV f n)

open Cert Cert.IV
instance instZeroIV : Zero IV := ⟨IV.c 0⟩
def Fits (X:J ℝ) (A:J IV):Prop:=∀ n,X n∈A n
end GeneralMahler.Jet

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Elem
attribute [-instance] _root_.OAI.GeneralMahler.Jet.instZeroIV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval square root and exponential. -/
namespace GeneralMahler.Cert.IV
def piB : IV := box 3141592653589793238460000000000
  3141592653589793238470000000000

def isrt (n: Int) : Nat → Int → Int
  | 0,x=>x
  | m+1,x=> let y:=(x+n/x)/2; if y<x then isrt n m y else x
def getR (a:Int) : Int :=
  -- A fixed initial upper estimate feeds the integer Newton iteration.
  -- Failed enclosure inequalities produce the unknown interval.
  isrt (a*den) 112 (1000*den)

def rlo (a:Int) : Int := if a>0 then getR a else 0

def rtB : IV→IV
  | unk=>unk
  | box a b =>
    let l:= rlo a
    let u:= getR (max b 0)+1
    if u≥0 && (max b 0)*den ≤ u*u && (a≤0 || (l≥0 && l*l ≤ a*den)) then box l u
    else unk

def eSeries (A:IV) : ℕ→IV×IV
  | 0=>(1,0)
  | n+1=>
    let p:=eSeries A n
    (p.1*A/c (Int.ofNat (n+1)),p.2+p.1)
open Finset

-- error < 1e-24 through terms n=0:24.
def terr : IV := box (-1000000) 1000000

protected def esmall (A:IV) : IV :=
  clampNN ((eSeries A 25).2+terr)

def ebox : ℕ→IV→IV
  | 0,A=> if LeB (Zabs A) 1 then A.esmall else unk
  | n+1,A=>
    if LeB (Zabs A) 1 then A.esmall
    else let B:= ebox n (A/(2:IV)); B*B

end GeneralMahler.Cert.IV

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Log
attribute [-instance] _root_.OAI.GeneralMahler.Jet.instZeroIV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.Cert.IV
open Real Finset

def seriesL (Y:IV):ℕ→IV×IV
  | 0=>(Y,0)
  | n+1=>let z:= seriesL Y n; (z.1*(sq Y), z.2+z.1/c (Int.ofNat (2*n+1)))
def logY (X:IV) := (X-1)/(X+1)
def lob (X:IV) := Less 0 X && LeB (Zabs (logY X)) (1/2)
def errLog : IV := box (-10000000000000) 10000000000000
def lbox0 (X:IV):=2*((seriesL (logY X) 32).2+errLog)

def lbox : ℕ→IV→IV
  | 0,A=> if lob A then lbox0 A else unk
  | n+1,A=>if Less 0 A then if lob A then lbox0 A else
      2*lbox n (rtB A)
    else unk

end GeneralMahler.Cert.IV

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_JCalc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Tower AD for exp, log, inverse, square root. -/
open Set Real
namespace GeneralMahler.Jet

noncomputable def vn (n:ℕ):ℝ:=n
def invJs {α} [Inv α] [Mul α] [Neg α] (c:ℕ→α) (x:α) : J α
  | 0=>x⁻¹
  | n+1=> -(c (n+1)*(x⁻¹)* invJs c x n)
def rootJs {α} [Inv α] [Mul α] [Sub α] (h:α) (c:ℕ→α) (x a:α) : J α
  | 0=>a
  | n+1=>(h-c n)*(x⁻¹)* rootJs h c x a n
def logJs {α} [Inv α] [Mul α] [Neg α] (c:ℕ→α) (x a:α) : J α
  | 0=>a
  | n+1=>invJs c x n

-- utilities (exp evaluation an external input)
def expSub {α} [Add α] [Mul α] (X:J α) (a:α) : J α :=
  compJ (fun _=>a) X
def invSub {α} [Add α] [Inv α] [Mul α] [Neg α] (c:ℕ→α) (X:J α) : J α :=
  compJ (invJs c (X 0)) X
def logSub {α} [Add α] [Inv α] [Mul α] [Neg α] (c:ℕ→α) (X:J α) (a:α) : J α :=
  compJ (logJs c (X 0) a) X
def rootSub {α} [Add α] [Inv α] [Mul α] [Sub α] (h:α) (c:ℕ→α) (X:J α) (a:α) : J α :=
  compJ (rootJs h c (X 0) a) X

variable {S:Set ℝ} {X:RF}

open Cert Cert.IV
def ub (n:ℕ):IV:=c n
end GeneralMahler.Jet

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Chord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interpolation/range certificate through second derivatives. -/
open Set Filter Real
namespace GeneralMahler
namespace Jet
variable {f g h:ℝ→ℝ}
def mix (x y a:ℝ):=(1-a)*x+a*y

end Jet
namespace Cert.IV
open Jet
-- largest norm limit as point
def limK : IV→IV
  | unk=>unk
  | box a b=>let c:=max (-a) (max 0 b); box c c
def Radius (D W:IV) := limK W/c 8 * sq D
def bcChord (D V W F:IV):=
  let R:=Radius D F
  IV.span V W+IV.span (-R) R

end Cert.IV
end GeneralMahler

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Intervals_Trig
attribute [-instance] _root_.OAI.GeneralMahler.Jet.instZeroIV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.Cert.IV
open Complex Finset

abbrev Duo:=IV×IV
def covers (v:Duo) (x:ℂ):Prop :=
  x.re∈v.1 ∧ x.im∈v.2
def isum (X:IV) : ℕ→ Duo × Duo
  | 0=> ((1,0),(0,0))
  | n+1=>
    let (a,b):=isum X n
    let Y:=X/c (Int.ofNat (n+1))
    ((-(a.2*Y),a.1*Y),(b.1+a.1,b.2+a.2))

def smallsc (X:IV) : Duo :=
  let a:=(isum X 25).2
  (a.1+terr,a.2+terr)

def trbox : ℕ→IV→ Duo
  | 0,X=> if LeB (Zabs X) 1 then smallsc X else (unk,unk)
  | n+1,X=>
    if LeB (Zabs X) 1 then smallsc X else
      let (c,s):=trbox n (X/(2:IV))
      (sq c - sq s,2*c*s)
end GeneralMahler.Cert.IV

end OAI
end

section
-- module Solutions.OAIQ026_GM.StdSimplexCompat
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Orthant
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Full-dimensional simplicial cones, coordinates and Laplace integrals. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ}

section Orthant

variable (b : Basis (Fin m) ℝ E)

def orthant : ProperCone ℝ E where
  carrier := {p | ∀ i, 0 ≤ b.equivFun p i}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    simpa using add_nonneg (hx i) (hy i)
  smul_mem' := by
    rintro ⟨r,hr⟩ x hx i
    change 0 ≤ b.equivFun (r • x) i
    simpa using mul_nonneg hr (hx i)
  isClosed' := by
    simp_rw [ofPred_forall]
    apply isClosed_iInter; intro i
    apply isClosed_le continuous_const
    exact (continuous_apply i).comp b.equivFun.toContinuousLinearEquiv.continuous

@[simp] theorem mem_orthant {p : E} :
    p ∈ orthant b ↔ ∀ i, 0 ≤ b.equivFun p i := Iff.rfl

/-- Exact cone equality class in the proof: image of a coordinate orthant
by an invertible linear map. Basis vectors serve as generating rays. -/
def IsLinearOrthant (m : ℕ) (C : ProperCone ℝ E) :=
  ∃ a : Basis (Fin m) ℝ E, C = orthant a

end Orthant

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Segments
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! End point profile tests for Eq26-27. Segment condition Eq4 (proved in scalar part). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler
namespace Segment
open Profile

/-- remainder of scalar profile. bstar uses A profile. -/
def rest (f:ℝ→ℝ) (u:Plane) := bav f u-f u.1
def dis (f:ℝ→ℝ) (u:Plane) := bav f u-f u.2
def sqav (f:ℝ→ℝ) (u:Plane) := bav (fun z=> f z^2) u
def mdis (f:ℝ→ℝ) (u:Plane) := sqav f u-2*bav f u*f u.2 + f u.2^2
def vdis (f:ℝ→ℝ) (u:Plane) := sqav f u-(bav f u)^2
def vsum (u:Plane) := vdis uc u+vdis us u+vdis qu u
def rsum (u:Plane) := mdis uc u+mdis us u+mdis qu u
def dsum (u:Plane) := dis uc u^2+dis us u^2+dis qu u^2
def bstar (u:Plane) := rest Cp u-rsum u
def anti (u:Plane) (f:ℝ→ℝ) := f u.2-f u.1
def sgamma (u:Plane) :=
  ((80/100)/mstar^2)*(125/100*(anti u Kp+tc*anti u Cp)^2+5*Profile.tr^2*anti u Cp^2)
def resid (u:Plane) :=
  rest Kp u+sgamma u+(1/(4*lam))*bstar u^2 + tmax*dsum u-vsum u
def symR (u:Plane) := (1/2:ℝ)*(resid u+resid u.swap)
def SegmentOK := ∀ x y:ℝ,x<y→ symR (x,y)<0

end Segment
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Nu
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Positive endpoint functional Nu. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Segment
variable {m:ℕ}
namespace LPt
variable (M:Mat m) (l:Fin m→ℝ)
def npt (f:Plane→ℝ) :=
  mats (fun i=>∑ j,M i j^2*f (l i,l j))
def mout (f:Plane→ℝ) : Mat m :=
  Matrix.of fun i j=>M i j*f (l i,l j)

end LPt
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Linear_Gram
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §06 weighted Dirichlet inequality: in a spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
namespace LPt
open HMode Profile Layers Segment
variable {m:ℕ}
variable (M W:Mat m) (l:Fin m→ℝ)
def uf (f:ℝ→ℝ) := Matrix.diagonal (fun i=> f (l i))
def RR0 (f:ℝ→ℝ) :=
  Pj W M (mout M l (bav f))-Pj W (M*M) (uf l f)
def JJ0 (f:ℝ→ℝ) :=
  Pj W M (mout M l (bav (fun x=>f x^2)))-
  Pj W (mout M l (bav f)) (mout M l (bav f))

end LPt
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Lift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cone over the affine section t=1. Coordinates here ordered t,x. -/
noncomputable section
open Filter Set MeasureTheory Real WithLp
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace
namespace GeneralMahler

/-- Paper K is a real convex body *with interior*. -/
structure Body (n : ℕ) extends ConvexBody (Rn n) where
  solid : (interior carrier).Nonempty

namespace Body
variable {n : ℕ}
instance instSetLikeRn : SetLike (Body n) (Rn n) where
  coe K := K.carrier
  coe_injective A B h := by cases A; cases B; congr; exact ConvexBody.ext h
protected theorem isCompact (K : Body n) : IsCompact (K : Set (Rn n)) := K.isCompact'
protected theorem convex (K : Body n) : Convex ℝ (K : Set (Rn n)) := K.convex'
protected theorem has_interior (K : Body n) : (interior (K : Set (Rn n))).Nonempty := K.solid
protected theorem nonempty (K : Body n) : (K : Set (Rn n)).Nonempty := K.nonempty'
end Body

abbrev LiftSpace (n : ℕ) := WithLp 2 (ℝ × Rn n)

variable {n : ℕ}
def pair (s : ℝ) (x : Rn n) : LiftSpace n := WithLp.toLp 2 (s,x)
def hgt (p : LiftSpace n) : ℝ := p.fst
def horiz (p : LiftSpace n) : Rn n := p.snd
@[simp] theorem pair_hgt (s : ℝ) (x : Rn n) : hgt (pair s x) = s := rfl
@[simp] theorem pair_horiz (s : ℝ) (x : Rn n) : horiz (pair s x) = x := rfl
@[simp] theorem hgt_horiz_pair (p : LiftSpace n) : pair (hgt p) (horiz p) = p := rfl
@[simp] theorem pair_zero : pair 0 (0:Rn n) = 0 := rfl
@[simp] theorem pair_inner (s t : ℝ) (x y : Rn n) :
    ⟪pair s x, pair t y⟫ = t*s + ⟪x,y⟫ := rfl
@[simp] theorem hgt_add (p q : LiftSpace n) : hgt (p+q) = hgt p + hgt q := rfl
@[simp] theorem horiz_add (p q : LiftSpace n) : horiz (p+q) = horiz p + horiz q := rfl
@[simp] theorem hgt_smul (a : ℝ) (p : LiftSpace n) : hgt (a • p) = a * hgt p := rfl
@[simp] theorem horiz_smul (a : ℝ) (p : LiftSpace n) :
    horiz (a • p) = a • horiz p := rfl
theorem smul_pair (a t : ℝ) (x : Rn n) :
    a • pair t x = pair (a*t) (a • x) := rfl
@[fun_prop] theorem continuous_pair : Continuous (fun p : ℝ × Rn n => pair p.1 p.2) :=
  WithLp.prod_continuous_toLp ..
@[fun_prop] theorem continuous_pair' {X : Type*} [TopologicalSpace X] {a : X → ℝ}
    {b : X → Rn n} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => pair (a x) (b x)) := continuous_pair.comp (ha.prodMk hb)
@[fun_prop] theorem continuous_hgt : Continuous (@hgt n) :=
  continuous_fst.comp (WithLp.prod_continuous_ofLp ..)
@[fun_prop] theorem continuous_horiz : Continuous (@horiz n) :=
  continuous_snd.comp (WithLp.prod_continuous_ofLp ..)

namespace Body

/-- The solid pointed cone generated by (1,K). -/
def cone (K : Body n) : ProperCone ℝ (LiftSpace n) where
  carrier := {p | 0 ≤ hgt p ∧ ∃ x ∈ (K:Set (Rn n)), horiz p = hgt p • x}
  zero_mem' := by simpa [hgt,horiz, Set.Nonempty] using K.nonempty
  add_mem' := by
    rintro p q ⟨hp, x, hx, he⟩ ⟨hq, y, hy, hf⟩
    change 0 ≤ hgt (p+q) ∧ _
    simp only [hgt_add,horiz_add, he,hf]
    refine ⟨add_nonneg hp hq,?_⟩
    set t := hgt p + hgt q
    by_cases ht : t = 0
    · have ha : hgt p = 0 := by dsimp [t] at ht; linarith
      have hb : hgt q = 0 := by dsimp [t] at ht; linarith
      exact ⟨x,hx,by simp [ha,hb,ht]⟩
    · have ht' : 0 < t := lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm ht)
      refine ⟨(hgt p/t) • x + (hgt q/t) • y, K.convex hx hy
        (div_nonneg hp ht'.le) (div_nonneg hq ht'.le) (by rw [← add_div]; exact div_self ht),?_⟩
      rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ ht, mul_div_cancel₀ _ ht]
  smul_mem' := by
    rintro ⟨r,hr⟩ p ⟨hp,x,hx,he⟩
    change 0 ≤ hgt (r • p) ∧ _
    change 0 ≤ r * hgt p ∧ ∃ x ∈ (K:Set (Rn n)), r • horiz p = (r * hgt p) • x
    exact ⟨mul_nonneg hr hp, x,hx,by rw [he,smul_smul]⟩
  isClosed' := by
    let : CompactSpace ↥(K : Set (Rn n)) := isCompact_iff_compactSpace.mp K.isCompact
    let S := {u : LiftSpace n × ↥(K:Set (Rn n)) |
      0 ≤ hgt u.1 ∧ horiz u.1 = hgt u.1 • u.2.val}
    have hu : IsClosed S := by
      change IsClosed ({u : LiftSpace n × ↥(K:Set (Rn n)) | 0 ≤ hgt u.1} ∩ {u | horiz u.1 = hgt u.1 • u.2.val})
      apply IsClosed.inter
      · exact isClosed_le continuous_const (by fun_prop)
      · exact isClosed_eq (by fun_prop) (by fun_prop)
    have h := isClosedMap_fst_of_compactSpace _ hu
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [S]

@[simp] theorem pair_mem_cone (K : Body n) (s : ℝ) (v : Rn n) :
    pair s v ∈ K.cone ↔ 0 ≤ s ∧ ∃ x ∈ K, v = s • x := Iff.rfl

theorem pair_mem_interior_cone_iff (K : Body n) (s : ℝ) (hs : 0 < s)
    (x : Rn n) :
    pair s (s • x) ∈ interior (K.cone : Set (LiftSpace n)) ↔ x ∈ interior (K : Set (Rn n)) := by
  constructor
  · intro h
    let f := fun y : Rn n => pair s (s • y)
    have he : f ⁻¹' (K.cone : Set (LiftSpace n)) = K := by
      ext y
      simp only [f, mem_preimage, SetLike.mem_coe, pair_mem_cone, hs.le, true_and]
      simp [smul_right_injective _ hs.ne' |>.eq_iff]
    have hfc : Continuous f := by dsimp [f]; fun_prop
    rw [mem_interior_iff_mem_nhds, ← he]
    exact (hfc.tendsto x) (mem_interior_iff_mem_nhds.mp h)
  · intro hx
    rw [mem_interior_iff_mem_nhds]
    let p := pair s (s • x)
    change ∀ᶠ t in 𝓝 p, t ∈ (K.cone : Set (LiftSpace n))
    let f := fun t : LiftSpace n => (hgt t)⁻¹ • horiz t
    have hfc : ContinuousAt f p := (continuous_hgt.continuousAt.inv₀ (show hgt p ≠ 0 from hs.ne')).smul
      continuous_horiz.continuousAt
    have he : f p = x := by simp [p,f,hs.ne']
    have ha : ∀ᶠ t in 𝓝 p, f t ∈ (K : Set (Rn n)) :=
      hfc (by rw [he]; exact mem_interior_iff_mem_nhds.mp hx)
    have hb : ∀ᶠ t in 𝓝 p, 0 < hgt t := continuous_hgt.continuousAt (Ioi_mem_nhds hs)
    filter_upwards [ha,hb] with t ht hy
    change 0 ≤ hgt t ∧ _
    exact ⟨hy.le, f t, ht, by simp [f,hy.ne']⟩

theorem axis_dual_interior (K : Body n) (s : ℝ) (hs : 0 < s) :
    pair s 0 ∈ interior (posDual K.cone : Set (LiftSpace n)) := by
  by_contra h
  obtain ⟨p,hp,hpq,hr⟩ := exists_ray_of_not_interior_dual h
  rw [← hgt_horiz_pair p] at hp hr hpq
  obtain ⟨hu,x,hx,he⟩ := (pair_mem_cone ..).mp hp
  rw [pair_inner, inner_zero_left, add_zero] at hr
  have h₀ : hgt p = 0 := by nlinarith
  rw [he,h₀,zero_smul,pair_zero,norm_zero] at hpq
  norm_num at hpq

end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Polar
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Polar bodies, translations, and slices. -/
noncomputable section
open Set MeasureTheory Real WithLp Metric Filter
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace
namespace GeneralMahler
variable {n : ℕ}

namespace Body

/-- K translated by -z. -/
def off (K : Body n) (z : Rn n) : Body n where
  carrier := (fun x => z + x) ⁻¹' (K : Set (Rn n))
  convex' := by
    intro x hx y hy a b ha hb hab
    have H := K.convex hx hy ha hb hab
    change z + (a • x + b • y) ∈ K
    change a • (z+x) + b • (z+y) ∈ K at H
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at H
    exact H
  isCompact' := (Homeomorph.addLeft z).isCompact_preimage.mpr K.isCompact
  nonempty' := by
    obtain ⟨x,hx⟩ := K.nonempty
    refine ⟨-z+x,?_⟩
    simpa using hx
  solid := by
    obtain ⟨x,hx⟩ := K.has_interior
    refine ⟨-z+x,?_⟩
    change _ ∈ interior ((Homeomorph.addLeft z) ⁻¹' _)
    rw [← Homeomorph.preimage_interior]
    simpa using hx

@[simp] theorem mem_off {K : Body n} (z x : Rn n) :
    x ∈ K.off z ↔ z+x ∈ K := Iff.rfl

theorem off_interior {K : Body n} {z : Rn n} (hz : z ∈ interior (K:Set (Rn n))) :
    0 ∈ interior (K.off z : Set (Rn n)) := by
  change _ ∈ interior ((Homeomorph.addLeft z) ⁻¹' _)
  rw [← Homeomorph.preimage_interior]
  simp
  exact hz

theorem polar_off (K : Body n) (z : Rn n) :
    polarAt K z = polarAt (K.off z) 0 := by
  ext y
  constructor
  · intro hy x hx
    simpa using hy (z+x) hx
  · intro hy x hx
    have hm : x-z ∈ K.off z := by
      simpa [sub_eq_add_neg, add_left_comm] using hx
    simpa using hy _ hm

/-- Uniform lower bound for height in the dual cone to K with 0 interior. -/
lemma dual_height {K : Body n} (hk : 0 ∈ interior (K:Set (Rn n))) :
    ∃ c > 0, ∀ p ∈ posDual K.cone, c * ‖p‖ ≤ hgt p := by
  have heq : posDual (posDual K.cone) = K.cone := ProperCone.innerDual_innerDual _
  have H : pair 1 0 ∈ interior (posDual (posDual K.cone) : Set (LiftSpace n)) := by
    rw [heq]
    simpa using (pair_mem_interior_cone_iff K 1 (by norm_num) 0).mpr hk
  obtain ⟨c,hc,hb⟩ := interior_dual_bound H
  refine ⟨c,hc,fun p hp => ?_⟩
  have h := hb p hp
  conv at h =>
    rhs
    rw [← hgt_horiz_pair p, pair_inner, inner_zero_left, add_zero, mul_one]
  exact h

lemma dual_head {K : Body n} (x : Rn n) :
    pair 1 x ∈ posDual K.cone ↔ -x ∈ polarAt (K : Set (Rn n)) 0 := by
  rw [mem_posDual]
  constructor
  · intro h y hy
    change y ∈ K at hy
    have H := h (show pair 1 y ∈ K.cone by simp [hy])
    rw [pair_inner, mul_one] at H
    change ⟪-x,y-0⟫ ≤ 1
    rw [inner_neg_left, sub_zero, real_inner_comm]
    linarith
  · intro h p hp
    rw [← hgt_horiz_pair p] at hp ⊢
    obtain ⟨hu,a,ha,he⟩ := (pair_mem_cone ..).mp hp
    have H := h _ ha
    rw [inner_neg_left, sub_zero, real_inner_comm] at H
    rw [pair_inner, he, real_inner_smul_left]
    nlinarith

/-- Slice t=1 of the dual, a reflected polar. -/
def polarSlice (K : Body n) (hk : 0 ∈ interior (K:Set (Rn n))) : Body n where
  carrier := {x | pair 1 x ∈ posDual K.cone}
  convex' := by
    intro x hx y hy a b ha hb hab
    have H := (posDual K.cone).convex hx hy ha hb hab
    change pair 1 (a • x + b • y) ∈ posDual K.cone
    change a • pair 1 x + b • pair 1 y ∈ posDual K.cone at H
    have he : a • pair 1 x + b • pair 1 y = pair 1 (a • x + b • y) := calc
      _ = pair (a * 1+b*1) (a • x+b • y) := rfl
      _ = _ := by rw [mul_one,mul_one,hab]
    rwa [he] at H
  isCompact' := by
    have hcl : IsClosed {x | pair 1 x ∈ posDual K.cone} :=
      (posDual K.cone).isClosed.preimage (show Continuous (fun x : Rn n => pair 1 x) by fun_prop)
    apply (Metric.isCompact_iff_isClosed_bounded).mpr
    obtain ⟨c,hc,hcw⟩ := dual_height hk
    refine ⟨hcl,(isBounded_closedBall (x := (0:Rn n)) (r := 1/c)).subset ?_⟩
    intro x hx
    rw [mem_closedBall, dist_zero_right, le_div_iff₀ hc, mul_comm]
    have H := hcw (pair 1 x) hx
    have hn := WithLp.prod_norm_sq_eq_of_L2 (pair 1 x)
    change ‖pair 1 x‖ ^ 2 = ‖(1:ℝ)‖ ^ 2 + ‖x‖^2 at hn
    have hp : ‖x‖ ≤ ‖pair 1 x‖ := by nlinarith [norm_nonneg (pair 1 x)]
    exact le_trans (mul_le_mul_of_nonneg_left hp hc.le) H
  nonempty' :=
    ⟨0, show pair 1 0 ∈ posDual K.cone from interior_subset (axis_dual_interior K 1 zero_lt_one)⟩
  solid := by
    refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
    have h : Continuous (fun x : Rn n => pair 1 x) := by fun_prop
    exact (h.tendsto 0) (mem_interior_iff_mem_nhds.mp (axis_dual_interior K 1 zero_lt_one))

theorem cone_polarSlice (K : Body n) (hk : 0 ∈ interior (K:Set (Rn n))) :
    (polarSlice K hk).cone = posDual K.cone := by
  ext p
  rw [← hgt_horiz_pair p, pair_mem_cone]
  constructor
  · rintro ⟨ht,x,hx,he⟩
    change pair 1 x ∈ posDual K.cone at hx
    have H := (posDual K.cone).smul_mem hx ht
    simpa only [smul_pair,mul_one,he] using H
  · rw [hgt_horiz_pair]
    intro hp
    obtain ⟨c,hc,hcw⟩ := dual_height hk
    have H := hcw p hp
    by_cases hz : p = 0
    · subst p
      obtain ⟨x,hx⟩ := (K.polarSlice hk).nonempty
      refine ⟨le_refl _,x,hx,?_⟩
      change 0 = (0:ℝ) • x
      simp
    · have hr : 0 < hgt p := lt_of_lt_of_le (mul_pos hc (norm_pos_iff.mpr hz)) H
      refine ⟨hr.le,(hgt p)⁻¹ • horiz p, ?_, by simp [hr.ne']⟩
      change pair 1 _ ∈ posDual _
      have he := (posDual K.cone).smul_mem hp (inv_nonneg.mpr hr.le)
      have hpair : (hgt p)⁻¹ • p = pair 1 ((hgt p)⁻¹ • horiz p) := calc
        _ = pair ((hgt p)⁻¹ * hgt p) ((hgt p)⁻¹ • horiz p) := rfl
        _ = _ := by rw [inv_mul_cancel₀ hr.ne']
      rwa [hpair] at he

theorem polarSlice_volume (K : Body n) (hk : 0 ∈ interior (K:Set (Rn n))) :
    volume (K.polarSlice hk : Set (Rn n)) = volume (polarAt (K : Set (Rn n)) 0) := by
  have he : (K.polarSlice hk : Set (Rn n)) = (fun x => -x) ⁻¹' polarAt (K : Set (Rn n)) 0 := by
    ext; exact dual_head _
  rw [he]; simp

end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Reduction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Cone-volume identities. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace
namespace GeneralMahler
namespace Body
variable {n : ℕ}

theorem vol_pos (K : Body n) : 0 < (volume (K : Set (Rn n))).toReal := by
  refine ENNReal.toReal_pos ?_ K.isCompact.measure_lt_top.ne
  exact ne_of_gt (lt_of_lt_of_le (isOpen_interior.measure_pos volume K.has_interior)
    (measure_mono interior_subset))

/-- Slice integral of a cone at a vertical dual vector. -/
theorem chi_axis (K : Body n) (r : ℝ) (hr : 0 < r) :
    chi K.cone (pair r 0) =
      (r⁻¹ ^ (n+1)) * n.factorial * (volume (K : Set (Rn n))).toReal := by
  classical
  let C : Set (LiftSpace n) := K.cone
  let v := (volume (K : Set (Rn n))).toReal
  let f := C.indicator fun p => Real.exp (-⟪pair r 0,p⟫)
  have hi : Integrable f :=
    (integrable_indicator_iff K.cone.isClosed.measurableSet).mpr
      (chi_integrable (axis_dual_interior K r hr))
  let e := MeasurableEquiv.toLp 2 (ℝ × Rn n)
  have he : MeasurePreserving e :=
    WithLp.volume_preserving_toLp ℝ (Rn n)
  have H : chi K.cone (pair r 0) = ∫ t : ℝ, ∫ y : Rn n, f (pair t y) := by
    unfold chi
    rw [← integral_indicator K.cone.isClosed.measurableSet]
    change (∫ x, f x) = _
    rw [← he.integral_comp']
    exact integral_prod _ ((integrable_map_equiv e f).mp (by change Integrable f (Measure.map e volume); rw [he.map_eq]; exact hi))
  let g : ℝ → ℝ := fun t => t ^ n * exp (-(r*t)) * v
  have heq : (fun t : ℝ => ∫ y : Rn n, f (pair t y)) =ᵐ[volume] (Ioi 0).indicator g := by
    filter_upwards [show ∀ᵐ t : ℝ, t ≠ 0 from by
      rw [ae_iff]; simp] with t ht
    rcases lt_or_gt_of_ne ht with h|h
    · have hh (y : Rn n) : f (pair t y) = 0 := indicator_of_notMem (by
        change pair t y ∉ K.cone
        rw [pair_mem_cone]; exact fun hx => h.not_ge hx.1) _
      simp [hh,h.not_gt]
    have ha : ∀ y : Rn n, pair t y ∈ C ↔ y ∈ t • (K : Set (Rn n)) := by
      intro y
      change pair t y ∈ K.cone ↔ _
      rw [pair_mem_cone, Set.mem_smul_set]
      simp only [h.le, true_and, SetLike.mem_coe, eq_comm]
    have he : (fun y : Rn n => f (pair t y)) =
        (t • (K:Set (Rn n))).indicator (fun y => exp (-(r*t))) := by
      ext y
      by_cases hh : y ∈ t • (K:Set (Rn n))
      · rw [indicator_of_mem hh]
        change C.indicator _ _ = _
        rw [indicator_of_mem ((ha y).mpr hh), pair_inner, inner_zero_left, add_zero, mul_comm]
      · exact (indicator_of_notMem (mt (ha y).mp hh) _).trans ((indicator_of_notMem hh _).symm)
    change (∫ y, f (pair t y)) = _
    rw [indicator_of_mem (mem_Ioi.mpr h)]
    rw [he, integral_indicator (K.isCompact.smul _).isClosed.measurableSet, setIntegral_const,
      measureReal_def, addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    change |t ^ Module.finrank ℝ (Rn n)| * v * exp _ = g t
    rw [abs_of_pos (by positivity)]
    have heR : Module.finrank ℝ (Rn n) = n := by simp [Rn]
    rw [heR]; dsimp only [g]; ring
  have hR : (n : ℝ) + 1 > 0 := by positivity
  have J := Real.integral_rpow_mul_exp_neg_mul_Ioi hR hr
  have HH : r⁻¹ ^ ((n:ℝ)+1) = r⁻¹^(n+1) := by
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [H, integral_congr_ae heq, integral_indicator measurableSet_Ioi]
  change (∫ t : ℝ in Ioi 0, t ^ n * exp (-(r*t)) * v) = _
  rw [integral_mul_const]
  simp only [add_sub_cancel_right, Real.rpow_natCast, one_div,
    Real.Gamma_nat_eq_factorial, HH] at J
  rw [J]

/-- Shear of cone coordinates for translations. -/
def shear (z : Rn n) : (LiftSpace n) ≃ₗ[ℝ] LiftSpace n where
  toFun p := pair (hgt p) (horiz p + hgt p • z)
  invFun p := pair (hgt p) (horiz p - hgt p • z)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by
    simp only [hgt_add, horiz_add, add_smul, add_add_add_comm (horiz p) (horiz q)]
    rfl
  map_smul' a p := by
    simp only [hgt_smul, horiz_smul, smul_pair, smul_add, smul_smul, RingHom.id_apply]

theorem shear_off (K : Body n) (z : Rn n) :
    K.cone = pushCone (shear z) (K.off z).cone := by
  ext p
  rw [mem_pushCone]
  change p ∈ K.cone ↔ pair _ _ ∈ (K.off z).cone
  conv_lhs => rw [← hgt_horiz_pair p]
  rw [pair_mem_cone, pair_mem_cone]
  apply and_congr_right; intro ht
  constructor
  · rintro ⟨x,hx,he⟩
    refine ⟨x-z,?_,?_⟩
    · simpa [sub_eq_add_neg, add_left_comm] using hx
    · rw [smul_sub,he]
  · rintro ⟨x,hx,he⟩
    refine ⟨z+x, hx,?_⟩
    rw [smul_add,add_comm]
    exact (sub_eq_iff_eq_add).mp he

theorem cone_volume (K : Body n) (z : Rn n) (hz : z ∈ interior (K:Set (Rn n)))
    (r : ℝ) (hr : 0 < r) :
    chi K.cone (pair 1 0) * chi (posDual K.cone) (pair r (r • z))
    = r⁻¹ ^ (n+1) * (n.factorial:ℝ)^2 * ((volume (K : Set (Rn n))).toReal *
      (volume (polarAt K z)).toReal) := by
  let K' := K.off z
  have hk' := off_interior hz
  have hsc : contra (shear z) (pair 1 0) = pair 1 0 := by
    apply ext_inner_left ℝ
    intro p
    obtain ⟨p,rfl⟩ := (shear z).surjective p
    rw [pair_contra]
    change ⟪p,pair 1 0⟫ = ⟪pair _ _,pair 1 0⟫
    conv_lhs => rw [← hgt_horiz_pair p]
    rw [pair_inner,pair_inner,inner_zero_right,inner_zero_right]
  have hsu : shear z (pair r 0) = pair r (r • z) := by
    change pair r (0 + r • z) = _
    rw [zero_add]
  have hv : volume (K' : Set (Rn n)) = volume (K : Set (Rn n)) :=
    measure_preimage_add _ _ _
  rw [shear_off K z, ← hsu, ← hsc, chi_transform, ← cone_polarSlice (K.off z) hk',
    chi_axis _ 1 zero_lt_one, chi_axis _ _ hr, polarSlice_volume,
    polar_off K z]
  change _ * _ * (volume (K': Set (Rn n))).toReal * _ = _
  rw [hv]; simp only [inv_one,one_pow]; ring

end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Santalo
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.mat_meas
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.GeneralMahler.HMode.HB_eq _root_.OAI.GeneralMahler.ProjField.coord_apply _root_.OAI.GeneralMahler.equivPD_spec _root_.OAI.GeneralMahler.opCLE_apply _root_.OAI.GeneralMahler.opCLE_symm_apply _root_.OAI.GeneralMahler.opPair_apply _root_.OAI.GeneralMahler.projJac_op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
## Santaló center

Rather than the spherical integral, we use equivalently
the cone Laplace integral and its divergence at the dual boundary. This way
of proving the center claims includes dimension 1 without a separate case.
-/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped RealInnerProductSpace ENNReal
namespace GeneralMahler
variable {n : ℕ}
namespace Body

def polarVol (K : Body n) (z : Rn n) : ℝ := (volume (polarAt K z)).toReal

lemma chi_pair_one {K : Body n} {x : Rn n} (hx : x ∈ interior (K:Set (Rn n))) :
    chi (posDual K.cone) (pair 1 x) = (n.factorial:ℝ)*polarVol K x := by
  have H := cone_volume K _ hx 1 zero_lt_one
  rw [chi_axis _ 1 zero_lt_one] at H
  let v := (volume (K:Set (Rn n))).toReal
  simp only [one_pow, one_smul, inv_one, one_mul] at H
  apply mul_left_cancel₀ (show (n.factorial:ℝ)*v ≠ 0 from mul_ne_zero (by positivity) K.vol_pos.ne')

  change (n.factorial:ℝ)*v*_ = _* (v*polarVol K x) at H
  rw [H]; ring

lemma mem_int' (K : Body n) (x : Rn n) :
    pair 1 x ∈ interior ((posDual (posDual K.cone)): Set (LiftSpace n)) ↔
      x ∈ interior (K:Set (Rn n)) := by
  have h : posDual (posDual K.cone) = K.cone := ProperCone.innerDual_innerDual _
  simpa [h] using ((K.pair_mem_interior_cone_iff 1 zero_lt_one x))


lemma polarVol_strict (K : Body n) :
    StrictConvexOn ℝ (interior (K:Set (Rn n))) K.polarVol := by
  refine ⟨K.convex.interior,?_⟩
  intro x hx y hy hn a b ha hb hab
  have hr : pair 1 x ≠ pair 1 y := by
    intro he
    exact hn (congrArg horiz he)
  have H := (chi_strictConvex (C := posDual K.cone)
    ⟨_, axis_dual_interior K 1 zero_lt_one⟩).2 ((K.mem_int' _).mpr hx)
      ((K.mem_int' _).mpr hy) hr ha hb hab
  have he : a • pair 1 x + b • pair 1 y = pair 1 (a • x + b • y) := calc
    _ = pair (a*1+b*1) (a • x + b • y) := rfl
    _ = _ := by rw [mul_one,mul_one,hab]
  rw [he, chi_pair_one hx, chi_pair_one hy,
    chi_pair_one (K.convex.interior hx hy ha.le hb.le hab)] at H
  simp only [smul_eq_mul] at *
  apply lt_of_mul_lt_mul_left (a := (n.factorial:ℝ))
  · convert H using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · positivity

/-- Existence and uniqueness of the polar-volume minimizer. -/
theorem santalo_exists (K : Body n) :
    ∃! x, x ∈ interior (K : Set (Rn n)) ∧ IsMinOn K.polarVol (interior (K:Set (Rn n))) x := by
  let D := posDual K.cone
  let f := fun x : Rn n => chiExt D (pair 1 x)
  have hsc : LowerSemicontinuous f := by
    intro x b hb
    have hc : Continuous (fun z : Rn n => pair 1 z) := by fun_prop
    exact (hc.tendsto x).eventually (chiExt_lsc D _ _ hb)
  have hpos' : (interior (D : Set (LiftSpace n))).Nonempty :=
    ⟨_, axis_dual_interior K 1 zero_lt_one⟩
  obtain ⟨x₀,h₀⟩ := K.has_interior
  have hpos : (interior (posDual D : Set (LiftSpace n))).Nonempty :=
    ⟨_, (K.mem_int' _).mpr h₀⟩
  obtain ⟨x,hx,he⟩ := LowerSemicontinuousOn.exists_isMinOn K.nonempty K.isCompact
    (hsc.lowerSemicontinuousOn _)
  have hh (y : Rn n) (hy : y ∈ interior (K : Set (Rn n))) :
      f y = ENNReal.ofReal ((n.factorial:ℝ)*polarVol K y) := by
    rw [← chi_pair_one hy]
    exact chiExt_eq ((K.mem_int' _).mpr hy)
  have hx' : x ∈ interior (K : Set (Rn n)) := by
    by_contra hn
    have htop : f x = ∞ := chiExt_top hpos' hpos (mt (K.mem_int' _).mp hn)
    have H : f x ≤ f x₀ := he (interior_subset h₀)
    rw [hh x₀ h₀, htop] at H
    exact ENNReal.ofReal_ne_top (top_le_iff.mp H)
  have he' : IsMinOn K.polarVol (interior (K:Set (Rn n))) x := by
    intro y hy
    have H : f x ≤ f y := he (interior_subset hy)
    rw [hh x hx', hh y hy] at H
    have hnon : 0 ≤ (n.factorial:ℝ)*polarVol K y :=
      mul_nonneg (by positivity) ENNReal.toReal_nonneg
    exact le_of_mul_le_mul_left ((ENNReal.ofReal_le_ofReal_iff hnon).mp H) (by positivity)
  exact ⟨x, ⟨hx',he'⟩, fun y hy =>
    (K.polarVol_strict).eq_of_isMinOn hy.2 he' hy.1 hx'⟩

def santalo (K : Body n) : Rn n := (santalo_exists K).exists.choose

def productAt (K : Body n) (z : Rn n) := (volume (K : Set (Rn n))).toReal * K.polarVol z
def P (K : Body n) := K.productAt K.santalo

end Body
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_SimplexCone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! §§01,06: Full-dimensional simplicial cones and simplex sections. -/
noncomputable section
open Set Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {n : ℕ}

/-- Exact affine simplex family. -/
def IsSimplex (K : Set (Rn n)) : Prop :=
  ∃ v : Fin (n+1) → Rn n, AffineIndependent ℝ v ∧ K = convexHull ℝ (range v)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Laplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Geometric Mahler bounds from cone Laplace integrals and profile inequalities. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile Segment
structure Input091 : Prop where
  ly : LayerOK
  ud : UpdatesOK Cp Kp
  sg : SegmentOK

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Data
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Jet Profile Cert Cert.IV

def dn8:Int:=den/100000000
def GP (a:Int):IV:=box (a*dn8) (a*dn8)
end GeneralMahler.SCal.Grid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Bound2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval on t; second derivative majorants. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment

def ddf (f:ℝ→ℝ):=deriv (deriv f)
end GeneralMahler.SCal.Mid

end

end OAI
end


