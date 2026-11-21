-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F001
-- name    : LevyStochCalc_Poisson_CompensatedProductMoments_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:01:27.900628+00:00
-- url     : https://prove2.me/theorems/08630bbe-eeb2-4061-84c3-2b01a6026051
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProductMoments
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProductMoments. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F000
import Definitions.Def_SourceProof_39bcf7b6426eb7b206aa98c5
import Definitions.Def_SourceProof_a7627240d6bb04f5e392fa17

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of the compensated product of two bounded mark profiles

For bounded square-integrable mark profiles `f, g : E → ℝ` and the compensated integral `J` over
the step `(a, b]` against a Poisson random measure with intensity `ν`, the compensated product
`Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν` is square integrable and centred, it is
orthogonal in `L²(P)` to `J(h)` for every square-integrable profile `h`, and, with
`⟨u, v⟩ = ∫ u v dν`,

  `E[Q(f, g) Q(f', g')] = (b − a)² (⟨f, f'⟩ ⟨g, g'⟩ + ⟨f, g'⟩ ⟨g, f'⟩)`.

The profiles `f, g` are arbitrary bounded square-integrable functions; their supports may
overlap, and no independence of their compensated integrals enters.

Each of `f, g` is approximated in `L²(ν)` by simple profiles obeying the same bound, and at simple
profiles the identities hold by `Poisson/CompensatedProduct.lean`. The Gram at simple profiles
writes the `L²(P)` distance of two compensated products through `L²(ν)` pairings, so the
compensated products of the approximants form a Cauchy sequence in `L²(P)`. The compensated
integrals of the approximants and of their products converge in `L²(P)` by the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}` at square-integrable profiles; along a
subsequence all of them converge almost surely, which identifies the `L²(P)` limit with
`Q(f, g)`. The identities then pass to the limit by continuity of the `L²` pairing, so no third or
fourth moment of the compensated integral of a general profile is needed.

## Main statements

* `LevyStochCalc.Poisson.integral_compensatedProfile_sub_sq`,
  `LevyStochCalc.Poisson.eLpNorm_compensatedProfile_sub` — the isometry at square-integrable
  profiles.
* `LevyStochCalc.Poisson.memLp_compensatedProduct` — square integrability.
* `LevyStochCalc.Poisson.integral_compensatedProduct` — the mean.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul` — the Gram.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul_compensatedProfile` — orthogonality to
  the first chaos.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

/-! ### `L²` facts -/

/-- A square-integrable function times a bounded measurable function is square integrable. -/
private theorem memLp_mul_of_bound {α : Type*} [MeasurableSpace α] {m : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 m) (hg : AEStronglyMeasurable g m) {Cg : ℝ}
    (hbg : ∀ x, |g x| ≤ Cg) : MemLp (fun x => f x * g x) 2 m :=
  hf.of_le_mul (hf.1.mul hg) (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm Cg]
    exact mul_le_mul_of_nonneg_left (hbg x) (abs_nonneg _))
/-- Products of `L²`-convergent sequences, the second one and the first limit bounded, converge
in `L²`. -/
private theorem tendsto_eLpNorm_mul_sub {α : Type*} [MeasurableSpace α] {m : Measure α}
    {u v : ℕ → α → ℝ} {f g : α → ℝ} (hu : ∀ n, AEStronglyMeasurable (u n) m)
    (hv : ∀ n, AEStronglyMeasurable (v n) m) (hf : AEStronglyMeasurable f m)
    (hg : AEStronglyMeasurable g m) {Cf Cg : ℝ} (hvb : ∀ n x, |v n x| ≤ Cg)
    (hfb : ∀ x, |f x| ≤ Cf)
    (huc : Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2 m) atTop (𝓝 0))
    (hvc : Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => u n x * v n x - f x * g x) 2 m) atTop (𝓝 0) := by
  have hbound : ∀ n, eLpNorm (fun x => u n x * v n x - f x * g x) 2 m
      ≤ ENNReal.ofReal Cg * eLpNorm (fun x => u n x - f x) 2 m
        + ENNReal.ofReal Cf * eLpNorm (fun x => v n x - g x) 2 m := by
    intro n
    have hsplit : (fun x => u n x * v n x - f x * g x)
        = (fun x => (u n x - f x) * v n x) + fun x => f x * (v n x - g x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [hsplit]
    have hm1 : AEStronglyMeasurable (fun x => (u n x - f x) * v n x) m :=
      ((hu n).sub hf).mul (hv n)
    have hm2 : AEStronglyMeasurable (fun x => f x * (v n x - g x)) m := hf.mul ((hv n).sub hg)
    refine (eLpNorm_add_le hm1 hm2 one_le_two).trans (add_le_add ?_ ?_)
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm Cg]
      exact mul_le_mul_of_nonneg_left (hvb n x) (abs_nonneg _)
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hfb x) (abs_nonneg _)
  have h1 := ENNReal.Tendsto.const_mul huc (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal Cg)
  have h2 := ENNReal.Tendsto.const_mul hvc (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal Cf)
  have hlim := h1.add h2
  rw [mul_zero, mul_zero, add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => by simp)
    hbound
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Along a strictly increasing subsequence, convergence in `L²(P)` becomes almost everywhere
convergence. -/
theorem exists_strictMono_ae_tendsto_of_tendsto_eLpNorm {X : ℕ → Ω → ℝ} {X' : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) P) (hX' : AEStronglyMeasurable X' P)
    (hc : Tendsto (fun n => eLpNorm (fun ω => X n ω - X' ω) 2 P) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X (φ n) ω) atTop (𝓝 (X' ω)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hX hX' hc).exists_seq_tendsto_ae
/-- **Identification of an `L²` limit.** If `A n → A'`, `B n → B'` and `C n → C'` in `L²(P)`,
`c n → c'`, and `A n B n − C n − c n → L` in `L²(P)`, then `L = A' B' − C' − c'` almost
everywhere. -/
theorem ae_eq_of_tendsto_eLpNorm_mul_sub {A B C : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    {A' B' C' L : Ω → ℝ} {c' : ℝ} (hA : ∀ n, AEStronglyMeasurable (A n) P)
    (hB : ∀ n, AEStronglyMeasurable (B n) P) (hC : ∀ n, AEStronglyMeasurable (C n) P)
    (hA' : AEStronglyMeasurable A' P) (hB' : AEStronglyMeasurable B' P)
    (hC' : AEStronglyMeasurable C' P) (hL : AEStronglyMeasurable L P)
    (hAc : Tendsto (fun n => eLpNorm (fun ω => A n ω - A' ω) 2 P) atTop (𝓝 0))
    (hBc : Tendsto (fun n => eLpNorm (fun ω => B n ω - B' ω) 2 P) atTop (𝓝 0))
    (hCc : Tendsto (fun n => eLpNorm (fun ω => C n ω - C' ω) 2 P) atTop (𝓝 0))
    (hcc : Tendsto c atTop (𝓝 c'))
    (hLc : Tendsto (fun n => eLpNorm (fun ω => (A n ω * B n ω - C n ω - c n) - L ω) 2 P)
      atTop (𝓝 0)) :
    L =ᵐ[P] fun ω => A' ω * B' ω - C' ω - c' := by
  obtain ⟨φ₁, hφ₁, h₁⟩ := exists_strictMono_ae_tendsto_of_tendsto_eLpNorm hA hA' hAc
  obtain ⟨φ₂, hφ₂, h₂⟩ := exists_strictMono_ae_tendsto_of_tendsto_eLpNorm (fun n => hB (φ₁ n))
    hB' (hBc.comp hφ₁.tendsto_atTop)
  obtain ⟨φ₃, hφ₃, h₃⟩ := exists_strictMono_ae_tendsto_of_tendsto_eLpNorm
    (fun n => hC (φ₁ (φ₂ n))) hC' (hCc.comp (hφ₁.comp hφ₂).tendsto_atTop)
  obtain ⟨φ₄, hφ₄, h₄⟩ := exists_strictMono_ae_tendsto_of_tendsto_eLpNorm
    (X := fun n ω => A (φ₁ (φ₂ (φ₃ n))) ω * B (φ₁ (φ₂ (φ₃ n))) ω - C (φ₁ (φ₂ (φ₃ n))) ω
      - c (φ₁ (φ₂ (φ₃ n))))
    (fun n => (((hA _).mul (hB _)).sub (hC _)).sub aestronglyMeasurable_const) hL
    (hLc.comp ((hφ₁.comp hφ₂).comp hφ₃).tendsto_atTop)
  filter_upwards [h₁, h₂, h₃, h₄] with ω h1 h2 h3 h4
  have e1 := h1.comp ((hφ₂.comp hφ₃).comp hφ₄).tendsto_atTop
  have e2 := h2.comp (hφ₃.comp hφ₄).tendsto_atTop
  have e3 := h3.comp hφ₄.tendsto_atTop
  have e4 := hcc.comp (((hφ₁.comp hφ₂).comp hφ₃).comp hφ₄).tendsto_atTop
  exact tendsto_nhds_unique h4 (((e1.mul e2).sub e3).sub e4)
end LevyStochCalc.Probability

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The isometry -/

/-- **The isometry, in second-moment form.** The second moment of the difference of the
compensated integrals of two square-integrable mark profiles over the step `(a, b]` is the step
length times the squared `L²(ν)` distance of the profiles. -/
theorem integral_compensatedProfile_sub_sq (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, (compensatedProfile N f a b ω - compensatedProfile N g a b ω) ^ 2 ∂P
      = (b - a) * ∫ e, (f e - g e) ^ 2 ∂ν := by
  rw [Probability.integral_sub_sq_of_memLp (memLp_compensatedProfile N f a b)
      (memLp_compensatedProfile N g a b),
    Probability.integral_sub_sq_of_memLp hf hg, _root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 N hf hf ha hab,
    _root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 N hf hg ha hab,
    _root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 N hg hf ha hab,
    _root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 N hg hg ha hab]
  ring
/-- **The isometry.** The `L²(P)` distance of the compensated integrals of two square-integrable
mark profiles over the step `(a, b]` is the square root of the step length times the `L²(ν)`
distance of the profiles. -/
theorem eLpNorm_compensatedProfile_sub (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    eLpNorm (fun ω => compensatedProfile N f a b ω - compensatedProfile N g a b ω) 2 P
      = ENNReal.ofReal (Real.sqrt (b - a)) * eLpNorm (fun e => f e - g e) 2 ν := by
  have hP : MemLp (fun ω => compensatedProfile N f a b ω - compensatedProfile N g a b ω) 2 P :=
    (memLp_compensatedProfile N f a b).sub (memLp_compensatedProfile N g a b)
  have hν : MemLp (fun e => f e - g e) 2 ν := hf.sub hg
  rw [Probability.eLpNorm_two_eq_ofReal_sqrt_integral_sq hP,
    Probability.eLpNorm_two_eq_ofReal_sqrt_integral_sq hν,
    integral_compensatedProfile_sub_sq N hf hg ha hab,
    Real.sqrt_mul (by linarith), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
/-- The compensated integrals over the step `(a, b]` of square-integrable mark profiles
converging in `L²(ν)` converge in `L²(P)`. -/
theorem tendsto_compensatedProfile_of_tendsto (N : PoissonRandomMeasure P ν)
    {u : ℕ → E → ℝ} {f : E → ℝ} (hu : ∀ n, MemLp (u n) 2 ν) (hf : MemLp f 2 ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : Tendsto (fun n => eLpNorm (fun e => u n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => compensatedProfile N (u n) a b ω
      - compensatedProfile N f a b ω) 2 P) atTop (𝓝 0) := by
  simp_rw [eLpNorm_compensatedProfile_sub N (hu _) hf ha hab]
  have h := ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top)
    (a := ENNReal.ofReal (Real.sqrt (b - a)))
  rwa [mul_zero] at h
/-! ### Passage to the limit -/

/-- **`L²` convergence of the compensated products of simple approximants.** For bounded
square-integrable mark profiles `f, g` approximated in `L²(ν)` by simple profiles, those of `g`
obeying its bound, the compensated product of `f` and `g` is square integrable and is the `L²(P)`
limit of the compensated products of the approximants. -/
private theorem memLp_tendsto_compensatedProduct (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {Cf Cg : ℝ} (hbf : ∀ e, |f e| ≤ Cf)
    (hbg : ∀ e, |g e| ≤ Cg) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {F G : ℕ → SimpleProfile E ν} (hGb : ∀ n e, |(G n).toFun e| ≤ Cg)
    (hF : Tendsto (fun n => eLpNorm (fun e => (F n).toFun e - f e) 2 ν) atTop (𝓝 0))
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - g e) 2 ν) atTop (𝓝 0)) :
    MemLp (compensatedProduct N f g a b) 2 P ∧
      Tendsto (fun n => eLpNorm (fun ω => compensatedProduct N (F n).toFun (G n).toFun a b ω
        - compensatedProduct N f g a b ω) 2 P) atTop (𝓝 0) := by
  set Q : ℕ → Ω → ℝ := fun n => compensatedProduct N (F n).toFun (G n).toFun a b with hQdef
  have hQ : ∀ n, MemLp (Q n) 2 P :=
    fun n => SimpleProfile.memLp_compensatedProduct N (F n) (G n) ha hab
  have hFm : ∀ n, MemLp (F n).toFun 2 ν := fun n => (F n).memLp_toFun
  have hGm : ∀ n, MemLp (G n).toFun 2 ν := fun n => (G n).memLp_toFun
  -- the Gram of the approximants along the two indices
  have hfst : Tendsto (fun nm : ℕ × ℕ => nm.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun nm : ℕ × ℕ => nm.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hpair : ∀ {X Y : ℕ → E → ℝ} {x y : E → ℝ}, (∀ n, MemLp (X n) 2 ν) →
      (∀ n, MemLp (Y n) 2 ν) → MemLp x 2 ν → MemLp y 2 ν →
      Tendsto (fun n => eLpNorm (fun e => X n e - x e) 2 ν) atTop (𝓝 0) →
      Tendsto (fun n => eLpNorm (fun e => Y n e - y e) 2 ν) atTop (𝓝 0) →
      ∀ {s t : ℕ × ℕ → ℕ}, Tendsto s atTop atTop → Tendsto t atTop atTop →
      Tendsto (fun nm => ∫ e, X (s nm) e * Y (t nm) e ∂ν) atTop (𝓝 (∫ e, x e * y e ∂ν)) :=
    fun hX hY hx hy hXc hYc _ _ hs ht =>
      _root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17 (fun _ => hX _) (fun _ => hY _) hx
        hy (hXc.comp hs) (hYc.comp ht)
  have hΓ : ∀ {s t : ℕ × ℕ → ℕ}, Tendsto s atTop atTop → Tendsto t atTop atTop →
      Tendsto (fun nm => ∫ ω, Q (s nm) ω * Q (t nm) ω ∂P) atTop
        (𝓝 ((b - a) ^ 2 * ((∫ e, f e * f e ∂ν) * (∫ e, g e * g e ∂ν)
          + (∫ e, f e * g e ∂ν) * (∫ e, g e * f e ∂ν)))) := by
    intro s t hs ht
    simp only [hQdef, SimpleProfile.integral_compensatedProduct_mul N _ _ _ _ ha hab]
    exact (((hpair hFm hFm hf hf hF hF hs ht).mul (hpair hGm hGm hg hg hG hG hs ht)).add
      ((hpair hFm hGm hf hg hF hG hs ht).mul (hpair hGm hFm hg hf hG hF hs ht))).const_mul _
  have hsq : Tendsto (fun nm : ℕ × ℕ => ∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simp_rw [Probability.integral_sub_sq_of_memLp (hQ _) (hQ _)]
    simpa using (((hΓ hfst hfst).sub (hΓ hfst hsnd)).sub (hΓ hsnd hfst)).add (hΓ hsnd hsnd)
  -- the approximants form a Cauchy sequence in `L²(P)`
  set q : ℕ → Lp ℝ 2 P := fun n => (hQ n).toLp (Q n) with hqdef
  have hcs : CauchySeq q := by
    rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    have heq : ∀ nm : ℕ × ℕ, eLpNorm (⇑(q nm.1) - ⇑(q nm.2)) 2 P
        = ENNReal.ofReal (Real.sqrt (∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P)) := by
      intro nm
      have hsub : MemLp (fun ω => Q nm.1 ω - Q nm.2 ω) 2 P := (hQ nm.1).sub (hQ nm.2)
      rw [← Probability.eLpNorm_two_eq_ofReal_sqrt_integral_sq hsub]
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hQ nm.1).coeFn_toLp, (hQ nm.2).coeFn_toLp] with ω h1 h2
      simp [hqdef, h1, h2]
    simp_rw [heq]
    have h1 : Tendsto (fun nm : ℕ × ℕ => Real.sqrt (∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P)) atTop
        (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h1
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hLc : Tendsto (fun n => eLpNorm (fun ω => Q n ω - L ω) 2 P) atTop (𝓝 0) := by
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' q L).1 hL).congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hQ n).coeFn_toLp] with ω h
    simp [hqdef, h]
  -- the limit is the compensated product of the limit profiles
  have hFG : ∀ n, MemLp (fun e => (F n).toFun e * (G n).toFun e) 2 ν :=
    fun n => Probability.memLp_mul_of_bound (hFm n) (hGm n).1 (hGb n)
  have hfg : MemLp (fun e => f e * g e) 2 ν := Probability.memLp_mul_of_bound hf hg.1 hbg
  have hA := tendsto_compensatedProfile_of_tendsto N hFm hf ha hab hF
  have hB := tendsto_compensatedProfile_of_tendsto N hGm hg ha hab hG
  have hC := tendsto_compensatedProfile_of_tendsto N hFG hfg ha hab
    (Probability.tendsto_eLpNorm_mul_sub (fun n => (hFm n).1) (fun n => (hGm n).1) hf.1 hg.1 hGb
      hbf hF hG)
  have hc : Tendsto (fun n => (b - a) * ∫ e, (F n).toFun e * (G n).toFun e ∂ν) atTop
      (𝓝 ((b - a) * ∫ e, f e * g e ∂ν)) :=
    (_root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17 hFm hGm hf hg hF hG).const_mul _
  have hae : (L : Ω → ℝ) =ᵐ[P] compensatedProduct N f g a b :=
    Probability.ae_eq_of_tendsto_eLpNorm_mul_sub (fun n => (memLp_compensatedProfile N _ a b).1)
      (fun n => (memLp_compensatedProfile N _ a b).1)
      (fun n => (memLp_compensatedProfile N _ a b).1)
      (memLp_compensatedProfile N f a b).1 (memLp_compensatedProfile N g a b).1
      (memLp_compensatedProfile N _ a b).1 (Lp.memLp L).1 hA hB hC hc hLc
  refine ⟨(Lp.memLp L).ae_eq hae, hLc.congr fun n => eLpNorm_congr_ae ?_⟩
  filter_upwards [hae] with ω h
  rw [h]
/-! ### The moments -/

/-- **Square integrability.** The compensated product of two bounded square-integrable mark
profiles over the step `(a, b]` is square integrable. -/
theorem memLp_compensatedProduct (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {Cf Cg : ℝ} (hbf : ∀ e, |f e| ≤ Cf)
    (hbg : ∀ e, |g e| ≤ Cg) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (compensatedProduct N f g a b) 2 P := by
  obtain ⟨F, hF⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  obtain ⟨G, hGb, hG⟩ := _root_.Prove2MeSourceProof.h_39bcf7b6426eb7b206aa98c5 hg hbg
  exact (memLp_tendsto_compensatedProduct N hf hg hbf hbg ha hab hGb hF hG).1
/-- **The mean.** The compensated product of two bounded square-integrable mark profiles over
the step `(a, b]` is centred. -/
theorem integral_compensatedProduct (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {Cf Cg : ℝ} (hbf : ∀ e, |f e| ≤ Cf)
    (hbg : ∀ e, |g e| ≤ Cg) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N f g a b ω ∂P = 0 := by
  obtain ⟨F, hF⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  obtain ⟨G, hGb, hG⟩ := _root_.Prove2MeSourceProof.h_39bcf7b6426eb7b206aa98c5 hg hbg
  obtain ⟨hQ, hc⟩ := memLp_tendsto_compensatedProduct N hf hg hbf hbg ha hab hGb hF hG
  have h := _root_.Prove2MeSourceProof.h_a7627240d6bb04f5e392fa17 (Y := fun _ _ => (1 : ℝ))
    (fun n => SimpleProfile.memLp_compensatedProduct N (F n) (G n) ha hab)
    (fun _ => memLp_const 1) hQ (memLp_const 1) hc (by simp)
  simp only [mul_one] at h
  exact tendsto_nhds_unique
    (h.congr fun n => SimpleProfile.integral_compensatedProduct N (F n) (G n) ha hab)
    tendsto_const_nhds
end LevyStochCalc.Poisson


