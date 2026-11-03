-- Prove2me | Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
-- name    : LeanLevy_RandomMeasure_PoissonCompensated
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T22:24:07.313914+00:00
-- url     : https://prove2.me/theorems/5b2ad309-8bc6-428b-82b8-6dc5ddfd2c18
-- title:
--   LeanLevy source module: RandomMeasure.PoissonCompensated
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.RandomMeasure.PoissonCompensated`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.ConjExponents
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily

/-!
# The compensated Poisson integral and its isometry

For a σ-finite intensity `m` on `E`, the Poisson point family `(K, X)` of `PoissonPointFamily`
attaches to each partition piece `k` the *piece sum* `pieceSum K X f k`, a random Poisson sum of a
test function `f`.  This file introduces the **compensated** piece sum
`compensatedPieceSum K X f m k = pieceSum K X f k - ∫_{piece k} f dm` and its countable aggregate
`compensatedPoissonSum K X f m = ∑' k, compensatedPieceSum K X f m k`, the pathwise value of the
compensated Poisson integral `∫ f d(N - m)`.

The main result is the **L² isometry** (Campbell's second formula)
`∫ (compensatedPoissonSum K X f m)² dμ = ∫ f² dm` for `f ∈ L¹(m) ∩ L²(m)`, together with the
supporting facts that the compensated integral is centered, is itself an `L²(μ)` random variable,
and is additive / homogeneous / subtractive in `f`.  This isometry is then used to extend the
compensated integral, by density of the `L¹(m) ∩ L²(m)` simple functions in `L²(m)`, to an
isometry `ProbabilityTheory.compensatedPoissonIntegral : L²(m) → L²(μ)` on all of `L²(m)`.

## Main definitions

* `ProbabilityTheory.compensatedPieceSum` — the centered piece sum on a single piece.
* `ProbabilityTheory.compensatedPoissonSum` — the aggregate compensated Poisson integral.
* `ProbabilityTheory.compensatedPoissonIntegral` — the **L²(m) → L²(μ) extension** of the
  compensated Poisson integral, obtained as the `L²(μ)`-limit over a simple-function
  approximating sequence.

## Main results

* `ProbabilityTheory.integral_compensatedPoissonSum` — the compensated integral has mean zero.
* `ProbabilityTheory.integral_sq_compensatedPoissonSum` — the **isometry** `E[(∫ f dÑ)²] = ∫ f² dm`.
* `ProbabilityTheory.memLp_two_compensatedPoissonSum` — the compensated integral lies in `L²(μ)`.
* `ProbabilityTheory.compensatedPoissonSum_add`, `ProbabilityTheory.compensatedPoissonSum_const_mul`,
  `ProbabilityTheory.compensatedPoissonSum_sub`
  — linearity of the compensated integral in the test function.
* `ProbabilityTheory.eLpNorm_compensatedPoissonIntegral`,
  `ProbabilityTheory.norm_compensatedPoissonIntegral` — the **isometry**
  `‖compensatedPoissonIntegral hd f‖ = ‖f‖` of the `L²(m) → L²(μ)` extension.
* `ProbabilityTheory.compensatedPoissonIntegral_eq_sum` — the extension agrees a.e. with the
  explicit pathwise `compensatedPoissonSum` on `L¹(m) ∩ L²(m)`.
* `ProbabilityTheory.integral_compensatedPoissonIntegral` — the `L²(m) → L²(μ)` extension has
  mean zero on all of `L²(m)`.
* `ProbabilityTheory.compensatedPoissonIntegral_add`,
  `ProbabilityTheory.compensatedPoissonIntegral_neg`,
  `ProbabilityTheory.compensatedPoissonIntegral_sub` — linearity of the `L²(m) → L²(μ)` extension.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Compensated

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {f g : E → ℝ} {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ}

/-- The **compensated piece sum**: the piece sum with its mean subtracted, so it is centered. -/
noncomputable def compensatedPieceSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (f : E → ℝ)
    (m : Measure E) [SigmaFinite m] (k : ℕ) (ω : Ω) : ℝ :=
  pieceSum K X f k ω - ∫ x in prmPiece m k, f x ∂m

/-- The **compensated Poisson integral**: the sum of the compensated piece sums over all pieces. -/
noncomputable def compensatedPoissonSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (f : E → ℝ)
    (m : Measure E) [SigmaFinite m] (ω : Ω) : ℝ :=
  ∑' k, compensatedPieceSum K X f m k ω

/-! ### Per-piece facts -/

/-- On a probability space the piece sum of an `L¹ ∩ L²` function is integrable. -/
private theorem integrable_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    Integrable (pieceSum K X f k) μ :=
  ((memLp_two_iff_integrable_sq
    (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf).aestronglyMeasurable).mpr
      (integrable_sq_pieceSum hd hf hf1.integrableOn hf2.integrable_sq.integrableOn)).integrable
    one_le_two

/-- The compensated piece sum is measurable. -/
theorem measurable_compensatedPieceSum (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) :
    Measurable (compensatedPieceSum K X f m k) :=
  (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf).sub_const _

/-- The compensated piece sum is integrable. -/
theorem integrable_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    Integrable (compensatedPieceSum K X f m k) μ :=
  (integrable_pieceSum (k := k) hd hf hf1 hf2).sub (integrable_const _)

/-- The compensated piece sum lies in `L²(μ)`. -/
theorem memLp_two_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    MemLp (compensatedPieceSum K X f m k) 2 μ :=
  ((memLp_two_iff_integrable_sq
    (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf).aestronglyMeasurable).mpr
      (integrable_sq_pieceSum hd hf hf1.integrableOn hf2.integrable_sq.integrableOn)).sub
    (memLp_const _)

/-- The compensated piece sum is centered: its mean is zero. -/
theorem integral_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, compensatedPieceSum K X f m k ω ∂μ = 0 := by
  simp only [compensatedPieceSum]
  rw [integral_sub (integrable_pieceSum (k := k) hd hf hf1 hf2) (integrable_const _),
    integral_pieceSum hd hf hf1.integrableOn, integral_const, probReal_univ, one_smul, sub_self]

/-- The second moment of the compensated piece sum equals the `L²`-mass of the piece. -/
theorem integral_sq_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, (compensatedPieceSum K X f m k ω) ^ 2 ∂μ = ∫ x in prmPiece m k, f x ^ 2 ∂m := by
  have hSint := integrable_pieceSum (k := k) hd hf hf1 hf2
  have hS2int := integrable_sq_pieceSum (k := k) hd hf hf1.integrableOn hf2.integrable_sq.integrableOn
  set C := ∫ x in prmPiece m k, f x ∂m with hC
  calc ∫ ω, (compensatedPieceSum K X f m k ω) ^ 2 ∂μ
      = ∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω + C ^ 2) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [compensatedPieceSum]; ring
    _ = (∫ ω, (pieceSum K X f k ω) ^ 2 ∂μ) + (-(2 * C)) * (∫ ω, pieceSum K X f k ω ∂μ) + C ^ 2 := by
        have e1 : ∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω + C ^ 2) ∂μ
            = (∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω) ∂μ)
              + ∫ _ω, C ^ 2 ∂μ :=
          integral_add (hS2int.add (hSint.const_mul _)) (integrable_const _)
        have e2 : ∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω) ∂μ
            = (∫ ω, (pieceSum K X f k ω) ^ 2 ∂μ) + ∫ ω, (-(2 * C)) * pieceSum K X f k ω ∂μ :=
          integral_add hS2int (hSint.const_mul _)
        rw [e1, e2, integral_const_mul, integral_const, probReal_univ, one_smul]
    _ = ∫ x in prmPiece m k, f x ^ 2 ∂m := by
        rw [integral_sq_pieceSum hd hf hf1.integrableOn hf2.integrable_sq.integrableOn,
          integral_pieceSum hd hf hf1.integrableOn]
        ring

/-- Compensated piece sums of distinct pieces are independent. -/
theorem indepFun_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hg : Measurable g) {j k : ℕ} (hjk : j ≠ k) :
    IndepFun (compensatedPieceSum K X f m j) (compensatedPieceSum K X g m k) μ :=
  (indepFun_pieceSum_pieceSum hd hf hg hjk).comp
    (φ := fun x => x - ∫ x in prmPiece m j, f x ∂m)
    (ψ := fun x => x - ∫ x in prmPiece m k, g x ∂m)
    (measurable_id.sub_const _) (measurable_id.sub_const _)

/-- **Bienaymé's identity** for a finite family of pieces: because the compensated piece sums are
centered and pairwise independent, the second moment of their sum is the sum of the piece
`L²`-masses. -/
theorem integral_sq_finsetSum_compensatedPieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) (s : Finset ℕ) :
    ∫ ω, (∑ k ∈ s, compensatedPieceSum K X f m k ω) ^ 2 ∂μ
      = ∑ k ∈ s, ∫ x in prmPiece m k, f x ^ 2 ∂m := by
  have hcenter : ∀ k, ∫ ω, compensatedPieceSum K X f m k ω ∂μ = 0 :=
    fun k => integral_compensatedPieceSum hd hf hf1 hf2
  have hfun_eq : (∑ k ∈ s, compensatedPieceSum K X f m k)
      = fun ω => ∑ k ∈ s, compensatedPieceSum K X f m k ω := by funext ω; rw [Finset.sum_apply]
  have hAEmeas : AEMeasurable (fun ω => ∑ k ∈ s, compensatedPieceSum K X f m k ω) μ :=
    (Finset.measurable_sum s fun k _ => measurable_compensatedPieceSum hd hf).aemeasurable
  have hSint0 : ∫ ω, (∑ k ∈ s, compensatedPieceSum K X f m k ω) ∂μ = 0 := by
    rw [integral_finsetSum s fun k _ => integrable_compensatedPieceSum hd hf hf1 hf2]
    simp [hcenter]
  calc ∫ ω, (∑ k ∈ s, compensatedPieceSum K X f m k ω) ^ 2 ∂μ
      = variance (fun ω => ∑ k ∈ s, compensatedPieceSum K X f m k ω) μ :=
        (variance_of_integral_eq_zero hAEmeas hSint0).symm
    _ = variance (∑ k ∈ s, compensatedPieceSum K X f m k) μ := by rw [hfun_eq]
    _ = ∑ k ∈ s, variance (compensatedPieceSum K X f m k) μ :=
        IndepFun.variance_sum (fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2)
          (fun i _ j _ hij => indepFun_compensatedPieceSum hd hf hf hij)
    _ = ∑ k ∈ s, ∫ x in prmPiece m k, f x ^ 2 ∂m := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [variance_of_integral_eq_zero (measurable_compensatedPieceSum hd hf).aemeasurable
          (hcenter k)]
        exact integral_sq_compensatedPieceSum hd hf hf1 hf2

/-! ### Analytic helpers -/

omit [Nonempty E] in
/-- The piece integrals of an integrable function over the pieces sum to its total integral. -/
private theorem hasSum_setIntegral_prmPiece {φ : E → ℝ} (hφ : Integrable φ m) :
    HasSum (fun k => ∫ x in prmPiece m k, φ x ∂m) (∫ x, φ x ∂m) := by
  have hunion : IntegrableOn φ (⋃ k, prmPiece m k) m := by
    rw [iUnion_prmPiece]; exact hφ.integrableOn
  have h := hasSum_integral_iUnion (fun k => measurableSet_prmPiece) pairwise_disjoint_prmPiece hunion
  rwa [iUnion_prmPiece, setIntegral_univ] at h

/-- Cauchy–Schwarz for real integrals against a probability measure. -/
private theorem abs_integral_mul_le_sqrt {a b : Ω → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    |∫ ω, a ω * b ω ∂μ| ≤ Real.sqrt (∫ ω, (a ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (b ω) ^ 2 ∂μ) := by
  have ha' : MemLp (fun ω => |a ω|) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; simpa [Real.norm_eq_abs] using ha.norm
  have hb' : MemLp (fun ω => |b ω|) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; simpa [Real.norm_eq_abs] using hb.norm
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun ω => abs_nonneg (a ω)) (Eventually.of_forall fun ω => abs_nonneg (b ω))
    ha' hb'
  have hrw : ∀ h : Ω → ℝ, (∫ ω, |h ω| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      = Real.sqrt (∫ ω, (h ω) ^ 2 ∂μ) := by
    intro h
    rw [← Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only []
    rw [← sq_abs (h ω), ← Real.rpow_natCast |h ω| 2]
    norm_num
  calc |∫ ω, a ω * b ω ∂μ|
      ≤ ∫ ω, |a ω * b ω| ∂μ := abs_integral_le_integral_abs
    _ = ∫ ω, |a ω| * |b ω| ∂μ := by simp_rw [abs_mul]
    _ ≤ (∫ ω, |a ω| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ ω, |b ω| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hCS
    _ = Real.sqrt (∫ ω, (a ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (b ω) ^ 2 ∂μ) := by rw [hrw, hrw]

/-- **Fatou lower-semicontinuity of the second moment.** If `gseq n → G` a.e. and the second
moments of `gseq n` are bounded by `C ≥ 0`, then `G` is square-integrable with second moment at
most `C`. -/
private theorem fatou_sq_bound {gseq : ℕ → Ω → ℝ} {G : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ n, Measurable (gseq n)) (hG : AEStronglyMeasurable G μ)
    (hint : ∀ n, Integrable (fun ω => (gseq n ω) ^ 2) μ)
    (htend : ∀ᵐ ω ∂μ, Tendsto (fun n => gseq n ω) atTop (𝓝 (G ω)))
    (hbnd : ∀ n, ∫ ω, (gseq n ω) ^ 2 ∂μ ≤ C) :
    Integrable (fun ω => (G ω) ^ 2) μ ∧ ∫ ω, (G ω) ^ 2 ∂μ ≤ C := by
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal ((gseq n ω) ^ 2) with hF
  have hFmeas : ∀ n, Measurable (F n) := fun n => ((hg n).pow_const 2).ennreal_ofReal
  have hFint : ∀ n, ∫⁻ ω, F n ω ∂μ = ENNReal.ofReal (∫ ω, (gseq n ω) ^ 2 ∂μ) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall fun ω => by positivity)).symm
  have hliminf : ∀ᵐ ω ∂μ, ENNReal.ofReal ((G ω) ^ 2) = liminf (fun n => F n ω) atTop := by
    filter_upwards [htend] with ω hω
    have : Tendsto (fun n => F n ω) atTop (𝓝 (ENNReal.ofReal ((G ω) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)
    exact this.liminf_eq.symm
  have hfatou : ∫⁻ ω, ENNReal.ofReal ((G ω) ^ 2) ∂μ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop := by
    rw [lintegral_congr_ae hliminf]
    exact lintegral_liminf_le hFmeas
  have hle : liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop ≤ ENNReal.ofReal C := by
    refine (Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans (by rw [liminf_const])
    rw [hFint n]; exact ENNReal.ofReal_le_ofReal (hbnd n)
  have hbnd2 : ∫⁻ ω, ENNReal.ofReal ((G ω) ^ 2) ∂μ ≤ ENNReal.ofReal C := hfatou.trans hle
  have hGsq_aesm : AEStronglyMeasurable (fun ω => (G ω) ^ 2) μ := hG.pow 2
  have henorm : ∀ ω, ‖(G ω) ^ 2‖ₑ = ENNReal.ofReal ((G ω) ^ 2) := fun ω =>
    Real.enorm_of_nonneg (by positivity)
  refine ⟨⟨hGsq_aesm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    simp_rw [henorm]
    exact lt_of_le_of_lt hbnd2 ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => by positivity) hGsq_aesm]
    calc (∫⁻ ω, ENNReal.ofReal ((G ω) ^ 2) ∂μ).toReal
        ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd2
      _ = C := ENNReal.toReal_ofReal hC

/-! ### Absolute convergence and mean zero -/

/-- The mean absolute size of a compensated piece sum is controlled by the piece `L¹`-mass. -/
private theorem integral_norm_compensatedPieceSum_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∫ ω, ‖compensatedPieceSum K X f m k ω‖ ∂μ ≤ 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m := by
  set C := ∫ x in prmPiece m k, f x ∂m with hC
  have hSnInt : Integrable (pieceSum K X (fun x => ‖f x‖) k) μ :=
    integrable_pieceSum (k := k) hd hf.norm hf1.norm hf2.norm
  have hcompInt : Integrable (compensatedPieceSum K X f m k) μ :=
    integrable_compensatedPieceSum (k := k) hd hf hf1 hf2
  have hle : ∀ ω, ‖compensatedPieceSum K X f m k ω‖ ≤ pieceSum K X (fun x => ‖f x‖) k ω + ‖C‖ := by
    intro ω
    have h1 : ‖compensatedPieceSum K X f m k ω‖ ≤ ‖pieceSum K X f k ω‖ + ‖C‖ := by
      simp only [compensatedPieceSum]; exact norm_sub_le _ _
    have h2 : ‖pieceSum K X f k ω‖ ≤ pieceSum K X (fun x => ‖f x‖) k ω := by
      simp only [pieceSum]
      exact norm_sum_le _ _
    linarith
  calc ∫ ω, ‖compensatedPieceSum K X f m k ω‖ ∂μ
      ≤ ∫ ω, (pieceSum K X (fun x => ‖f x‖) k ω + ‖C‖) ∂μ :=
        integral_mono hcompInt.norm (hSnInt.add (integrable_const _)) hle
    _ = (∫ ω, pieceSum K X (fun x => ‖f x‖) k ω ∂μ) + ‖C‖ := by
        rw [integral_add hSnInt (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m := by
        rw [integral_pieceSum hd hf.norm hf1.norm.integrableOn]
        have hCnorm : ‖C‖ ≤ ∫ x in prmPiece m k, ‖f x‖ ∂m := by
          rw [hC]; exact norm_integral_le_integral_norm _
        linarith

/-- The mean absolute sizes of the compensated piece sums are summable (they are controlled by the
`L¹`-mass of `f`), so the compensated Poisson series converges absolutely almost surely. -/
private theorem tsum_lintegral_enorm_compensatedPieceSum_ne_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∑' k, ∫⁻ ω, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ ≠ ⊤ := by
  have hbound : ∀ k, ∫⁻ ω, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ
      ≤ ENNReal.ofReal (2 * ∫ x in prmPiece m k, ‖f x‖ ∂m) := by
    intro k
    rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_compensatedPieceSum hd hf hf1 hf2)]
    exact ENNReal.ofReal_le_ofReal (integral_norm_compensatedPieceSum_le hd hf hf1 hf2)
  have hsum : Summable (fun k => 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m) :=
    ((hasSum_setIntegral_prmPiece hf1.norm).mul_left 2).summable
  exact ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)

/-- The compensated Poisson series converges absolutely almost surely. -/
theorem ae_summable_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∀ᵐ ω ∂μ, Summable (fun k => compensatedPieceSum K X f m k ω) := by
  have hmeas : ∀ k, AEMeasurable (fun ω => ‖compensatedPieceSum K X f m k ω‖ₑ) μ :=
    fun k => (measurable_compensatedPieceSum hd hf).enorm.aemeasurable
  have hfin : ∫⁻ ω, ∑' k, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    exact tsum_lintegral_enorm_compensatedPieceSum_ne_top hd hf hf1 hf2
  have hae := ae_lt_top' (AEMeasurable.tsum hmeas) hfin
  filter_upwards [hae] with ω hω
  have hsc : Summable (fun k => ‖compensatedPieceSum K X f m k ω‖₊) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa only [enorm_eq_nnnorm] using hω.ne
  have hsr : Summable (fun k => ‖compensatedPieceSum K X f m k ω‖) := by
    simpa only [coe_nnnorm] using NNReal.summable_coe.mpr hsc
  exact hsr.of_norm

/-- The compensated Poisson integral is almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_compensatedPoissonSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) : AEStronglyMeasurable (compensatedPoissonSum K X f m) μ := by
  have htend : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω)
      atTop (𝓝 (compensatedPoissonSum K X f m ω)) := by
    filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (Finset.measurable_sum _ fun k _ =>
      measurable_compensatedPieceSum hd hf).aestronglyMeasurable) htend



/-! ### The isometry -/

/-- The compensated Poisson integral is square-integrable, with second moment at most `∫ f² dm`. -/
private theorem memLp_two_and_integral_sq_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    MemLp (compensatedPoissonSum K X f m) 2 μ
      ∧ ∫ ω, (compensatedPoissonSum K X f m ω) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂m := by
  set v : ℕ → ℝ := fun k => ∫ x in prmPiece m k, f x ^ 2 ∂m with hv
  have hv_nonneg : ∀ k, 0 ≤ v k := fun k => integral_nonneg fun x => sq_nonneg (f x)
  have hv_hasSum : HasSum v (∫ x, f x ^ 2 ∂m) := hasSum_setIntegral_prmPiece hf2.integrable_sq
  set Tn : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω with hTn
  have hTnmeas : ∀ n, Measurable (Tn n) :=
    fun n => Finset.measurable_sum _ fun k _ => measurable_compensatedPieceSum hd hf
  have hTnint : ∀ n, Integrable (fun ω => (Tn n ω) ^ 2) μ :=
    fun n => (memLp_finsetSum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2).integrable_sq
  have hTnle : ∀ n, ∫ ω, (Tn n ω) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂m := by
    intro n
    rw [integral_sq_finsetSum_compensatedPieceSum hd hf hf1 hf2 (Finset.range n)]
    exact sum_le_hasSum _ (fun i _ => hv_nonneg i) hv_hasSum
  have htend : ∀ᵐ ω ∂μ, Tendsto (fun n => Tn n ω) atTop (𝓝 (compensatedPoissonSum K X f m ω)) := by
    filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  obtain ⟨hTsq_int, hTsq_le⟩ := fatou_sq_bound (integral_nonneg fun x => sq_nonneg (f x)) hTnmeas
    (aestronglyMeasurable_compensatedPoissonSum hd hf hf1 hf2) hTnint htend hTnle
  exact ⟨(memLp_two_iff_integrable_sq
    (aestronglyMeasurable_compensatedPoissonSum hd hf hf1 hf2)).mpr hTsq_int, hTsq_le⟩

/-- The compensated Poisson integral lies in `L²(μ)`. -/
theorem memLp_two_compensatedPoissonSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    MemLp (compensatedPoissonSum K X f m) 2 μ :=
  (memLp_two_and_integral_sq_le hd hf hf1 hf2).1

/-- **The compensated Poisson integral isometry (Campbell's second formula).** For an `L¹ ∩ L²`
test function, the second moment of the compensated Poisson integral equals the `L²`-mass of the
function against the intensity. -/
theorem integral_sq_compensatedPoissonSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∫ ω, (compensatedPoissonSum K X f m ω) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂m := by
  obtain ⟨hTmemlp, hTsq_le⟩ := memLp_two_and_integral_sq_le hd hf hf1 hf2
  have hTsq_int : Integrable (fun ω => (compensatedPoissonSum K X f m ω) ^ 2) μ :=
    hTmemlp.integrable_sq
  set T := compensatedPoissonSum K X f m with hTdef
  set v : ℕ → ℝ := fun k => ∫ x in prmPiece m k, f x ^ 2 ∂m with hv
  have hv_nonneg : ∀ k, 0 ≤ v k := fun k => integral_nonneg fun x => sq_nonneg (f x)
  have hv_hasSum : HasSum v (∫ x, f x ^ 2 ∂m) := hasSum_setIntegral_prmPiece hf2.integrable_sq
  set Tn : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω with hTn
  have hTnmemlp : ∀ n, MemLp (Tn n) 2 μ :=
    fun n => memLp_finsetSum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2
  have hTnint : ∀ n, Integrable (fun ω => (Tn n ω) ^ 2) μ := fun n => (hTnmemlp n).integrable_sq
  have hTnsq : ∀ n, ∫ ω, (Tn n ω) ^ 2 ∂μ = ∑ k ∈ Finset.range n, v k :=
    fun n => integral_sq_finsetSum_compensatedPieceSum hd hf hf1 hf2 (Finset.range n)
  have hTnle : ∀ n, ∫ ω, (Tn n ω) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂m := by
    intro n; rw [hTnsq]; exact sum_le_hasSum _ (fun i _ => hv_nonneg i) hv_hasSum
  have htend : ∀ᵐ ω ∂μ, Tendsto (fun n => Tn n ω) atTop (𝓝 (T ω)) := by
    filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  -- tail control of the partial sums
  set Sv : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, v k with hSv
  have hSv_tend : Tendsto Sv atTop (𝓝 (∫ x, f x ^ 2 ∂m)) := hv_hasSum.tendsto_sum_nat
  set r : ℕ → ℝ := fun n => (∫ x, f x ^ 2 ∂m) - Sv n with hr
  have hr_tend : Tendsto r atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => ∫ x, f x ^ 2 ∂m) atTop (𝓝 (∫ x, f x ^ 2 ∂m)) :=
      tendsto_const_nhds
    simpa [hr] using hc.sub hSv_tend
  have hr_nonneg : ∀ n, 0 ≤ r n := fun n => by
    rw [hr]; exact sub_nonneg.mpr (sum_le_hasSum _ (fun i _ => hv_nonneg i) hv_hasSum)
  have hdiff_le : ∀ n, ∫ ω, (T ω - Tn n ω) ^ 2 ∂μ ≤ r n := by
    intro n
    set gseq : ℕ → Ω → ℝ :=
      fun N ω => (∑ k ∈ Finset.range (N + n), compensatedPieceSum K X f m k ω)
        - ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω with hgseq
    have hgmeas : ∀ N, Measurable (gseq N) := fun N =>
      (Finset.measurable_sum _ fun k _ => measurable_compensatedPieceSum hd hf).sub
        (Finset.measurable_sum _ fun k _ => measurable_compensatedPieceSum hd hf)
    have hgIco : ∀ N ω,
        gseq N ω = ∑ k ∈ Finset.Ico n (N + n), compensatedPieceSum K X f m k ω := fun N ω =>
      (Finset.sum_Ico_eq_sub _ (Nat.le_add_left n N)).symm
    have hgsq : ∀ N, ∫ ω, (gseq N ω) ^ 2 ∂μ = ∑ k ∈ Finset.Ico n (N + n), v k := by
      intro N
      rw [show (fun ω => (gseq N ω) ^ 2)
        = fun ω => (∑ k ∈ Finset.Ico n (N + n), compensatedPieceSum K X f m k ω) ^ 2 from
          funext fun ω => by rw [hgIco]]
      exact integral_sq_finsetSum_compensatedPieceSum hd hf hf1 hf2 (Finset.Ico n (N + n))
    have hgle : ∀ N, ∫ ω, (gseq N ω) ^ 2 ∂μ ≤ r n := by
      intro N
      rw [hgsq, Finset.sum_Ico_eq_sub _ (Nat.le_add_left n N), hr]
      have hbnd := sum_le_hasSum (Finset.range (N + n)) (fun i _ => hv_nonneg i) hv_hasSum
      simp only [hSv]; linarith
    have hgint : ∀ N, Integrable (fun ω => (gseq N ω) ^ 2) μ := fun N =>
      ((memLp_finsetSum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2).sub
        (memLp_finsetSum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2)).integrable_sq
    have hgtend : ∀ᵐ ω ∂μ, Tendsto (fun N => gseq N ω) atTop (𝓝 (T ω - Tn n ω)) := by
      filter_upwards [htend] with ω hω
      exact (hω.comp (tendsto_add_atTop_nat n)).sub_const _
    exact (fatou_sq_bound (hr_nonneg n) hgmeas (hTmemlp.1.sub (hTnmemlp n).1) hgint hgtend hgle).2
  -- closing: ∫ Tn² converges to both ∫ T² and ∫ f²
  have hclose : Tendsto (fun n => ∫ ω, (Tn n ω) ^ 2 ∂μ) atTop (𝓝 (∫ ω, (T ω) ^ 2 ∂μ)) := by
    have hbound : ∀ n, |(∫ ω, (T ω) ^ 2 ∂μ) - ∫ ω, (Tn n ω) ^ 2 ∂μ|
        ≤ 2 * Real.sqrt (∫ x, f x ^ 2 ∂m) * Real.sqrt (r n) := by
      intro n
      have haMemLp : MemLp (fun ω => T ω - Tn n ω) 2 μ := hTmemlp.sub (hTnmemlp n)
      have hbMemLp : MemLp (fun ω => T ω + Tn n ω) 2 μ := hTmemlp.add (hTnmemlp n)
      have hdiffsq : (∫ ω, (T ω) ^ 2 ∂μ) - ∫ ω, (Tn n ω) ^ 2 ∂μ
          = ∫ ω, (T ω - Tn n ω) * (T ω + Tn n ω) ∂μ := by
        rw [← integral_sub hTsq_int (hTnint n)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_); ring
      have hsum_le : ∫ ω, (T ω + Tn n ω) ^ 2 ∂μ ≤ 4 * ∫ x, f x ^ 2 ∂m := by
        have hpt : ∀ ω, (T ω + Tn n ω) ^ 2 ≤ 2 * (T ω) ^ 2 + 2 * (Tn n ω) ^ 2 :=
          fun ω => by nlinarith [sq_nonneg (T ω - Tn n ω)]
        calc ∫ ω, (T ω + Tn n ω) ^ 2 ∂μ
            ≤ ∫ ω, (2 * (T ω) ^ 2 + 2 * (Tn n ω) ^ 2) ∂μ :=
              integral_mono hbMemLp.integrable_sq
                ((hTsq_int.const_mul 2).add ((hTnint n).const_mul 2)) hpt
          _ = 2 * (∫ ω, (T ω) ^ 2 ∂μ) + 2 * ∫ ω, (Tn n ω) ^ 2 ∂μ := by
              rw [integral_add (hTsq_int.const_mul 2) ((hTnint n).const_mul 2), integral_const_mul,
                integral_const_mul]
          _ ≤ 4 * ∫ x, f x ^ 2 ∂m := by nlinarith [hTsq_le, hTnle n]
      rw [hdiffsq]
      calc |∫ ω, (T ω - Tn n ω) * (T ω + Tn n ω) ∂μ|
          ≤ Real.sqrt (∫ ω, (T ω - Tn n ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (T ω + Tn n ω) ^ 2 ∂μ) :=
            abs_integral_mul_le_sqrt haMemLp hbMemLp
        _ ≤ Real.sqrt (r n) * (2 * Real.sqrt (∫ x, f x ^ 2 ∂m)) := by
            refine mul_le_mul (Real.sqrt_le_sqrt (hdiff_le n)) ?_ (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
            rw [show (2 : ℝ) * Real.sqrt (∫ x, f x ^ 2 ∂m) = Real.sqrt (4 * ∫ x, f x ^ 2 ∂m) by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
                Real.sqrt_sq (by norm_num)]]
            exact Real.sqrt_le_sqrt hsum_le
        _ = 2 * Real.sqrt (∫ x, f x ^ 2 ∂m) * Real.sqrt (r n) := by ring
    have hbtend : Tendsto (fun n => 2 * Real.sqrt (∫ x, f x ^ 2 ∂m) * Real.sqrt (r n)) atTop
        (𝓝 0) := by
      have hsqrt : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
        simpa using hr_tend.sqrt
      simpa using hsqrt.const_mul (2 * Real.sqrt (∫ x, f x ^ 2 ∂m))
    have hzero : Tendsto (fun n => (∫ ω, (T ω) ^ 2 ∂μ) - ∫ ω, (Tn n ω) ^ 2 ∂μ) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hbound n) hbtend
    have hcT : Tendsto (fun _ : ℕ => ∫ ω, (T ω) ^ 2 ∂μ) atTop (𝓝 (∫ ω, (T ω) ^ 2 ∂μ)) :=
      tendsto_const_nhds
    simpa using hcT.sub hzero
  have hclose2 : Tendsto (fun n => ∫ ω, (Tn n ω) ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂m)) := by
    simp_rw [hTnsq]; exact hSv_tend
  exact tendsto_nhds_unique hclose hclose2

/-! ### Linearity -/

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The compensated piece sum is additive in the test function. -/
theorem compensatedPieceSum_add (hf1 : Integrable f (m.restrict (prmPiece m k)))
    (hg1 : Integrable g (m.restrict (prmPiece m k))) (ω : Ω) :
    compensatedPieceSum K X (fun x => f x + g x) m k ω
      = compensatedPieceSum K X f m k ω + compensatedPieceSum K X g m k ω := by
  simp only [compensatedPieceSum, pieceSum]
  rw [Finset.sum_add_distrib, integral_add hf1 hg1]
  ring

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The compensated piece sum is homogeneous in the test function. -/
theorem compensatedPieceSum_const_mul (c : ℝ) (ω : Ω) :
    compensatedPieceSum K X (fun x => c * f x) m k ω = c * compensatedPieceSum K X f m k ω := by
  simp only [compensatedPieceSum, pieceSum]
  rw [← Finset.mul_sum, integral_const_mul]
  ring

/-- The compensated Poisson integral is additive in the test function (almost everywhere). -/
theorem compensatedPoissonSum_add [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) (hg : Measurable g)
    (hg1 : Integrable g m) (hg2 : MemLp g 2 m) :
    ∀ᵐ ω ∂μ, compensatedPoissonSum K X (fun x => f x + g x) m ω
      = compensatedPoissonSum K X f m ω + compensatedPoissonSum K X g m ω := by
  filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2,
    ae_summable_compensatedPieceSum hd hg hg1 hg2] with ω hsf hsg
  simp only [compensatedPoissonSum]
  rw [← (hsf.hasSum.add hsg.hasSum).tsum_eq]
  exact tsum_congr fun k => compensatedPieceSum_add hf1.integrableOn hg1.integrableOn ω

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The compensated Poisson integral is homogeneous in the test function. -/
theorem compensatedPoissonSum_const_mul (c : ℝ) (ω : Ω) :
    compensatedPoissonSum K X (fun x => c * f x) m ω = c * compensatedPoissonSum K X f m ω := by
  simp only [compensatedPoissonSum]
  rw [← tsum_mul_left]
  exact tsum_congr fun k => compensatedPieceSum_const_mul c ω

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The compensated piece sum is subtractive in the test function. -/
theorem compensatedPieceSum_sub (hf1 : Integrable f (m.restrict (prmPiece m k)))
    (hg1 : Integrable g (m.restrict (prmPiece m k))) (ω : Ω) :
    compensatedPieceSum K X (fun x => f x - g x) m k ω
      = compensatedPieceSum K X f m k ω - compensatedPieceSum K X g m k ω := by
  simp only [compensatedPieceSum, pieceSum]
  rw [Finset.sum_sub_distrib, integral_sub hf1 hg1]
  ring

/-- The compensated Poisson integral is subtractive in the test function (almost everywhere). -/
theorem compensatedPoissonSum_sub [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) (hg : Measurable g)
    (hg1 : Integrable g m) (hg2 : MemLp g 2 m) :
    ∀ᵐ ω ∂μ, compensatedPoissonSum K X (fun x => f x - g x) m ω
      = compensatedPoissonSum K X f m ω - compensatedPoissonSum K X g m ω := by
  filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2,
    ae_summable_compensatedPieceSum hd hg hg1 hg2] with ω hsf hsg
  simp only [compensatedPoissonSum]
  rw [← (hsf.hasSum.sub hsg.hasSum).tsum_eq]
  exact tsum_congr fun k => compensatedPieceSum_sub hf1.integrableOn hg1.integrableOn ω

/-! ### The `L²(μ)`-valued compensated integral -/

/-- The real `L²`-seminorm of a square-integrable real function is the square root of its second
moment. -/
private theorem eLpNorm_two_toReal_eq_sqrt {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {h : α → ℝ} (hh : MemLp h 2 ν) :
    (eLpNorm h 2 ν).toReal = Real.sqrt (∫ a, (h a) ^ 2 ∂ν) := by
  rw [hh.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have he : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [he]
  have hint : (∫ a, ‖h a‖ ^ (2 : ℝ) ∂ν) = ∫ a, (h a) ^ 2 ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hint, Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]

/-- The `L²(μ)` element attached to a measurable `L¹ ∩ L²` test function by the compensated Poisson
sum. -/
private noncomputable def compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) : Lp ℝ 2 μ :=
  (memLp_two_compensatedPoissonSum hd hf hf1 hf2).toLp (compensatedPoissonSum K X f m)

private theorem coeFn_compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ⇑(compensatedPoissonToLp hd hf hf1 hf2) =ᵐ[μ] compensatedPoissonSum K X f m :=
  MemLp.coeFn_toLp _

/-- The compensated Poisson map is an isometry from `L¹ ∩ L²` into `L²(μ)`. -/
private theorem norm_compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ‖compensatedPoissonToLp hd hf hf1 hf2‖ = (eLpNorm f 2 m).toReal := by
  unfold compensatedPoissonToLp
  rw [Lp.norm_toLp, eLpNorm_two_toReal_eq_sqrt (memLp_two_compensatedPoissonSum hd hf hf1 hf2),
    eLpNorm_two_toReal_eq_sqrt hf2, integral_sq_compensatedPoissonSum hd hf hf1 hf2]

/-- The distance between two compensated Poisson images is the `L²(m)`-distance of the test
functions (the isometry, in `dist` form). -/
private theorem dist_compensatedPoissonToLp [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) (hg : Measurable g) (hg1 : Integrable g m) (hg2 : MemLp g 2 m) :
    dist (compensatedPoissonToLp hd hf hf1 hf2) (compensatedPoissonToLp hd hg hg1 hg2)
      = (eLpNorm (fun x => f x - g x) 2 m).toReal := by
  have hmemf := memLp_two_compensatedPoissonSum hd hf hf1 hf2
  have hmemg := memLp_two_compensatedPoissonSum hd hg hg1 hg2
  have hsub : ∀ᵐ ω ∂μ, (compensatedPoissonSum K X f m - compensatedPoissonSum K X g m) ω
      = compensatedPoissonSum K X (fun x => f x - g x) m ω := by
    filter_upwards [compensatedPoissonSum_sub hd hf hf1 hf2 hg hg1 hg2] with ω hω
    simpa [Pi.sub_apply] using hω.symm
  -- The `.sub` combinators yield the `f - g` (`Pi.sub`) shape, but the sum lemmas above
  -- carry the `fun x => f x - g x` shape; pin the fun-form so the rewrites line up.
  have hfg : Measurable (fun x => f x - g x) := hf.sub hg
  have hfg1 : Integrable (fun x => f x - g x) m := hf1.sub hg1
  have hfg2 : MemLp (fun x => f x - g x) 2 m := hf2.sub hg2
  rw [dist_eq_norm]
  unfold compensatedPoissonToLp
  rw [← MemLp.toLp_sub, Lp.norm_toLp, eLpNorm_congr_ae hsub,
    eLpNorm_two_toReal_eq_sqrt (memLp_two_compensatedPoissonSum hd hfg hfg1 hfg2),
    integral_sq_compensatedPoissonSum hd hfg hfg1 hfg2]
  exact (eLpNorm_two_toReal_eq_sqrt hfg2).symm

/-! ### Simple-function approximation and the density extension -/

omit [SigmaFinite m] [Nonempty E] in
/-- A simple-function approximation of `f ∈ L²(m)` accurate to `1 / (n + 1)`, extracted from
`MemLp.exists_simpleFunc_eLpNorm_sub_lt`. -/
private theorem exists_approxSimple (f : Lp ℝ 2 m) (n : ℕ) :
    ∃ h : SimpleFunc E ℝ, eLpNorm (⇑f - ⇑h) 2 m < ENNReal.ofReal (1 / (n + 1)) ∧ MemLp h 2 m :=
  (Lp.memLp f).exists_simpleFunc_eLpNorm_sub_lt (by norm_num)
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'

private noncomputable def approxSimple (f : Lp ℝ 2 m) (n : ℕ) : SimpleFunc E ℝ :=
  (exists_approxSimple f n).choose

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_eLpNorm_lt (f : Lp ℝ 2 m) (n : ℕ) :
    eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m < ENNReal.ofReal (1 / (n + 1)) :=
  (exists_approxSimple f n).choose_spec.1

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_memLp (f : Lp ℝ 2 m) (n : ℕ) : MemLp (approxSimple f n) 2 m :=
  (exists_approxSimple f n).choose_spec.2

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_measurable (f : Lp ℝ 2 m) (n : ℕ) :
    Measurable (⇑(approxSimple f n)) :=
  (approxSimple f n).measurable

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_integrable (f : Lp ℝ 2 m) (n : ℕ) :
    Integrable (⇑(approxSimple f n)) m :=
  (SimpleFunc.memLp_iff_integrable two_ne_zero (by norm_num)).mp (approxSimple_memLp f n)

omit [SigmaFinite m] [Nonempty E] in
private theorem approxSimple_eLpNorm_tendsto (f : Lp ℝ 2 m) :
    Tendsto (fun n => eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m) atTop (𝓝 0) := by
  have hub : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1))) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  exact (approxSimple_eLpNorm_lt f n).le

omit [SigmaFinite m] [Nonempty E] in
/-- The `L²(m)`-image of the approximation converges to `f`. -/
private theorem tendsto_toLp_approxSimple (f : Lp ℝ 2 m) :
    Tendsto (fun n => (approxSimple_memLp f n).toLp (⇑(approxSimple f n))) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ n, ‖(approxSimple_memLp f n).toLp (⇑(approxSimple f n)) - f‖
      = (eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m).toReal := by
    intro n
    rw [Lp.norm_def]
    congr 1
    rw [eLpNorm_sub_comm (⇑f) (⇑(approxSimple f n))]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((approxSimple_memLp f n).toLp (⇑(approxSimple f n))) f,
      MemLp.coeFn_toLp (approxSimple_memLp f n)] with x h1 h2
    rw [h1]; simp only [Pi.sub_apply]; rw [h2]
  simp_rw [heq]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp (approxSimple_eLpNorm_tendsto f)

/-- The compensated images of the approximation form a Cauchy sequence in `L²(μ)`. -/
private theorem cauchySeq_compApproxSeq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    CauchySeq (fun n => compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n)) := by
  have hb : CauchySeq (fun n => (approxSimple_memLp f n).toLp (⇑(approxSimple f n))) :=
    (tendsto_toLp_approxSimple f).cauchySeq
  have hdist : ∀ n k, dist (compensatedPoissonToLp hd (approxSimple_measurable f n)
        (approxSimple_integrable f n) (approxSimple_memLp f n))
        (compensatedPoissonToLp hd (approxSimple_measurable f k)
        (approxSimple_integrable f k) (approxSimple_memLp f k))
      = dist ((approxSimple_memLp f n).toLp (⇑(approxSimple f n)))
        ((approxSimple_memLp f k).toLp (⇑(approxSimple f k))) := by
    intro n k
    rw [dist_compensatedPoissonToLp, dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  rw [Metric.cauchySeq_iff] at hb ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hb ε hε
  exact ⟨N, fun n hn k hk => (hdist n k).symm ▸ hN n hn k hk⟩

/-- The **compensated Poisson integral** as a map `L²(m) → L²(μ)`: the `L²(μ)`-limit of the
compensated sums of a simple-function approximation of `f`.  It is an isometry
(`eLpNorm_compensatedPoissonIntegral`) and agrees a.e. with the explicit pathwise sum on `L¹ ∩ L²`
(`compensatedPoissonIntegral_eq_sum`). -/
noncomputable def compensatedPoissonIntegral [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) : Lp ℝ 2 μ :=
  (cauchySeq_tendsto_of_complete (cauchySeq_compApproxSeq hd f)).choose

private theorem compApproxSeq_tendsto [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    Tendsto (fun n => compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n)) atTop
      (𝓝 (compensatedPoissonIntegral hd f)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_compApproxSeq hd f)).choose_spec

/-- **Well-definedness of the extension.** For *any* measurable `L¹ ∩ L²` sequence `gm n`
converging to `f` in `L²(m)`, the compensated images converge to `compensatedPoissonIntegral hd f`.
This is the isometric limit being independent of the approximating sequence. -/
private theorem tendsto_compensatedPoissonToLp_of_eLpNorm_sub_tendsto [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) {gm : ℕ → E → ℝ}
    (hg : ∀ n, Measurable (gm n)) (hg1 : ∀ n, Integrable (gm n) m) (hg2 : ∀ n, MemLp (gm n) 2 m)
    (htend : Tendsto (fun n => eLpNorm (⇑f - gm n) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => compensatedPoissonToLp hd (hg n) (hg1 n) (hg2 n)) atTop
      (𝓝 (compensatedPoissonIntegral hd f)) := by
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  have hd2 : Tendsto (fun n => dist (compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n))
      (compensatedPoissonIntegral hd f)) atTop (𝓝 0) := by
    have h := (compApproxSeq_tendsto hd f).dist
      (tendsto_const_nhds (x := compensatedPoissonIntegral hd f))
    rwa [dist_self] at h
  have t1 : Tendsto (fun n => (eLpNorm (⇑f - gm n) 2 m).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp htend
  have t2 : Tendsto (fun n => (eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp (approxSimple_eLpNorm_tendsto f)
  have hd1 : Tendsto (fun n => dist (compensatedPoissonToLp hd (hg n) (hg1 n) (hg2 n))
      (compensatedPoissonToLp hd (approxSimple_measurable f n) (approxSimple_integrable f n)
        (approxSimple_memLp f n))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (by simpa using t1.add t2)
    rw [dist_compensatedPoissonToLp]
    have hfin1 : eLpNorm (⇑f - gm n) 2 m ≠ ⊤ := ((Lp.memLp f).sub (hg2 n)).2.ne
    have hfin2 : eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m ≠ ⊤ :=
      ((Lp.memLp f).sub (approxSimple_memLp f n)).2.ne
    have htri : eLpNorm (fun x => gm n x - (approxSimple f n) x) 2 m
        ≤ eLpNorm (⇑f - gm n) 2 m + eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m := by
      have hrw : (fun x => gm n x - (approxSimple f n) x)
          = (fun x => gm n x - ⇑f x) + (fun x => ⇑f x - (approxSimple f n) x) := by
        funext x; simp only [Pi.add_apply]; ring
      rw [hrw]
      refine (eLpNorm_add_le ((hg2 n).sub (Lp.memLp f)).aestronglyMeasurable
        ((Lp.memLp f).sub (approxSimple_memLp f n)).aestronglyMeasurable one_le_two).trans_eq ?_
      rw [eLpNorm_sub_comm (gm n) (⇑f)]
    calc (eLpNorm (fun x => gm n x - (approxSimple f n) x) 2 m).toReal
        ≤ (eLpNorm (⇑f - gm n) 2 m + eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) htri
      _ = (eLpNorm (⇑f - gm n) 2 m).toReal + (eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m).toReal :=
          ENNReal.toReal_add hfin1 hfin2
  have hg0 : Tendsto (fun n => dist (compensatedPoissonToLp hd (hg n) (hg1 n) (hg2 n))
        (compensatedPoissonToLp hd (approxSimple_measurable f n) (approxSimple_integrable f n)
          (approxSimple_memLp f n))
      + dist (compensatedPoissonToLp hd (approxSimple_measurable f n) (approxSimple_integrable f n)
          (approxSimple_memLp f n)) (compensatedPoissonIntegral hd f)) atTop (𝓝 0) := by
    simpa using hd1.add hd2
  exact squeeze_zero (fun n => dist_nonneg) (fun n => dist_triangle _ _ _) hg0

/-- **Isometry of the compensated Poisson integral on all of `L²(m)`.** -/
theorem eLpNorm_compensatedPoissonIntegral [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    eLpNorm (compensatedPoissonIntegral hd f) 2 μ = eLpNorm f 2 m := by
  have h1 : Tendsto (fun n => ‖compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n)‖) atTop
      (𝓝 ‖compensatedPoissonIntegral hd f‖) := (compApproxSeq_tendsto hd f).norm
  have h2 : Tendsto (fun n => ‖compensatedPoissonToLp hd (approxSimple_measurable f n)
      (approxSimple_integrable f n) (approxSimple_memLp f n)‖) atTop (𝓝 ‖f‖) := by
    have heq : ∀ n, ‖compensatedPoissonToLp hd (approxSimple_measurable f n)
        (approxSimple_integrable f n) (approxSimple_memLp f n)‖
        = ‖(approxSimple_memLp f n).toLp (⇑(approxSimple f n))‖ := by
      intro n
      rw [norm_compensatedPoissonToLp, Lp.norm_toLp]
    simp_rw [heq]
    exact (tendsto_toLp_approxSimple f).norm
  have hnorm : ‖compensatedPoissonIntegral hd f‖ = ‖f‖ := tendsto_nhds_unique h1 h2
  rw [Lp.norm_def, Lp.norm_def] at hnorm
  exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).mp hnorm

/-- The compensated Poisson integral is an isometry in the `‖·‖` sense. -/
theorem norm_compensatedPoissonIntegral [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    ‖compensatedPoissonIntegral hd f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_compensatedPoissonIntegral hd f]





/-- **Agreement with the explicit sum.** On `L¹ ∩ L²`, the extended integral of `f` agrees a.e.
with the pathwise compensated Poisson sum. -/
theorem compensatedPoissonIntegral_eq_sum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    compensatedPoissonIntegral hd (hf2.toLp f) =ᵐ[μ] compensatedPoissonSum K X f m := by
  have hz : eLpNorm (⇑(hf2.toLp f) - f) 2 m = 0 := by
    have hae : (⇑(hf2.toLp f) - f) =ᵐ[m] (0 : E → ℝ) := by
      filter_upwards [MemLp.coeFn_toLp hf2] with x hx
      simp [Pi.sub_apply, hx]
    rw [eLpNorm_congr_ae hae, eLpNorm_zero]
  have hconst : Tendsto (fun _ : ℕ => compensatedPoissonToLp hd hf hf1 hf2) atTop
      (𝓝 (compensatedPoissonIntegral hd (hf2.toLp f))) := by
    refine tendsto_compensatedPoissonToLp_of_eLpNorm_sub_tendsto hd (hf2.toLp f)
      (gm := fun _ => f) (fun _ => hf) (fun _ => hf1) (fun _ => hf2) ?_
    have hfun : (fun n : ℕ => eLpNorm (⇑(hf2.toLp f) - (fun _ => f) n) 2 m)
        = fun _ => (0 : ℝ≥0∞) := funext fun _ => hz
    rw [hfun]
    exact tendsto_const_nhds
  have hEq : compensatedPoissonIntegral hd (hf2.toLp f) = compensatedPoissonToLp hd hf hf1 hf2 :=
    tendsto_nhds_unique hconst tendsto_const_nhds
  rw [hEq]
  exact coeFn_compensatedPoissonToLp hd hf hf1 hf2

/-! ### Linearity of the `L²(m) → L²(μ)` extension -/

/-- Additivity of the compensated Poisson map at the `L²(μ)`-element level, for measurable
`L¹ ∩ L²` test functions. -/
private theorem compensatedPoissonToLp_add [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) (hg : Measurable g) (hg1 : Integrable g m) (hg2 : MemLp g 2 m) :
    compensatedPoissonToLp hd (hf.add hg) (hf1.add hg1) (hf2.add hg2)
      = compensatedPoissonToLp hd hf hf1 hf2 + compensatedPoissonToLp hd hg hg1 hg2 := by
  have hae : compensatedPoissonSum K X (fun x => f x + g x) m
      =ᵐ[μ] compensatedPoissonSum K X f m + compensatedPoissonSum K X g m := by
    filter_upwards [compensatedPoissonSum_add hd hf hf1 hf2 hg hg1 hg2] with ω hω
    simpa [Pi.add_apply] using hω
  simp only [compensatedPoissonToLp]
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ hae

/-- The compensated Poisson map negates at the `L²(μ)`-element level. -/
private theorem compensatedPoissonToLp_neg [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    compensatedPoissonToLp hd hf.neg hf1.neg hf2.neg = -compensatedPoissonToLp hd hf hf1 hf2 := by
  have hae : compensatedPoissonSum K X (fun x => -f x) m
      =ᵐ[μ] -compensatedPoissonSum K X f m := by
    refine Filter.EventuallyEq.of_eq (funext fun ω => ?_)
    have h := compensatedPoissonSum_const_mul (K := K) (X := X) (f := f) (m := m) (-1) ω
    simp only [neg_one_mul] at h
    simpa [Pi.neg_apply] using h
  simp only [compensatedPoissonToLp]
  rw [← MemLp.toLp_neg]
  exact MemLp.toLp_congr _ _ hae

/-- **Additivity of the compensated Poisson integral** on all of `L²(m)`. -/
theorem compensatedPoissonIntegral_add [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f g : Lp ℝ 2 m) :
    compensatedPoissonIntegral hd (f + g)
      = compensatedPoissonIntegral hd f + compensatedPoissonIntegral hd g := by
  have hsum0 : Tendsto (fun n => eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m
      + eLpNorm (⇑g - ⇑(approxSimple g n)) 2 m) atTop (𝓝 0) := by
    simpa using (approxSimple_eLpNorm_tendsto f).add (approxSimple_eLpNorm_tendsto g)
  have htend : Tendsto (fun n => eLpNorm (⇑(f + g)
      - (⇑(approxSimple f n) + ⇑(approxSimple g n))) 2 m) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum0
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    have hae : (⇑(f + g) - (⇑(approxSimple f n) + ⇑(approxSimple g n)))
        =ᵐ[m] (⇑f - ⇑(approxSimple f n)) + (⇑g - ⇑(approxSimple g n)) := by
      filter_upwards [Lp.coeFn_add f g] with x hx
      simp only [Pi.add_apply] at hx
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hx]; ring
    rw [eLpNorm_congr_ae hae]
    exact eLpNorm_add_le (((Lp.memLp f).sub (approxSimple_memLp f n)).aestronglyMeasurable)
      (((Lp.memLp g).sub (approxSimple_memLp g n)).aestronglyMeasurable) one_le_two
  have key := tendsto_compensatedPoissonToLp_of_eLpNorm_sub_tendsto hd (f + g)
    (gm := fun n => ⇑(approxSimple f n) + ⇑(approxSimple g n))
    (fun n => (approxSimple_measurable f n).add (approxSimple_measurable g n))
    (fun n => (approxSimple_integrable f n).add (approxSimple_integrable g n))
    (fun n => (approxSimple_memLp f n).add (approxSimple_memLp g n)) htend
  have hsplit : (fun n => compensatedPoissonToLp hd
        ((approxSimple_measurable f n).add (approxSimple_measurable g n))
        ((approxSimple_integrable f n).add (approxSimple_integrable g n))
        ((approxSimple_memLp f n).add (approxSimple_memLp g n)))
      = fun n => compensatedPoissonToLp hd (approxSimple_measurable f n)
          (approxSimple_integrable f n) (approxSimple_memLp f n)
        + compensatedPoissonToLp hd (approxSimple_measurable g n)
          (approxSimple_integrable g n) (approxSimple_memLp g n) := by
    funext n
    exact compensatedPoissonToLp_add hd _ _ _ _ _ _
  rw [hsplit] at key
  exact tendsto_nhds_unique key ((compApproxSeq_tendsto hd f).add (compApproxSeq_tendsto hd g))

/-- **The compensated Poisson integral negates** on all of `L²(m)`. -/
theorem compensatedPoissonIntegral_neg [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f : Lp ℝ 2 m) :
    compensatedPoissonIntegral hd (-f) = -compensatedPoissonIntegral hd f := by
  have htend : Tendsto (fun n => eLpNorm (⇑(-f) - (-⇑(approxSimple f n))) 2 m) atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (⇑(-f) - (-⇑(approxSimple f n))) 2 m)
        = fun n => eLpNorm (⇑f - ⇑(approxSimple f n)) 2 m := by
      funext n
      have hae : (⇑(-f) - (-⇑(approxSimple f n))) =ᵐ[m] -(⇑f - ⇑(approxSimple f n)) := by
        filter_upwards [Lp.coeFn_neg f] with x hx
        simp only [Pi.neg_apply] at hx
        simp only [Pi.sub_apply, Pi.neg_apply]
        rw [hx]; ring
      rw [eLpNorm_congr_ae hae, eLpNorm_neg]
    rw [heq]
    exact approxSimple_eLpNorm_tendsto f
  have key := tendsto_compensatedPoissonToLp_of_eLpNorm_sub_tendsto hd (-f)
    (gm := fun n => -⇑(approxSimple f n))
    (fun n => (approxSimple_measurable f n).neg)
    (fun n => (approxSimple_integrable f n).neg)
    (fun n => (approxSimple_memLp f n).neg) htend
  have hsplit : (fun n => compensatedPoissonToLp hd (approxSimple_measurable f n).neg
        (approxSimple_integrable f n).neg (approxSimple_memLp f n).neg)
      = fun n => -compensatedPoissonToLp hd (approxSimple_measurable f n)
          (approxSimple_integrable f n) (approxSimple_memLp f n) := by
    funext n
    exact compensatedPoissonToLp_neg hd _ _ _
  rw [hsplit] at key
  exact tendsto_nhds_unique key (compApproxSeq_tendsto hd f).neg

/-- **The compensated Poisson integral is subtractive** on all of `L²(m)`. -/
theorem compensatedPoissonIntegral_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (f g : Lp ℝ 2 m) :
    compensatedPoissonIntegral hd (f - g)
      = compensatedPoissonIntegral hd f - compensatedPoissonIntegral hd g := by
  rw [show f - g = f + (-g) from sub_eq_add_neg f g, compensatedPoissonIntegral_add,
    compensatedPoissonIntegral_neg, ← sub_eq_add_neg]

end Compensated

end ProbabilityTheory


