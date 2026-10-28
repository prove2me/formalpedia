-- Prove2me | Definitions.Def_OAIQ062C001
-- name    : OAIQ062C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:53:40.690371+00:00
-- url     : https://prove2.me/theorems/116f480c-3fc4-48e3-9613-696c39812dfc
-- title:
--   Definitions bundle OAIQ062C001 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 523 declarations of OpenAI's Lean: 90 definitions, 15 instances and 418 theorems. The definitions and types are `OAI.Coulomb.CompleteOrbitals`, `OAI.Coulomb.FermionicCoefficients`, `OAI.Coulomb.GridAssignment`, `OAI.Coulomb.ProductAntisymmetric`, `OAI.Coulomb.Rotation`, `OAI.Coulomb.TFExponent`, `OAI.Coulomb.TFFieldExponent`, `OAI.Coulomb.TFLp`, `OAI.Coulomb.TFLq`, `OAI.Coulomb.TFNonneg`, `OAI.Coulomb.bernoulliWeight`, `OAI.Coulomb.blockGroup`, `OAI.Coulomb.blockHom`, `OAI.Coulomb.complexMollify`, `OAI.Coulomb.complexSign`, `OAI.Coulomb.cosineMode`, `OAI.Coulomb.cosineWeight`, `OAI.Coulomb.cubeMeasure`, `OAI.Coulomb.cubeMode`, `OAI.Coulomb.determinantWave`, `OAI.Coulomb.dirichletMode`, `OAI.Coulomb.euclideanMollifier`, `OAI.Coulomb.evenOnSegment`, `OAI.Coulomb.fineLocalizationError`, `OAI.Coulomb.finiteCubeMeasure`, `OAI.Coulomb.finiteCubeMode`, `OAI.Coulomb.flatDensityPower`, `OAI.Coulomb.flatFineKernel`, `OAI.Coulomb.gridBox`, `OAI.Coulomb.gridCell`, `OAI.Coulomb.gridIndex`, `OAI.Coulomb.gridLeadingCount`, `OAI.Coulomb.groupLeadingCount`, `OAI.Coulomb.integerCell`, `OAI.Coulomb.l2MeasureInclusion`, `OAI.Coulomb.latticeRadius`, `OAI.Coulomb.neumannBoundary`, `OAI.Coulomb.neumannLeading`, `OAI.Coulomb.neumannMode`, `OAI.Coulomb.occupancy` and 50 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_ComplexMollify`, `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_CoreCoulombPotential`, `CoulombRadii_FieldAnalysis_CosineWeight`, `CoulombRadii_FieldAnalysis_CoulombBilinear`, `CoulombRadii_FieldAnalysis_CubeLabelEquiv`, `CoulombRadii_FieldAnalysis_CubeMeasure`, `CoulombRadii_FieldAnalysis_DeterminantWave`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_FieldSubmean`, `CoulombRadii_FieldAnalysis_FiniteProdSum`, `CoulombRadii_FieldAnalysis_FlatDensityPower`, `CoulombRadii_FieldAnalysis_GeometricRecursion`, `CoulombRadii_FieldAnalysis_GridIndex`, `CoulombRadii_FieldAnalysis_GroupFermionicCoefficients`, `CoulombRadii_FieldAnalysis_IntegrableTsumSummableNormIntegral`, `CoulombRadii_FieldAnalysis_JoinSpins`, `CoulombRadii_FieldAnalysis_MinimizerMidpointControl`, `CoulombRadii_FieldAnalysis_NormSqSumCosets`, `CoulombRadii_FieldAnalysis_Occupancy`, `CoulombRadii_FieldAnalysis_OuterJoinConfiguration`, `CoulombRadii_FieldAnalysis_PairRegroup`, `CoulombRadii_FieldAnalysis_PermOrCompSwapOffTwo`, `CoulombRadii_FieldAnalysis_Rotation`, `CoulombRadii_FieldAnalysis_SliceExpectation`, `CoulombRadii_FieldAnalysis_SlotTensor`, `CoulombRadii_FieldAnalysis_SpinConfigurationIntegral`, `CoulombRadii_FieldAnalysis_SpinCubeEquiv`, `CoulombRadii_FieldAnalysis_SpinMode`, `CoulombRadii_FieldAnalysis_SumSpinDuplicate`, `CoulombRadii_FieldAnalysis_SumSwapNonnegative`, `CoulombRadii_FieldAnalysis_TwoBodyTensorIntegrable`, `CoulombRadii_FieldAnalysis_WeakDirectionalUnique`, `CoulombRadii_FieldAnalysis_WedgeMultiplicity`, `CoulombRadii_FieldAnalysis_WeightedExchangeAlgebra`, `CoulombRadii_FormDomain_FieldOptimization`, `CoulombRadii_FormDomain_L2KernelIntegral`, `CoulombRadii_FormDomain_L2MeasureInclusion`, `CoulombRadii_FormDomain_L2MultiplierDistribution`, `CoulombRadii_FormDomain_OrbitalHilbertBasis`, `CoulombRadii_FormDomain_PatchErrors`, `CoulombRadii_FormDomain_PhysicalEnsemble`, `CoulombRadii_FormDomain_Pullback`, `CoulombRadii_FormDomain_SmoothCompact`, `CoulombRadii_FormDomain_Translate`, `CoulombRadii_Localization_ConfigSupported`, `CoulombRadii_Localization_DeletedLabels`, `CoulombRadii_Localization_ThinCut`, `CoulombRadii_Packets_CoulombKernel`, `CoulombRadii_Packets_CoulombKernelFiveHalvesIntegrable`, `CoulombRadii_Packets_OrbitalKernel`, `CoulombRadii_RadialBounds_InteriorBarrier`, `CoulombRadii_Screening_AtomicPatchCap`, `CoulombRadii_Screening_CountScalar`, `CoulombRadii_Screening_PatchComparison`, `CoulombRadii_Screening_ScreenNumeric`, `CoulombRadii_Screening_ScreenUnits`, `CoulombRadii_Screening_ScreeningNormalization`, `CoulombRadii_ThomasFermi_ScaledProfile`, `CoulombRadii_ThomasFermi_TFExponent`, `CoulombRadii_ThomasFermi_TFInterior`, `CoulombRadii_ThomasFermi_TFNonneg`, `CoulombRadii_ThomasFermi_TfFunctional`, `CoulombRadii_ThomasFermi_TfFunctionalGapControl`, `CoulombRadii_ThomasFermi_TfFunctionalUniformBound`, `CoulombRadii_ThomasFermi_TfPotential`, `CoulombRadii_ThomasFermi_TfRawVariation`, `CoulombRadii_Variational_Axis`, `CoulombRadii_Variational_CorrectionDensity`, `CoulombRadii_Variational_WeakLaplacian`.
--
--   **Imports.** It imports the published bundle `Def_CoulombRadii`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ062C003`, `OAIQ062C004` and `OAIQ062C005`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombRadii

section
-- module Solutions.OAIQ062_CR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

def FermionicCoefficients {n : ℕ} {α : Type*} (f : (Fin n → α) → ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) b, f (b ∘ p) = ((p.sign : ℤ) : ℂ) * f b

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

def CompleteOrbitals {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (v : ι → A → ℂ) : Prop :=
  ∀ f : A → ℂ, MemLp f 2 μ → (∀ i, (∫ a, star (v i a) * f a ∂μ) = 0) → f =ᵐ[μ] 0

theorem CompleteOrbitals.comp {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {v : ι → A → ℂ}
    (hc : CompleteOrbitals μ v) (e : B ≃ᵐ A) (he : MeasurePreserving e ν μ) :
    CompleteOrbitals ν (fun i b => v i (e b)) := by
  intro f hf hz
  have hs := hc (f ∘ e.symm) (hf.comp_measurePreserving (he.symm e)) (by
    intro i
    dsimp only [Function.comp_apply]
    rw [← he.integral_comp' (fun a => star (v i a) * f (e.symm a))]
    simpa using hz i)
  filter_upwards [he.quasiMeasurePreserving.ae hs] with b hb
  simpa using hb

lemma scalarTensor_memLp {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (b : Fin n → ι) :
    MemLp (fun x : Fin n → A => ∏ i, v (b i) (x i)) 2 (Measure.pi fun _ => μ) := by
  have hm : AEStronglyMeasurable (fun x : Fin n → A => ∏ i, v (b i) (x i))
      (Measure.pi fun _ => μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hv (b i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_prod, ← Finset.prod_pow] using
    Integrable.fintype_prod (fun i => (hv (b i)).norm.integrable_sq)

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_OrbitalHilbertBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

theorem hilbertBasis_parseval {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : HilbertBasis ι ℂ E) (f : E) :
    (∑' i, ‖inner ℂ (b i) f‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (b.repr f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] at h
  exact h.symm

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma scalarTensor_inner_integral {n : ℕ} (v : ι → A → ℂ) (b c : Fin n → ι) :
    (∫ x : Fin n → A, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = ∏ i, ∫ a, star (v (b i) a) * v (c i) a ∂μ := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i a => star (v (b i) a) * v (c i) a)

def ProductAntisymmetric {n : ℕ} (f : (Fin n → A) → ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)), ∀ᵐ x ∂(Measure.pi fun _ => μ),
    f (x ∘ p) = ((p.sign : ℤ) : ℂ) * f x

end GeneralFermionSpace

noncomputable def cosineMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (Real.cos ((n : ℝ) * Real.pi * x / b) : ℂ)

noncomputable def evenOnSegment (b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Ioc 0 b).indicator f x + (Ioc 0 b).indicator f (-x)

lemma evenOnSegment_memLp {b : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b))) :
    MemLp (evenOnSegment b f) 2 volume := by
  have hg : MemLp ((Ioc 0 b).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc).2 hf
  exact hg.add (hg.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ)))

lemma evenOnSegment_pos {b x : ℝ} (f : ℝ → ℂ) (hx : x ∈ Ioc 0 b) :
    evenOnSegment b f x = f x := by
  have hn : -x ∉ Ioc 0 b := by rintro ⟨hh, _⟩; linarith [hx.1]
  simp only [evenOnSegment, indicator_of_mem hx, indicator_of_notMem hn, add_zero]

lemma evenOnSegment_neg (b : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    evenOnSegment b f (-x) = evenOnSegment b f x := by
  simp only [evenOnSegment, neg_neg, add_comm]

lemma fourierOn_ae_zero {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hz : ∀ n : ℤ, fourierCoeffOn hab f n = 0) :
    f =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hp := tsum_sq_fourierCoeffOn hab hf
  simp only [hz, norm_zero, zero_pow (by omega : 2 ≠ 0), tsum_zero,
    smul_eq_mul, intervalIntegral.integral_of_le hab.le] at hp
  have hnorm : (∫ x in Ioc a b, ‖f x‖^2) = 0 := by
    exact (mul_eq_zero.mp hp.symm).resolve_left (inv_ne_zero (sub_ne_zero.mpr hab.ne'))
  have hz' := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖)
    hf.norm.integrable_sq).1 hnorm
  filter_upwards [hz'] with x hx
  simpa using hx

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CosineWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

lemma evenOnSegment_intervalIntegrable {b : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b))) (c d : ℝ) :
    IntervalIntegrable (evenOnSegment b f) volume c d := by
  apply intervalIntegrable_iff.mpr
  let : IsFiniteMeasure (volume.restrict (uIoc c d)) := by
    unfold uIoc
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact ((evenOnSegment_memLp hf).restrict _).integrable (by norm_num)

lemma integral_evenOnSegment {b : ℝ} {f : ℝ → ℂ} (hb : 0 < b)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b)))
    (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ x in (-b)..b, g x * evenOnSegment b f x) =
      ∫ x in (0 : ℝ)..b, (g x + g (-x)) * f x := by
  have hi (c d : ℝ) : IntervalIntegrable
      (fun x => g x * evenOnSegment b f x) volume c d :=
    (evenOnSegment_intervalIntegrable hf c d).continuousOn_mul hg.continuousOn
  have hn : IntervalIntegrable (fun x => g (-x) * evenOnSegment b f x) volume 0 b :=
    (evenOnSegment_intervalIntegrable hf 0 b).continuousOn_mul
      (hg.comp continuous_neg).continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-b) 0) (hi 0 b)]
  have he : (∫ x in (-b)..(0 : ℝ), g x * evenOnSegment b f x) =
      ∫ x in (0 : ℝ)..b, g (-x) * evenOnSegment b f x := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := b)
      (fun x => g x * evenOnSegment b f x)
    simpa only [neg_zero, evenOnSegment_neg] using h.symm
  rw [he, ← intervalIntegral.integral_add hn (hi 0 b)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [uIoc_of_le hb.le] at hx
  rw [evenOnSegment_pos f hx]
  ring

lemma complex_exp_pair (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + Complex.exp ((-t : ℝ) * Complex.I) =
      2 * (Real.cos t : ℂ) := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  ring

lemma cosine_natAbs (b x : ℝ) (n : ℤ) :
    (Real.cos ((n : ℝ) * Real.pi * x / b) : ℂ) = cosineMode b n.natAbs x := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp only [Int.cast_natCast, Int.natAbs_natCast, cosineMode]
  · simp only [Int.cast_neg, Int.cast_natCast, Int.natAbs_neg, Int.natAbs_natCast,
      neg_mul, neg_div, Real.cos_neg, cosineMode]

lemma fourier_pair_cosine {b : ℝ} (_hb : 0 < b) (n : ℤ) (x : ℝ) :
    fourier (-n) (x : AddCircle (b - -b)) +
      fourier (-n) ((-x : ℝ) : AddCircle (b - -b)) =
      2 * cosineMode b n.natAbs x := by
  rw [fourier_coe_apply, fourier_coe_apply]
  have h1 : (2 : ℂ) * Real.pi * Complex.I * (-n) * x / (b - -b) =
      ((-((n : ℝ) * Real.pi * x / b) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring
  have h2 : (2 : ℂ) * Real.pi * Complex.I * (-n) * (-x) / (b - -b) =
      (((n : ℝ) * Real.pi * x / b : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring
  simp only [Complex.ofReal_neg, Complex.ofReal_sub, Int.cast_neg] at h1 h2 ⊢
  rw [h1, h2, add_comm]
  simpa only [Complex.ofReal_neg, cosine_natAbs] using complex_exp_pair ((n : ℝ) * Real.pi * x / b)

lemma fourierOn_evenOnSegment {b : ℝ} {f : ℝ → ℂ} (hb : 0 < b)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 b))) (n : ℤ) :
    fourierCoeffOn (by linarith : -b < b) (evenOnSegment b f) n =
      (1 / b : ℝ) • ∫ x in (0 : ℝ)..b, cosineMode b n.natAbs x * f x := by
  rw [fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul]
  rw [integral_evenOnSegment hb hf
    (fun x => fourier (-n) (x : AddCircle (b - -b))) (by fun_prop)]
  simp_rw [fourier_pair_cosine hb, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_sub, Complex.ofReal_neg]
  field_simp
  ring

theorem cosineModes_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (volume.restrict (Ioc 0 b)) (cosineMode b) := by
  intro f hf hz
  have he : evenOnSegment b f =ᵐ[volume.restrict (Ioc (-b) b)] 0 := by
    apply fourierOn_ae_zero (by linarith : -b < b) ((evenOnSegment_memLp hf).restrict _)
    intro n
    rw [fourierOn_evenOnSegment hb hf n]
    have hh := hz n.natAbs
    simp only [cosineMode, Complex.star_def, Complex.conj_ofReal] at hh
    have hh' : (∫ x in (0 : ℝ)..b, cosineMode b n.natAbs x * f x) = 0 := by
      simpa only [cosineMode, intervalIntegral.integral_of_le hb.le] using hh
    rw [hh', smul_zero]
  have hs : Ioc 0 b ⊆ Ioc (-b) b := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have he' := ae_restrict_of_ae_restrict_of_subset hs he
  filter_upwards [he', ae_restrict_mem measurableSet_Ioc] with x hx hxb
  simpa only [evenOnSegment_pos f hxb] using hx

lemma cosineMode_continuous (b : ℝ) (n : ℕ) : Continuous (cosineMode b n) := by
  unfold cosineMode
  fun_prop

lemma cosineMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (cosineMode b n) 2 (volume.restrict (Ioc 0 b)) := by
  apply MemLp.of_bound (cosineMode_continuous b n).aestronglyMeasurable 1
  filter_upwards with x
  simpa only [cosineMode, Complex.norm_real, Real.norm_eq_abs] using
    Real.abs_cos_le_one ((n : ℝ) * Real.pi * x / b)

lemma integral_cosine_product_pi (n m : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos (n * x) * Real.cos (m * x)) =
      if n = m then (if n = 0 then Real.pi else Real.pi / 2) else 0 := by
  classical
  have he := Polynomial.Chebyshev.integral_measureT_eq_integral_cos
    (f := fun x => (Polynomial.Chebyshev.T ℝ n).eval x *
      (Polynomial.Chebyshev.T ℝ m).eval x)
  simp only [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast] at he
  rw [← he]
  by_cases hnm : n = m
  · subst m
    simp only [ite_true]
    by_cases hn : n = 0
    · subst n
      simpa using Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    · simpa only [hn, ite_false] using
        Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn
  · simpa only [hnm, ite_false] using
      Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hnm

lemma integral_cosine_product {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in (0 : ℝ)..b,
      Real.cos ((n : ℝ) * Real.pi * x / b) *
      Real.cos ((m : ℝ) * Real.pi * x / b)) =
      if n = m then (if n = 0 then b else b / 2) else 0 := by
  classical
  have hc : Real.pi / b ≠ 0 := div_ne_zero Real.pi_ne_zero hb.ne'
  have he := intervalIntegral.integral_comp_mul_left
    (a := 0) (b := b) (c := Real.pi / b)
    (fun x : ℝ => Real.cos (n * x) * Real.cos (m * x)) hc
  have harg (k : ℕ) (x : ℝ) :
      (k : ℝ) * (Real.pi / b * x) = (k : ℝ) * Real.pi * x / b := by ring
  simp_rw [harg] at he
  rw [mul_zero, div_mul_cancel₀ _ hb.ne', integral_cosine_product_pi] at he
  rw [he, smul_eq_mul]
  split_ifs <;> field_simp
  simp

noncomputable def cosineWeight (b : ℝ) (n : ℕ) : ℝ := if n = 0 then b else b / 2

lemma cosineWeight_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < cosineWeight b n := by
  unfold cosineWeight
  split_ifs <;> positivity

lemma cosineMode_inner {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (cosineMode b n x) * cosineMode b m x) =
      if n = m then (cosineWeight b n : ℂ) else 0 := by
  calc
    _ = ((∫ x in Ioc 0 b, Real.cos ((n : ℝ) * Real.pi * x / b) *
       Real.cos ((m : ℝ) * Real.pi * x / b) : ℝ) : ℂ) := by
      trans ∫ x in Ioc 0 b, ((Real.cos ((n : ℝ) * Real.pi * x / b) *
        Real.cos ((m : ℝ) * Real.pi * x / b) : ℝ) : ℂ)
      · apply integral_congr_ae
        filter_upwards with x
        simp only [cosineMode, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
      · exact integral_ofReal
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hb.le, integral_cosine_product hb]
      by_cases hnm : n = m <;> simp only [hnm, ite_true, ite_false, cosineWeight, Complex.ofReal_zero]

noncomputable def neumannMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) * cosineMode b n x

lemma neumannMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (neumannMode b n) 2 (volume.restrict (Ioc 0 b)) :=
  (cosineMode_memLp b n).const_mul _

lemma neumannMode_star (b : ℝ) (n : ℕ) (x : ℝ) :
    star (neumannMode b n x) =
      ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) * star (cosineMode b n x) := by
  simp [neumannMode, star_mul, mul_comm]

lemma neumannMode_orthonormal {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (neumannMode b n x) * neumannMode b m x) =
      if n = m then 1 else 0 := by
  simp_rw [neumannMode_star, neumannMode]
  have he : ∀ x : ℝ,
      (((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) : ℂ) * star (cosineMode b n x) *
        ((((Real.sqrt (cosineWeight b m))⁻¹ : ℝ) : ℂ) * cosineMode b m x) =
      ((((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (cosineWeight b m))⁻¹ : ℝ) : ℂ)) *
        (star (cosineMode b n x) * cosineMode b m x) := by intro x; ring
  simp_rw [he]
  rw [integral_const_mul, cosineMode_inner hb]
  by_cases hnm : n = m
  · subst m
    simp only [ite_true]
    have hw := Real.sq_sqrt (cosineWeight_pos hb n).le
    have hn : Real.sqrt (cosineWeight b n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (cosineWeight_pos hb n))
    have hh : ((Real.sqrt (cosineWeight b n))⁻¹)^2 * cosineWeight b n = 1 := by
      calc
        _ = ((Real.sqrt (cosineWeight b n))⁻¹)^2 *
            (Real.sqrt (cosineWeight b n))^2 :=
          congrArg (fun t : ℝ => ((Real.sqrt (cosineWeight b n))⁻¹)^2 * t) hw.symm
        _ = 1 := by field_simp
    have hh' : ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) *
        ((Real.sqrt (cosineWeight b n))⁻¹ : ℝ) * cosineWeight b n = 1 := by
      simpa only [pow_two] using hh
    exact_mod_cast hh'
  · simp only [hnm, ite_false, mul_zero]

lemma neumannModes_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (volume.restrict (Ioc 0 b)) (neumannMode b) := by
  intro f hf hz
  apply cosineModes_complete hb f hf
  intro n
  have hh := hz n
  simp only [neumannMode_star, mul_assoc, integral_const_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply Complex.ofReal_ne_zero.mpr
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (cosineWeight_pos hb n))))

noncomputable def sineMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (Real.sin (((n : ℝ) + 1) * Real.pi * x / b) : ℂ)

lemma sineMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (sineMode b n) 2 (volume.restrict (Ioc 0 b)) := by
  apply MemLp.of_bound (show Continuous (sineMode b n) by unfold sineMode; fun_prop).aestronglyMeasurable 1
  filter_upwards with x
  simpa only [sineMode, Complex.norm_real, Real.norm_eq_abs] using
    Real.abs_sin_le_one (((n : ℝ) + 1) * Real.pi * x / b)

lemma integral_cosine_nonzero {b : ℝ} (hb : 0 < b) (n : ℕ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..b, Real.cos ((n : ℝ) * Real.pi * x / b)) = 0 := by
  simpa only [Nat.cast_zero, zero_mul, zero_div, Real.cos_zero, mul_one, hn, ite_false]
    using integral_cosine_product hb n 0

lemma integral_sine_product {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in (0 : ℝ)..b,
      Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
      Real.sin (((m : ℝ) + 1) * Real.pi * x / b)) =
      if n = m then b / 2 else 0 := by
  classical
  have he (x : ℝ) :
      Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
        Real.sin (((m : ℝ) + 1) * Real.pi * x / b) =
      Real.cos (((n : ℝ) + 1) * Real.pi * x / b) *
        Real.cos (((m : ℝ) + 1) * Real.pi * x / b) -
        Real.cos (((n : ℝ) + (m : ℝ) + 2) * Real.pi * x / b) := by
    have hh := Real.cos_add (((n : ℝ) + 1) * Real.pi * x / b)
      (((m : ℝ) + 1) * Real.pi * x / b)
    have ha : ((n : ℝ) + 1) * Real.pi * x / b +
        ((m : ℝ) + 1) * Real.pi * x / b =
        ((n : ℝ) + (m : ℝ) + 2) * Real.pi * x / b := by ring
    rw [ha] at hh
    linarith
  simp_rw [he]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have hsum (x : ℝ) : ((n : ℝ) + (m : ℝ) + 2) * Real.pi * x / b =
      ((n + m + 2 : ℕ) : ℝ) * Real.pi * x / b := by push_cast; rfl
  simp_rw [hsum]
  rw [integral_cosine_nonzero hb (n + m + 2) (by omega), sub_zero]
  have hh := integral_cosine_product hb (n+1) (m+1)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_right_cancel_iff,
    Nat.add_one_ne_zero, ite_false] using hh

lemma sineMode_inner {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (sineMode b n x) * sineMode b m x) =
      if n = m then ((b / 2 : ℝ) : ℂ) else (0 : ℂ) := by
  calc
    _ = ((∫ x in Ioc 0 b,
      Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
      Real.sin (((m : ℝ) + 1) * Real.pi * x / b) : ℝ) : ℂ) := by
      trans ∫ x in Ioc 0 b, ((Real.sin (((n : ℝ) + 1) * Real.pi * x / b) *
        Real.sin (((m : ℝ) + 1) * Real.pi * x / b) : ℝ) : ℂ)
      · apply integral_congr_ae
        filter_upwards with x
        simp only [sineMode, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
      · exact integral_ofReal
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hb.le, integral_sine_product hb]
      by_cases hnm : n = m <;> simp only [hnm, ite_true, ite_false, Complex.ofReal_zero]

noncomputable def dirichletMode (b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt (b / 2))⁻¹ : ℝ) * sineMode b n x

lemma dirichletMode_memLp (b : ℝ) (n : ℕ) :
    MemLp (dirichletMode b n) 2 (volume.restrict (Ioc 0 b)) :=
  (sineMode_memLp b n).const_mul _

lemma dirichletMode_star (b : ℝ) (n : ℕ) (x : ℝ) :
    star (dirichletMode b n x) = dirichletMode b n x := by
  simp only [dirichletMode, sineMode, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma dirichletMode_orthonormal {b : ℝ} (hb : 0 < b) (n m : ℕ) :
    (∫ x in Ioc 0 b, star (dirichletMode b n x) * dirichletMode b m x) =
      if n = m then 1 else 0 := by
  change (∫ x in Ioc 0 b, star (((Real.sqrt (b / 2))⁻¹ : ℝ) * sineMode b n x) *
    (((Real.sqrt (b / 2))⁻¹ : ℝ) * sineMode b m x)) = _
  have he (x : ℝ) : star ((((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ) * sineMode b n x) *
      ((((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ) * sineMode b m x) =
      ((((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ))^2 * (star (sineMode b n x) * sineMode b m x) := by
    rw [star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  simp_rw [he]
  rw [integral_const_mul, sineMode_inner hb]
  by_cases hnm : n = m
  · simp only [hnm, ite_true]
    have hn : Real.sqrt (b / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have hh : ((Real.sqrt (b / 2))⁻¹)^2 * (b / 2) = 1 := by
      have hw := Real.sq_sqrt (show 0 ≤ b / 2 by positivity)
      calc
        _ = ((Real.sqrt (b / 2))⁻¹)^2 * (Real.sqrt (b / 2))^2 :=
          congrArg (fun t : ℝ => ((Real.sqrt (b / 2))⁻¹)^2 * t) hw.symm
        _ = 1 := by field_simp
    exact_mod_cast hh
  · simp only [hnm, ite_false, mul_zero]

lemma dirichletMode_hasDerivAt (b : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (dirichletMode b n)
      ((((n : ℝ) + 1) * Real.pi / b : ℝ) * neumannMode b (n+1) x) x := by
  have hlin : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1) * Real.pi * y / b)
      (((n : ℝ) + 1) * Real.pi / b) x := by
    simpa only [id, mul_one] using
      ((hasDerivAt_id x).const_mul (((n : ℝ) + 1) * Real.pi)).div_const b
  have hh := ((Real.hasDerivAt_sin _).comp x hlin).ofReal_comp.const_mul
    ((((Real.sqrt (b / 2))⁻¹ : ℝ)) : ℂ)
  have he : ((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) * neumannMode b (n+1) x =
      (((Real.sqrt (b / 2))⁻¹ : ℝ) : ℂ) *
        ((Real.cos (((n : ℝ) + 1) * Real.pi * x / b) *
          (((n : ℝ) + 1) * Real.pi / b) : ℝ) : ℂ) := by
    simp only [neumannMode, cosineWeight, Nat.add_one_ne_zero, ite_false,
      cosineMode, Nat.cast_add, Nat.cast_one, Complex.ofReal_mul]
    ring
  rw [he]
  exact hh

lemma dirichletMode_endpoints {b : ℝ} (hb : 0 < b) (n : ℕ) :
    dirichletMode b n 0 = 0 ∧ dirichletMode b n b = 0 := by
  constructor
  · simp [dirichletMode, sineMode]
  · have he : ((n : ℝ) + 1) * Real.pi * b / b = (n + 1 : ℕ) * Real.pi := by
      push_cast
      field_simp
    simp only [dirichletMode, sineMode, he, Real.sin_nat_mul_pi,
      Complex.ofReal_zero, mul_zero]

lemma neumannMode_continuous (b : ℝ) (n : ℕ) :
    Continuous (neumannMode b n) :=
  continuous_const.mul (cosineMode_continuous b n)

lemma neumannMode_star_self (b : ℝ) (n : ℕ) (x : ℝ) :
    star (neumannMode b n x) = neumannMode b n x := by
  simp only [neumannMode, cosineMode, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma neumann_coefficient_derivative {b : ℝ} (hb : 0 < b) {f g : ℝ → ℂ}
    (hf : ∀ x ∈ Icc 0 b, HasDerivAt f (g x) x)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 b))) (n : ℕ) :
    ((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) *
      (∫ x in Ioc 0 b, star (neumannMode b (n+1) x) * f x) =
      -(∫ x in Ioc 0 b, star (dirichletMode b n x) * g x) := by
  have hu : ∀ x ∈ uIcc 0 b, HasDerivAt (dirichletMode b n)
      (((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) * neumannMode b (n+1) x) x := by
    intro x _
    exact dirichletMode_hasDerivAt b n x
  have hv : ∀ x ∈ uIcc 0 b, HasDerivAt f (g x) x := by
    simpa only [uIcc_of_le hb.le] using hf
  have hu' : IntervalIntegrable (fun x =>
      (((((n : ℝ) + 1) * Real.pi / b : ℝ) : ℂ) * neumannMode b (n+1) x)) volume 0 b :=
    (continuous_const.mul (neumannMode_continuous b (n+1))).intervalIntegrable _ _
  have hv' : IntervalIntegrable g volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
    exact hg.integrable (by norm_num)
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [(dirichletMode_endpoints hb n).1, (dirichletMode_endpoints hb n).2,
    zero_mul, zero_mul, sub_self, zero_sub] at he
  simp_rw [mul_assoc] at he
  rw [intervalIntegral.integral_const_mul] at he
  simp_rw [neumannMode_star_self, dirichletMode_star]
  rw [← intervalIntegral.integral_of_le hb.le,
    ← intervalIntegral.integral_of_le hb.le, he]
  simp

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CubeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
section TensorNeumann
variable {A ι : Type*} [MeasurableSpace A] {ν : Measure A} [SigmaFinite ν]

lemma tensorPair_inner {v v' : ℝ → ℂ} {w w' : A → ℂ} {b : ℝ}
    (_hv : MemLp v 2 (volume.restrict (Ioc 0 b)))
    (_hv' : MemLp v' 2 (volume.restrict (Ioc 0 b)))
    (_hw : MemLp w 2 ν) (_hw' : MemLp w' 2 ν) :
    (∫ z : A × ℝ, star (w z.1 * v z.2) * (w' z.1 * v' z.2)
      ∂(ν.prod (volume.restrict (Ioc 0 b)))) =
      (∫ a, star (w a) * w' a ∂ν) *
        (∫ x in Ioc 0 b, star (v x) * v' x) := by
  have he (z : A × ℝ) : star (w z.1 * v z.2) * (w' z.1 * v' z.2) =
      (star (w z.1) * w' z.1) * (star (v z.2) * v' z.2) := by
    rw [star_mul]; ring
  simp_rw [he]
  exact integral_prod_mul (fun a => star (w a) * w' a)
    (fun x => star (v x) * v' x)

end TensorNeumann

noncomputable def cubeMeasure (b : ℝ) (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => volume.restrict (Ioc 0 b)

instance cubeMeasure_isFiniteMeasure (b : ℝ) (d : ℕ) : IsFiniteMeasure (cubeMeasure b d) := by
  unfold cubeMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def cubeMode {d : ℕ} (b : ℝ) (q : Fin d → ℕ) (x : Fin d → ℝ) : ℂ :=
  ∏ i, neumannMode b (q i) (x i)

noncomputable def splitCube {d : ℕ} (i : Fin (d+1)) :
    (Fin (d+1) → ℝ) ≃ᵐ ((Fin d → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) i).trans
    (MeasurableEquiv.prodComm (α := ℝ) (β := Fin d → ℝ))

lemma splitCube_measurePreserving {b : ℝ} {d : ℕ} (i : Fin (d+1)) :
    MeasurePreserving (splitCube i) (cubeMeasure b (d+1))
      ((cubeMeasure b d).prod (volume.restrict (Ioc 0 b))) := by
  exact Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => volume.restrict (Ioc 0 b)) i)

lemma splitCube_symm_apply {d : ℕ} (i : Fin (d+1)) (x : Fin d → ℝ) (t : ℝ) :
    (splitCube i).symm (x,t) = Fin.insertNth i t x := rfl

lemma splitCube_apply {d : ℕ} (i : Fin (d+1)) (x : Fin (d+1) → ℝ) :
    splitCube i x = ((fun j => x (i.succAbove j)), x i) := rfl

lemma cubeMode_insertNth {d : ℕ} (b : ℝ) (i : Fin (d+1))
    (q : Fin d → ℕ) (m : ℕ) (x : Fin (d+1) → ℝ) :
    cubeMode b (Fin.insertNth i m q) x =
      cubeMode b q ((splitCube i x).1) * neumannMode b m ((splitCube i x).2) := by
  rw [splitCube_apply, cubeMode, Fin.prod_univ_succAbove _ i]
  simp [cubeMode, mul_comm]

open Filter

lemma integral_le_of_ae_tendsto_of_frequently_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} {F : ℕ → X → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hF : ∀ n, Integrable (F n) μ)
    (hn : ∀ n x, 0 ≤ F n x) (hf0 : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x)))
    (hC : ∃ᶠ n in atTop, (∫ x, F n x ∂μ) ≤ C) :
    (∫ x, f x ∂μ) ≤ C := by
  have hCn : 0 ≤ C := by
    obtain ⟨n, hn'⟩ := hC.exists
    exact (integral_nonneg (hn n)).trans hn'
  apply (ENNReal.ofReal_le_ofReal_iff hCn).1
  rw [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0)]
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal C := by
      apply liminf_le_of_frequently_le (hu_le := isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
      apply hC.mono
      intro n hn'
      rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Eventually.of_forall (hn n))]
      exact ENNReal.ofReal_le_ofReal hn'

theorem tendsto_integral_sq_sub_of_ae_of_sq_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} {F : ℕ → X → ℝ}
    (hf : MemLp f 2 μ) (hF : ∀ n, MemLp (F n) 2 μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds (f x)))
    (hb : ∀ n, (∫ x, (F n x)^2 ∂μ) ≤ ∫ x, (f x)^2 ∂μ) :
    Tendsto (fun n => ∫ x, (F n x - f x)^2 ∂μ) atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun x => sq_nonneg _)
  · intro ε hε
    by_contra hh
    have hfreq : ∃ᶠ n in atTop, ε ≤ ∫ x, (F n x - f x)^2 ∂μ := by
      simpa only [not_lt] using (not_eventually.mp hh)
    have hI (n : ℕ) :
        (∫ x, (F n x + f x)^2 ∂μ) + (∫ x, (F n x - f x)^2 ∂μ) =
        2 * (∫ x, (F n x)^2 ∂μ) + 2 * (∫ x, (f x)^2 ∂μ) := by
      have hp : Integrable (fun x => (F n x + f x)^2) μ := ((hF n).add hf).integrable_sq
      have hm : Integrable (fun x => (F n x - f x)^2) μ := ((hF n).sub hf).integrable_sq
      rw [← integral_add hp hm, ← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hF n).integrable_sq.const_mul 2) (hf.integrable_sq.const_mul 2)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    have hlt := integral_le_of_ae_tendsto_of_frequently_le μ
      (f := fun x => (2 * f x)^2) (F := fun n x => (F n x + f x)^2)
      (C := 4 * (∫ x, (f x)^2 ∂μ) - ε)
      (hf.const_mul 2).integrable_sq (fun n => ((hF n).add hf).integrable_sq)
      (fun n x => sq_nonneg _) (fun x => sq_nonneg _) ?_ ?_
    · have he : (∫ x, (2 * f x)^2 ∂μ) = 4 * ∫ x, (f x)^2 ∂μ := by
        simp_rw [mul_pow]
        norm_num
        rw [integral_const_mul]
      rw [he] at hlt
      linarith
    · filter_upwards [ht] with x hx
      simpa only [two_mul] using (hx.add_const (f x)).pow 2
    · apply hfreq.mono
      intro n hn
      linarith [hI n, hb n]

open scoped Convolution
open ContinuousLinearMap

lemma euclidean_convolution_sq_le {I : Type*} [Fintype I] (κ u : EuclideanSpace ℝ I → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2))
    (x : EuclideanSpace ℝ I) :
    ((κ ⋆ u) x)^2 ≤ (κ ⋆ (fun x => (u x)^2)) x := by
  have h1 : Integrable (fun y => κ (x-y) * u y) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu hκ x
  have h2 : Integrable (fun y => κ (x-y) * (u y)^2) := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul, mul_comm] using
      hκC.convolutionExists_right (lsmul ℝ ℝ) hu2.locallyIntegrable hκ x
  have h0 : Integrable (fun y => κ (x-y)) :=
    (hκ.integrable_of_hasCompactSupport hκC).comp_sub_left x
  have heq : (∫ y, κ (x-y) * u y) = (κ ⋆ u) x := by
    rw [convolution_eq_swap]
    rfl
  have heq0 : (∫ y, κ (x-y)) = 1 := by
    rw [integral_sub_left_eq_self, hκI]
  have hm : (∫ y, (2 * (κ ⋆ u) x) * (κ (x-y) * u y) -
      ((κ ⋆ u) x)^2 * κ (x-y)) ≤ ∫ y, κ (x-y) * (u y)^2 := by
    apply integral_mono ((h1.const_mul _).sub (h0.const_mul _)) h2
    intro y
    simp only [Pi.sub_apply]
    nlinarith [mul_nonneg (hκn (x-y)) (sq_nonneg (u y - (κ ⋆ u) x))]
  rw [integral_sub (h1.const_mul _) (h0.const_mul _), integral_const_mul,
    integral_const_mul, heq, heq0] at hm
  have heq2 : (κ ⋆ (fun x => (u x)^2)) x = ∫ y, κ (x-y) * (u y)^2 := by
    rw [convolution_eq_swap]
    rfl
  rw [heq2]
  nlinarith

lemma euclidean_convolution_sq_integral_le {I : Type*} [Fintype I] (κ u : EuclideanSpace ℝ I → ℝ)
    (hκ : Continuous κ) (hκC : HasCompactSupport κ)
    (hκn : ∀ x, 0 ≤ κ x) (hκI : (∫ x, κ x) = 1)
    (hu : LocallyIntegrable u) (hu2 : Integrable (fun x => (u x)^2)) :
    Integrable (fun x => ((κ ⋆ u) x)^2) ∧
    (∫ x, ((κ ⋆ u) x)^2) ≤ ∫ x, (u x)^2 := by
  have hdom : Integrable (κ ⋆ (fun x => (u x)^2)) :=
    (hκ.integrable_of_hasCompactSupport hκC).integrable_convolution (lsmul ℝ ℝ) hu2
  have hcont : Continuous (κ ⋆ u) :=
    hκC.continuous_convolution_left (lsmul ℝ ℝ) hκ hu
  have hsq : Integrable (fun x => ((κ ⋆ u) x)^2) := by
    apply hdom.mono' (hcont.pow 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact euclidean_convolution_sq_le κ u hκ hκC hκn hκI hu hu2 x
  refine ⟨hsq, ?_⟩
  calc
    _ ≤ ∫ x, (κ ⋆ (fun x => (u x)^2)) x :=
      integral_mono hsq hdom (euclidean_convolution_sq_le κ u hκ hκC hκn hκI hu hu2)
    _ = _ := by
      rw [integral_convolution (lsmul ℝ ℝ)
        (hκ.integrable_of_hasCompactSupport hκC) hu2, hκI]
      simp

lemma euclidean_real_convolution_comm {I : Type*} [Fintype I] (u κ : EuclideanSpace ℝ I → ℝ) :
    u ⋆ κ = κ ⋆ u := by
  ext x
  rw [convolution_eq_swap, convolution_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => mul_comm _ _)

lemma euclidean_fderiv_const_sub_comp {I : Type*} [Fintype I] (κ : EuclideanSpace ℝ I → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (x y v : EuclideanSpace ℝ I) :
    fderiv ℝ (fun z => κ (x - z)) y v = -(fderiv ℝ κ (x-y) v) := by
  have hd := ((hκ.differentiable (by simp) (x-y)).hasFDerivAt).comp y
    ((hasFDerivAt_id y).const_sub x)
  change HasFDerivAt (fun z => κ (x-z)) _ y at hd
  rw [hd.fderiv]
  simp

lemma euclidean_weak_convolution_partial {I : Type*} [Fintype I] (u g κ : EuclideanSpace ℝ I → ℝ)
    (v : EuclideanSpace ℝ I) (hu : LocallyIntegrable u)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκC : HasCompactSupport κ)
    (hw : ∀ φ : EuclideanSpace ℝ I → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (x : EuclideanSpace ℝ I) :
    fderiv ℝ (κ ⋆ u) x v = (κ ⋆ g) x := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (x-y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hφC : HasCompactSupport (fun y => κ (x-y)) :=
    hκC.comp_homeomorph (Homeomorph.subLeft x)
  have ht := hw (fun y => κ (x-y)) hφ hφC
  simp_rw [euclidean_fderiv_const_sub_comp κ hκ x] at ht
  simp only [mul_neg, integral_neg, neg_inj] at ht
  rw [euclidean_real_convolution_comm κ u,
    (hκC.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hκ.of_le (by simp)) x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hu (hκC.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)) x v]
  rw [euclidean_real_convolution_comm κ g]
  simpa only [convolution_def, lsmul_apply, smul_eq_mul] using ht

noncomputable def euclideanMollifier {I : Type*} [Fintype I] (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ I) where
  rIn := 1 / ((k : ℝ) + 1)
  rOut := 2 / ((k : ℝ) + 1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

lemma euclideanMollifier_tendsto {I : Type*} [Fintype I] :
    Filter.Tendsto (fun k => (euclideanMollifier (I := I) k).rOut) Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [euclideanMollifier, mul_one_div, mul_zero] using h

noncomputable def realMollify {I : Type*} [Fintype I] (k : ℕ)
    (u : EuclideanSpace ℝ I → ℝ) : EuclideanSpace ℝ I → ℝ :=
  (euclideanMollifier k).normed volume ⋆ u

lemma realMollify_contDiff {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    ContDiff ℝ (⊤ : ℕ∞) (realMollify k u) :=
  (euclideanMollifier k).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (euclideanMollifier k).contDiff_normed (hu.locallyIntegrable (by norm_num))

lemma realMollify_memLp {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    MemLp (realMollify k u) 2 := by
  apply (memLp_two_iff_integrable_sq (realMollify_contDiff k hu).continuous.aestronglyMeasurable).2
  exact (euclidean_convolution_sq_integral_le (I := I)
    ((euclideanMollifier (I := I) k).normed volume) u
    ((euclideanMollifier (I := I) k).contDiff_normed (n := (⊤ : ℕ∞))).continuous (euclideanMollifier k).hasCompactSupport_normed
    (euclideanMollifier k).nonneg_normed (euclideanMollifier k).integral_normed
    (hu.locallyIntegrable (by norm_num)) hu.integrable_sq).1

lemma realMollify_sq_integral_le {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    (∫ x, (realMollify k u x)^2) ≤ ∫ x, (u x)^2 :=
  (euclidean_convolution_sq_integral_le (I := I)
    ((euclideanMollifier (I := I) k).normed volume) u
    ((euclideanMollifier (I := I) k).contDiff_normed (n := (⊤ : ℕ∞))).continuous (euclideanMollifier k).hasCompactSupport_normed
    (euclideanMollifier k).nonneg_normed (euclideanMollifier k).integral_normed
    (hu.locallyIntegrable (by norm_num)) hu.integrable_sq).2

lemma realMollify_ae_tendsto {I : Type*} [Fintype I]
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    ∀ᵐ x ∂volume, Tendsto (fun k => realMollify k u x) atTop (nhds (u x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun k => euclideanMollifier k) (K := 2) euclideanMollifier_tendsto _
    (hu.locallyIntegrable (by norm_num))
  exact Eventually.of_forall fun k => by simp [euclideanMollifier, div_eq_mul_inv]

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ComplexMollify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

theorem realMollify_L2_tendsto {I : Type*} [Fintype I]
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    Tendsto (fun k => ∫ x, (realMollify k u x - u x)^2) atTop (nhds 0) :=
  tendsto_integral_sq_sub_of_ae_of_sq_le hu (fun k => realMollify_memLp k hu)
    (realMollify_ae_tendsto hu) (fun k => realMollify_sq_integral_le k hu)

noncomputable def complexMollify {I : Type*} [Fintype I] (k : ℕ)
    (u : EuclideanSpace ℝ I → ℂ) : EuclideanSpace ℝ I → ℂ :=
  fun x => (realMollify k (fun y => (u y).re) x : ℂ) +
    (realMollify k (fun y => (u y).im) x : ℂ) * Complex.I

lemma complexMollify_contDiff {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) :
    ContDiff ℝ (⊤ : ℕ∞) (complexMollify k u) := by
  exact (Complex.ofRealCLM.contDiff.comp (realMollify_contDiff k
    (Complex.reCLM.comp_memLp' hu))).add
      ((Complex.ofRealCLM.contDiff.comp (realMollify_contDiff k
        (Complex.imCLM.comp_memLp' hu))).mul contDiff_const)

lemma complexMollify_memLp {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) :
    MemLp (complexMollify k u) 2 := by
  exact (Complex.ofRealCLM.comp_memLp' (realMollify_memLp k (Complex.reCLM.comp_memLp' hu))).add
    ((Complex.ofRealCLM.comp_memLp' (realMollify_memLp k
      (Complex.imCLM.comp_memLp' hu))).mul_const Complex.I)

lemma integral_sq_sub_restrict_tendsto {A : Type*} [MeasurableSpace A] {μ ν : Measure A}
    (hμ : ν ≤ μ) {f : A → ℂ} {F : ℕ → A → ℂ}
    (hf : MemLp f 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂ν) atTop (nhds 0) := by
  apply squeeze_zero (fun k => integral_nonneg fun _ => sq_nonneg _) _ h
  intro k
  exact integral_mono_measure hμ (Eventually.of_forall fun _ => sq_nonneg _)
    ((hF k).sub hf).norm.integrable_sq

lemma mollify_realCLM_mul_ofReal (L : ℂ →L[ℝ] ℝ) (z : ℂ) (t : ℝ) :
    L (z * (t : ℂ)) = L z * t := by
  rw [mul_comm, mul_comm (L z)]
  exact L.map_smul t z

lemma euclidean_weak_complex_component {I : Type*} [Fintype I] (u g : EuclideanSpace ℝ I → ℂ)
    (hu : MemLp u 2) (hg : MemLp g 2) (v : EuclideanSpace ℝ I)
    (hw : ∀ (φ : EuclideanSpace ℝ I → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) (φ : EuclideanSpace ℝ I → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x, L (u x) * fderiv ℝ φ x v) = -(∫ x, L (g x) * φ x) := by
  have hφL : MemLp (fun x => (φ x : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hφC.comp_left (by simp))
  have hdφL : MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hφC.fderiv_apply ℝ v).comp_left (by simp))
  have hA := L.integral_comp_comm (hu.integrable_mul hdφL)
  have hB := L.integral_comp_comm (hg.integrable_mul hφL)
  simp only [Pi.mul_apply, mollify_realCLM_mul_ofReal] at hA hB
  rw [hA, hw φ hφ hφC, map_neg, ← hB]

lemma realMollify_fderiv {I : Type*} [Fintype I] (k : ℕ)
    {u g : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) (v : EuclideanSpace ℝ I)
    (hw : ∀ φ : EuclideanSpace ℝ I → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (x : EuclideanSpace ℝ I) :
    fderiv ℝ (realMollify k u) x v = realMollify k g x := by
  exact euclidean_weak_convolution_partial u g ((euclideanMollifier k).normed volume) v
    (hu.locallyIntegrable (by norm_num)) (euclideanMollifier k).contDiff_normed
    (euclideanMollifier k).hasCompactSupport_normed hw x

lemma complexMollify_fderiv {I : Type*} [Fintype I] (k : ℕ)
    {u g : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) (hg : MemLp g 2)
    (v : EuclideanSpace ℝ I)
    (hw : ∀ φ : EuclideanSpace ℝ I → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    (x : EuclideanSpace ℝ I) :
    fderiv ℝ (complexMollify k u) x v = complexMollify k g x := by
  have hr : MemLp (fun x => (u x).re) 2 := Complex.reCLM.comp_memLp' hu
  have hi : MemLp (fun x => (u x).im) 2 := Complex.imCLM.comp_memLp' hu
  have hwr := euclidean_weak_complex_component u g hu hg v hw Complex.reCLM
  have hwi := euclidean_weak_complex_component u g hu hg v hw Complex.imCLM
  have hfr := (realMollify_contDiff k hr).differentiable (by simp)
  have hfi := (realMollify_contDiff k hi).differentiable (by simp)
  have hR := Complex.ofRealCLM.hasFDerivAt.comp x ((hfr x).hasFDerivAt)
  have hJ := Complex.ofRealCLM.hasFDerivAt.comp x ((hfi x).hasFDerivAt)
  have ht := hR.add (hJ.mul_const Complex.I)
  change HasFDerivAt (complexMollify k u) _ x at ht
  rw [ht.fderiv]
  change ((fderiv ℝ (realMollify k (fun y => (u y).re)) x v : ℝ) : ℂ) +
    Complex.I * ((fderiv ℝ (realMollify k (fun y => (u y).im)) x v : ℝ) : ℂ) = _
  rw [realMollify_fderiv k hr v hwr x, realMollify_fderiv k hi v hwi x]
  simp only [complexMollify, Complex.reCLM_apply, Complex.imCLM_apply, mul_comm]

lemma cubeMeasure_le_volume {b : ℝ} {d : ℕ} :
    cubeMeasure b d ≤ (volume : Measure (Fin d → ℝ)) := by
  unfold cubeMeasure
  rw [← Measure.restrict_pi_pi]
  exact Measure.restrict_le_self

lemma insertNth_path_hasDerivAt {d : ℕ} (i : Fin (d+1)) (x : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun t => (WithLp.toLp 2 (Fin.insertNth i t x) : EuclideanSpace ℝ (Fin (d+1))))
      (EuclideanSpace.single i 1) t := by
  classical
  have he : (fun t => (WithLp.toLp 2 (Fin.insertNth i t x) : EuclideanSpace ℝ (Fin (d+1)))) =
      (fun t => t • EuclideanSpace.single i 1 + WithLp.toLp 2 (Fin.insertNth i 0 x)) := by
    funext t
    ext j
    obtain rfl | ⟨j, rfl⟩ := i.eq_self_or_eq_succAbove j
    · simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, Fin.succAbove_ne]
  rw [he]
  simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).add_const
    (WithLp.toLp 2 (Fin.insertNth i 0 x) : EuclideanSpace ℝ (Fin (d+1)))

lemma euclidean_hasDerivAt_insertNth {d : ℕ} (i : Fin (d+1)) (x : Fin d → ℝ) (t : ℝ)
    {f : EuclideanSpace ℝ (Fin (d+1)) → ℂ} (hf : Differentiable ℝ f) :
    HasDerivAt (fun t => f (WithLp.toLp 2 (Fin.insertNth i t x)))
      (fderiv ℝ f (WithLp.toLp 2 (Fin.insertNth i t x)) (EuclideanSpace.single i 1)) t := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt t (insertNth_path_hasDerivAt i x t)

noncomputable def latticeRadius (q : Fin 3 → ℕ) : ℝ :=
  ‖WithLp.toLp 2 (fun i => (q i : ℝ))‖

def integerCell (m : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (m i : ℝ) ((m i : ℝ) + 1))

lemma integerCell_measurable (m : Fin 3 → ℤ) : MeasurableSet (integerCell m) := by
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

lemma integerCell_volume (m : Fin 3 → ℤ) : volume (integerCell m) = 1 := by
  simp [integerCell, Real.volume_pi_Ioc]

lemma integerCell_disjoint {m n : Fin 3 → ℤ} (hmn : m ≠ n) :
    Disjoint (integerCell m) (integerCell n) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hm := hx i (Set.mem_univ i)
  have hn := hy i (Set.mem_univ i)
  rcases lt_or_gt_of_ne hi with h | h
  · have hle : (m i : ℝ) + 1 ≤ (n i : ℝ) := by exact_mod_cast h
    linarith [hm.2, hn.1]
  · have hle : (n i : ℝ) + 1 ≤ (m i : ℝ) := by exact_mod_cast h
    linarith [hn.2, hm.1]

lemma piEuclidean_closedBall_volume (r : ℝ) :
    volume {x : Fin 3 → ℝ | ‖WithLp.toLp 2 x‖ ≤ r} =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  have h := PiLp.volume_preserving_toLp (Fin 3)
  have he : {x : Fin 3 → ℝ | ‖WithLp.toLp 2 x‖ ≤ r} =
      (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [he, h.measure_preimage (measurableSet_closedBall.nullMeasurableSet),
    EuclideanSpace.volume_closedBall_fin_three]

lemma integerCell_card_le_ball_volume (s : Finset (Fin 3 → ℤ)) (r : ℝ)
    (hs : ∀ m ∈ s, integerCell m ⊆ {x | ‖WithLp.toLp 2 x‖ ≤ r}) :
    (s.card : ℝ≥0∞) ≤ ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  have hd : Set.PairwiseDisjoint (↑s) integerCell := by
    intro m _ n _ hmn
    exact integerCell_disjoint hmn
  have hv : volume (⋃ m ∈ s, integerCell m) = (s.card : ℝ≥0∞) := by
    rw [measure_biUnion_finset hd (fun m _ => integerCell_measurable m)]
    simp [integerCell_volume]
  rw [← piEuclidean_closedBall_volume r, ← hv]
  apply measure_mono
  exact Set.iUnion₂_subset (fun m hm => hs m hm)

def signedCoordinate (b : Bool) (q : ℕ) : ℤ := if b then q else -(q : ℤ) - 1

lemma signedCoordinate_injective : Function.Injective (fun p : Bool × ℕ => signedCoordinate p.1 p.2) := by
  rintro ⟨a, m⟩ ⟨b, n⟩ h
  cases a <;> cases b <;> simp [signedCoordinate] at h ⊢ <;> omega

def signedLattice (a : (Fin 3 → Bool) × (Fin 3 → ℕ)) : Fin 3 → ℤ :=
  fun i => signedCoordinate (a.1 i) (a.2 i)

lemma signedLattice_injective : Function.Injective signedLattice := by
  intro a b h
  have hi (i : Fin 3) : (a.1 i, a.2 i) = (b.1 i, b.2 i) :=
    signedCoordinate_injective (congrFun h i)
  apply Prod.ext <;> funext i
  · exact congrArg Prod.fst (hi i)
  · exact congrArg Prod.snd (hi i)

lemma signedCell_abs_le {a : (Fin 3 → Bool) × (Fin 3 → ℕ)}
    {x : Fin 3 → ℝ} (hx : x ∈ integerCell (signedLattice a)) (i : Fin 3) :
    |x i| ≤ (a.2 i : ℝ) + 1 := by
  have h := hx i (Set.mem_univ i)
  change (signedCoordinate (a.1 i) (a.2 i) : ℝ) < x i ∧
    x i ≤ (signedCoordinate (a.1 i) (a.2 i) : ℝ) + 1 at h
  cases hd : a.1 i <;> simp [signedCoordinate, hd] at h
  · apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (a.2 i)]
  · apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (a.2 i)]

lemma signedCell_radius_le {a : (Fin 3 → Bool) × (Fin 3 → ℕ)}
    {x : Fin 3 → ℝ} (hx : x ∈ integerCell (signedLattice a)) :
    ‖WithLp.toLp 2 x‖ ≤ latticeRadius a.2 + Real.sqrt 3 := by
  let q : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => (a.2 i : ℝ))
  let e : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun _ => 1)
  have hle : ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖q+e‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change ‖x i‖^2 ≤ ‖(a.2 i : ℝ) + 1‖^2
    simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (a.2 i : ℝ) + 1 by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) (signedCell_abs_le hx i) 2
  have hnorm : ‖WithLp.toLp 2 x‖ ≤ ‖q+e‖ := by
    nlinarith [norm_nonneg (q+e), norm_nonneg (WithLp.toLp 2 x)]
  have he : ‖e‖ = Real.sqrt 3 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [e, Fin.sum_univ_succ]
  calc
    ‖WithLp.toLp 2 x‖ ≤ ‖q+e‖ := hnorm
    _ ≤ ‖q‖ + ‖e‖ := norm_add_le q e
    _ = latticeRadius a.2 + Real.sqrt 3 := by rw [he]; rfl

theorem spin_two_lattice_count (s : Finset (Fin 3 → ℕ)) {r : ℝ}
    (hr : 0 ≤ r) (hs : ∀ q ∈ s, latticeRadius q ≤ r) :
    2 * (s.card : ℝ) ≤ (Real.pi / 3) * (r + Real.sqrt 3)^3 := by
  classical
  let a : Finset ((Fin 3 → Bool) × (Fin 3 → ℕ)) := Finset.univ ×ˢ s
  let t := a.image signedLattice
  have H := integerCell_card_le_ball_volume t (r + Real.sqrt 3) (by
    intro m hm x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have h := signedCell_radius_le hx
    exact h.trans (add_le_add (hs p.2 (Finset.mem_product.mp hp).2) le_rfl))
  have ht : t.card = 8 * s.card := by
    rw [Finset.card_image_of_injective _ signedLattice_injective, Finset.card_product]
    simp
  rw [ht] at H
  have hR : 0 ≤ r + Real.sqrt 3 := by positivity
  have hp : 0 ≤ Real.pi * 4 / 3 := by positivity
  rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (pow_nonneg hR 3)] at H
  have hnat : ((8 * s.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal (8 * (s.card : ℝ)) := by
    simp
  rw [hnat] at H
  have HH := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hR 3) hp)).mp H
  nlinarith

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PairRegroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable def pairRegroup {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D) where
  toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2))); fun_prop
  measurable_invFun := by change Measurable (fun p : (A × C) × (B × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2))); fun_prop
lemma pairRegroup_measurePreserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μa : Measure A) (μb : Measure B)
    (μc : Measure C) (μd : Measure D) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (pairRegroup : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

lemma integrable_finite_count_prod {S E F : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {μ : Measure E} (f : S × E → F)
    (hf : ∀ s, Integrable (fun x => f (s,x)) μ) : Integrable f (Measure.count.prod μ) := by
  rw [Measure.prod, Measure.count,
    Measure.bind_sum _ _ (measurable_of_countable _).aemeasurable]
  simp only [Measure.dirac_bind (measurable_of_countable _)]
  refine integrable_sum_measure (fun spin => ?_) (hasSum_fintype _).summable
  exact (measurableEmbedding_prodMk_left spin).integrable_map_iff.mpr (hf spin)

lemma integral_finite_count_prod {S E F : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {μ : Measure E} [SFinite μ] (f : S × E → F)
    (hf : ∀ s, Integrable (fun x => f (s,x)) μ) :
    (∫ sx, f sx ∂(Measure.count.prod μ)) = ∑ s, ∫ x, f (s,x) ∂μ := by
  rw [integral_prod _ (integrable_finite_count_prod f hf), integral_count]
lemma count_prod_count {S T : Type*} [Countable S] [Countable T] [MeasurableSpace S]
    [MeasurableSpace T] [MeasurableSingletonClass S] [MeasurableSingletonClass T] :
    (Measure.count : Measure S).prod (Measure.count : Measure T) = Measure.count := by
  apply Measure.ext_of_singleton
  intro st
  rw [← singleton_prod_singleton, Measure.prod_prod]
  simp
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_DeterminantWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def determinantWave {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : ℂ := Matrix.det (fun i j => v i (x j))

lemma determinantWave_expansion {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : determinantWave v x =
    ∑ p : Equiv.Perm (Fin n), ((p.sign : ℤ) : ℂ) * ∏ i, v (p i) (x i) :=
  Matrix.det_apply' _

lemma determinantWave_permute {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (x : Fin n → A) :
    determinantWave v (x ∘ p) = ((p.sign : ℤ) : ℂ) * determinantWave v x := by
  exact Matrix.det_permute' p (fun i j => v i (x j))

lemma determinantWave_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) :
    MemLp (determinantWave v) 2 (Measure.pi fun _ : Fin n => μ) := by
  change MemLp (fun x => determinantWave v x) 2 _
  simp_rw [determinantWave_expansion]
  exact memLp_finsetSum _ (fun p _ => (scalarTensor_memLp v hv p).const_mul _)

lemma sign_star_mul {n : ℕ} (p : Equiv.Perm (Fin n)) :
    star (((p.sign : ℤ) : ℂ)) * (((p.sign : ℤ) : ℂ)) = 1 := by
  rcases Int.units_eq_one_or p.sign with h | h <;> simp [h]

noncomputable def slaterWave {A : Type*} {n : ℕ} (v : Fin n → A → ℂ)
    (x : Fin n → A) : ℂ := (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * determinantWave v x

lemma perm_eq_of_eq_off {α : Type*} (p q : Equiv.Perm α) (i : α)
    (h : ∀ j, j ≠ i → p j = q j) : p = q := by
  apply Equiv.ext
  intro j
  by_cases hj : j = i
  · subst j
    by_cases hk : q.symm (p i) = i
    · simpa only [hk] using (q.apply_symm_apply (p i)).symm
    · have he : p (q.symm (p i)) = p i := (h _ hk).trans (q.apply_symm_apply _)
      exact False.elim (hk (p.injective he))
  · exact h j hj

lemma determinant_bilinear_expansion {A : Type*} {n : ℕ}
    (v u : Fin n → A → ℂ) (x y : Fin n → A) :
    star (determinantWave v x) * determinantWave u y =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          (star (∏ i, v (p i) (x i)) * ∏ i, u (q i) (y i)) := by
  simp only [determinantWave_expansion, star_sum, star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma determinant_one_body_expansion {A : Type*} {n : ℕ}
    (v : Fin n → A → ℂ) (w : A → ℂ) (x : Fin n → A) :
    (∑ i, w (x i)) * (star (determinantWave v x) * determinantWave v x) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j)) := by
  rw [determinant_bilinear_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma latticeRadius_nonneg (q : Fin 3 → ℕ) : 0 ≤ latticeRadius q := norm_nonneg _

lemma sum_two_thirds_lower (n : ℕ) :
    (3/5 : ℝ) * (n : ℝ) ^ (5/3 : ℝ) ≤
      ∑ i ∈ Finset.range n, ((i+1 : ℕ) : ℝ) ^ (2/3 : ℝ) := by
  have hm : MonotoneOn (fun x : ℝ => x ^ (2/3 : ℝ)) (Set.Icc 0 (0+n)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow hx.1 hxy (by norm_num)
  have h := hm.integral_le_sum
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 2/3))] at h
  norm_num at h ⊢
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma sum_one_third_upper (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) ≤
      (n : ℝ) ^ (4/3 : ℝ) := by
  have H : (∑ i ∈ Finset.range n, ((i+1 : ℕ) : ℝ) ^ (1/3 : ℝ)) ≤
      ∑ _ ∈ Finset.range n, (n : ℝ) ^ (1/3 : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact_mod_cast (show i+1 ≤ n from Nat.succ_le_of_lt (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rw [show (4/3 : ℝ) = 1 + 1/3 by norm_num,
    Real.rpow_add' (Nat.cast_nonneg n) (by norm_num : (1 : ℝ)+1/3 ≠ 0), Real.rpow_one]

lemma square_lower_of_shift {r t c : ℝ} (_hr : 0 ≤ r) (ht : 0 ≤ t) (_hc : 0 ≤ c)
    (h : t ≤ r+c) : t^2 - 2*c*t ≤ r^2 := by
  by_cases htc : t ≤ c
  · nlinarith [mul_nonneg (sub_nonneg.mpr htc) ht, sq_nonneg r]
  · have h2 := pow_le_pow_left₀ (sub_nonneg.mpr (le_of_not_ge htc))
      (show t-c ≤ r by linarith) 2
    nlinarith [sq_nonneg c]

lemma finite_sort_values {n : ℕ} (v : Fin n → ℝ) :
    ∃ e : Equiv.Perm (Fin n), Monotone (fun i => v (e i)) := by
  classical
  let key : Fin n → ℝ ×ₗ Fin n := fun i => toLex (v i, i)
  have hk : Function.Injective key := by
    intro i j h
    exact congrArg (fun z => (ofLex z).2) h
  let s := Finset.univ.image key
  have hs : s.card = n := by
    simp only [s, Finset.card_image_of_injective _ hk, Finset.card_univ, Fintype.card_fin]
  let b := s.orderEmbOfFin hs
  have hb (i : Fin n) : key (ofLex (b i)).2 = b i := by
    have hi := s.orderEmbOfFin_mem hs i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    rw [← hj]
    rfl
  let e : Fin n → Fin n := fun i => (ofLex (b i)).2
  have he : Function.Injective e := by
    intro i j hij
    apply b.injective
    rw [← hb i, ← hb j]
    exact congrArg key hij
  let E : Equiv.Perm (Fin n) := Equiv.ofBijective e
    ⟨he, (Finite.injective_iff_surjective).mp he⟩
  refine ⟨E, ?_⟩
  intro i j hij
  have H := b.monotone hij
  have hi : v (E i) = (ofLex (b i)).1 := by
    exact congrArg (fun z => (ofLex z).1) (hb i)
  have hj : v (E j) = (ofLex (b j)).1 := by
    exact congrArg (fun z => (ofLex z).1) (hb j)
  change v (E i) ≤ v (E j)
  rw [hi, hj]
  rcases Prod.Lex.le_iff.mp H with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

noncomputable def neumannLeading : ℝ := (3/5 : ℝ) * (3/Real.pi) ^ (2/3 : ℝ)
noncomputable def neumannBoundary : ℝ := 2 * Real.sqrt 3 * (3/Real.pi) ^ (1/3 : ℝ)

section IndexBridge
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def finiteCubeMeasure (b : ℝ) (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Ioc 0 b))

noncomputable def finiteCubeMode (b : ℝ) (q : I → ℕ) (x : I → ℝ) : ℂ :=
  ∏ i, neumannMode b (q i) (x i)

noncomputable def reindexCube (e : I ≃ J) : (I → ℝ) ≃ᵐ (J → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma reindexCube_apply (e : I ≃ J) (x : I → ℝ) (j : J) :
    reindexCube e x j = x (e.symm j) := by
  simpa only [reindexCube, e.apply_symm_apply] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : J => ℝ) e x (e.symm j)

omit [DecidableEq I] [DecidableEq J] in
lemma reindexCube_measurePreserving (b : ℝ) (e : I ≃ J) :
    MeasurePreserving (reindexCube e) (finiteCubeMeasure b I) (finiteCubeMeasure b J) := by
  exact measurePreserving_piCongrLeft (fun _ : J => volume.restrict (Ioc 0 b)) e

omit [DecidableEq I] [DecidableEq J] in
lemma finiteCubeMode_reindex (b : ℝ) (e : I ≃ J) (q : I → ℕ) (x : I → ℝ) :
    finiteCubeMode b (q ∘ e.symm) (reindexCube e x) = finiteCubeMode b q x := by
  simpa only [finiteCubeMode, Function.comp_apply, reindexCube_apply] using
    Equiv.prod_comp e.symm (fun i => neumannMode b (q i) (x i))

omit [DecidableEq I] [DecidableEq J] in
lemma euclidean_reindex_toLp_cancel (e : I ≃ J) (x : I → ℝ) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 (reindexCube e x)) =
      WithLp.toLp 2 x := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', reindexCube_apply]

omit [DecidableEq I] [DecidableEq J] in
lemma finiteCube_integral_reindex (b : ℝ) (e : I ≃ J)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ I → E) :
    (∫ y, f (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y))
      ∂(finiteCubeMeasure b J)) =
      ∫ x, f (WithLp.toLp 2 x) ∂(finiteCubeMeasure b I) := by
  rw [← (reindexCube_measurePreserving b e).integral_comp'
    (fun y => f (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y)))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by dsimp only; rw [euclidean_reindex_toLp_cancel])

omit [DecidableEq I] [DecidableEq J] in
lemma finiteCube_coefficient_reindex (b : ℝ) (e : I ≃ J)
    (u : EuclideanSpace ℝ I → ℂ) (q : I → ℕ) :
    (∫ y, star (finiteCubeMode b (q ∘ e.symm) y) *
      u (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y))
      ∂(finiteCubeMeasure b J)) =
      ∫ x, star (finiteCubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(finiteCubeMeasure b I) := by
  rw [← (reindexCube_measurePreserving b e).integral_comp'
    (fun y => star (finiteCubeMode b (q ∘ e.symm) y) *
      u (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm (WithLp.toLp 2 y)))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by dsimp only; rw [finiteCubeMode_reindex, euclidean_reindex_toLp_cancel])

lemma euclidean_weak_reindex (e : I ≃ J) {u : EuclideanSpace ℝ I → ℂ}
    {g : I → EuclideanSpace ℝ I → ℂ}
    (hw : ∀ i (φ : EuclideanSpace ℝ I → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g i x * (φ x : ℂ))) (j : J)
    (φ : EuclideanSpace ℝ J → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, u (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm x) *
      (fderiv ℝ φ x (EuclideanSpace.single j 1) : ℂ)) =
      -(∫ x, g (e.symm j) (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm x) * (φ x : ℂ)) := by
  classical
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ L) :=
    hφ.comp L.contDiff
  have hc : HasCompactSupport (φ ∘ L) := hφc.comp_homeomorph L.toHomeomorph
  have H := hw (e.symm j) (φ ∘ L) hcomp hc
  have hd (x : EuclideanSpace ℝ I) :
      fderiv ℝ (φ ∘ L) x (EuclideanSpace.single (e.symm j) 1) =
      fderiv ℝ φ (L x) (EuclideanSpace.single j 1) := by
    rw [fderiv_comp x (hφ.differentiable (by simp) _) L.differentiableAt]
    rw [L.fderiv]
    change fderiv ℝ φ (L x) (L (EuclideanSpace.single (e.symm j) 1)) = _
    have hs : L (EuclideanSpace.single (e.symm j) 1) = EuclideanSpace.single j 1 := by
      simp [L, EuclideanSpace.single, LinearIsometryEquiv.piLpCongrLeft_single]
    rw [hs]
  simp_rw [hd] at H
  have hp : MeasurePreserving L.symm.toHomeomorph.toMeasurableEquiv volume volume :=
    L.symm.measurePreserving
  rw [← hp.integral_comp' (fun x => u x * (fderiv ℝ φ (L x) (EuclideanSpace.single j 1) : ℂ)),
      ← hp.integral_comp' (fun x => g (e.symm j) x * ((φ ∘ L) x : ℂ))] at H
  change (∫ x, u (L.symm x) *
    (fderiv ℝ φ (L (L.symm x)) (EuclideanSpace.single j 1) : ℂ)) =
    -(∫ x, g (e.symm j) (L.symm x) * (φ (L (L.symm x)) : ℂ)) at H
  simp_rw [L.apply_symm_apply] at H
  simpa only [L, LinearIsometryEquiv.piLpCongrLeft_symm] using H

end IndexBridge

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CubeLabelEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

section FiniteCubeBasis
variable {I : Type*} [Fintype I]

lemma finiteCubeMeasure_le_volume (b : ℝ) :
    finiteCubeMeasure b I ≤ (volume : Measure (I → ℝ)) := by
  unfold finiteCubeMeasure
  rw [← Measure.restrict_pi_pi]
  exact Measure.restrict_le_self

lemma finiteCubeMode_memLp (b : ℝ) (q : I → ℕ) :
    MemLp (finiteCubeMode b q) 2 (finiteCubeMeasure b I) := by
  have hm : AEStronglyMeasurable (finiteCubeMode b q) (finiteCubeMeasure b I) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (neumannMode_memLp b (q i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : I => volume.restrict (Ioc 0 b)) i)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [finiteCubeMode, finiteCubeMeasure, norm_prod, ← Finset.prod_pow] using
    Integrable.fintype_prod (fun i => (neumannMode_memLp b (q i)).norm.integrable_sq)

end FiniteCubeBasis

lemma configuration_nonempty_equiv {n : ℕ} (hn : 0 < n) :
    Nonempty ((Fin n × Fin 3) ≃ Fin ((3*n-1)+1)) := by
  have hc : Fintype.card (Fin n × Fin 3) = (3*n-1)+1 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  exact ⟨(Fintype.equivFin _).trans (finCongr hc)⟩

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinCubeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb
lemma measurePreserving_const_uncurry {I J A : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry I J A).symm
      (Measure.pi fun _ : I => Measure.pi fun _ : J => μ)
      (Measure.pi fun _ : I × J => μ) := by
  refine ⟨(MeasurableEquiv.curry I J A).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [(MeasurableEquiv.curry I J A).symm.map_apply]
  have he : (MeasurableEquiv.curry I J A).symm ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext x
    simp only [mem_preimage, mem_univ_pi, MeasurableEquiv.curry_symm_apply]
    exact ⟨fun h i j => h (i,j), fun h p => h p.1 p.2⟩
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

lemma measure_pi_count {I A : Type*} [Fintype I] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    (Measure.pi fun _ : I => (Measure.count : Measure A)) = Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

instance finiteCubeMeasure_isFinite (b : ℝ) (I : Type*) [Fintype I] :
    IsFiniteMeasure (finiteCubeMeasure b I) := by
  unfold finiteCubeMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Translate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

noncomputable def spinSpaceMeasure : Measure (Fin 2 × (Fin 3 → ℝ)) := Measure.count.prod volume
instance spinSpaceMeasure_sigmaFinite : SigmaFinite spinSpaceMeasure := by
  unfold spinSpaceMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SmoothCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma tensor_compact_support {A : Type*} [TopologicalSpace A] [T2Space A]
    {n : ℕ} (f : Fin n → A → ℂ) (hC : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x : Fin n → A => ∏ i, f i (x i)) := by
  apply HasCompactSupport.intro (isCompact_univ_pi (fun i => (hC i).isCompact))
  intro x hx
  have hn : ¬ ∀ i, x i ∈ tsupport (f i) := by simpa only [mem_univ_pi] using hx
  obtain ⟨i,hi⟩ := not_forall.mp hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PermOrCompSwapOffTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma perm_eq_or_comp_swap_of_eq_off_two {α : Type*} [DecidableEq α]
    (p q : Equiv.Perm α) (i j : α) (_hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → p k = q k) :
    q = p ∨ q = p * Equiv.swap i j := by
  by_cases hi : p i = q i
  · left
    symm
    apply perm_eq_of_eq_off p q j
    intro k hkj
    by_cases hki : k = i
    · simpa only [hki] using hi
    · exact h k hki hkj
  · right
    have hki : q.symm (p i) ≠ i := by
      intro he
      apply hi
      simpa only [he] using (q.apply_symm_apply (p i)).symm
    have hkj : q.symm (p i) = j := by
      by_contra he
      have H : p (q.symm (p i)) = p i := (h _ hki he).trans (q.apply_symm_apply _)
      exact hki (p.injective H)
    have hji : p i = q j := by simpa only [hkj] using (q.apply_symm_apply (p i)).symm
    have hE : p = q * Equiv.swap i j := by
      apply perm_eq_of_eq_off p (q * Equiv.swap i j) j
      intro k hkj'
      by_cases hki' : k = i
      · subst k
        simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using hji
      · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki' hkj'] using h k hki' hkj'
    rw [hE, mul_assoc, Equiv.swap_mul_self, mul_one]

lemma perm_mul_swap_ne {α : Type*} [DecidableEq α] (p : Equiv.Perm α)
    (i j : α) (hij : i ≠ j) : p * Equiv.swap i j ≠ p := by
  intro h
  have H := congrArg (fun r : Equiv.Perm α => r i) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at H
  exact hij (p.injective H).symm

lemma sign_star_mul_swap {n : ℕ} (p : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    star (((p.sign : ℤ) : ℂ)) * ((((p * Equiv.swap i j).sign : ℤ) : ℂ)) = -1 := by
  rw [map_mul, Equiv.Perm.sign_swap hij]
  simp only [Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg,
    Int.cast_one, ← mul_assoc, sign_star_mul, one_mul]

lemma pair_trace_reindex {n : ℕ} (K : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p : Equiv.Perm (Fin n)) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i))) =
      ∑ i, ∑ j, (K i j i j - K i j j i) := by
  have he (i : Fin n) : (∑ j ∈ Finset.univ.erase i,
      (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i))) =
      ∑ j, (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i)) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [sub_self, sub_zero]
  simp_rw [he]
  have hi (i : Fin n) : (∑ j, (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i))) =
      ∑ j, (K (p i) j (p i) j - K (p i) j j (p i)) :=
    Equiv.sum_comp p (fun j => K (p i) j (p i) j - K (p i) j j (p i))
  simp_rw [hi]
  exact Equiv.sum_comp p (fun i => ∑ j, (K i j i j - K i j j i))

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def pairIndexEquiv {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j) :
    Fin 2 ≃ {k : I // k = i ∨ k = j} where
  toFun b := if b = 0 then ⟨i, Or.inl rfl⟩ else ⟨j, Or.inr rfl⟩
  invFun k := if k.1 = i then 0 else 1
  left_inv b := by fin_cases b <;> simp [Ne.symm hij]
  right_inv k := by
    rcases k with ⟨k,hk | hk⟩ <;> subst k <;> simp [Ne.symm hij]

noncomputable def pairSelectedEquiv {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) : ({k : I // k = i ∨ k = j} → A) ≃ᵐ (A × A) :=
  (MeasurableEquiv.piCongrLeft (fun _ : {k : I // k = i ∨ k = j} => A)
    (pairIndexEquiv i j hij)).symm.trans MeasurableEquiv.finTwoArrow

noncomputable def pairSplit {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) : (I → A) ≃ᵐ (A × A) × ({k : I // ¬ (k = i ∨ k = j)} → A) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => A) (fun k => k = i ∨ k = j)).trans
    ((pairSelectedEquiv i j hij).prodCongr (MeasurableEquiv.refl _))

lemma pairSplit_first {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) : ((pairSplit i j hij) x).1.1 = x i := by
  change x ((pairIndexEquiv i j hij) 0).1 = x i
  simp [pairIndexEquiv]

lemma pairSplit_second {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) : ((pairSplit i j hij) x).1.2 = x j := by
  change x ((pairIndexEquiv i j hij) 1).1 = x j
  simp [pairIndexEquiv]

lemma pairSplit_rest {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) (k : {k : I // ¬ (k = i ∨ k = j)}) :
    ((pairSplit i j hij) x).2 k = x k := rfl

lemma pairSplit_measurePreserving {I A : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] (i j : I) (hij : i ≠ j) :
    MeasurePreserving (pairSplit (A := A) i j hij) (Measure.pi fun _ => μ)
      ((μ.prod μ).prod (Measure.pi fun _ => μ)) := by
  have hp : MeasurePreserving (pairSelectedEquiv (A := A) i j hij)
      (Measure.pi fun _ => μ) (μ.prod μ) :=
    (measurePreserving_finTwoArrow μ).comp
      ((measurePreserving_piCongrLeft (fun _ => μ) (pairIndexEquiv i j hij)).symm)
  exact (hp.prod (MeasurePreserving.id _)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ => μ) (fun k => k = i ∨ k = j))

lemma prod_erase_pair {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (hij : i ≠ j)
    (f : I → ℂ) :
    (∏ k, f k) = (f i * f j) * ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
    ← mul_assoc]
  congr 1
  exact Finset.prod_subtype ((Finset.univ.erase i).erase j) (fun k => by simp [and_comm]) f

lemma pair_weight_tensor_integrable {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] (i j : I) (hij : i ≠ j)
    (f : I → A → ℂ) (w : A → A → ℂ) (hf : ∀ k, Integrable (f k) μ)
    (hw : Integrable (fun ab : A × A => w ab.1 ab.2 * (f i ab.1 * f j ab.2)) (μ.prod μ)) :
    Integrable (fun x : I → A => w (x i) (x j) * ∏ k, f k (x k)) (Measure.pi fun _ => μ) := by
  have hR : Integrable (fun x : {k : I // ¬ (k = i ∨ k = j)} → A => ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (x k))
      (Measure.pi fun _ => μ) := Integrable.fintype_prod (fun k => hf k)
  have h := (pairSplit_measurePreserving μ i j hij).integrable_comp_of_integrable (hw.mul_prod hR)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Function.comp_apply, pairSplit_first, pairSplit_second, pairSplit_rest,
    prod_erase_pair i j hij]
  ring

lemma pair_weight_tensor_integral {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] (i j : I) (hij : i ≠ j)
    (f : I → A → ℂ) (w : A → A → ℂ) :
    (∫ x : I → A, w (x i) (x j) * ∏ k, f k (x k) ∂(Measure.pi fun _ => μ)) =
      (∫ ab : A × A, w ab.1 ab.2 * (f i ab.1 * f j ab.2) ∂(μ.prod μ)) *
        ∏ k ∈ (Finset.univ.erase i).erase j, ∫ a, f k a ∂μ := by
  have he (x : I → A) : w (x i) (x j) * ∏ k, f k (x k) =
      (w ((pairSplit i j hij) x).1.1 ((pairSplit i j hij) x).1.2 *
        (f i ((pairSplit i j hij) x).1.1 * f j ((pairSplit i j hij) x).1.2)) *
          ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (((pairSplit i j hij) x).2 k) := by
    simp only [pairSplit_first, pairSplit_second, pairSplit_rest, prod_erase_pair i j hij]
    ring
  simp_rw [he]
  rw [(pairSplit_measurePreserving μ i j hij).integral_comp'
    (fun z => (w z.1.1 z.1.2 * (f i z.1.1 * f j z.1.2)) * ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (z.2 k)),
    integral_prod_mul (fun ab : A × A => w ab.1 ab.2 * (f i ab.1 * f j ab.2))
      (fun x : {k : I // ¬ (k = i ∨ k = j)} → A => ∏ k, f k.1 (x k)),
    integral_fintype_prod_eq_prod]
  congr 1
  exact (Finset.prod_subtype ((Finset.univ.erase i).erase j) (fun k => by simp [and_comm]) (fun k => ∫ a, f k a ∂μ)).symm

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_TwoBodyTensorIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma two_body_tensor_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v a xy.1) * v c xy.1) * (star (v b xy.2) * v d xy.2))) (μ.prod μ))
    (p q : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x : Fin n → A => w (x i) (x j) *
      (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k))) (Measure.pi fun _ => μ) := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact pair_weight_tensor_integrable i j hij (fun k a => star (v (p k) a) * v (q k) a) w
    (fun k => (hv (p k)).star.integrable_mul (hv (q k))) (hw _ _ _ _)

lemma two_body_tensor_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (p q : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    (∫ x : Fin n → A, w (x i) (x j) *
      (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k)) ∂(Measure.pi fun _ => μ)) =
      (∫ xy : A × A, w xy.1 xy.2 *
        ((star (v (p i) xy.1) * v (q i) xy.1) * (star (v (p j) xy.2) * v (q j) xy.2))
          ∂(μ.prod μ)) * ∏ k ∈ (Finset.univ.erase i).erase j,
            if p k = q k then (1:ℂ) else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [pair_weight_tensor_integral i j hij (fun k a => star (v (p k) a) * v (q k) a) w]
  simp_rw [ho]

lemma determinant_two_body_expansion {A : Type*} {n : ℕ}
    (v : Fin n → A → ℂ) (w : A → A → ℂ) (x : Fin n → A) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      (star (determinantWave v x) * determinantWave v x) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j) *
            (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k)) := by
  rw [determinant_bilinear_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_OrbitalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma complex_star_mul_self (z : ℂ) : star z * z = (↑(‖z‖^2) : ℂ) := by
  rw [mul_comm, Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinConfigurationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma sum_pair_symmetric {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ i j, w i j = w j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, w i j) =
      2 * ∑ i, ∑ j, if i < j then w i j else 0 := by
  have he (i : Fin n) : (∑ j ∈ Finset.univ.erase i, w i j) =
      (∑ j, if i < j then w i j else 0) + (∑ j, if j < i then w i j else 0) := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have hpoint (j : Fin n) : w i j = (if i < j then w i j else 0) +
        (if j < i then w i j else 0) + (if j = i then w i i else 0) := by
      rcases lt_trichotomy i j with h|h|h
      · simp [h, h.not_gt, h.ne'];
      · subst j; simp
      · simp [h, h.not_gt, h.ne]
    conv_lhs => lhs; arg 2; ext j; rw [hpoint j]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then w i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then w i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j i]
  rw [hs]
  ring

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SlotTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def slotTensor {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) : ℂ :=
  ∏ j, if j = i then d (p j) (x j) else v (p j) (x j)

noncomputable def slotDeterminant {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (i : Fin n) (x : Fin n → A) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) * slotTensor v d p i x

lemma slotDeterminant_bilinear {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (i : Fin n) (x : Fin n → A) :
    star (slotDeterminant v d i x) * slotDeterminant v d i x =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          (star (slotTensor v d p i x) * slotTensor v d q i x) := by
  simp only [slotDeterminant, star_sum, star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Occupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable def occupancy (b : Bool) : ℝ := if b then 1 else 0
noncomputable def bernoulliWeight {ι : Type*} [Fintype ι] (lam : ι → ℝ) (w : ι → Bool) : ℝ :=
  ∏ i, if w i then lam i else 1-lam i
lemma bernoulliWeight_nonneg {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (hl : ∀ i, 0 ≤ lam i) (hu : ∀ i, lam i ≤ 1) (w : ι → Bool) :
    0 ≤ bernoulliWeight lam w := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact hl i
  · exact sub_nonneg.mpr (hu i)
lemma bernoulli_product_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (f : ι → Bool → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * ∏ i, f i (w i)) =
      ∏ i, ((1-lam i)*f i false+lam i*f i true) := by
  simp only [bernoulliWeight,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i b => (if b then lam i else 1-lam i)*f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]
lemma bernoulliWeight_sum {ι : Type*} [Fintype ι] (lam : ι → ℝ) :
    ∑ w : ι → Bool, bernoulliWeight lam w = 1 := by
  simpa using bernoulli_product_mean lam (fun _ _ => 1)
lemma bernoulli_forced_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (s : Finset ι) :
    (∑ w : ι → Bool, bernoulliWeight lam w * ∏ i ∈ s,occupancy (w i)) = ∏ i ∈ s,lam i := by
  have he (w : ι → Bool) : (∏ i ∈ s,occupancy (w i)) = ∏ i,if i ∈ s then occupancy (w i) else 1 := by
    rw [Finset.prod_ite]
    simp
  simp_rw [he]
  rw [bernoulli_product_mean lam (fun i b => if i ∈ s then occupancy b else 1)]
  have hp (i : ι) : (1-lam i)*(if i ∈ s then occupancy false else 1)+
      lam i*(if i ∈ s then occupancy true else 1) = if i ∈ s then lam i else 1 := by
    by_cases hs : i ∈ s <;> simp [hs,occupancy]
  simp_rw [hp]
  rw [Finset.prod_ite]
  simp
lemma bernoulli_one_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (i : ι) :
    (∑ w : ι → Bool,bernoulliWeight lam w*occupancy (w i)) = lam i := by
  simpa using bernoulli_forced_mean lam {i}
lemma bernoulli_two_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∑ w : ι → Bool,bernoulliWeight lam w*(occupancy (w i)*occupancy (w j))) = lam i*lam j := by
  simpa [hij] using bernoulli_forced_mean lam {i,j}
lemma bernoulli_linear_mean {ι : Type*} [Fintype ι] (lam a : ι → ℝ) :
    (∑ w : ι → Bool,bernoulliWeight lam w*(∑ i,occupancy (w i)*a i)) = ∑ i,lam i*a i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [←mul_assoc,←Finset.sum_mul,bernoulli_one_mean]
lemma bernoulli_pair_mean {ι : Type*} [Fintype ι] (lam : ι → ℝ) (d : ι → ι → ℝ)
    (hd : ∀ i, d i i = 0) :
    (∑ w : ι → Bool,bernoulliWeight lam w*(∑ i,∑ j,occupancy (w i)*occupancy (w j)*d i j)) =
      ∑ i,∑ j,lam i*lam j*d i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i=j
  · subst j; simp [hd]
  · calc
      _ = (∑ w : ι → Bool,bernoulliWeight lam w*(occupancy (w i)*occupancy (w j)))*d i j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [bernoulli_two_mean lam hij]

noncomputable def occupiedIndex {ι : Type*} [Fintype ι] (w : ι → Bool) :
    Fin (Fintype.card {i // w i = true}) ↪ ι :=
  (Fintype.equivFin {i // w i = true}).symm.toEmbedding.trans (Function.Embedding.subtype _)

lemma sum_occupiedIndex {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (w : ι → Bool) (f : ι → R) :
    (∑ a, f (occupiedIndex w a)) = ∑ i, if w i then f i else 0 := by
  classical
  rw [show (∑ a, f (occupiedIndex w a)) = ∑ a : {i // w i = true}, f a by
    exact Equiv.sum_comp (Fintype.equivFin {i // w i = true}).symm (fun a => f a)]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => w i = true)) (by simp) f,
    Finset.sum_filter]

lemma sum_occupiedIndex_real {ι : Type*} [Fintype ι] (w : ι → Bool) (f : ι → ℝ) :
    (∑ a, f (occupiedIndex w a)) = ∑ i, occupancy (w i) * f i := by
  rw [sum_occupiedIndex]
  apply Finset.sum_congr rfl
  intro i _
  cases w i <;> simp [occupancy]

noncomputable def slaterPairEntry {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (v : ι → A → ℂ) (W : A → A → ℝ) (i j : ι) : ℝ :=
  (∫ xy : A × A, (W xy.1 xy.2 : ℂ) *
      ((star (v i xy.1)*v i xy.1)*(star (v j xy.2)*v j xy.2)) ∂(μ.prod μ)).re -
  (∫ xy : A × A, (W xy.1 xy.2 : ℂ) *
      ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2)) ∂(μ.prod μ)).re

lemma slaterPairEntry_self {A ι : Type*} [MeasurableSpace A] (μ : Measure A)
    (v : ι → A → ℂ) (W : A → A → ℝ) (i : ι) : slaterPairEntry μ v W i i = 0 := by
  simp [slaterPairEntry]

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WeightedExchangeAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma weighted_exchange_algebra {A ι : Type*} [Fintype ι]
    (v : ι → A → ℂ) (lam : ι → ℝ) (x y : A) :
    (∑ i, ∑ j, (lam i : ℂ)*(lam j : ℂ)*
      ((star (v i x)*v j x)*(star (v j y)*v i y))) =
      (↑(‖∑ i, (lam i : ℂ)*(v i x*star (v i y))‖^2) : ℂ) := by
  have hs (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  rw [← complex_star_mul_self]
  simp only [star_sum, star_mul, star_star, hs, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma weighted_exchange_integral {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (v : ι → A → ℂ) (lam : ι → ℝ) (W : A → A → ℝ)
    (hW : ∀ i j, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ)*
      ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2))) (μ.prod μ)) :
    (∑ i, ∑ j, (lam i : ℂ)*(lam j:ℂ)*
      (∫ xy : A × A, (W xy.1 xy.2 : ℂ)*
        ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2)) ∂(μ.prod μ))) =
    (↑(∫ xy : A × A, W xy.1 xy.2 *
      ‖∑ i, (lam i : ℂ)*(v i xy.1*star (v i xy.2))‖^2 ∂(μ.prod μ)) : ℂ) := by
  simp_rw [← integral_const_mul]
  calc
    _ = ∫ xy : A × A, ∑ i, ∑ j, (lam i : ℂ)*(lam j:ℂ)*((W xy.1 xy.2 : ℂ)*
        ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2))) ∂(μ.prod μ) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        (hW i j).const_mul _))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => (hW i j).const_mul _)).symm
    _ = ∫ xy : A × A, ((W xy.1 xy.2 *
        ‖∑ i, (lam i : ℂ)*(v i xy.1*star (v i xy.2))‖^2 : ℝ) : ℂ) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [] with xy
      rw [Complex.ofReal_mul, ← weighted_exchange_algebra v lam xy.1 xy.2]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := integral_complex_ofReal

lemma weighted_slaterPairEntry_upper {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (v : ι → A → ℂ) (lam : ι → ℝ) (W : A → A → ℝ)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ)*
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ))
    (hW0 : ∀ x y, 0 ≤ W x y) :
    (∑ i, ∑ j, lam i*lam j*slaterPairEntry μ v W i j) ≤
      ∫ xy : A × A, W xy.1 xy.2 *
        ((∑ i, lam i*‖v i xy.1‖^2)*(∑ j, lam j*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
  have hd (i j : ι) : Integrable
      (fun xy : A × A => W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2)) (μ.prod μ) := by
    have h := (hW i j i j).re
    simp only [complex_star_mul_self, ← Complex.ofReal_mul] at h
    change Integrable (fun xy : A × A => (↑(W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2)) : ℂ).re) _ at h
    simpa only [Complex.ofReal_re] using h
  have he := congrArg Complex.re (weighted_exchange_integral μ v lam W (fun i j => hW i j j i))
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero] at he
  simp only [slaterPairEntry, complex_star_mul_self, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  have hdir : (∑ i, ∑ j, lam i*lam j*
      (∫ xy : A × A, W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2) ∂(μ.prod μ))) =
      ∫ xy : A × A, W xy.1 xy.2 *
        ((∑ i, lam i*‖v i xy.1‖^2)*(∑ j, lam j*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
    simp_rw [← integral_const_mul]
    calc
      _ = ∫ xy : A × A, ∑ i, ∑ j, lam i*lam j *
          (W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hd i j).const_mul _))]
        apply Finset.sum_congr rfl
        intro i _
        exact (integral_finsetSum _ (fun j _ => (hd i j).const_mul _)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with xy
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hdir]
  exact sub_le_self _ (integral_nonneg (fun xy => mul_nonneg (hW0 _ _) (sq_nonneg _)))

lemma bernoulli_chosen_sum {ι : Type*} [Fintype ι] (lam f : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * ∑ a, f (occupiedIndex w a)) =
      ∑ i, lam i*f i := by
  simp_rw [sum_occupiedIndex_real]
  exact bernoulli_linear_mean lam f

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FiniteProdSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma finiteProd_sum {ι : Type*} [Fintype ι] (W : ℝ) (a b : ι → ℝ) :
    W*((∑ i, a i)*(∑ j, b j)) = ∑ i, ∑ j, W*(a i*b j) := by
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]

lemma finite_weighted_bilinear_integrable {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (u v : ι → A → ℝ) (lam : ι → ℝ) (W : A → A → ℝ)
    (hW : ∀ a b, Integrable (fun xy : A × A => W xy.1 xy.2*(u a xy.1*v b xy.2)) (μ.prod μ)) :
    Integrable (fun xy : A × A => W xy.1 xy.2 *
      ((∑ i, lam i*u i xy.1)*(∑ j, lam j*v j xy.2))) (μ.prod μ) := by
  have H := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hW i j).const_mul (lam i*lam j)))
  apply H.congr
  filter_upwards [] with xy
  rw [finiteProd_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma exists_le_weighted_average {ι : Type*} [Fintype ι] [Nonempty ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    ∃ i, f i ≤ ∑ j, p j*f j := by
  classical
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc
    f i = ∑ j, p j*f i := by rw [← Finset.sum_mul, hpsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hmin j hj) (hp j))

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WeakDirectionalUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma weak_directional_unique {f d e : E → ℂ} (a : E)
    (hd : LocallyIntegrable d volume) (he : LocallyIntegrable e volume)
    (hfd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = -(∫ x, (φ x : ℂ)*d x))
    (hfe : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = -(∫ x, (φ x : ℂ)*e x)) :
    d =ᵐ[volume] e := by
  apply ae_eq_of_integral_contDiff_smul_eq hd he
  intro φ hφ hφC
  simpa only [← Complex.real_smul, neg_inj] using (hfd φ hφ hφC).symm.trans (hfe φ hφ hφC)

lemma weak_directional_zero_on_open {f d : E → ℂ} (a : E)
    (hd : LocallyIntegrable d volume)
    (hfd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = -(∫ x, (φ x : ℂ)*d x))
    (U : Set E) (hU : IsOpen U) (hfU : ∀ᵐ x ∂volume, x ∈ U → f x = 0) :
    ∀ᵐ x ∂volume, x ∈ U → d x = 0 := by
  apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hd.locallyIntegrableOn U)
  intro φ hφ hφC hφU
  have hzero : (∫ x, (fderiv ℝ φ x a : ℂ)*f x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hfU] with x hx
    by_cases h : x ∈ U
    · simp [hx h]
    · have hn : x ∉ tsupport φ := fun hh => h (hφU hh)
      simp [fderiv_of_notMem_tsupport ℝ hn]
  have H := hfd φ hφ hφC
  rw [hzero] at H
  simpa only [← Complex.real_smul, neg_eq_zero] using H.symm

lemma smooth_compact_weak_directional (f : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (a : E)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, (fderiv ℝ φ x a : ℂ)*f x) =
      -(∫ x, (φ x : ℂ)*fderiv ℝ f x a) := by
  let g : E → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hφ
  have hgc : HasCompactSupport g := hφc.comp_left Complex.ofReal_zero
  have hd (x : E) : fderiv ℝ g x a = (fderiv ℝ φ x a : ℂ) := by
    exact congrArg (fun L : E →L[ℝ] ℂ => L a)
      ((Complex.ofRealCLM.hasFDerivAt.comp x
        ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hdf : Continuous (fun x => fderiv ℝ f x a) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x a) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun x => fderiv ℝ g x a*f x) :=
    (hdg.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left
  have h2 : Integrable (fun x => g x*fderiv ℝ f x a) :=
    (hg.continuous.mul hdf).integrable_of_hasCompactSupport hgc.mul_right
  have h3 : Integrable (fun x => g x*f x) :=
    (hg.continuous.mul hf.continuous).integrable_of_hasCompactSupport hgc.mul_right
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hg.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  simpa only [hd, g] using (neg_eq_iff_eq_neg.mp H.symm)

lemma weak_directional_eq_smooth {u d : Lp ℂ 2 (volume : Measure E)}
    (a : E) (F : E → ℂ) (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hu : (u : E → ℂ) =ᵐ[volume] F)
    (hd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*u x) = -(∫ x, (φ x : ℂ)*d x)) :
    (d : E → ℂ) =ᵐ[volume] fun x => fderiv ℝ F x a := by
  apply weak_directional_unique (f := F) a
    ((Lp.memLp d).locallyIntegrable (by norm_num))
    (((hFs.continuous_fderiv (by simp)).clm_apply continuous_const).locallyIntegrable)
  · intro φ hφ hφC
    rw [← hd φ hφ hφC]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx]
  · exact smooth_compact_weak_directional F hFs hFc a

lemma weak_directional_smooth_norm_sq {u d : Lp ℂ 2 (volume : Measure E)}
    (a : E) (F : E → ℂ) (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hu : (u : E → ℂ) =ᵐ[volume] F)
    (hd : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*u x) = -(∫ x, (φ x : ℂ)*d x)) :
    (∫ x, ‖fderiv ℝ F x a‖^2) = ‖d‖^2 := by
  have he := weak_directional_eq_smooth a F hFs hFc hu hd
  calc
    _ = ∫ x, ‖d x‖^2 := integral_congr_ae (he.mono (fun x hx => by dsimp only at hx ⊢; rw [hx]))
    _ = ‖d‖^2 := by
      apply Complex.ofReal_injective
      rw [← integral_complex_ofReal]
      calc
        _ = inner ℂ d d := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [] with x
          simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
        _ = _ := by simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
end Coulomb

end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ConfigSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma compactSupport_slice_right {φ : E × F → ℝ} (hC : HasCompactSupport φ) (x : E) :
    HasCompactSupport (fun y => φ (x,y)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hC.image continuous_snd)
  intro y hy
  exact ⟨(x,y), subset_tsupport φ hy, rfl⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)] in
lemma compactSupport_slice_left {φ : E × F → ℝ} (hC : HasCompactSupport φ) (y : F) :
    HasCompactSupport (fun x => φ (x,y)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hC.image continuous_fst)
  intro x hx
  exact ⟨(x,y), subset_tsupport φ hx, rfl⟩

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_JoinSpins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb

lemma sum_configurationBlocks {m k : ℕ} (F : Fin (m+k) × Fin 3 → ℝ) :
    (∑ a, F a) = (∑ a : Fin m × Fin 3, F (Fin.castAdd k a.1,a.2)) +
      (∑ a : Fin k × Fin 3, F (Fin.natAdd m a.1,a.2)) := by
  simp only [Fintype.sum_prod_type]
  exact Fin.sum_univ_add _

end Coulomb

open scoped Classical
namespace Coulomb
def blockHom (m k : ℕ) :
    (Equiv.Perm (Fin m) × Equiv.Perm (Fin k)) →* Equiv.Perm (Fin (m+k)) :=
  ((finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m+k)).permCongrHom).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin m) (Fin k))

def blockGroup (m k : ℕ) : Subgroup (Equiv.Perm (Fin (m+k))) := (blockHom m k).range

lemma blockHom_left {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k)) (i : Fin m) :
    blockHom m k (p,q) (Fin.castAdd k i) = Fin.castAdd k (p i) := by
  change finSumFinEquiv ((Equiv.sumCongr p q) (finSumFinEquiv.symm (Fin.castAdd k i))) = _
  simp [← finSumFinEquiv_apply_left]

lemma blockHom_right {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k)) (i : Fin k) :
    blockHom m k (p,q) (Fin.natAdd m i) = Fin.natAdd m (q i) := by
  change finSumFinEquiv ((Equiv.sumCongr p q) (finSumFinEquiv.symm (Fin.natAdd m i))) = _
  simp [← finSumFinEquiv_apply_right]

lemma blockHom_sign {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k)) :
    (blockHom m k (p,q)).sign = p.sign*q.sign := by
  change (finSumFinEquiv.permCongr (Equiv.sumCongr p q)).sign = _
  rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

lemma mem_blockGroup_of_no_crossing {m k : ℕ} (r : Equiv.Perm (Fin (m+k)))
    (hr : ∀ i : Fin m, ∃ j : Fin m, r (Fin.castAdd k i) = Fin.castAdd k j) :
    r ∈ blockGroup m k := by
  let t : Equiv.Perm (Fin m ⊕ Fin k) := finSumFinEquiv.symm.permCongr r
  have ht : Set.MapsTo t (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    rcases hr i with ⟨j,hj⟩
    refine ⟨j, ?_⟩
    change Sum.inl j = finSumFinEquiv.symm (r (finSumFinEquiv (Sum.inl i)))
    rw [finSumFinEquiv_apply_left, hj]
    simp [← finSumFinEquiv_apply_left]
  rcases Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ht with ⟨pq,hpq⟩
  refine ⟨pq, ?_⟩
  apply finSumFinEquiv.symm.permCongr.injective
  change finSumFinEquiv.symm.permCongr
    (finSumFinEquiv.permCongr (Equiv.Perm.sumCongrHom (Fin m) (Fin k) pq)) = _
  rw [← Equiv.permCongr_symm, Equiv.symm_apply_apply]
  exact hpq

lemma exists_crossing_of_not_mem {m k : ℕ} (r : Equiv.Perm (Fin (m+k)))
    (hr : r ∉ blockGroup m k) :
    ∃ i : Fin m, ∃ j : Fin k, r (Fin.castAdd k i) = Fin.natAdd m j := by
  have hn : ¬ ∀ i : Fin m, ∃ j : Fin m, r (Fin.castAdd k i) = Fin.castAdd k j :=
    fun h => hr (mem_blockGroup_of_no_crossing r h)
  push Not at hn
  rcases hn with ⟨i,hi⟩
  refine ⟨i, ?_⟩
  have hcases := Fin.addCases (motive := fun z : Fin (m+k) =>
    (∃ j : Fin k, z = Fin.natAdd m j) ∨ ∃ j : Fin m, z = Fin.castAdd k j)
    (fun j => Or.inr ⟨j,rfl⟩) (fun j => Or.inl ⟨j,rfl⟩) (r (Fin.castAdd k i))
  rcases hcases with h|⟨j,hj⟩
  · exact h
  · exact (hi j hj).elim
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
namespace Coulomb

noncomputable section

lemma sign_complex_sq {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ((p.sign : ℤ) : ℂ)*((p.sign : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or p.sign with h|h <;> simp [h]

lemma sign_complex_mul {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    (((p*q).sign : ℤ) : ℂ) = ((p.sign : ℤ) : ℂ)*((q.sign : ℤ) : ℂ) := by
  simp

end
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NormSqSumCosets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
lemma norm_sq_sum_cosets {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (f : G → ℂ)
    (hc : ∀ p q, conj (f p)*f q = if p⁻¹*q ∈ H then ((‖f p‖^2 : ℝ) : ℂ) else 0) :
    ‖∑ p, f p‖^2 = (Fintype.card H : ℝ)*∑ p, ‖f p‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  rw [← Complex.conj_mul', map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, hc]
  have hi (p : G) :
      (∑ q : G, if p⁻¹*q ∈ H then ((‖f p‖^2 : ℝ) : ℂ) else (0:ℂ)) =
        (Fintype.card H : ℂ)*(‖f p‖^2 : ℝ) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft p)]
    change (∑ r : G, if p⁻¹*(p*r) ∈ H then ((‖f p‖^2 : ℝ) : ℂ) else 0) = _
    simp only [inv_mul_cancel_left]
    rw [← Finset.sum_filter]
    simp [Fintype.card_subtype]
  simp_rw [hi]
  push_cast
  rfl

def complexSign (n : ℕ) : Equiv.Perm (Fin n) →* ℂ where
  toFun := fun p => ((p.sign : ℤ) : ℂ)
  map_one' := by simp
  map_mul' := by intro p q; simp

lemma complexSign_sq {n : ℕ} (p : Equiv.Perm (Fin n)) : complexSign n p*complexSign n p = 1 :=
  sign_complex_sq p
lemma complexSign_real {n : ℕ} (p : Equiv.Perm (Fin n)) : conj (complexSign n p) = complexSign n p := by
  simp [complexSign]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WedgeMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb

def wedgeMultiplicity (m k : ℕ) : ℝ :=
  (Fintype.card (blockGroup m k) : ℝ)*(Fintype.card (Equiv.Perm (Fin (m+k))) : ℝ)

lemma wedgeMultiplicity_pos (m k : ℕ) : 0 < wedgeMultiplicity m k := by
  unfold wedgeMultiplicity
  positivity

lemma wedge_normalizer_sq (m k : ℕ) :
    ‖(((Real.sqrt (wedgeMultiplicity m k))⁻¹ : ℝ) : ℂ)‖^2 = (wedgeMultiplicity m k)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (le_of_lt (wedgeMultiplicity_pos m k))]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoreCoulombPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb

variable {Y ι : Type*} [MeasurableSpace Y] [Countable ι]
lemma weighted_series_integrable_hasSum {ν : Measure Y} {F : ι → Y → ℝ}
    (hF : ∀ i, AEStronglyMeasurable (F i) ν) (hpos : ∀ i y, 0 ≤ F i y)
    (hs : ∀ᵐ y ∂ν, Summable (fun i => F i y)) {W : Y → ℝ}
    (hW : AEStronglyMeasurable W ν) (hWp : ∀ y, 0 ≤ W y)
    (hI : Integrable (fun y => W y * ∑' i, F i y) ν) :
    (∀ i, Integrable (fun y => W y * F i y) ν) ∧
      HasSum (fun i => ∫ y, W y * F i y ∂ν) (∫ y, W y * ∑' i, F i y ∂ν) := by
  have hp (i : ι) (y : Y) : 0 ≤ W y * F i y := mul_nonneg (hWp y) (hpos i y)
  have hi (i : ι) : Integrable (fun y => W y * F i y) ν := by
    apply hI.mono' (hW.mul (hF i))
    filter_upwards [hs] with y hy
    change ‖W y * F i y‖ ≤ _
    rw [Real.norm_of_nonneg (hp i y)]
    exact mul_le_mul_of_nonneg_left (hy.le_tsum i (fun j _ => hpos j y)) (hWp y)
  have hsum : Summable (fun i => ∫ y, W y * F i y ∂ν) := by
    apply summable_of_sum_le (fun i => integral_nonneg (hp i))
    intro s
    rw [← integral_finsetSum s (fun i _ => hi i)]
    apply integral_mono_ae (integrable_finsetSum s (fun i _ => hi i)) hI
    filter_upwards [hs] with y hy
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hy.sum_le_tsum s (fun i _ => hpos i y)) (hWp y)
  have hn : Summable (fun i => ∫ y, ‖W y * F i y‖ ∂ν) := by
    simpa only [Real.norm_of_nonneg (hp _ _)] using hsum
  have h := hasSum_integral_of_summable_integral_norm hi hn
  simpa only [tsum_mul_left] using And.intro hi h
end Coulomb

open scoped Classical

open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GroupFermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Coulomb

open scoped Classical

open scoped Classical

open Filter
open scoped Convolution
open ContinuousLinearMap

section GridTiling
variable {I : Type*} [Fintype I]

def gridBox (b : ℝ) (k : I → ℤ) : Set (I → ℝ) :=
  Set.univ.pi (fun i => Ioc (b * (k i : ℝ)) (b * ((k i : ℝ)+1)))

lemma gridBox_measurable (b : ℝ) (k : I → ℤ) : MeasurableSet (gridBox b k) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

omit [Fintype I] in
lemma gridBox_disjoint {b : ℝ} (hb : 0 < b) :
    Pairwise (fun k l : I → ℤ => Disjoint (gridBox b k) (gridBox b l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hxl
  apply hkl
  funext i
  have hk := (Set.mem_univ_pi.mp hx) i
  have hl := (Set.mem_univ_pi.mp hxl) i
  have h1 : (k i : ℝ) < (l i : ℝ)+1 :=
    (mul_lt_mul_iff_right₀ hb).mp (hk.1.trans_le hl.2)
  have h2 : (l i : ℝ) < (k i : ℝ)+1 :=
    (mul_lt_mul_iff_right₀ hb).mp (hl.1.trans_le hk.2)
  have h1' : k i < l i + 1 := by exact_mod_cast h1
  have h2' : l i < k i + 1 := by exact_mod_cast h2
  omega

omit [Fintype I] in
lemma gridBox_iUnion {b : ℝ} (hb : 0 < b) :
    (⋃ k : I → ℤ, gridBox b k) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨fun i => ⌈x i / b⌉ - 1, ?_⟩
  apply Set.mem_univ_pi.mpr
  intro i
  have hL := Int.ceil_lt_add_one (x i / b)
  have hU := Int.le_ceil (x i / b)
  constructor
  · have h : (⌈x i/b⌉ : ℝ)-1 < x i/b := by linarith
    have hh := (lt_div_iff₀ hb).mp h
    push_cast
    nlinarith
  · have hh := (div_le_iff₀ hb).mp hU
    push_cast
    nlinarith

lemma finiteCubeMeasure_eq_restrict (b : ℝ) :
    finiteCubeMeasure b I = volume.restrict (Set.univ.pi (fun _ : I => Ioc 0 b)) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl

omit [Fintype I] in
lemma gridBox_preimage_add (b : ℝ) (k : I → ℤ) :
    (fun x : I → ℝ => x + (fun i => b*(k i : ℝ))) ⁻¹' gridBox b k =
      Set.univ.pi (fun _ : I => Ioc 0 b) := by
  ext x
  simp only [Set.mem_preimage, gridBox, Set.mem_univ_pi, Pi.add_apply, mem_Ioc]
  apply forall_congr'
  intro i
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma gridBox_integral_eq_cube (b : ℝ) (k : I → ℤ) (f : (I → ℝ) → ℝ) :
    (∫ x in gridBox b k, f x) =
      ∫ x, f (x + (fun i => b*(k i : ℝ))) ∂(finiteCubeMeasure b I) := by
  have mp := (measurePreserving_add_right (volume : Measure (I → ℝ))
    (fun i => b*(k i : ℝ))).restrict_preimage (gridBox_measurable b k)
  rw [gridBox_preimage_add, ← finiteCubeMeasure_eq_restrict] at mp
  exact (mp.integral_comp (MeasurableEquiv.addRight _).measurableEmbedding f).symm

lemma gridBox_hasSum_integral {b : ℝ} (hb : 0 < b) {f : (I → ℝ) → ℝ}
    (hf : Integrable f) :
    HasSum (fun k : I → ℤ => ∫ x, f (x+(fun i => b*(k i : ℝ)))
      ∂(finiteCubeMeasure b I)) (∫ x, f x) := by
  have H := hasSum_integral_iUnion (gridBox_measurable b) (gridBox_disjoint hb)
    (hf.integrableOn (s := ⋃ k : I → ℤ, gridBox b k))
  simp_rw [gridBox_integral_eq_cube] at H
  simpa only [gridBox_iUnion hb, Measure.restrict_univ] using H

end GridTiling

lemma sum_fiber_card {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → ι) :
    (∑ k : ι, (Fintype.card {i : Fin n // g i = k} : ℝ)) = n := by
  have H : (∑ k : ι, Fintype.card {i : Fin n // g i = k}) = n := by
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv g),
      Fintype.card_fin]
  exact_mod_cast H

lemma sum_power_le_power_sum {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, w i ^ p) ≤ (∑ i, w i) ^ p := by
  have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have he (x : ℝ) (hx : 0 ≤ x) : x^p = x*x^(p-1) := by
    conv_lhs => rw [show p = 1+(p-1) by ring]
    rw [Real.rpow_add_of_nonneg hx (by norm_num) (by linarith), Real.rpow_one]
  simp_rw [he _ (hw _)]
  rw [he _ hs]
  calc
    _ ≤ ∑ i, w i * (∑ j, w j)^(p-1) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact Real.rpow_le_rpow (hw i)
        (Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)) (by linarith)
    _ = _ := (Finset.sum_mul ..).symm

lemma sum_fiber_power_le {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin n → ι) {p : ℝ} (hp : 1 ≤ p) :
    (∑ k : ι, (Fintype.card {i : Fin n // g i = k} : ℝ)^p) ≤ (n : ℝ)^p := by
  simpa only [sum_fiber_card] using
    sum_power_le_power_sum
      (fun k => (Fintype.card {i : Fin n // g i = k} : ℝ)) (fun _ => Nat.cast_nonneg _) hp

lemma neumannBoundary_nonneg : 0 ≤ neumannBoundary := by
  unfold neumannBoundary
  positivity

noncomputable def groupLeadingCount {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) : ℝ :=
  ∑ k : ι, (Fintype.card {i : Fin n // g i = k} : ℝ) ^ (5/3 : ℝ)

lemma groupLeadingCount_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) : 0 ≤ groupLeadingCount g :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma groupLeadingCount_le {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) : groupLeadingCount g ≤ (n : ℝ)^(5/3 : ℝ) :=
  sum_fiber_power_le g (by norm_num)

abbrev GridAssignment (n : ℕ) := (Fin n × Fin 3) → ℤ

def gridCell {n : ℕ} (k : GridAssignment n) (i : Fin n) : Fin 3 → ℤ :=
  fun j => k (i,j)

noncomputable def gridLeadingCount {n : ℕ} (k : GridAssignment n) : ℝ :=
  groupLeadingCount (Set.rangeFactorization (gridCell k))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GridIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

section GridIndex
variable {I : Type*}

noncomputable def gridIndex (b : ℝ) (x : I → ℝ) : I → ℤ := fun i => ⌈x i / b⌉ - 1

lemma gridIndex_of_mem {b : ℝ} (hb : 0 < b) {k : I → ℤ} {x : I → ℝ}
    (hx : x ∈ gridBox b k) : gridIndex b x = k := by
  funext i
  have hi := Set.mem_univ_pi.mp hx i
  have hceil : ⌈x i / b⌉ = k i + 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · push_cast
      have h : (k i : ℝ) < x i / b := (lt_div_iff₀ hb).mpr (by nlinarith [hi.1])
      linarith
    · push_cast
      exact (div_le_iff₀ hb).mpr (by nlinarith [hi.2])
  simp only [gridIndex, hceil]
  omega

lemma gridIndex_measurable (b : ℝ) : Measurable (gridIndex b : (I → ℝ) → I → ℤ) := by
  apply Measurable.of_eval
  intro i
  have hi : Measurable (fun x : I → ℝ => x i / b) :=
    (measurable_pi_apply (X := fun _ : I => ℝ) i).div_const b
  have hc : Measurable (fun x : I → ℝ => ⌈x i / b⌉) := Int.measurable_ceil.comp hi
  exact hc.sub_const (1 : ℤ)

variable [Fintype I]

lemma gridBox_hasSum_weighted {b : ℝ} (hb : 0 < b) (F : (I → ℤ) → ℝ)
    {C : ℝ} (hF : ∀ k, ‖F k‖ ≤ C) {f : (I → ℝ) → ℝ} (hf : Integrable f) :
    HasSum (fun k => F k * ∫ x in gridBox b k, f x)
      (∫ x, F (gridIndex b x) * f x) := by
  have hfm : AEStronglyMeasurable (fun x : I → ℝ => F (gridIndex b x)) volume :=
    ((measurable_of_countable F).comp (gridIndex_measurable b)).aestronglyMeasurable
  have hi := hf.bdd_mul hfm (Filter.Eventually.of_forall (fun x => hF (gridIndex b x)))
  have H := hasSum_integral_iUnion (gridBox_measurable b) (gridBox_disjoint hb)
    (hi.integrableOn (s := ⋃ k, gridBox b k))
  rw [gridBox_iUnion hb, Measure.restrict_univ] at H
  apply H.congr_fun
  intro k
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (gridBox_measurable b k)] with x hx
  rw [gridIndex_of_mem hb hx]

end GridIndex

noncomputable def sameCell1 (b x y : ℝ) : ℝ := if ⌈x/b⌉ = ⌈y/b⌉ then 1 else 0

lemma sameCell1_nonneg (b x y : ℝ) : 0 ≤ sameCell1 b x y := by
  unfold sameCell1
  split <;> norm_num

lemma sameCell1_le_one (b x y : ℝ) : sameCell1 b x y ≤ 1 := by
  unfold sameCell1
  split <;> norm_num

lemma sameCell1_periodic {b : ℝ} (hb : b ≠ 0) (x y : ℝ) :
    Function.Periodic (fun t => sameCell1 b (x+t) (y+t)) b := by
  intro t
  have hx : (x+(t+b))/b = (x+t)/b+1 := by field_simp; ring
  have hy : (y+(t+b))/b = (y+t)/b+1 := by field_simp; ring
  simp only [sameCell1, hx, hy, Int.ceil_add_one, add_left_inj]

lemma sameCell1_measurable (b x y : ℝ) :
    Measurable (fun t => sameCell1 b (x+t) (y+t)) := by
  have hx : Measurable (fun t : ℝ => ⌈(x+t)/b⌉) :=
    Int.measurable_ceil.comp ((measurable_const.add measurable_id).div_const b)
  have hy : Measurable (fun t : ℝ => ⌈(y+t)/b⌉) :=
    Int.measurable_ceil.comp ((measurable_const.add measurable_id).div_const b)
  exact measurable_const.ite (measurableSet_eq_fun hx hy) measurable_const

lemma sameCell1_Ioc {b : ℝ} (hb : 0 < b) {u : ℝ} (hu : u ∈ Ioc 0 b) (d : ℝ) :
    sameCell1 b u (d+u) = (Ioc 0 b).indicator (fun _ => (1 : ℝ)) (d+u) := by
  have hc : ⌈u/b⌉ = 1 := Int.ceil_eq_iff.mpr (by
    norm_num
    exact ⟨div_pos hu.1 hb, (div_le_one hb).mpr hu.2⟩)
  have hd : ⌈(d+u)/b⌉ = 1 ↔ d+u ∈ Ioc 0 b := by
    rw [Int.ceil_eq_iff]
    norm_num
    exact and_congr (by simpa only [zero_mul] using (lt_div_iff₀ hb : 0 < (d+u)/b ↔ 0*b < d+u)) (div_le_one hb)
  simp only [sameCell1, hc, eq_comm (a := (1 : ℤ)), hd, Set.indicator]

lemma sameCell1_integral_zero {b : ℝ} (hb : 0 < b) (d : ℝ) :
    (∫ u in Ioc 0 b, sameCell1 b u (d+u)) = max 0 (b-|d|) := by
  have he : (∫ u in Ioc 0 b, sameCell1 b u (d+u)) =
      ∫ u in Ioc 0 b ∩ Ioc (-d) (b-d), (1 : ℝ) := by
    calc
      _ = ∫ u in Ioc 0 b, (Ioc (-d) (b-d)).indicator (fun _ => (1 : ℝ)) u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        rw [sameCell1_Ioc hb hu]
        have hi : d+u ∈ Ioc 0 b ↔ u ∈ Ioc (-d) (b-d) := by
          constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
        simp only [Set.indicator, hi]
      _ = _ := by
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          Set.inter_comm]
  rw [he, Set.Ioc_inter_Ioc, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal', smul_eq_mul, mul_one]
  rcases le_total 0 d with hd | hd
  · rw [abs_of_nonneg hd, max_eq_left (neg_nonpos.mpr hd),
      min_eq_right (by linarith : b-d ≤ b), sub_zero, max_comm]
  · rw [abs_of_nonpos hd, max_eq_right (neg_nonneg.mpr hd),
      min_eq_left (by linarith : b ≤ b-d), max_comm]

lemma sameCell1_integral {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    (∫ t in Ioc 0 b, sameCell1 b (x+t) (y+t)) = max 0 (b-|y-x|) := by
  have hP := (sameCell1_periodic hb.ne' x y).intervalIntegral_add_eq 0 (-x)
  simp only [zero_add, intervalIntegral.integral_of_le hb.le,
    intervalIntegral.integral_of_le (show -x ≤ -x+b by linarith)] at hP
  rw [hP]
  have hA := intervalIntegral.integral_comp_add_left
    (fun u => sameCell1 b u (y-x+u)) x (a := -x) (b := -x+b)
  simp only [add_neg_cancel, add_neg_cancel_left,
    intervalIntegral.integral_of_le hb.le,
    intervalIntegral.integral_of_le (show -x ≤ -x+b by linarith)] at hA
  convert sameCell1_integral_zero hb (y-x) using 1
  all_goals try with_reducible_and_instances rfl
  rw [← hA]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [show y-x+(x+t) = y+t by ring])

noncomputable def sameGridCell (b : ℝ) (x y : Fin 3 → ℝ) : ℝ :=
  ∏ j, sameCell1 b (x j) (y j)

noncomputable def flatFineKernel (b : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (b⁻¹)^6 * ∏ j, max 0 (b-|x j|)

lemma sameGridCell_integral {b : ℝ} (hb : 0 < b) (x y : Fin 3 → ℝ) :
    (∫ t, sameGridCell b (x+t) (y+t) ∂finiteCubeMeasure b (Fin 3)) =
      ∏ j, max 0 (b-|y j-x j|) := by
  unfold sameGridCell finiteCubeMeasure
  have H := integral_fintype_prod_eq_prod
    (fun j u => sameCell1 b (x j+u) (y j+u))
    (μ := fun _ : Fin 3 => volume.restrict (Ioc 0 b))
  exact H.trans (by simp_rw [sameCell1_integral hb])

lemma sameGridCell_nonneg (b : ℝ) (x y : Fin 3 → ℝ) : 0 ≤ sameGridCell b x y :=
  Finset.prod_nonneg (fun j _ => sameCell1_nonneg b (x j) (y j))

lemma sameGridCell_le_one (b : ℝ) (x y : Fin 3 → ℝ) : sameGridCell b x y ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _; exact sameCell1_nonneg b (x j) (y j)
  · intro j _; exact sameCell1_le_one b (x j) (y j)

lemma sameGridCell_measurable (b : ℝ) (x y : Fin 3 → ℝ) :
    Measurable (fun t => sameGridCell b (x+t) (y+t)) := by
  apply Finset.measurable_prod
  intro j _
  exact (sameCell1_measurable b (x j) (y j)).comp
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j)

lemma sameGridCell_integrable (b : ℝ) (x y : Fin 3 → ℝ) :
    Integrable (fun t => sameGridCell b (x+t) (y+t)) (finiteCubeMeasure b (Fin 3)) := by
  have : IsFiniteMeasure (finiteCubeMeasure b (Fin 3)) := by
    unfold finiteCubeMeasure
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply (integrable_const (1 : ℝ)).mono' (sameGridCell_measurable b x y).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_of_nonneg (sameGridCell_nonneg ..)]
    exact sameGridCell_le_one ..)

noncomputable def translatedGridDensity {n : ℕ} (b : ℝ) (t : Fin 3 → ℝ)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (b⁻¹)^3 * ∑ i : Fin n, sameGridCell b ((fun j => x (i,j))+t) (y+t)

lemma translatedGridDensity_integral {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    (b⁻¹)^3 * (∫ t, translatedGridDensity b t x y ∂finiteCubeMeasure b (Fin 3)) =
      ∑ i : Fin n, flatFineKernel b (y-(fun j => x (i,j))) := by
  unfold translatedGridDensity
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => sameGridCell_integrable ..)]
  simp_rw [sameGridCell_integral hb]
  rw [← mul_assoc, ← pow_add, Finset.mul_sum]
  rfl

lemma sameCell1_eq_ite (b x y : ℝ) :
    sameCell1 b x y = if ⌈x/b⌉-1 = ⌈y/b⌉-1 then 1 else 0 := by
  simp only [sameCell1, sub_left_inj]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FlatDensityPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma finiteCubeMeasure_real_univ {b : ℝ} (hb : 0 < b) (I : Type*) [Fintype I] :
    (finiteCubeMeasure b I).real univ = b ^ Fintype.card I := by
  simp [Measure.real, finiteCubeMeasure, Measure.pi_univ, hb.le]

lemma finiteCubeMeasure_neZero {b : ℝ} (hb : 0 < b) (I : Type*) [Fintype I] :
    NeZero (finiteCubeMeasure b I) := by
  constructor
  intro h
  have H := finiteCubeMeasure_real_univ hb I
  rw [h] at H
  simp only [Measure.real, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero] at H
  exact (pow_pos hb _).ne' H.symm

lemma translatedGridDensity_nonneg {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    0 ≤ translatedGridDensity b t x y := by
  apply mul_nonneg (pow_nonneg (inv_nonneg.mpr hb.le) _)
  exact Finset.sum_nonneg (fun _ _ => sameGridCell_nonneg ..)

lemma translatedGridDensity_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    translatedGridDensity b t x y ≤ (b⁻¹)^3*n := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr hb.le) _)
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => sameGridCell_le_one ..)
    _ = _ := by simp

lemma translatedGridDensity_measurable {n : ℕ} (b : ℝ)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    Measurable (fun t => translatedGridDensity b t x y) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun _ _ => sameGridCell_measurable ..)

lemma translatedGridDensity_integrable {n : ℕ} (b : ℝ)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    Integrable (fun t => translatedGridDensity b t x y) (finiteCubeMeasure b (Fin 3)) := by
  exact Integrable.const_mul
    (integrable_finsetSum _ (fun _ _ => sameGridCell_integrable ..)) _

lemma flatFineKernel_nonneg (b : ℝ) (y : Fin 3 → ℝ) : 0 ≤ flatFineKernel b y :=
  mul_nonneg (by positivity) (Finset.prod_nonneg (fun _ _ => le_max_left _ _))

lemma translated_count_measurable {n : ℕ} (b : ℝ) :
    Measurable (fun p : (Fin 3 → ℝ) × ((Fin n × Fin 3) → ℝ) =>
      gridLeadingCount (gridIndex b (fun ij => p.2 ij + p.1 ij.2))) := by
  apply (measurable_of_countable (gridLeadingCount (n := n))).comp
  apply (gridIndex_measurable b).comp
  apply Measurable.of_eval
  intro ij
  exact ((measurable_pi_apply (X := fun _ : Fin n × Fin 3 => ℝ) ij).comp measurable_snd).add
    ((measurable_pi_apply (X := fun _ : Fin 3 => ℝ) ij.2).comp measurable_fst)

lemma translated_count_integrable {n : ℕ} {b : ℝ} (_hb : 0 < b)
    {w : ((Fin n × Fin 3) → ℝ) → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun p : (Fin 3 → ℝ) × ((Fin n × Fin 3) → ℝ) =>
      gridLeadingCount (gridIndex b (fun ij => p.2 ij+p.1 ij.2)) * w p.2)
      ((finiteCubeMeasure b (Fin 3)).prod volume) := by
  have hwm := hw.aestronglyMeasurable.comp_snd (μ := finiteCubeMeasure b (Fin 3))
  have hm := (translated_count_measurable b).aestronglyMeasurable.mul hwm
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t => by
      apply (hw.const_mul ((n:ℝ)^(5/3:ℝ))).mono'
        (((translated_count_measurable b).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul hw.aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun x => by
        change ‖gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x‖ ≤ _
        simp only [gridLeadingCount]
        rw [Real.norm_of_nonneg (mul_nonneg (groupLeadingCount_nonneg _) (hw0 x))]
        exact mul_le_mul_of_nonneg_right (groupLeadingCount_le _) (hw0 x)))
  · have H (t : Fin 3 → ℝ) :
        ∫ x, ‖gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x‖ ≤
          (n:ℝ)^(5/3:ℝ) * ∫ x, w x := by
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
      · exact hw.const_mul _
      · exact Filter.Eventually.of_forall (fun x => by
          change ‖gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x‖ ≤ _
          simp only [gridLeadingCount]
          rw [Real.norm_of_nonneg (mul_nonneg (groupLeadingCount_nonneg _) (hw0 x))]
          exact mul_le_mul_of_nonneg_right (groupLeadingCount_le _) (hw0 x))
    apply (integrable_const ((n:ℝ)^(5/3:ℝ) * ∫ x, w x)).mono'
      hm.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact H t)

noncomputable def flatDensityPower {n : ℕ} (b : ℝ) (x : (Fin n × Fin 3) → ℝ) : ℝ :=
  ∫ y : Fin 3 → ℝ, (∑ i : Fin n,
    flatFineKernel b (y-(fun j => x (i,j))))^(5/3:ℝ)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Rotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb
abbrev Rotation := Matrix.specialOrthogonalGroup (Fin 3) ℝ

lemma rotation_entry_sq_sum (Q : Rotation) (j : Fin 3) :
    ∑ i : Fin 3, (Q.1 i j)^2 = 1 := by
  have H := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j j) Q.prop.1.1
  simpa [Matrix.mul_apply, Matrix.star_apply, pow_two] using H

lemma rotation_entry_abs_le (Q : Rotation) (i j : Fin 3) : |Q.1 i j| ≤ 1 := by
  have H : (Q.1 i j)^2 ≤ 1 := by
    rw [← rotation_entry_sq_sum Q j]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (Q.1 k j)) (Finset.mem_univ i)
  exact (sq_le_one_iff_abs_le_one _).mp H

lemma rotation_closed : IsClosed (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  change IsClosed ((unitary (Matrix (Fin 3) (Fin 3) ℝ) : Set _) ∩
    (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det) ⁻¹' {1})
  exact isClosed_unitary.inter (isClosed_singleton.preimage continuous_id.matrix_det)

lemma rotation_set_compact : IsCompact (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ _ : Fin 3 => (-1:ℝ)) (fun _ _ => (1:ℝ)) )).of_isClosed_subset rotation_closed
  intro Q hQ
  constructor <;> intro i j
  · exact (abs_le.mp (rotation_entry_abs_le ⟨Q,hQ⟩ i j)).1
  · exact (abs_le.mp (rotation_entry_abs_le ⟨Q,hQ⟩ i j)).2

noncomputable instance rotation_compact : CompactSpace Rotation :=
  isCompact_iff_compactSpace.mp rotation_set_compact

instance rotation_continuousStar : ContinuousStar Rotation where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star
instance rotation_continuousInv : ContinuousInv Rotation where
  continuous_inv := continuous_star
instance rotation_topologicalGroup : IsTopologicalGroup Rotation where

instance rotation_measurable : MeasurableSpace Rotation := borel Rotation
instance rotation_borel : BorelSpace Rotation := ⟨rfl⟩

noncomputable def rotationMeasure : Measure Rotation :=
  Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩,by simp⟩ : TopologicalSpace.PositiveCompacts Rotation)

instance instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure : IsProbabilityMeasure rotationMeasure := ⟨Measure.haarMeasure_self⟩

lemma flatFineKernel_continuous (b : ℝ) : Continuous (flatFineKernel b) := by
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro j _
  exact continuous_const.max (continuous_const.sub (continuous_apply j).abs)

lemma flatFineKernel_le {b : ℝ} (hb : 0 < b) (x : Fin 3 → ℝ) :
    flatFineKernel b x ≤ (b⁻¹)^3 := by
  have H : (∏ j : Fin 3, max 0 (b-|x j|)) ≤ b^3 := by
    calc
      _ ≤ ∏ _ : Fin 3, b := Finset.prod_le_prod (fun _ _ => le_max_left _ _)
        (fun i _ => max_le hb.le (sub_le_self _ (abs_nonneg _)))
      _ = _ := by simp
  apply (mul_le_mul_of_nonneg_left H (show 0 ≤ (b⁻¹)^6 by positivity)).trans_eq
  field_simp [hb.ne']

instance instIsMulLeftInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure : Measure.IsMulLeftInvariant rotationMeasure := by
  unfold rotationMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure : Measure.IsHaarMeasure rotationMeasure := by
  unfold rotationMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance instIsMulRightInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure : Measure.IsMulRightInvariant rotationMeasure where
  map_mul_right_eq_self P := by
    have : IsProbabilityMeasure (Measure.map (· * P) rotationMeasure) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    have H := Measure.isMulInvariant_eq_smul_of_compactSpace
      (Measure.map (· * P) rotationMeasure) rotationMeasure
    have H1 := congrArg (fun μ : Measure Rotation => μ univ) H
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at H1
    have H2 : (Measure.map (· * P) rotationMeasure).haarScalarFactor rotationMeasure = 1 :=
      ENNReal.coe_injective (by
        have h3 : (Measure.map (· * P) rotationMeasure) Set.univ = 1 := by
          rw [Measure.map_apply (measurable_mul_const P) MeasurableSet.univ]
          simp [measure_univ]
        rw [ENNReal.coe_one]; first | exact H1.symm | exact H1.symm.trans h3)
    rw [H2, one_smul] at H
    exact H

lemma tent_continuous (b : ℝ) : Continuous (fun x : ℝ => max 0 (b-|x|)) := by fun_prop
lemma tent_eq_zero {b : ℝ} (x : ℝ) (hx : x ∉ Icc (-b) b) : max 0 (b-|x|) = 0 := by
  apply max_eq_left
  have : b ≤ |x| := by
    by_contra! h
    exact hx ⟨by linarith [(neg_abs_le x)], by linarith [le_abs_self x]⟩
  linarith
lemma tent_integrable (b : ℝ) : Integrable (fun x : ℝ => max 0 (b-|x|)) := by
  have H := (tent_continuous b).integrableOn_Icc (μ := volume) (a := -b) (b := b)
  have he : (Icc (-b) b).indicator (fun x : ℝ => max 0 (b-|x|)) =
      (fun x : ℝ => max 0 (b-|x|)) := by
    funext x
    by_cases hx : x ∈ Icc (-b) b
    · simp [hx]
    · simp [hx, tent_eq_zero x hx]
  rw [← he]
  exact H.integrable_indicator measurableSet_Icc
lemma tent_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, max 0 (b-|x|)) = b^2 := by
  have hi (a c : ℝ) := (tent_continuous b).intervalIntegrable (μ := volume) a c
  calc
    _ = ∫ x in Icc (-b) b, max 0 (b-|x|) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => tent_eq_zero x hx)).symm
    _ = ∫ x in (-b)..b, max 0 (b-|x|) := by
      rw [intervalIntegral.integral_of_le (by linarith : -b ≤ b), integral_Icc_eq_integral_Ioc]
    _ = (∫ x in (-b)..0, max 0 (b-|x|)) + ∫ x in (0 : ℝ)..b, max 0 (b-|x|) :=
      (intervalIntegral.integral_add_adjacent_intervals (hi (-b) 0) (hi 0 b)).symm
    _ = (∫ x in (-b)..0, b+x) + ∫ x in (0 : ℝ)..b, b-x := by
      congr 1 <;> apply intervalIntegral.integral_congr
      · intro x hx
        dsimp only
        rw [uIcc_of_le (by linarith)] at hx
        rw [abs_of_nonpos hx.2, sub_neg_eq_add, max_eq_right (by linarith [hx.1])]
      · intro x hx
        dsimp only
        rw [uIcc_of_le hb.le] at hx
        rw [abs_of_nonneg hx.1, max_eq_right (by linarith [hx.2])]
    _ = b^2 := by
      rw [intervalIntegral.integral_add (intervalIntegrable_const (c := b)) (show IntervalIntegrable (fun x : ℝ => x) volume _ _ from continuous_id.intervalIntegrable _ _),
        intervalIntegral.integral_sub (intervalIntegrable_const (c := b)) (show IntervalIntegrable (fun x : ℝ => x) volume _ _ from continuous_id.intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
      ring

lemma flatFineKernel_integrable (b : ℝ) : Integrable (flatFineKernel b) := by
  exact ((Integrable.fintype_prod_dep (fun _ : Fin 3 => tent_integrable b)).const_mul ((b⁻¹)^6))

lemma flatFineKernel_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : Fin 3 → ℝ, flatFineKernel b x) = 1 := by
  unfold flatFineKernel
  rw [integral_const_mul,
    integral_fintype_prod_volume_eq_prod (fun (_ : Fin 3) (u : ℝ) => max 0 (b-|u|))]
  simp_rw [tent_integral hb]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hb.ne']

lemma rpow_five_thirds_le_linear {a A : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) :
    a^(5/3 : ℝ) ≤ A^(2/3 : ℝ)*a := by
  calc
    _ = a^(2/3 : ℝ)*a := by
      rw [show (5/3 : ℝ) = 2/3 + 1 by norm_num, Real.rpow_add_one' ha (by norm_num)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hA (by norm_num)) ha

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoulombBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
namespace Coulomb

lemma flatFineKernel_neg (b : ℝ) (x : Fin 3 → ℝ) :
    flatFineKernel b (-x) = flatFineKernel b x := by simp [flatFineKernel]

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2KernelIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
namespace Coulomb
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SigmaFinite ν]

lemma l2_kernel_integral (v : X → Lp ℂ 2 ν) (hv : MemLp v 2 μ)
    (V : X → Y → ℂ) (hV : ∀ t, (v t : Y → ℂ) =ᵐ[ν] V t)
    (hK : MemLp (fun z : X × Y => V z.1 z.2) 2 (μ.prod ν))
    (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hC : ∀ t, ‖c t‖ ≤ C)
    (hF : MemLp (fun y => ∫ t, c t*V t y ∂μ) 2 ν) :
    (∫ t, c t • v t ∂μ) = hF.toLp (fun y => ∫ t, c t*V t y ∂μ) := by
  have hctop : MemLp c ∞ μ := memLp_top_of_bound hc C (Filter.Eventually.of_forall hC)
  have hcv : MemLp (fun t => c t • v t) 2 μ := hv.smul hctop
  have hi := hcv.integrable (by norm_num)
  have hcprod : MemLp (fun z : X × Y => c z.1) ∞ (μ.prod ν) :=
    memLp_top_of_bound hc.comp_fst C (Filter.Eventually.of_forall (fun z => hC z.1))
  have hcvprod : MemLp (fun z : X × Y => c z.1*V z.1 z.2) 2 (μ.prod ν) := hK.mul' hcprod
  apply ext_inner_left ℂ
  intro w
  have hw : MemLp (fun z : X × Y => star (w z.2)) 2 (μ.prod ν) :=
    (Lp.memLp w).star.comp_snd μ
  have hint : Integrable (fun z : X × Y => star (w z.2)*(c z.1*V z.1 z.2)) (μ.prod ν) := by
    exact memLp_one_iff_integrable.mp (hcvprod.mul' hw)
  calc
    inner ℂ w (∫ t, c t • v t ∂μ) = ∫ t, inner ℂ w (c t • v t) ∂μ := by
      exact ((innerSL ℂ w).integral_comp_comm hi).symm
    _ = ∫ t, ∫ y, star (w y)*(c t*V t y) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [inner_smul_right, L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hV t] with y hy
      simp only [RCLike.inner_apply', starRingEnd_apply, hy]
      ring
    _ = ∫ y, ∫ t, star (w y)*(c t*V t y) ∂μ ∂ν := integral_integral_swap hint
    _ = ∫ y, star (w y)*(∫ t, c t*V t y ∂μ) ∂ν := by simp only [integral_const_mul]
    _ = inner ℂ w (hF.toLp _) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with y hy
      simp only [RCLike.inner_apply', starRingEnd_apply, hy]
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SumSwapNonnegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma hasSum_swap_nonnegative {ι κ : Type*} {f : ι × κ → ℝ}
    (hf : ∀ i, 0 ≤ f i) {r : ι → ℝ} {c : κ → ℝ} {s : ℝ}
    (hr : ∀ i, HasSum (fun j => f (i,j)) (r i))
    (hc : ∀ j, HasSum (fun i => f (i,j)) (c j)) (hs : HasSum r s) : HasSum c s := by
  have her : (fun i => ∑' j, f (i,j)) = r := funext (fun i => (hr i).tsum_eq)
  have hec : (fun j => ∑' i, f (i,j)) = c := funext (fun j => (hc j).tsum_eq)
  have hf' : Summable f := (summable_prod_of_nonneg hf).mpr
    ⟨fun i => (hr i).summable, by rw [her]; exact hs.summable⟩
  have hh := hf'.prod_symm.prod.hasSum
  change HasSum (fun j => ∑' i, f (i,j)) (∑' j, ∑' i, f (i,j)) at hh
  rw [hec] at hh
  apply hh.summable.hasSum_iff.mpr
  calc
    (∑' j, c j) = ∑' j, ∑' i, f (i,j) := by rw [hec]
    _ = ∑' i, ∑' j, f (i,j) := (Summable.tsum_comm (f := fun i j => f (i,j)) hf')
    _ = s := by rw [her]; exact hs.tsum_eq

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2MeasureInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb

section
variable {Y : Type*} [MeasurableSpace Y]

noncomputable def l2MeasureInclusion {ν η : Measure Y} (h : η ≤ ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 η where
  toFun := Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h)
  map_add' := by intro u v; exact map_add _ u v
  map_smul' := by
    intro z u
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) (z • u),
      Lp.coeFn_smul z (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) u),
      Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) u,
      (Measure.absolutelyContinuous_of_le h).ae_eq (Lp.coeFn_smul z u)] with y h1 h2 h3 h4
    simp only [h1, h2, h4, Pi.smul_apply, h3, RingHom.id_apply]
  cont := (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h)).continuous

lemma l2MeasureInclusion_coe {ν η : Measure Y} (h : η ≤ ν) (u : Lp ℂ 2 ν) :
    l2MeasureInclusion h u =ᵐ[η] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h) u

end

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_IntegrableTsumSummableNormIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {Y ι : Type*} [MeasurableSpace Y] [Countable ι]

lemma integrable_tsum_of_summable_norm_integral {ν : Measure Y} {F : ι → Y → ℝ}
    (hF : ∀ i, Integrable (F i) ν) (hs : Summable (fun i => ∫ y, ‖F i y‖ ∂ν)) :
    Integrable (fun y => ∑' i, F i y) ν ∧ ∀ᵐ y ∂ν, Summable (fun i => F i y) := by
  let f : ι → Lp ℝ 1 ν := fun i => (hF i).toL1 (F i)
  have hn (i : ι) : ‖f i‖ = ∫ y, ‖F i y‖ ∂ν := by
    rw [Integrable.norm_toL1_eq_lintegral_norm]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (hF i).norm.aestronglyMeasurable).symm
  have he : ∑' i, ‖f i‖ₑ ≠ ⊤ := by
    apply tsum_enorm_ne_top_iff_summable_norm.mpr
    simpa only [hn] using hs
  have ha : ∀ᵐ y ∂ν, ∀ i, f i y = F i y := ae_all_iff.mpr (fun i => (hF i).coeFn_toL1)
  have hb := Lp.hasSum_coeFn_tsum he
  have hc : (fun y => ∑' i, F i y) =ᵐ[ν] (∑' i, f i : Lp ℝ 1 ν) := by
    filter_upwards [ha, hb] with y hy hz
    simpa only [hy] using hz.tsum_eq
  refine ⟨(L1.integrable_coeFn (∑' i, f i)).congr hc.symm, ?_⟩
  filter_upwards [ha, hb] with y hy hz
  simpa only [hy] using hz.summable

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2MultiplierDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma l2_multiplier_distribution {u w : Lp ℂ 2 (volume : Measure E)} (a : E)
    (hw : w =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ) * u ξ) :
    (w : 𝓢'(E,ℂ)) = (2 * Real.pi * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ (fun ξ => (inner ℝ ξ a : ℂ)) (u : 𝓢'(E,ℂ)) := by
  have ht : (fun ξ => (inner ℝ ξ a : ℂ)).HasTemperateGrowth := by fun_prop
  ext φ
  change Lp.toTemperedDistribution w φ = (2 * Real.pi * Complex.I) •
    Lp.toTemperedDistribution u (SchwartzMap.smulLeftCLM ℂ (fun ξ => (inner ℝ ξ a : ℂ)) φ)
  simp only [Lp.toTemperedDistribution_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [hw] with ξ hξ
  simp only [hξ, SchwartzMap.smulLeftCLM_apply ht, smul_eq_mul]
  ring

lemma l2_fourier_weakDeriv_distribution {u w : Lp ℂ 2 (volume : Measure E)} (a : E)
    (hw : w =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ) * (𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ) :
    ∂_{a} (u : 𝓢'(E,ℂ)) = (𝓕⁻ w : Lp ℂ 2 (volume : Measure E)) := by
  have h := l2_multiplier_distribution a hw
  rw [← Lp.fourier_toTemperedDistribution_eq u,
    ← TemperedDistribution.fourier_lineDerivOp_eq] at h
  have H := congrArg (fun z : 𝓢'(E,ℂ) => 𝓕⁻ z) h
  simpa only [Lp.fourierInv_toTemperedDistribution_eq,
    FourierTransform.fourierInv_fourier_eq] using H.symm

lemma l2_fourier_weakDeriv {u w : Lp ℂ 2 (volume : Measure E)} (a : E)
    (hw : w =ᵐ[volume] fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ) * (𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ)
    (φ : E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x : E, (fderiv ℝ φ x a : ℂ) * u x) =
      -(∫ x : E, (φ x : ℂ) * (𝓕⁻ w : Lp ℂ 2 (volume : Measure E)) x) := by
  let φc : E → ℂ := fun x => (φ x : ℂ)
  have hφc : ContDiff ℝ (⊤ : ℕ∞) φc := Complex.ofRealCLM.contDiff.comp hφ
  have hφcC : HasCompactSupport φc := hφC.comp_left Complex.ofReal_zero
  let Φ : 𝓢(E,ℂ) := hφcC.toSchwartzMap hφc
  have h := congrArg (fun T : 𝓢'(E,ℂ) => T Φ) (l2_fourier_weakDeriv_distribution a hw)
  have hd (x : E) : (∂_{a} Φ) x = (fderiv ℝ φ x a : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change fderiv ℝ φc x a = _
    exact congrArg (fun L : E →L[ℝ] ℂ => L a)
      ((Complex.ofRealCLM.hasFDerivAt.comp x
        ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at h
  have h' : -(∫ x : E, (fderiv ℝ φ x a : ℂ) * u x) =
      ∫ x : E, (φ x : ℂ) * (𝓕⁻ w : Lp ℂ 2 (volume : Measure E)) x := by
    have hp (x : E) : Φ x = (φ x : ℂ) := rfl
    simpa only [hd, hp] using h
  simpa only [neg_neg] using congrArg Neg.neg h'

lemma fourierMultiplier_norm_sq (r : ℝ) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I) * (r : ℂ) * z‖^2 = (2*Real.pi*r)^2 * ‖z‖^2 := by
  have he : (2 * Real.pi * Complex.I) * (r : ℂ) * z =
      ((2*Real.pi*r : ℝ) : ℂ) * Complex.I * z := by push_cast; ring
  rw [he, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, mul_pow]
  rw [Real.norm_eq_abs, sq_abs]

lemma l2_norm_sq_fourier (u : Lp ℂ 2 (volume : Measure E)) :
    ‖u‖^2 = ∫ y, ‖u y‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

lemma l2_fourier_weighted_derivative (u : Lp ℂ 2 (volume : Measure E)) (a : E)
    (hI : Integrable (fun ξ => (2*Real.pi*inner ℝ ξ a)^2 *
      ‖(𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ‖^2)) :
    ∃ g : Lp ℂ 2 (volume : Measure E),
      (∀ (φ : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x : E, (fderiv ℝ φ x a : ℂ) * u x) = -(∫ x : E, (φ x : ℂ) * g x)) ∧
      ‖g‖^2 = ∫ ξ, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ‖^2 := by
  let F : E → ℂ := fun ξ => (2 * Real.pi * Complex.I) * (inner ℝ ξ a : ℂ) *
    (𝓕 u : Lp ℂ 2 (volume : Measure E)) ξ
  have hm : AEStronglyMeasurable F volume := by
    exact (by fun_prop : Continuous (fun ξ => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ a : ℂ))).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  have hF : MemLp F 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    simpa only [F, fourierMultiplier_norm_sq] using hI
  refine ⟨𝓕⁻ (hF.toLp F), ?_, ?_⟩
  · intro φ hφ hφC
    exact l2_fourier_weakDeriv a hF.coeFn_toLp φ hφ hφC
  · change ‖(Lp.fourierTransformₗᵢ E ℂ).symm (hF.toLp F)‖^2 = _
    rw [(Lp.fourierTransformₗᵢ E ℂ).symm.norm_map, l2_norm_sq_fourier]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with ξ hξ
    rw [hξ]
    exact fourierMultiplier_norm_sq _ _
end Coulomb

open scoped LineDeriv

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SumSpinDuplicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
namespace Coulomb
lemma hasSum_spin_duplicate {ι : Type*} {f : ι → ℝ} {a : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hs : HasSum f a) :
    HasSum (fun i : ι × Fin 2 => f i.1) (2*a) := by
  have hsum : Summable (fun i : ι × Fin 2 => f i.1) := by
    apply (summable_prod_of_nonneg (fun i => hf i.1)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype,Fin.sum_univ_two,← two_mul] using hs.summable.mul_left 2
  apply hsum.hasSum_iff.mpr
  rw [hsum.tsum_prod]
  simp only [tsum_fintype,Fin.sum_univ_two,← two_mul]
  rw [tsum_mul_left,hs.tsum_eq]

end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FieldSubmean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma square_weighted_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f ρ : X → ℝ) (hρ : Integrable ρ μ) (hp : ∀ x, 0 ≤ ρ x) (hm : (∫ x, ρ x ∂μ)=1)
    (h1 : Integrable (fun x => f x*ρ x) μ) (h2 : Integrable (fun x => f x^2*ρ x) μ) :
    (∫ x, f x*ρ x ∂μ)^2 ≤ ∫ x, f x^2*ρ x ∂μ := by
  let c : ℝ := ∫ x, f x*ρ x ∂μ
  have hsub : Integrable (fun x => f x^2*ρ x-(2*c)*(f x*ρ x)) μ := by
    exact h2.sub (h1.const_mul (2*c))
  have he : (∫ x, (f x-c)^2*ρ x ∂μ) = (∫ x, f x^2*ρ x ∂μ)-2*c^2+c^2 := by
    calc
      _ = ∫ x, (f x^2*ρ x-(2*c)*(f x*ρ x))+c^2*ρ x ∂μ :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = _ := by
        rw [integral_add hsub (hρ.const_mul (c^2)),
          integral_sub h2 (h1.const_mul _),integral_const_mul,integral_const_mul,hm]
        dsimp only [c]
        ring
  have h : 0 ≤ (∫ x, (f x-c)^2*ρ x ∂μ) := integral_nonneg (fun x => mul_nonneg (sq_nonneg (f x-c)) (hp x))
  rw [he] at h
  dsimp only [c] at h
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_OuterJoinConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

noncomputable def outerPerm (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k+m)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr p (Equiv.refl (Fin m)))
lemma outerPerm_left (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    outerPerm m p (Fin.castAdd m i) = Fin.castAdd m (p i) := by simp [outerPerm]
lemma outerPerm_right (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin m) :
    outerPerm m p (Fin.natAdd k i) = Fin.natAdd k i := by simp [outerPerm]
lemma outerPerm_sign (m : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    (outerPerm m p).sign = p.sign := by simp [outerPerm, Equiv.Perm.sign_sumCongr]
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SliceExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma measurable_retained_sum {α : Type*} [MeasurableSpace α] {n : ℕ}
    (r : α → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (f : Fin n → α → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => ∑ i ∈ r x, f i x) := by
  have he (x : α) : (∑ i ∈ r x, f i x) = ∑ i : Fin n, if i ∈ r x then f i x else 0 := by simp
  simp_rw [he]
  exact Finset.measurable_sum _ (fun i _ => Measurable.ite (hr i) (hf i) measurable_const)

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DeletedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def fineLocalizationError (m : ℕ) (b : ℝ) : ℝ :=
  (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (m:ℝ)^(4/3:ℝ) + ((2*Real.pi+1)/(2*b))*m

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_FieldOptimization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
noncomputable section
namespace Coulomb

lemma trial_kinetic_absorption {a M m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hM : m ≤ M) (hs : 1 ≤ a*m^(1/3:ℝ)) : M^(5/3:ℝ) ≤ a*M^2 := by
  have hM0 : 0 ≤ M := hm.trans hM
  have hsM : 1 ≤ a*M^(1/3:ℝ) := hs.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm hM (by norm_num)) ha)
  rcases eq_or_lt_of_le hM0 with h | h
  · simp [←h]
  · have he : M^(5/3:ℝ)*M^(1/3:ℝ) = M^2 := by
      rw [←Real.rpow_add h]
      norm_num
    calc
      M^(5/3:ℝ) ≤ M^(5/3:ℝ)*(a*M^(1/3:ℝ)) :=
        le_mul_of_one_le_right (Real.rpow_nonneg hM0 _) hsM
      _ = a*M^2 := by rw [←he]; ring

theorem positive_field_trial_optimization {E e a h C m : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hm : 0 ≤ m)
    (ham : 1 ≤ a*m) (ham' : 1 ≤ a*m^(1/3:ℝ))
    (htrial : ∀ M : ℝ, 0 ≤ M →
      E ≤ e-M*h+C*(M^(5/3:ℝ)/a^2+M/a^2+M^2/a)) :
    E ≤ e-a*(max h 0)^2/(16*C)+4*C*m^2/a := by
  have hE : E ≤ e := by simpa using htrial 0 (le_refl 0)
  have hp : 0 ≤ max h 0 := le_max_right _ _
  by_cases hh : a*max h 0 ≤ 8*C*m
  · have hs : (a*max h 0)^2 ≤ (8*C*m)^2 :=
      pow_le_pow_left₀ (mul_nonneg ha.le hp) hh 2
    have hg : a*(max h 0)^2/(16*C) ≤ 4*C*m^2/a := by
      apply (div_le_div_iff₀ (by positivity : 0 < 16*C) ha).2
      nlinarith [hs]
    linarith
  · have hh' : 8*C*m < a*max h 0 := lt_of_not_ge hh
    have hhp : 0 < h := by
      by_contra hn
      rw [max_eq_right (le_of_not_gt hn)] at hh'
      have : 0 ≤ 8*C*m := by positivity
      nlinarith
    rw [max_eq_left hhp.le] at hh' ⊢
    let M : ℝ := a*h/(8*C)
    have hM0 : 0 ≤ M := by dsimp [M]; positivity
    have hmM : m ≤ M := by
      apply (le_div_iff₀ (by positivity : 0 < 8*C)).2
      linarith
    have hk := trial_kinetic_absorption ha.le hm hmM ham'
    have hq : C*M^2/a = M*h/8 := by
      dsimp [M]
      field_simp
    have hscale : 8*C ≤ a^2*h := by
      have H := mul_le_mul_of_nonneg_left hh'.le ha.le
      have H' := mul_le_mul_of_nonneg_left ham (show 0 ≤ 8*C by positivity)
      nlinarith
    have hl : C*M/a^2 ≤ M*h/8 := by
      apply (div_le_div_iff₀ (by positivity : 0 < a^2) (by norm_num : (0:ℝ)<8)).2
      nlinarith [mul_le_mul_of_nonneg_left hscale hM0]
    have ht : C*(M^(5/3:ℝ)/a^2) ≤ M*h/8 := by
      calc
        _ ≤ C*(a*M^2/a^2) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hk (sq_nonneg a)) hC.le
        _ = C*M^2/a := by field_simp
        _ = M*h/8 := hq
    have hgain : M*h/2 = a*h^2/(16*C) := by dsimp [M]; ring
    have H := htrial M hM0
    have herr : 0 ≤ 4*C*m^2/a := by positivity
    have hMh : 0 ≤ M*h := mul_nonneg hM0 hhp.le
    rw [mul_add,mul_add] at H
    simp only [←mul_div_assoc] at H ht
    rw [hq] at H
    linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScreeningNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace Coulomb

def screenBaseMass (a : ℝ) : ℝ := max ((a^3)⁻¹) 1

lemma screenBaseMass_nonneg (a : ℝ) : 0 ≤ screenBaseMass a :=
  le_trans (by norm_num) (le_max_right _ _)

lemma screenBaseMass_ge_one (a : ℝ) : 1 ≤ screenBaseMass a := le_max_right _ _

lemma screenBaseMass_scale {a : ℝ} (ha : 0 < a) : 1 ≤ a*screenBaseMass a := by
  by_cases h : 1 ≤ a
  · calc
      1 ≤ a := h
      _ ≤ a*screenBaseMass a := le_mul_of_one_le_right ha.le (screenBaseMass_ge_one a)
  · have h' : a ≤ 1 := (lt_of_not_ge h).le
    have hpow : a^3 ≤ a := by nlinarith [sq_nonneg a,mul_nonneg ha.le (sub_nonneg.mpr h')]
    have hi : a⁻¹ ≤ (a^3)⁻¹ := (inv_le_inv₀ ha (by positivity)).2 hpow
    calc
      1 = a*a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
      _ ≤ a*screenBaseMass a := mul_le_mul_of_nonneg_left (hi.trans (le_max_left _ _)) ha.le

lemma screenBaseMass_cuberoot_scale {a : ℝ} (ha : 0 < a) :
    1 ≤ a*(screenBaseMass a)^(1/3:ℝ) := by
  have hi : ((a^3)⁻¹)^(1/3:ℝ) = a⁻¹ := by
    rw [Real.inv_rpow (pow_nonneg ha.le 3),←Real.rpow_natCast a 3,←Real.rpow_mul ha.le]
    norm_num
  calc
    1 = a*((a^3)⁻¹)^(1/3:ℝ) := by rw [hi,mul_inv_cancel₀ ha.ne']
    _ ≤ a*(screenBaseMass a)^(1/3:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (le_max_left _ _) (by norm_num)) ha.le

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScreenUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace Coulomb

def screenMass (δ a : ℝ) : ℝ := screenBaseMass a+Real.sqrt (δ*a)
def screenEnergy (δ a : ℝ) : ℝ := (screenMass δ a)^2/a

lemma screenMass_ge_base (δ a : ℝ) : screenBaseMass a ≤ screenMass δ a := by
  unfold screenMass
  linarith [Real.sqrt_nonneg (δ*a)]
lemma screenMass_ge_one (δ a : ℝ) : 1 ≤ screenMass δ a :=
  (screenBaseMass_ge_one a).trans (screenMass_ge_base δ a)
lemma screenMass_pos (δ a : ℝ) : 0 < screenMass δ a := lt_of_lt_of_le zero_lt_one (screenMass_ge_one δ a)
lemma screenMass_scale (δ : ℝ) {a : ℝ} (ha : 0<a) : 1 ≤ a*screenMass δ a :=
  (screenBaseMass_scale ha).trans (mul_le_mul_of_nonneg_left (screenMass_ge_base δ a) ha.le)
lemma screenEnergy_pos (δ : ℝ) {a : ℝ} (ha : 0<a) : 0 < screenEnergy δ a :=
  div_pos (sq_pos_of_pos (screenMass_pos δ a)) ha
lemma screenEnergy_ge_offset {δ a : ℝ} (hδ : 0 ≤ δ) (ha : 0<a) : δ ≤ screenEnergy δ a := by
  rw [screenEnergy,le_div_iff₀ ha]
  have hm : Real.sqrt (δ*a) ≤ screenMass δ a := by
    unfold screenMass
    linarith [screenBaseMass_nonneg a]
  have H := pow_le_pow_left₀ (Real.sqrt_nonneg (δ*a)) hm 2
  rwa [Real.sq_sqrt (mul_nonneg hδ ha.le)] at H

lemma screenBaseMass_comparable {a b q : ℝ} (ha : 0<a) (hq : 1 ≤ q)
    (hab : a/q ≤ b) : screenBaseMass b ≤ q^3*screenBaseMass a := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hb : 0<b := lt_of_lt_of_le (div_pos ha hq0) hab
  have H : a ≤ b*q := (div_le_iff₀ hq0).mp hab
  have H3 := pow_le_pow_left₀ ha.le H 3
  have Hi : (b^3)⁻¹ ≤ q^3*(a^3)⁻¹ := by
    calc
      (b^3)⁻¹=q^3/(b*q)^3 := by field_simp
      _ ≤ q^3/a^3 := div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (pow_pos ha _) H3
      _ = q^3*(a^3)⁻¹ := div_eq_mul_inv _ _
  apply max_le
  · exact Hi.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hq0.le 3))
  · exact (one_le_pow₀ hq).trans (le_mul_of_one_le_right (pow_nonneg hq0.le 3) (screenBaseMass_ge_one a))

lemma screenMass_comparable {δ a b q : ℝ} (hδ : 0 ≤ δ) (ha : 0<a) (hq : 1 ≤ q)
    (hab : a/q ≤ b) (hba : b ≤ a*q) : screenMass δ b ≤ q^3*screenMass δ a := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hb : 0<b := lt_of_lt_of_le (div_pos ha hq0) hab
  have hq6 : q ≤ q^6 := by
    calc
      q=q^1 := by simp
      _ ≤ q^6 := pow_le_pow_right₀ hq (by omega)
  have hroot : Real.sqrt (δ*b) ≤ q^3*Real.sqrt (δ*a) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow,Real.sq_sqrt (mul_nonneg hδ ha.le)]
      have hb' : b ≤ a*q^6 := hba.trans (mul_le_mul_of_nonneg_left hq6 ha.le)
      nlinarith [mul_le_mul_of_nonneg_left hb' hδ]
  unfold screenMass
  nlinarith [screenBaseMass_comparable ha hq hab]

lemma screenEnergy_comparable {δ a b q : ℝ} (hδ : 0 ≤ δ) (ha : 0<a) (hq : 1 ≤ q)
    (hab : a/q ≤ b) (hba : b ≤ a*q) : screenEnergy δ b ≤ q^7*screenEnergy δ a := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hb : 0<b := lt_of_lt_of_le (div_pos ha hq0) hab
  have H := screenMass_comparable hδ ha hq hab hba
  have H2 := pow_le_pow_left₀ (screenMass_pos δ b).le H 2
  unfold screenEnergy
  calc
    (screenMass δ b)^2/b ≤ (q^3*screenMass δ a)^2/(a/q) :=
      div_le_div₀ (sq_nonneg _) H2 (div_pos ha hq0) hab
    _ = q^7*((screenMass δ a)^2/a) := by field_simp

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScreenNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Coulomb

lemma screening_ims_units {P a m : ℝ} (hP : 1 ≤ P) (ha : 0<a) (hm : 0 ≤ m)
    (hscale : 1 ≤ a*m) : Real.sqrt P*m/a^2 ≤ P*m^2/a := by
  have hp0 : 0 ≤ P := by linarith
  have hs : Real.sqrt P ≤ P := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hp0,by nlinarith⟩
  have hmass : m ≤ a*m^2 := by nlinarith [mul_le_mul_of_nonneg_left hscale hm]
  calc
    _ ≤ P*m/a^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs hm) (sq_nonneg _)
    _ ≤ P*(a*m^2)/a^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hp0) (sq_nonneg _)
    _ = _ := by field_simp

lemma screening_gain_normalized {a b q K P e w r B : ℝ}
    (ha : 0<a) (hb : 0<b) (hq : 0<q) (hK : 0<K) (hw : 0<w)
    (hr : 0 ≤ r) (hscale : a ≤ q*b) (hunit : a*w^2=P*e)
    (hgain : b/(16*K)*r ≤ P*q^7*e*B) :
    (Real.sqrt r/w)^2 ≤ 16*K*q^8*B := by
  rw [div_pow,Real.sq_sqrt hr,div_le_iff₀ (sq_pos_of_pos hw)]
  have hg : b*r ≤ 16*K*(P*q^7*e*B) := by
    have H := (div_le_iff₀ (show 0<16*K by positivity)).mp
      (show b*r/(16*K) ≤ P*q^7*e*B by simpa only [div_mul_eq_mul_div] using hgain)
    simpa only [mul_comm (16*K)] using H
  have H := mul_le_mul_of_nonneg_left hg hq.le
  have hl := mul_le_mul hscale (le_refl r) hr (mul_nonneg hq.le hb.le)
  have HH : a*r ≤ a*(16*K*q^8*B*w^2) := by
    calc
      _ ≤ q*(b*r) := by nlinarith
      _ ≤ q*(16*K*(P*q^7*e*B)) := H
      _ = (P*e)*(16*K*q^8*B) := by ring
      _ = _ := by rw [←hunit]; ring
  exact (mul_le_mul_iff_right₀ ha).mp HH

lemma screening_polynomial_bound {I K M G t L J : ℝ}
    (hI : 0 ≤ I) (hK : 0 ≤ K) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (_ht : 0 ≤ t) (hL : 0 ≤ L) (hJ : 1 ≤ J) (htJ : t ≤ J) (hLM : L ≤ J*M) :
    1+t*I+4*K+3*L*G+L^3 ≤ (1+I+4*K+3*M+M^3)*J^3*(1+G) := by
  have hj0 : 0 ≤ J := by linarith
  have hj3 : 1 ≤ J^3 := one_le_pow₀ hJ
  have hj : J ≤ J^3 := by simpa only [pow_one] using pow_le_pow_right₀ hJ (show 1 ≤ 3 by omega)
  have htI : t*I ≤ J^3*I := mul_le_mul_of_nonneg_right (htJ.trans hj) hI
  have h4 : 4*K ≤ J^3*(4*K) := le_mul_of_one_le_left (by positivity) hj3
  have hLG : 3*L*G ≤ J^3*(3*M*G) := by
    have hL' := hLM.trans (mul_le_mul_of_nonneg_right hj hM)
    nlinarith [mul_le_mul_of_nonneg_right hL' hG]
  have hLc : L^3 ≤ J^3*M^3 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hL hLM 3
  have hp : 1+I+4*K+M^3 ≥ 0 := by positivity
  calc
    _ ≤ J^3*(1+I+4*K+3*M*G+M^3) := by nlinarith
    _ ≤ J^3*((1+I+4*K+3*M+M^3)*(1+G)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hj0 _)
      nlinarith [mul_nonneg hG hp]
    _ = _ := by ring

lemma screening_exponential_majorant {A : ℝ} (hA : 1 ≤ A) (j : ℕ) :
    A*((4:ℝ)^(j+1))^8*((j+1:ℕ):ℝ)^3 ≤ (A*524288)^(j+1) := by
  have hj : ((j+1:ℕ):ℝ) ≤ 2^(j+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=j+1)).le
  have hj3 : ((j+1:ℕ):ℝ)^3 ≤ (8:ℝ)^(j+1) := by
    calc
      _ ≤ (2^(j+1):ℝ)^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hj _
      _ = _ := by rw [←pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have ha : A ≤ A^(j+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hA (show 1 ≤ j+1 by omega)
  have hae : 0 ≤ A := by linarith
  calc
    _ ≤ A*((4:ℝ)^(j+1))^8*(8:ℝ)^(j+1) :=
      mul_le_mul_of_nonneg_left hj3 (mul_nonneg hae (by positivity))
    _ = A*(524288:ℝ)^(j+1) := by
      rw [←pow_mul (4:ℝ), Nat.mul_comm (j+1) 8, pow_mul]
      rw [mul_assoc,←mul_pow]
      norm_num
    _ ≤ A^(j+1)*(524288:ℝ)^(j+1) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := (mul_pow _ _ _).symm

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def screenFieldUnit (δ P a : ℝ) : ℝ := Real.sqrt P*screenMass δ a/a
lemma screenFieldUnit_pos {δ P a : ℝ} (hP : 1 ≤ P) (ha : 0<a) : 0 < screenFieldUnit δ P a :=
  div_pos (mul_pos (Real.sqrt_pos.mpr (by linarith)) (screenMass_pos δ a)) ha
lemma screenFieldUnit_square {δ P a : ℝ} (hP : 0 ≤ P) (ha : 0<a) :
    a*(screenFieldUnit δ P a)^2=P*screenEnergy δ a := by
  unfold screenFieldUnit screenEnergy
  rw [div_pow,mul_pow,Real.sq_sqrt hP]
  field_simp
lemma screenFieldUnit_product {δ P a : ℝ} (hP : 0 ≤ P) :
    Real.sqrt P*screenMass δ a*screenFieldUnit δ P a=P*screenEnergy δ a := by
  unfold screenFieldUnit screenEnergy
  have hs := Real.sq_sqrt hP
  calc
    _ = (Real.sqrt P)^2*(screenMass δ a)^2/a := by ring
    _ = _ := by rw [hs]; ring

lemma sqrt_count_raw_product {X P m w G : ℝ} (hP : 0 ≤ P) (hm : 0 ≤ m)
    (hw : 0 ≤ w) (hG : 0 ≤ G) (hX : X ≤ P*m^2) :
    Real.sqrt (X*(8*(w*G)^2)) ≤ 3*Real.sqrt P*m*w*G := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ P*m^2*(8*(w*G)^2) := mul_le_mul_of_nonneg_right hX (by positivity)
    _ ≤ (3*Real.sqrt P*m*w*G)^2 := by
      simp only [mul_pow,Real.sq_sqrt hP]
      nlinarith [mul_nonneg (mul_nonneg hP (sq_nonneg m)) (sq_nonneg (w*G))]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GeometricRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma square_recursion_bounded {x : ℕ → ℝ} {B : ℝ}
    (hb : ∀ j, x j≤B) (hs : ∀ j, (x j)^2-1≤x (j+1)) : x 0≤2 := by
  by_contra hn
  have hx0 : 2<x 0 := lt_of_not_ge hn
  have hg : ∀ j : ℕ, x 0+(j:ℝ)≤x j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hj : 2≤x j := by linarith [Nat.cast_nonneg (α:=ℝ) j]
      have hp := mul_nonneg (sub_nonneg.mpr hj) (show 0≤x j+1 by linarith)
      have hstep := hs j
      push_cast
      nlinarith
  obtain ⟨j,hj⟩ := exists_nat_gt (B-x 0)
  have hh := hg j
  have hh' := hb j
  linarith

lemma normalized_square_step {a c g h : ℝ} (ha : 1≤a) (hc : 1 ≤ c)
    (hstep : g^2≤a*(1+h)) : (g/(a*c))^2-1≤h/(a*c*c) := by
  have ha0 : 0<a := by linarith
  have hc0 : 0 < c := by linarith
  have hprod : a≤a*c := le_mul_of_one_le_right ha0.le hc
  have hsq : a≤(a*c)^2 := by nlinarith
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (mul_pos ha0 hc0))).mp
  calc
    (a*c)^2*((g/(a*c))^2-1)=g^2-(a*c)^2 := by field_simp
    _ ≤ a*h := by nlinarith
    _ = (a*c)^2*(h/(a*c*c)) := by field_simp

theorem geometric_screening_recursion_all {g : ℕ → ℝ} {C D : ℝ}
    (hC : 1≤C) (hD : 0≤D)
    (hcap : ∀ j, g j≤D*C^(j+1))
    (hstep : ∀ j, (g j)^2≤C^(j+1)*(1+g (j+1))) (l : ℕ) :
    g l≤2*C^(l+2) := by
  let x : ℕ → ℝ := fun j => g j/C^(j+2)
  have hC0 : 0<C := by linarith
  have hb : ∀ j, x j≤D := by
    intro j
    dsimp [x]
    rw [div_le_iff₀ (pow_pos hC0 _)]
    apply (hcap j).trans
    apply mul_le_mul_of_nonneg_left _ hD
    exact pow_le_pow_right₀ hC (by omega)
  have hs : ∀ j, (x j)^2-1≤x (j+1) := by
    intro j
    have H := normalized_square_step (one_le_pow₀ hC : 1≤C^(j+1)) hC (hstep j)
    simpa only [x,show j+2=(j+1)+1 by omega,show j+1+2=((j+1)+1)+1 by omega,pow_succ] using H
  have H := square_recursion_bounded (x:=fun j => x (l+j))
    (fun j => hb (l+j)) (fun j => by simpa only [Nat.add_assoc] using hs (l+j))
  simp only [Nat.add_zero,x] at H
  exact (div_le_iff₀ (pow_pos hC0 _)).mp H

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_MinimizerMidpointControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma exists_minimizer_of_midpoint_control {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {S : Set E} (hS : IsClosed S) (hne : S.Nonempty)
    (hm : ∀ f ∈ S, ∀ g ∈ S, (1/2:ℝ) • (f+g) ∈ S)
    {J : E → ℝ} (hJ : Continuous J) (hb : BddBelow (J '' S))
    (hconv : ∀ f ∈ S, ∀ g ∈ S, J ((1/2:ℝ) • (f+g)) ≤ (J f+J g)/2)
    (hR : ∀ a : ℝ, ∃ R : ℝ, 0 < R ∧ ∀ f ∈ S, J f ≤ a → ‖f‖ ≤ R)
    (hgap : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ f ∈ S, ∀ g ∈ S, ‖f‖ ≤ R → ‖g‖ ≤ R →
        ‖f-g‖^(5/3:ℝ) ≤ C * ((J f+J g)/2 - J ((1/2:ℝ) • (f+g)))^(5/6:ℝ)) :
    ∃ f ∈ S, ∀ g ∈ S, J f ≤ J g := by
  let I := sInf (J '' S)
  obtain ⟨u, hu, hulim, huS⟩ := exists_seq_tendsto_sInf (hne.image J) hb
  choose f hfS hfu using huS
  obtain ⟨R,hR0,hRb⟩ := hR (u 0)
  have hfR (n : ℕ) : ‖f n‖ ≤ R := hRb _ (hfS n) (by rw [hfu]; exact hu (Nat.zero_le n))
  obtain ⟨C,hC,hCb⟩ := hgap R hR0
  have hlow {g : E} (hg : g ∈ S) : I ≤ J g := csInf_le hb ⟨g,hg,rfl⟩
  have huI (n : ℕ) : 0 ≤ u n-I := by have := hlow (hfS n); rw [hfu] at this; linarith
  have hwlim : Tendsto (fun n => C*(u n-I)^(5/6:ℝ)) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => u n-I) atTop (𝓝 (0:ℝ)) := by
      simpa only [I,sub_self] using hulim.sub_const I
    have hlr := hl.rpow_const (p := (5/6:ℝ)) (Or.inr (by norm_num))
    simpa using hlr.const_mul C
  have hcauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hεp : 0 < ε^(5/3:ℝ) := Real.rpow_pos_of_pos hε _
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hwlim.eventually (gt_mem_nhds hεp))
    refine ⟨N,fun m hm' n hn' => ?_⟩
    have hmid := hlow (hm _ (hfS m) _ (hfS n))
    have hg0 : 0 ≤ (J (f m)+J (f n))/2-J ((1/2:ℝ) • (f m+f n)) := by
      exact sub_nonneg.mpr (hconv _ (hfS m) _ (hfS n))
    have hgup : (J (f m)+J (f n))/2-J ((1/2:ℝ) • (f m+f n)) ≤ u N-I := by
      have hum := hu hm'
      have hun := hu hn'
      rw [← hfu m] at hum
      rw [← hfu n] at hun
      linarith
    have H := (hCb _ (hfS m) _ (hfS n) (hfR m) (hfR n)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg0 hgup (by norm_num : (0:ℝ)≤5/6)) hC.le)
    have Hlt := H.trans_lt (hN N le_rfl)
    have hd : ‖f m-f n‖ < ε := (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le (by norm_num : (0:ℝ)<5/3)).mp Hlt
    simpa only [dist_eq_norm] using hd
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hgS : g ∈ S := hS.mem_of_tendsto hg (Eventually.of_forall hfS)
  have hJI : J g = I := by
    apply tendsto_nhds_unique (hJ.continuousAt.tendsto.comp hg)
    simpa only [Function.comp_def,hfu] using hulim
  exact ⟨g,hgS,fun x hx => by rw [hJI]; exact hlow hx⟩
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_Axis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hn : IsLocalMin f x := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hm, hn] with y hy hz
    exact le_antisymm hy hz
  have hed : deriv f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [he.eventually_nhds] with y hy
    have hy' : f =ᶠ[𝓝 y] fun _ => f x := hy
    simpa using hy'.deriv_eq
  have : deriv (deriv f) x = 0 := by simpa using hed.deriv_eq
  linarith

def axis (a : Fin 3) : Position := EuclideanSpace.single a 1

def coordinateLaplacian (f : Position → ℝ) (x : Position) : ℝ :=
  ∑ a : Fin 3, deriv (deriv (fun t : ℝ => f (x+t • axis a))) 0

theorem coordinateLaplacian_nonpos_of_local_max {f : Position → ℝ} {x : Position}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : coordinateLaplacian f x ≤ 0 := by
  apply Finset.sum_nonpos
  intro a _
  have hl : ContinuousAt (fun t : ℝ => x+t • axis a) 0 := by fun_prop
  have hl' : Tendsto (fun t : ℝ => x+t • axis a) (𝓝 0) (𝓝 x) := by simpa using hl.tendsto
  apply second_deriv_nonpos_of_local_max
  · change ∀ᶠ t in 𝓝 0, f (x+t • axis a) ≤ f (x+0 • axis a)
    simpa only [zero_smul, add_zero] using hl'.eventually hm
  · simpa only [ContinuousAt, Function.comp_def, zero_smul, add_zero] using hc.tendsto.comp hl'

theorem norm_sq_axis_shift (x : Position) (a : Fin 3) (t : ℝ) :
    ‖x+t • axis a‖^2 = ‖x‖^2 + 2*t*x a + t^2 := by
  rw [norm_add_sq_real]
  simp [axis, inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    Real.norm_eq_abs, sq_abs]
  ring

theorem second_deriv_quadratic_rpow {q b p : ℝ} (hq : 0 < q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2 + 2*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      ((hasDerivAt_id t).pow 2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  have hQ0 : Q 0 = q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0 : ℝ), Q t ≠ 0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hder : deriv (fun t => Q t ^ p) =ᶠ[𝓝 0]
      fun t => p*Q t^(p-1)*(2*b+2*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hder.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
      (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul 2))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*2) 0 := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv]
  rw [show p-1-1 = p-2 by ring]
  ring

theorem deriv_affine_line {f : Position → ℝ} {x v : Position} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x+t • v)) :
    deriv (fun u : ℝ => f (x+u • v)) t = fderiv ℝ f (x+t • v) v := by
  have hl : HasDerivAt (fun u : ℝ => x+u • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf.hasFDerivAt.comp_hasDerivAt t hl).deriv

theorem second_deriv_affine_line {f : Position → ℝ} {x v : Position}
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun u : ℝ => f (x+u • v))) 0 =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hl : Tendsto (fun u : ℝ => x+u • v) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun u : ℝ => x+u • v) 0 by fun_prop).tendsto
  have he : deriv (fun u : ℝ => f (x+u • v)) =ᶠ[𝓝 0]
      fun u => fderiv ℝ f (x+u • v) v := by
    filter_upwards [hl.eventually (hf.eventually (by norm_num))] with u hu
    exact deriv_affine_line (hu.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiffAt_const).differentiableAt_one
  simpa using deriv_affine_line (x := x) (v := v) (t := 0) (by simpa using hd)

theorem coordinateLaplacian_reflect (f : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => f (x-z)) y = coordinateLaplacian f (x-y) := by
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun t : ℝ => f (x-(y+t • axis a))) =
      (fun t : ℝ => f ((x-y)+(-t) • axis a)) := by
    ext t
    congr 1
    module
  rw [he]
  let g : ℝ → ℝ := fun t => f ((x-y)+t • axis a)
  change deriv (deriv (fun t => g (-t))) 0 = deriv (deriv g) 0
  have hd : deriv (fun t => g (-t)) = fun t => -deriv g (-t) := by
    ext t
    exact deriv_comp_neg g t
  rw [hd]
  change deriv (-(fun t => deriv g (-t))) 0 = _
  rw [deriv.neg, deriv_comp_neg]
  simp

open scoped Convolution
open ContinuousLinearMap

def dirPartial (f : Position → ℝ) (v : Position) : Position → ℝ :=
  fun x => fderiv ℝ f x v

theorem contDiff_partial {f : Position → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ (n+1) f) (v : Position) : ContDiff ℝ n (dirPartial f v) := by
  exact (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem hasCompactSupport_partial {f : Position → ℝ} (hf : HasCompactSupport f)
    (v : Position) : HasCompactSupport (dirPartial f v) := hf.fderiv_apply ℝ v

theorem partial_convolution {f g : Position → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (x v : Position) :
    dirPartial (f ⋆[lsmul ℝ ℝ, volume] g) v x =
      (f ⋆[lsmul ℝ ℝ, volume] dirPartial g v) x := by
  unfold dirPartial
  rw [(hcg.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf hg x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) hf (hcg.fderiv ℝ)
    (hg.continuous_fderiv (by norm_num)) x v

theorem coordinateLaplacian_eq_partials {f : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) :
    coordinateLaplacian f x = ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x := by
  apply Finset.sum_congr rfl
  intro a _
  exact second_deriv_affine_line hf

theorem coordinateLaplacian_convolution {f g : Position → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) (x : Position) :
    coordinateLaplacian (f ⋆[lsmul ℝ ℝ, volume] g) x =
      ∫ y, f y * coordinateLaplacian g (x-y) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hc : ContDiff ℝ 2 (f ⋆[lsmul ℝ ℝ, volume] g) :=
    hcg.contDiff_convolution_right (lsmul ℝ ℝ) hf hg
  rw [coordinateLaplacian_eq_partials (hc.contDiffAt)]
  have hpart (a : Fin 3) : dirPartial (f ⋆[lsmul ℝ ℝ, volume] g) (axis a) =
      f ⋆[lsmul ℝ ℝ, volume] dirPartial g (axis a) := by
    ext y
    exact partial_convolution hf hg1 hcg y (axis a)
  simp_rw [hpart]
  have hgpart (a : Fin 3) : ContDiff ℝ 1 (dirPartial g (axis a)) := by
    exact contDiff_partial hg (axis a)
  simp_rw [partial_convolution hf (hgpart _) (hasCompactSupport_partial hcg _) x]
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with y
    rw [coordinateLaplacian_eq_partials hg.contDiffAt, Finset.mul_sum]
  · intro a _
    have hs := hasCompactSupport_partial (hasCompactSupport_partial hcg (axis a)) (axis a)
    have hd : Continuous (dirPartial (dirPartial g (axis a)) (axis a)) := by
      exact ((hgpart a).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hs.convolutionExists_right (lsmul ℝ ℝ) hf hd x

theorem dirPartial_sub {f g : Position → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Position) :
    dirPartial (fun x => f x-g x) v = fun x => dirPartial f v x-dirPartial g v x := by
  ext x
  exact congrArg (fun T : Position →L[ℝ] ℝ => T v) (fderiv_sub (hf x) (hg x))

theorem coordinateLaplacian_sub {f g : Position → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Position) :
    coordinateLaplacian (fun y => f y-g y) x =
      coordinateLaplacian f x-coordinateLaplacian g x := by
  rw [coordinateLaplacian_eq_partials (hf.sub hg).contDiffAt,
    coordinateLaplacian_eq_partials hf.contDiffAt, coordinateLaplacian_eq_partials hg.contDiffAt,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [dirPartial_sub (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  rw [dirPartial_sub ((contDiff_partial (n := 1) hf (axis a)).differentiable (by norm_num))
    ((contDiff_partial (n := 1) hg (axis a)).differentiable (by norm_num))]

theorem coordinateLaplacian_quadratic (z x : Position) (c : ℝ) :
    coordinateLaplacian (fun y => c*‖y-z‖^2) x = 6*c := by
  unfold coordinateLaplacian
  have he (a : Fin 3) : (fun t : ℝ => c*‖x+t • axis a-z‖^2) =
      fun t : ℝ => c*(‖x-z‖^2+2*t*(x-z) a+t^2) := by
    ext t
    rw [show x+t • axis a-z = (x-z)+t • axis a by module, norm_sq_axis_shift]
  simp_rw [he]
  have hd (a : Fin 3) : deriv (fun t : ℝ => c*(‖x-z‖^2+2*t*(x-z) a+t^2)) =
      fun t => c*(2*(x-z) a+2*t) := by
    ext t
    convert (((hasDerivAt_const t (‖x-z‖^2)).add
      (((hasDerivAt_id t).const_mul 2).mul_const ((x-z) a))).add
      ((hasDerivAt_id t).pow 2)).const_mul c |>.deriv using 1
    all_goals try with_reducible_and_instances rfl
    all_goals norm_num [id_eq, Pi.add_apply]
  simp_rw [hd]
  have hdd (a : Fin 3) : deriv (fun t : ℝ => c*(2*(x-z) a+2*t)) 0 = 2*c := by
    convert (((hasDerivAt_const 0 (2*(x-z) a)).add
      ((hasDerivAt_id 0).const_mul 2)).const_mul c).deriv using 1
    all_goals try with_reducible_and_instances rfl
    all_goals norm_num [id_eq, Pi.add_apply]
    ring
  simp_rw [hdd]
  simp
  ring

def WeakLaplacianLower (f : Position → ℝ) (U : Set Position) (c : ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) →
      c*(∫ x, φ x) ≤ ∫ x, f x*coordinateLaplacian φ x

theorem normed_bump_reflect_tsupport (φ : ContDiffBump (0 : Position)) (x : Position) :
    tsupport (fun y => φ.normed volume (x-y)) ⊆ Metric.closedBall x φ.rOut := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  have hy' : x-y ∈ Function.support (φ.normed volume) := hy
  rw [φ.support_normed_eq] at hy'
  have hh : ‖x-y‖ < φ.rOut := by simpa using hy'
  simpa only [Metric.mem_closedBall, dist_eq_norm_sub'] using hh.le

theorem continuous_convolution_comm (f g : Position → ℝ) :
    f ⋆[lsmul ℝ ℝ, volume] g = g ⋆[lsmul ℝ ℝ, volume] f := by
  ext x
  rw [convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [] with y
  exact mul_comm _ _

theorem weakLaplacianLower_mollify {f : Position → ℝ} {U : Set Position} {c : ℝ}
    (hf : LocallyIntegrable f volume) (hw : WeakLaplacianLower f U c)
    (φ : ContDiffBump (0 : Position)) {x : Position}
    (hx : Metric.closedBall x φ.rOut ⊆ U) :
    c ≤ coordinateLaplacian (f ⋆[lsmul ℝ ℝ, volume] φ.normed volume) x := by
  have ht := normed_bump_reflect_tsupport φ x
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    (isCompact_closedBall x φ.rOut).of_isClosed_subset (isClosed_tsupport _) ht
  have hs : ContDiff ℝ ∞ (fun y => φ.normed volume (x-y)) :=
    φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hb := hw _ hs hc (ht.trans hx) (fun y => φ.nonneg_normed _)
  rw [integral_sub_left_eq_self, φ.integral_normed, mul_one] at hb
  rw [coordinateLaplacian_convolution hf φ.contDiff_normed φ.hasCompactSupport_normed]
  simpa only [coordinateLaplacian_reflect] using hb

theorem integrable_normed_bump_reflect (φ : ContDiffBump (0 : Position)) (x : Position) :
    Integrable (fun y => φ.normed volume (x-y)) := by
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    (isCompact_closedBall x φ.rOut).of_isClosed_subset (isClosed_tsupport _)
      (normed_bump_reflect_tsupport φ x)
  exact (φ.continuous_normed.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport hc

theorem mollify_le_of_bound {f : Position → ℝ} {U : Set Position} {a : ℝ}
    (hf : LocallyIntegrable f volume) (hbound : ∀ y ∈ U, f y ≤ a)
    (φ : ContDiffBump (0 : Position)) {x : Position}
    (hx : Metric.closedBall x φ.rOut ⊆ U) :
    (f ⋆[lsmul ℝ ℝ, volume] φ.normed volume) x ≤ a := by
  have hi := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_right (lsmul ℝ ℝ) hf
    φ.continuous_normed x
  calc
    _ ≤ ∫ y, a*φ.normed volume (x-y) := by
      apply integral_mono hi ((integrable_normed_bump_reflect φ x).const_mul a)
      intro y
      by_cases hy : φ.normed volume (x-y) = 0
      · simp [hy]
      · have hm : y ∈ tsupport (fun y => φ.normed volume (x-y)) := subset_closure hy
        exact mul_le_mul_of_nonneg_right
          (hbound y (hx (normed_bump_reflect_tsupport φ x hm))) (φ.nonneg_normed _)
    _ = a := by rw [integral_const_mul, integral_sub_left_eq_self, φ.integral_normed, mul_one]

theorem no_maximum_of_strict_weakLaplacian {f : Position → ℝ} {o : Position} {R c : ℝ}
    (hf : Continuous f) (hR : 0 < R) (hc : 0 < c)
    (hw : WeakLaplacianLower f (Metric.ball o R) c)
    (hmax : ∀ y ∈ Metric.ball o R, f y ≤ f o) : False := by
  let r := R/2
  let η := c/12
  let κ := η*r^2/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have he : ∀ᶠ y in 𝓝 o, dist (f y) (f o) < κ :=
    hf.continuousAt.eventually (Metric.ball_mem_nhds _ hκ)
  obtain ⟨d, hd, hfd⟩ := Metric.mem_nhds_iff.mp he
  let e := min (R/4) (d/2)
  have hep : 0 < e := by dsimp [e]; positivity
  let φ : ContDiffBump (0 : Position) := ⟨e/2, e, by positivity, by linarith⟩
  have hφR : φ.rOut ≤ R/4 := min_le_left _ _
  have hφd : φ.rOut < d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let u := f ⋆[lsmul ℝ ℝ, volume] φ.normed volume
  have hu : ContDiff ℝ 2 u := φ.hasCompactSupport_normed.contDiff_convolution_right
    (lsmul ℝ ℝ) hf.locallyIntegrable φ.contDiff_normed
  have hcenter : f o-κ ≤ u o := by
    have hh := φ.dist_normed_convolution_le (μ := volume) (g := f) (x₀ := o) hf.aestronglyMeasurable (fun y hy =>
      (hfd (lt_trans hy hφd)).le)
    rw [continuous_convolution_comm] at hh
    rw [Real.dist_eq] at hh
    exact sub_le_iff_le_add.mpr (by linarith [(abs_le.mp hh).1])
  have hinside {x : Position} (hx : x ∈ Metric.closedBall o r) :
      Metric.closedBall x φ.rOut ⊆ Metric.ball o R := by
    intro y hy
    apply lt_of_le_of_lt (dist_triangle y x o)
    have hxy : dist y x ≤ φ.rOut := hy
    have hxo : dist x o ≤ r := hx
    dsimp [r] at hxo
    linarith
  have hub {x : Position} (hx : x ∈ Metric.closedBall o r) : u x ≤ f o :=
    mollify_le_of_bound hf.locallyIntegrable hmax φ (hinside hx)
  let v : Position → ℝ := fun x => u x-η*‖x-o‖^2
  have hq : ContDiff ℝ 2 (fun y : Position => η*‖y-o‖^2) :=
    contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  have hv : ContDiff ℝ 2 v := hu.sub hq
  obtain ⟨x, hx, hxm⟩ := (isCompact_closedBall o r).exists_isMaxOn
    ⟨o, Metric.mem_closedBall_self hr.le⟩ hv.continuous.continuousOn
  have hvcenter : f o-η*r^2 < v o := by
    dsimp [v]
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
    dsimp [κ] at hcenter
    nlinarith [sq_pos_of_pos hr]
  have hxi : x ∈ Metric.ball o r := by
    by_contra hn
    have hdist : ‖x-o‖ = r := by
      apply le_antisymm
      · exact hx
      · exact le_of_not_gt hn
    have hvb : v x ≤ f o-η*r^2 := by dsimp [v]; rw [hdist]; linarith [hub hx]
    have hcx : v o ≤ v x := hxm (Metric.mem_closedBall_self hr.le)
    linarith
  have hlmax : IsLocalMax v x := hxm.isLocalMax
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxi) Metric.ball_subset_closedBall)
  have hl := coordinateLaplacian_nonpos_of_local_max hlmax hv.continuous.continuousAt
  have hp := weakLaplacianLower_mollify hf.locallyIntegrable hw φ (hinside hx)
  change coordinateLaplacian (fun y => u y-η*‖y-o‖^2) x ≤ 0 at hl
  rw [coordinateLaplacian_sub hu hq, coordinateLaplacian_quadratic] at hl
  change c ≤ coordinateLaplacian u x at hp
  dsimp [η] at hl
  linarith

theorem coordinateLaplacian_congr_nhds {f g : Position → ℝ} {x : Position}
    (h : f =ᶠ[𝓝 x] g) : coordinateLaplacian f x = coordinateLaplacian g x := by
  apply Finset.sum_congr rfl
  intro a _
  have ht : Tendsto (fun t : ℝ => x+t • axis a) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun t : ℝ => x+t • axis a) 0 by fun_prop).tendsto
  have he : (fun t : ℝ => f (x+t • axis a)) =ᶠ[𝓝 0]
      (fun t : ℝ => g (x+t • axis a)) := ht.eventually h
  exact he.deriv.deriv_eq

theorem coordinateLaplacian_zero (x : Position) :
    coordinateLaplacian (fun _ => (0 : ℝ)) x = 0 := by
  simp [coordinateLaplacian]

theorem coordinateLaplacian_eq_zero_of_notMem_tsupport {f : Position → ℝ} {x : Position}
    (h : x ∉ tsupport f) : coordinateLaplacian f x = 0 := by
  rw [coordinateLaplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp h)]
  exact coordinateLaplacian_zero x

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WeakLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem WeakLaplacianLower.congr {f g : Position → ℝ} {U : Set Position} {c : ℝ}
    (h : WeakLaplacianLower f U c) (he : Set.EqOn f g U) : WeakLaplacianLower g U c := by
  intro φ hφ hc ht hp
  convert h φ hφ hc ht hp using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport φ
  · rw [he (ht hx)]
  · simp only [coordinateLaplacian_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem no_maximum_of_strict_weakLaplacian_local
    {f : Position → ℝ} {o : Position} {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hf : ContinuousOn f (Metric.closedBall o R))
    (hw : WeakLaplacianLower f (Metric.ball o R) c)
    (hm : ∀ x ∈ Metric.ball o R, f x ≤ f o) : False := by
  let f' : C(Metric.closedBall o R, ℝ) := ⟨_, hf.domRestrict⟩
  obtain ⟨g, hg⟩ := f'.exists_restrict_eq Metric.isClosed_closedBall
  have he : Set.EqOn f g (Metric.closedBall o R) := by
    intro x hx
    exact (congrArg (fun u : C(Metric.closedBall o R, ℝ) => u ⟨x, hx⟩) hg).symm
  have heb : Set.EqOn f g (Metric.ball o R) := he.mono Metric.ball_subset_closedBall
  have hcenter := he (Metric.mem_closedBall_self hR.le)
  exact no_maximum_of_strict_weakLaplacian g.continuous hR hc (hw.congr heb)
    (by intro x hx; rw [← heb hx, ← hcenter]; exact hm x hx)

theorem integrable_mul_compact_of_continuousAt {f g : Position → ℝ}
    (hf : ∀ x ∈ tsupport g, ContinuousAt f x) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x*g x) := by
  have hc : Continuous (fun x => f x*g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport g
    · exact (hf x hx).mul hg.continuousAt
    · have he : (fun y => f y*g y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change g y = 0 at hy
        simp only [hy, mul_zero]
      exact continuousAt_const.congr_of_eventuallyEq he
  exact hc.integrable_of_hasCompactSupport (hgc.mono (Function.support_mul_subset_right f g))

theorem tsupport_dirPartial_subset (f : Position → ℝ) (v : Position) :
    tsupport (dirPartial f v) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v

theorem integral_mul_coordinateLaplacian_eq {f φ : Position → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, f x * coordinateLaplacian φ x) =
      ∫ x, coordinateLaplacian f x * φ x := by
  have hpφ (v : Position) : ContDiff ℝ ∞ (dirPartial φ v) :=
    contDiff_partial (by simpa using hφ) v
  have hppφ (v : Position) : ContDiff ℝ ∞ (dirPartial (dirPartial φ v) v) :=
    contDiff_partial (by simpa using hpφ v) v
  have hdφ (v : Position) := (hpφ v).differentiable (by simp)
  have hiφ (v : Position) := hasCompactSupport_partial hφc v
  have hpcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (dirPartial f v) x :=
    ((hf x hx).fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const
  have hppcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hpcont v x hx).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have hleft (v : Position) : Integrable (fun x => f x*dirPartial (dirPartial φ v) v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x ((tsupport_dirPartial_subset φ v)
        (tsupport_dirPartial_subset (dirPartial φ v) v hx))).continuousAt)
      (hppφ v).continuous
      (hasCompactSupport_partial (hiφ v) v)
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x*φ x) :=
    integrable_mul_compact_of_continuousAt (hppcont v) hφ.continuous hφc
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hpcont v x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfg (v : Position) : Integrable (fun x => f x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x*φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => (hpcont v x hx).continuousAt)
      hφ.continuous hφc
  have hby (v : Position) :
      (∫ x, f x*dirPartial (dirPartial φ v) v x) = ∫ x, dirPartial (dirPartial f v) v x*φ x := by
    calc
      _ = -(∫ x, dirPartial f v x*dirPartial φ v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).differentiableAt (by norm_num))
          (fun x _ => hdφ v x)
      _ = _ := by
        have he : (∫ x, dirPartial f v x*dirPartial φ v x) =
            -(∫ x, dirPartial (dirPartial f v) v x*φ x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x hx => (hpcont v x hx).differentiableAt (by norm_num))
            (fun x _ => hφ.differentiable (by simp) x)
        rw [he, neg_neg]
  calc
    _ = ∫ x, ∑ a : Fin 3, f x*dirPartial (dirPartial φ (axis a)) (axis a) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coordinateLaplacian_eq_partials (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt, Finset.mul_sum]
    _ = ∑ a : Fin 3, ∫ x, f x*dirPartial (dirPartial φ (axis a)) (axis a) x :=
      integral_finsetSum _ (fun a _ => hleft (axis a))
    _ = ∑ a : Fin 3, ∫ x, dirPartial (dirPartial f (axis a)) (axis a) x*φ x := by
      simp_rw [hby]
    _ = ∫ x, ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x*φ x :=
      (integral_finsetSum _ (fun a _ => hright (axis a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [coordinateLaplacian_eq_partials (hf x hx), Finset.sum_mul]
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, Finset.sum_const_zero]

theorem continuousAt_coordinateLaplacian {f : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) : ContinuousAt (coordinateLaplacian f) x := by
  have hp (v : Position) : ContDiffAt ℝ 1 (dirPartial f v) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiffAt_const
  have hpp (v : Position) : ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hp v).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have he : coordinateLaplacian f =ᶠ[𝓝 x]
      fun y => ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact coordinateLaplacian_eq_partials hy
  have hsum : ContinuousAt (fun y => ∑ a : Fin 3,
      dirPartial (dirPartial f (axis a)) (axis a) y) x :=
    tendsto_finsetSum _ (fun a _ => hpp (axis a))
  exact hsum.congr_of_eventuallyEq he

theorem continuous_coordinateLaplacian {f : Position → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (coordinateLaplacian f) :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_coordinateLaplacian hf.contDiffAt

theorem hasCompactSupport_coordinateLaplacian {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateLaplacian f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

def HasWeakLaplacian (f : Position → ℝ) (U : Set Position) (q : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x, f x*coordinateLaplacian φ x) = ∫ x, q x*φ x

theorem HasWeakLaplacian.mono {f q : Position → ℝ} {U V : Set Position}
    (h : HasWeakLaplacian f U q) (he : V ⊆ U) : HasWeakLaplacian f V q := by
  intro φ hφ hc ht
  exact h φ hφ hc (ht.trans he)

theorem HasWeakLaplacian.sub_smooth_lower {f q b : Position → ℝ}
    {U : Set Position} {c : ℝ} (ho : IsOpen U)
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) (hb : ContDiffOn ℝ 2 b U)
    (hw : HasWeakLaplacian f U q) (hl : ∀ x ∈ U, c ≤ q x-coordinateLaplacian b x) :
    WeakLaplacianLower (fun x => f x-b x) U c := by
  intro φ hφ hc ht hp
  have hb' (x : Position) (hx : x ∈ U) := hb.contDiffAt (ho.mem_nhds hx)
  have hiq : Integrable (fun x => q x*φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => hq.continuousAt (ho.mem_nhds (ht hx))) hφ.continuous hc
  have hib : Integrable (fun x => coordinateLaplacian b x*φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => continuousAt_coordinateLaplacian (hb' x (ht hx))) hφ.continuous hc
  have hts : tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hφl := continuous_coordinateLaplacian (hφ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top))
  have hφlc := hasCompactSupport_coordinateLaplacian hc
  have hif : Integrable (fun x => f x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => hf.continuousAt (ho.mem_nhds (ht (hts hx)))) hφl hφlc
  have hib' : Integrable (fun x => b x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hb' x (ht (hts hx))).continuousAt) hφl hφlc
  simp_rw [sub_mul]
  rw [integral_sub hif hib', hw φ hφ hc ht,
    integral_mul_coordinateLaplacian_eq (fun x hx => hb' x (ht hx)) hφ hc,
    ← integral_sub hiq hib, ← integral_const_mul]
  apply integral_mono (hφ.continuous.integrable_of_hasCompactSupport hc |>.const_mul c)
    (hiq.sub hib)
  intro x
  change c*φ x ≤ q x*φ x-coordinateLaplacian b x*φ x
  by_cases hx : x ∈ tsupport φ
  · rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (hl x (ht hx)) (hp x)
  · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, sub_self, le_refl]

theorem weakLaplacian_le_at_local_max {f q b : Position → ℝ} {U : Set Position}
    {o : Position} (ho : IsOpen U) (hx : o ∈ U)
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) (hb : ContDiffOn ℝ 2 b U)
    (hw : HasWeakLaplacian f U q) (hm : IsLocalMax (fun x => f x-b x) o) :
    q o ≤ coordinateLaplacian b o := by
  by_contra hn
  have hg : 0 < q o-coordinateLaplacian b o := sub_pos.mpr (lt_of_not_ge hn)
  let c := (q o-coordinateLaplacian b o)/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hg' : c < q o-coordinateLaplacian b o := by dsimp [c]; linarith
  have hcont : ContinuousAt (fun x => q x-coordinateLaplacian b x) o :=
    (hq.continuousAt (ho.mem_nhds hx)).sub
      (continuousAt_coordinateLaplacian (hb.contDiffAt (ho.mem_nhds hx)))
  have he : ∀ᶠ x in 𝓝 o, x ∈ U ∧ c < q x-coordinateLaplacian b x ∧
      f x-b x ≤ f o-b o := by
    filter_upwards [ho.mem_nhds hx, hcont.eventually (Ioi_mem_nhds hg'), hm] with x hx hg hm
    exact ⟨hx, hg, hm⟩
  obtain ⟨d, hd, hd'⟩ := Metric.mem_nhds_iff.mp he
  let R := d/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRd : R < d := by dsimp [R]; linarith
  have hlocal (x : Position) (hx : x ∈ Metric.closedBall o R) :
      x ∈ U ∧ c < q x-coordinateLaplacian b x ∧ f x-b x ≤ f o-b o :=
    hd' (lt_of_le_of_lt hx hRd)
  have hsub : Metric.ball o R ⊆ U :=
    fun x hx => (hlocal x (Metric.ball_subset_closedBall hx)).1
  exact no_maximum_of_strict_weakLaplacian_local hR hc
    ((hf.sub hb.continuousOn).mono (fun x hx => (hlocal x hx).1))
    ((hw.mono hsub).sub_smooth_lower Metric.isOpen_ball (hf.mono hsub) (hq.mono hsub)
      (hb.mono hsub) (fun x hx => (hlocal x (Metric.ball_subset_closedBall hx)).2.1.le))
    (fun x hx => (hlocal x (Metric.ball_subset_closedBall hx)).2.2)

theorem coordinateLaplacian_const_mul (f : Position → ℝ) (x : Position) (c : ℝ) :
    coordinateLaplacian (fun y => c*f y) x = c*coordinateLaplacian f x := by
  unfold coordinateLaplacian
  simp only [deriv_const_mul_field', deriv_const_mul_field, Finset.mul_sum]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_CoulombKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def coulombKernel (x : Position) : ℝ := ‖x‖⁻¹

def potentialOf (ρ : Position → ℝ) (x : Position) : ℝ :=
  ∫ y, coulombKernel (x-y)*ρ y

theorem coulombKernel_nonneg (x : Position) : 0 ≤ coulombKernel x :=
  inv_nonneg.mpr (norm_nonneg x)

theorem measurable_coulombKernel : Measurable coulombKernel :=
  measurable_norm.inv

theorem coulombKernel_integrableOn_ball (r : ℝ) :
    IntegrableOn coulombKernel (Metric.ball (0 : Position) r) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by simp : 1 ≤ Module.finrank ℝ Position)
    (C := 1) (α := 1) (by norm_num : (1:ℝ) < Module.finrank ℝ Position)
    _ measurable_coulombKernel.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simp [coulombKernel, Real.rpow_neg_one])

def regularizedKernel (ε : ℝ) (x : Position) : ℝ :=
  (‖x‖^2+ε^2)^(-1/2 : ℝ)

def regularizedCharge (ε : ℝ) (x : Position) : ℝ :=
  3*ε^2*(‖x‖^2+ε^2)^(-5/2 : ℝ)

theorem contDiff_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedKernel ε) := by
  apply ContDiff.rpow_const_of_ne
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · intro x
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)).ne'

theorem laplacian_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) (x : Position) :
    coordinateLaplacian (regularizedKernel ε) x = -regularizedCharge ε x := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have he : ∀ a : Fin 3, (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      (fun t => ((‖x‖^2+ε^2)+2*t*x a+t^2)^(-1/2 : ℝ)) := by
    intro a
    ext t
    unfold regularizedKernel
    rw [norm_sq_axis_shift]
    congr 1
    ring
  unfold coordinateLaplacian
  simp_rw [he, second_deriv_quadratic_rpow hq]
  norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2+ε^2)^(-5/2 : ℝ)*(‖x‖^2+ε^2) =
      (‖x‖^2+ε^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hq.ne']
    norm_num
  calc
    _ = 3*(‖x‖^2+ε^2)^(-5/2 : ℝ)*(∑ a : Fin 3, (x a)^2) -
        3*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
      rw [Finset.mul_sum]
      congr 1
      all_goals ring_nf
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      unfold regularizedCharge
      rw [← hpow]
      ring

def chargePrimitive (r : ℝ) : ℝ := r^3*(1+r^2)^(-3/2 : ℝ)

theorem hasDerivAt_chargePrimitive (r : ℝ) :
    HasDerivAt chargePrimitive (3*r^2*(1+r^2)^(-5/2 : ℝ)) r := by
  have hp : 0 < 1+r^2 := by positivity
  have hd := ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hp.ne'))
  unfold chargePrimitive
  apply hd.congr_deriv
  norm_num
  have he : (1+r^2)^(-5/2 : ℝ)*(1+r^2) = (1+r^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hp.ne']; norm_num
  norm_num at he
  rw [← he]
  ring

theorem chargePrimitive_eq_ratio {r : ℝ} (hr : 0 ≤ r) :
    chargePrimitive r = (1-(1+r^2)⁻¹)^(3/2 : ℝ) := by
  have hp : 0 < 1+r^2 := by positivity
  have hh : 1-(1+r^2)⁻¹ = r^2/(1+r^2) := by field_simp; ring
  rw [hh, Real.div_rpow (sq_nonneg _) hp.le]
  have hn : (r^2)^(3/2 : ℝ) = r^3 := by
    rw [← Real.rpow_natCast_mul hr]
    norm_num
  rw [hn]
  unfold chargePrimitive
  rw [show (-3/2:ℝ) = -(3/2:ℝ) by ring, Real.rpow_neg hp.le]
  rfl

theorem tendsto_chargePrimitive : Tendsto chargePrimitive atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hp
  have hh := (tendsto_const_nhds.sub hi).rpow tendsto_const_nhds
    (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0) : (1:ℝ)-0 ≠ 0 ∨ 0 < (3/2:ℝ))
  apply Filter.Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact (chargePrimitive_eq_ratio hr).symm

theorem integrable_radial_regularizedCharge_one :
    IntegrableOn (fun r : ℝ => 3*r^2*(1+r^2)^(-5/2 : ℝ)) (Set.Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity) tendsto_chargePrimitive

theorem integral_radial_regularizedCharge_one :
    (∫ r : ℝ in Set.Ioi 0, 3*r^2*(1+r^2)^(-5/2 : ℝ)) = 1 := by
  have hder := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0:ℝ)) (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ 3*r^2*(1+r^2)^(-5/2 : ℝ))
    tendsto_chargePrimitive
  simpa [chargePrimitive] using hder

theorem regularizedCharge_one_eq : regularizedCharge 1 =
    fun x : Position => 3*(1+‖x‖^2)^(-5/2 : ℝ) := by
  ext x
  simp [regularizedCharge, add_comm]

theorem integrable_regularizedCharge_one : Integrable (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq, integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul, mul_comm, mul_assoc,
    mul_left_comm] using integrable_radial_regularizedCharge_one

theorem integral_regularizedCharge_one : (∫ x, regularizedCharge 1 x) = 4*Real.pi := by
  rw [regularizedCharge_one_eq, integral_fun_norm_addHaar volume
    (fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  norm_num
  have hi : (∫ r : ℝ in Set.Ioi 0, r^2*(3*(1+r^2)^(-(5/2): ℝ))) = 1 := by
    simpa only [neg_div, mul_assoc, mul_comm, mul_left_comm] using
      integral_radial_regularizedCharge_one
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

theorem regularizedCharge_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    regularizedCharge ε (ε • x) = (ε^3)⁻¹*regularizedCharge 1 x := by
  unfold regularizedCharge
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have he : (ε*‖x‖)^2+ε^2 = ε^2*(‖x‖^2+1) := by ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε^2)^(-5/2:ℝ) = (ε^5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num [Real.rpow_neg hε.le]
  rw [hp]
  norm_num
  field_simp

theorem integral_regularizedCharge_scale {ε : ℝ} (hε : 0 < ε) (φ : Position → ℝ) :
    (∫ x, regularizedCharge ε x*φ x) = ∫ x, regularizedCharge 1 x*φ (ε • x) := by
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun x => regularizedCharge ε x*φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hs
  have ht : (∫ x, regularizedCharge ε (ε • x)*φ (ε • x)) =
      (ε^3)⁻¹*(∫ x, regularizedCharge 1 x*φ (ε • x)) := by
    simp_rw [regularizedCharge_smul hε, mul_assoc]
    exact integral_const_mul _ _
  rw [ht] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) hs).symm

theorem regularizedCharge_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedCharge ε x := by unfold regularizedCharge; positivity

theorem continuous_regularizedCharge_one : Continuous (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq]
  apply Continuous.const_mul
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    positivity

theorem regularizedCharge_tendsto_dirac {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedCharge (ε n) x*φ x)
      atTop (𝓝 (4*Real.pi*φ 0)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hD := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Position)) (fun x => regularizedCharge 1 x*C)
    (F := fun n x => regularizedCharge 1 x*φ (ε n • x))
    (f := fun x => regularizedCharge 1 x*φ 0)
    (fun n => (continuous_regularizedCharge_one.mul
      (hφ.comp (show Continuous (fun x : Position => ε n • x) by fun_prop))).aestronglyMeasurable)
    (integrable_regularizedCharge_one.mul_const C)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedCharge_nonneg 1 x)]
      exact mul_le_mul_of_nonneg_left (hC _) (regularizedCharge_nonneg 1 x)))
    (Filter.Eventually.of_forall (fun x => by
      have he : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Position)) := by
        simpa using hlim.smul_const x
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp he)))
  simp only [integral_mul_const, integral_regularizedCharge_one] at hD
  simpa only [integral_regularizedCharge_scale (hε _)] using hD

theorem locallyIntegrable_coulombKernel : LocallyIntegrable coulombKernel volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

theorem coulombKernel_eq_rpow (x : Position) :
    coulombKernel x = (‖x‖^2)^(-1/2 : ℝ) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num [coulombKernel, Real.rpow_neg_one]

theorem regularizedKernel_le {ε : ℝ} {x : Position} (hx : x ≠ 0) :
    regularizedKernel ε x ≤ coulombKernel x := by
  rw [coulombKernel_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg ε)) (by norm_num)

theorem regularizedKernel_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedKernel ε x := by unfold regularizedKernel; positivity

theorem regularizedKernel_tendsto {ε : ℕ → ℝ} (hlim : Tendsto ε atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedKernel (ε n) x) atTop (𝓝 (coulombKernel x)) := by
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  have hr := hh.rpow tendsto_const_nhds
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) : ‖x‖^2 ≠ 0 ∨ 0 < (-1/2:ℝ))
  simpa only [regularizedKernel, coulombKernel_eq_rpow] using hr

theorem regularizedKernel_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedKernel (ε n) x*φ x)
      atTop (𝓝 (∫ x, coulombKernel x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => coulombKernel x*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => coulombKernel x*‖φ x‖)
  · intro n
    exact ((contDiff_regularizedKernel (hε n).ne').continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regularizedKernel_le hx) (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedKernel_tendsto hlim hx).mul_const (φ x)

theorem integral_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, coulombKernel x*coordinateLaplacian φ x) = -(4*Real.pi*φ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hleft := regularizedKernel_integral_tendsto hε hεlim
    (continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)))
    (hasCompactSupport_coordinateLaplacian hφc)
  have hright := (regularizedCharge_tendsto_dirac hε hεlim hφ.continuous hφc).neg
  have he : (fun n => ∫ x, regularizedKernel (ε n) x*coordinateLaplacian φ x) =
      (fun n => -(∫ x, regularizedCharge (ε n) x*φ x)) := by
    funext n
    rw [integral_mul_coordinateLaplacian_eq
      (fun x _ => ((contDiff_regularizedKernel (hε n).ne').of_le
        (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt) hφ hφc]
    simp_rw [laplacian_regularizedKernel (hε n).ne', neg_mul, integral_neg]
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem integrable_coulomb_test_product {ρ φ : Position → ℝ}
    (hρ : Integrable ρ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*φ z.1)
      (volume.prod volume) := by
  let k : Position → ℝ := (Metric.ball 0 1).indicator coulombKernel
  have hk : Integrable k :=
    (coulombKernel_integrableOn_ball 1).integrable_indicator measurableSet_ball
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hn : Integrable (fun z : Position × Position => ‖ρ z.2‖*k (z.1-z.2))
      (volume.prod volume) := by
    simpa using hρ.norm.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk
  have hf : Integrable (fun z : Position × Position => ‖φ z.1‖*‖ρ z.2‖)
      (volume.prod volume) := hφ.integrable_of_hasCompactSupport hφc |>.norm.mul_prod hρ.norm
  have hm : AEStronglyMeasurable
      (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*φ z.1)
      (volume.prod volume) := by
    have hh := hρ.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) measurable_coulombKernel.aestronglyMeasurable
    have hh' : AEStronglyMeasurable
        (fun z : Position × Position => ρ z.2*coulombKernel (z.1-z.2)*φ z.1)
        (volume.prod volume) := hh.mul hφ.aestronglyMeasurable.comp_fst
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    ring
  refine Integrable.mono' ((hn.const_mul C).add hf) hm (Filter.Eventually.of_forall ?_)
  intro z
  have hK : coulombKernel (z.1-z.2) ≤ k (z.1-z.2)+1 := by
    by_cases hz : z.1-z.2 ∈ Metric.ball (0 : Position) 1
    · simp only [k, Set.indicator_of_mem hz]
      linarith
    · have hl : 1 ≤ ‖z.1-z.2‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
      have hh : ‖z.1-z.2‖⁻¹ ≤ (1:ℝ) := by simpa using inv_anti₀ (by norm_num : (0:ℝ)<1) hl
      simpa only [k, Set.indicator_of_notMem hz, zero_add, coulombKernel] using hh
  have hkpos : 0 ≤ k (z.1-z.2) := Set.indicator_nonneg (fun x _ => coulombKernel_nonneg x) _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (coulombKernel_nonneg _)]
  calc
    coulombKernel (z.1-z.2)*‖ρ z.2‖*‖φ z.1‖ ≤
        (k (z.1-z.2)+1)*‖ρ z.2‖*‖φ z.1‖ := by gcongr
    _ = ‖ρ z.2‖*k (z.1-z.2)*‖φ z.1‖+‖φ z.1‖*‖ρ z.2‖ := by ring
    _ ≤ C*(‖ρ z.2‖*k (z.1-z.2))+‖φ z.1‖*‖ρ z.2‖ := by
      nlinarith [mul_nonneg (norm_nonneg (ρ z.2)) hkpos,
        mul_le_mul_of_nonneg_left (hC z.1) (mul_nonneg (norm_nonneg (ρ z.2)) hkpos)]

theorem coordinateLaplacian_translate (φ : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => φ (z+y)) x = coordinateLaplacian φ (x+y) := by
  unfold coordinateLaplacian
  simp only [add_right_comm _ _ y]

theorem integral_translated_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (y : Position) :
    (∫ x, coulombKernel (x-y)*coordinateLaplacian φ x) = -(4*Real.pi*φ y) := by
  have ht : ContDiff ℝ ∞ (fun z => φ (z+y)) := hφ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun z => φ (z+y)) :=
    hφc.comp_homeomorph (Homeomorph.addRight y)
  have he := integral_coulombKernel_laplacian ht hc
  simp only [coordinateLaplacian_translate, zero_add] at he
  rw [← integral_add_right_eq_self (fun x => coulombKernel (x-y)*coordinateLaplacian φ x) y]
  simpa only [add_sub_cancel_right] using he

theorem potentialOf_weakLaplacian {ρ : Position → ℝ} (hρ : Integrable ρ) :
    HasWeakLaplacian (potentialOf ρ) Set.univ (fun x => -(4*Real.pi)*ρ x) := by
  intro φ hφ hφc _
  have hL : Continuous (coordinateLaplacian φ) :=
    continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  calc
    (∫ x, potentialOf ρ x*coordinateLaplacian φ x) =
        ∫ x, ∫ y, coulombKernel (x-y)*ρ y*coordinateLaplacian φ x := by
      simp only [potentialOf, integral_mul_const]
    _ = ∫ y, ∫ x, coulombKernel (x-y)*ρ y*coordinateLaplacian φ x :=
      integral_integral_swap (integrable_coulomb_test_product hρ hL
        (hasCompactSupport_coordinateLaplacian hφc))
    _ = ∫ y, (-(4*Real.pi)*ρ y)*φ y := by
      apply integral_congr_ae
      filter_upwards [] with y
      calc
        (∫ x, coulombKernel (x-y)*ρ y*coordinateLaplacian φ x) =
            (∫ x, coulombKernel (x-y)*coordinateLaplacian φ x)*ρ y := by
          simp only [mul_right_comm _ (ρ y), integral_mul_const]
        _ = _ := by rw [integral_translated_coulombKernel_laplacian hφ hφc]; ring

theorem bounded_density_convolution {k ρ : Position → ℝ} {A : ℝ}
    (hk : Measurable k) (hkpos : ∀ x, 0 ≤ k x)
    (hki : IntegrableOn k (Metric.ball 0 1))
    (hkfar : ∀ x, 1 ≤ ‖x‖ → k x ≤ 1)
    (hρ : Integrable ρ) (hρpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) (x : Position) :
    Integrable (fun y => k (x-y)*ρ y) ∧
      (∫ y, k (x-y)*ρ y) ≤ A*(∫ y in Metric.ball 0 1, k y)+(∫ y, ρ y) := by
  let kn := (Metric.ball (0 : Position) 1).indicator k
  have hi : Integrable (fun y => kn (x-y)) :=
    (integrable_comp_sub_left kn x).mpr (hki.integrable_indicator measurableSet_ball)
  have hb : Integrable (fun y => A*kn (x-y)+ρ y) := (hi.const_mul A).add hρ
  have hd : ∀ y, k (x-y)*ρ y ≤ A*kn (x-y)+ρ y := by
    intro y
    by_cases hy : x-y ∈ Metric.ball (0 : Position) 1
    · simp only [kn, Set.indicator_of_mem hy]
      nlinarith [mul_le_mul_of_nonneg_left (hA y) (hkpos (x-y)), hρpos y]
    · simp only [kn, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hh : 1 ≤ ‖x-y‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hy
      simpa using mul_le_mul_of_nonneg_right (hkfar _ hh) (hρpos y)
  have hm : AEStronglyMeasurable (fun y => k (x-y)*ρ y) volume :=
    (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hρ.aestronglyMeasurable
  have hp : Integrable (fun y => k (x-y)*ρ y) :=
    hb.mono' hm (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hkpos _) (hρpos _))]
      exact hd y))
  refine ⟨hp, (integral_mono hp hb hd).trans_eq ?_⟩
  rw [integral_add (hi.const_mul A) hρ, integral_const_mul, integral_sub_left_eq_self]
  rw [integral_indicator measurableSet_ball]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_CoulombKernelFiveHalvesIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma coulomb_holder_exponents : (5/2:ℝ).HolderConjugate (5/3:ℝ) := by
  constructor <;> norm_num

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable abbrev TFExponent : ℝ≥0∞ := ENNReal.ofReal (5/3:ℝ)
instance instFactLeENNRealOfNatTFExponent : Fact (1 ≤ TFExponent) := ⟨by norm_num [TFExponent]⟩
noncomputable abbrev TFLp {α : Type*} [MeasurableSpace α] (μ : Measure α) := Lp ℝ TFExponent μ
lemma tfLp_norm {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : TFLp μ) :
    ‖f‖ = (∫ x, ‖f x‖^(5/3:ℝ) ∂μ)^(3/5:ℝ) := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.memLp f).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num [TFExponent]) (by simp)
      (Lp.memLp f).aestronglyMeasurable]
  norm_num [TFExponent]
lemma tfLp_norm_power {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : TFLp μ) :
    ‖f‖^(5/3:ℝ) = ∫ x, ‖f x‖^(5/3:ℝ) ∂μ := by
  rw [tfLp_norm, ← Real.rpow_mul (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
  norm_num
lemma tfLp_integral_norm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (f : TFLp μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ (μ.real univ)^(2/5:ℝ)*‖f‖ := by
  have H := integral_mul_norm_le_Lp_mul_Lq coulomb_holder_exponents
    (memLp_const (p := ENNReal.ofReal (5/2:ℝ)) (1:ℝ)) (Lp.memLp f)
  simp only [norm_one, one_mul, Real.one_rpow, integral_const, smul_eq_mul] at H
  rw [tfLp_norm]
  convert H using 1; norm_num

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_power_strong_convex {R : ℝ} (_hR : 0 < R) :
    StrongConvexOn (Icc 0 R) ((10/9:ℝ)*R^(-(1/3:ℝ))) (fun x : ℝ => x^(5/3:ℝ)) := by
  rw [strongConvexOn_iff_convex]
  have he : (fun x : ℝ => x^(5/3:ℝ) - ((10/9:ℝ)*R^(-(1/3:ℝ)))/2*‖x‖^2) =
      (fun x : ℝ => x^(5/3:ℝ) - (5/9:ℝ)*R^(-(1/3:ℝ))*x^2) := by
    ext x
    rw [Real.norm_eq_abs, sq_abs]
    ring
  rw [he]
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 R)
    (f' := fun x => (5/3:ℝ)*x^(2/3:ℝ) - (10/9:ℝ)*R^(-(1/3:ℝ))*x)
    (f'' := fun x => (10/9:ℝ)*(x^(-(1/3:ℝ))-R^(-(1/3:ℝ))))
  · exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤5/3)).sub
      (continuous_const.mul (continuous_pow 2))).continuousOn
  · intro x hx
    have hd := (Real.hasDerivAt_rpow_const (x := x) (p := 5/3) (Or.inr (by norm_num))).sub
      (((hasDerivAt_pow 2 x).const_mul ((5/9:ℝ)*R^(-(1/3:ℝ)))))
    convert! hd.hasDerivWithinAt (s := interior (Icc (0:ℝ) R)) using 1; norm_num
    all_goals first | rfl | ring
  · intro x hx
    rw [interior_Icc] at hx
    have hd := ((Real.hasDerivAt_rpow_const (x := x) (p := 2/3) (Or.inl hx.1.ne')).const_mul (5/3:ℝ)).sub
      ((hasDerivAt_id x).const_mul ((10/9:ℝ)*R^(-(1/3:ℝ))))
    convert! hd.hasDerivWithinAt (s := interior (Icc (0:ℝ) R)) using 1; norm_num
    all_goals first | rfl | ring
  · intro x hx
    rw [interior_Icc] at hx
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hx.1 hx.2.le (by norm_num)))

lemma tf_power_midpoint_gap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (5/36:ℝ)*(a+b+1)^(-(1/3:ℝ))*(a-b)^2 ≤
      (a^(5/3:ℝ)+b^(5/3:ℝ))/2 - ((a+b)/2)^(5/3:ℝ) := by
  have H := (tf_power_strong_convex (show 0 < a+b+1 by linarith)).2
    (show a ∈ Icc 0 (a+b+1) from ⟨ha,by linarith⟩)
    (show b ∈ Icc 0 (a+b+1) from ⟨hb,by linarith⟩)
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at H
  have he : (1/2:ℝ)*a+(1/2:ℝ)*b=(a+b)/2 := by ring
  rw [he] at H
  nlinarith
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_power_difference_factor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a-b‖^(5/3:ℝ) =
      ((a+b+1)^(-(1/3:ℝ))*(a-b)^2)^(5/6:ℝ) *
        ((a+b+1)^(5/3:ℝ))^(1/6:ℝ) := by
  have hR : 0 < a+b+1 := by linarith
  rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) (sq_nonneg _),
    ← Real.rpow_mul hR.le, ← Real.rpow_mul hR.le]
  have hs : ((a-b)^2)^(5/6:ℝ) = ‖a-b‖^(5/3:ℝ) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  rw [hs, mul_right_comm, ← Real.rpow_add hR]
  norm_num

lemma tf_midpoint_gap_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (a^(5/3:ℝ)+b^(5/3:ℝ))/2 - ((a+b)/2)^(5/3:ℝ) :=
  (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
    (sq_nonneg _)).trans (tf_power_midpoint_gap ha hb)

lemma integrable_rpow_of_memLp_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x) : Integrable (fun x => f x ^ p) μ := by
  have H := hf.integrable_norm_rpow (by simpa using hp) (by simp)
  apply H.congr
  filter_upwards [hn] with x hx
  simp [Real.norm_of_nonneg hx, ENNReal.toReal_ofReal hp.le]

lemma memLp_rpow_of_integrable_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x)
    {q : ℝ} (hq : 0 < q) : MemLp (fun x => f x ^ q) (ENNReal.ofReal (1/q)) μ := by
  have H := (memLp_one_iff_integrable.mpr hf).norm_rpow_div (ENNReal.ofReal q)
  have he : (1:ℝ≥0∞) / ENNReal.ofReal q = ENNReal.ofReal (1/q) := by
    rw [ENNReal.ofReal_div_of_pos hq, ENNReal.ofReal_one]
  rw [he] at H
  apply H.ae_eq
  filter_upwards [hn] with x hx
  simp [Real.norm_of_nonneg hx, ENNReal.toReal_ofReal hq.le]

lemma tf_integrated_midpoint_gap {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal (5/3:ℝ)) μ) (hg : MemLp g (ENNReal.ofReal (5/3:ℝ)) μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, ‖f x-g x‖^(5/3:ℝ) ∂μ) ≤
      ((36/5:ℝ)*((∫ x, f x^(5/3:ℝ) ∂μ)+(∫ x, g x^(5/3:ℝ) ∂μ))/2 -
        (36/5:ℝ)*(∫ x, ((f x+g x)/2)^(5/3:ℝ) ∂μ))^(5/6:ℝ) *
      (∫ x, (f x+g x+1)^(5/3:ℝ) ∂μ)^(1/6:ℝ) := by
  let d := fun x => (f x^(5/3:ℝ)+g x^(5/3:ℝ))/2 - ((f x+g x)/2)^(5/3:ℝ)
  let u := fun x => (f x+g x+1)^(-(1/3:ℝ))*(f x-g x)^2
  let v := fun x => (f x+g x+1)^(5/3:ℝ)
  have hfi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hf hf0
  have hgi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hg hg0
  have hm : MemLp (fun x => (f x+g x)/2) (ENNReal.ofReal (5/3:ℝ)) μ := by
    simpa only [div_eq_mul_inv, Pi.add_apply] using (hf.add hg).mul_const (2:ℝ)⁻¹
  have hmi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hm
    (by filter_upwards [hf0,hg0] with x hx hy; positivity)
  have hdi : Integrable d μ := ((hfi.add hgi).div_const 2).sub hmi
  have hd0 : ∀ᵐ x ∂μ, 0 ≤ d x := by
    filter_upwards [hf0,hg0] with x hx hy
    exact tf_midpoint_gap_nonneg hx hy
  have hu0 : ∀ᵐ x ∂μ, 0 ≤ u x := by
    filter_upwards [hf0,hg0] with x hx hy
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (sq_nonneg _)
  have hule : ∀ᵐ x ∂μ, u x ≤ (36/5:ℝ)*d x := by
    filter_upwards [hf0,hg0] with x hx hy
    have H := tf_power_midpoint_gap hx hy
    dsimp [u,d]
    nlinarith
  have hum : AEStronglyMeasurable u μ := by
    exact (((hf.aestronglyMeasurable.add hg.aestronglyMeasurable).add
      aestronglyMeasurable_const).aemeasurable.pow_const _).aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)
  have hui : Integrable u μ := (hdi.const_mul (36/5:ℝ)).mono' hum (by
    filter_upwards [hule, hu0] with x hx hn
    simpa only [Real.norm_of_nonneg hn] using hx)
  have hvp := (hf.add hg).add (memLp_const (1:ℝ))
  have hv0 : ∀ᵐ x ∂μ, 0 ≤ v x := by
    filter_upwards [hf0,hg0] with x hx hy
    exact Real.rpow_nonneg (by linarith) _
  have hvi : Integrable v μ := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hvp
    (by filter_upwards [hf0,hg0] with x hx hy; positivity)
  have hup := memLp_rpow_of_integrable_nonneg hui hu0 (by norm_num : (0:ℝ)<5/6)
  have hvp' := memLp_rpow_of_integrable_nonneg hvi hv0 (by norm_num : (0:ℝ)<1/6)
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (6/5:ℝ).HolderConjugate 6 by constructor <;> norm_num)
    (show ∀ᵐ x ∂μ, 0 ≤ u x^(5/6:ℝ) by filter_upwards [hu0] with x hx; positivity)
    (show ∀ᵐ x ∂μ, 0 ≤ v x^(1/6:ℝ) by filter_upwards [hv0] with x hx; positivity)
    (by convert hup using 1; norm_num) (by convert hvp' using 1; norm_num)
  have hlu : (∫ x, (u x^(5/6:ℝ))^(6/5:ℝ) ∂μ) = ∫ x, u x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu0] with x hx
    rw [← Real.rpow_mul hx]
    norm_num
  have hlv : (∫ x, (v x^(1/6:ℝ))^(6:ℝ) ∂μ) = ∫ x, v x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv0] with x hx
    rw [← Real.rpow_mul hx]
    norm_num
  rw [hlu, hlv] at H
  have hleft : (∫ x, ‖f x-g x‖^(5/3:ℝ) ∂μ) = ∫ x, u x^(5/6:ℝ)*v x^(1/6:ℝ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf0,hg0] with x hx hy
    exact tf_power_difference_factor hx hy
  rw [hleft]
  have huint : (∫ x, u x ∂μ) ≤ (36/5:ℝ)*(∫ x, d x ∂μ) := by
    rw [← integral_const_mul]
    exact integral_mono_ae hui (hdi.const_mul _) hule
  have hdint : (36/5:ℝ)*(∫ x, d x ∂μ) =
      (36/5:ℝ)*((∫ x, f x^(5/3:ℝ) ∂μ)+(∫ x, g x^(5/3:ℝ) ∂μ))/2 -
        (36/5:ℝ)*(∫ x, ((f x+g x)/2)^(5/3:ℝ) ∂μ) := by
    dsimp [d]
    rw [integral_sub (by exact (hfi.add hgi).div_const 2) hmi, integral_div]
    rw [integral_add hfi hgi]
    ring
  rw [← hdint]
  norm_num only [show (1:ℝ)/(6/5)=5/6 by norm_num] at H
  exact H.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (integral_nonneg_of_ae hu0) huint (by norm_num : (0:ℝ)≤5/6))
    (Real.rpow_nonneg (integral_nonneg_of_ae hv0) _))
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
def TFNonneg (f : TFLp μ) : Prop := ∀ᵐ x ∂μ, 0 ≤ f x
lemma tfNonneg_zero : TFNonneg (0 : TFLp μ) := by
  change ∀ᵐ x ∂μ, 0 ≤ (0 : Lp ℝ TFExponent μ) x
  filter_upwards [Lp.coeFn_zero ℝ TFExponent μ] with x hx
  rw [hx]
  rfl
lemma TFNonneg.add {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) : TFNonneg (f+g) := by
  filter_upwards [hf,hg,Lp.coeFn_add f g] with x hx hy hz
  simpa only [hz, Pi.add_apply] using add_nonneg hx hy
lemma TFNonneg.smul {f : TFLp μ} (hf : TFNonneg f) {c : ℝ} (hc : 0 ≤ c) : TFNonneg (c • f) := by
  filter_upwards [hf,Lp.coeFn_smul c f] with x hx hz
  simpa only [hz, Pi.smul_apply, smul_eq_mul] using mul_nonneg hc hx
lemma tfNonneg_closed : IsClosed {f : TFLp μ | TFNonneg f} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨ns, hns, hn⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [hn, ae_all_iff.mpr hf] with x hx hy
  exact ge_of_tendsto hx (Filter.Eventually.of_forall (fun n => hy (ns n)))
lemma tfLp_nonneg_power {f : TFLp μ} (hf : TFNonneg f) :
    (∫ x, (f x)^(5/3:ℝ) ∂μ) = ‖f‖^(5/3:ℝ) := by
  rw [tfLp_norm_power]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  rw [Real.norm_of_nonneg hx]
lemma tfLp_midpoint_power {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    (∫ x, ((f x+g x)/2)^(5/3:ℝ) ∂μ) = ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ) := by
  rw [← tfLp_nonneg_power ((hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (1/2:ℝ) (f+g), Lp.coeFn_add f g] with x hx hy
  simp only [hx,hy,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  congr 1; ring
noncomputable def tfOne [IsFiniteMeasure μ] : TFLp μ :=
  (memLp_const (p := TFExponent) (1:ℝ)).toLp (fun _ => 1)
lemma tfOne_coe [IsFiniteMeasure μ] : (tfOne : TFLp μ) =ᵐ[μ] fun _ => 1 :=
  MemLp.coeFn_toLp _
lemma tfNonneg_one [IsFiniteMeasure μ] : TFNonneg (tfOne : TFLp μ) := by
  filter_upwards [tfOne_coe (μ := μ)] with x hx
  simp [hx]
lemma tfLp_gap_nonneg {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    0 ≤ (‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ) := by
  rw [← tfLp_nonneg_power hf, ← tfLp_nonneg_power hg, ← tfLp_midpoint_power hf hg]
  have hi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp f) hf
  have hj := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp g) hg
  have hk : Integrable (fun x => ((f x+g x)/2)^(5/3:ℝ)) μ := by
    apply integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3)
      (by simpa only [TFExponent,div_eq_mul_inv, Pi.add_apply] using ((Lp.memLp f).add (Lp.memLp g)).mul_const (2:ℝ)⁻¹)
      (by filter_upwards [hf,hg] with x hx hy; positivity)
  rw [← integral_add hi hj, ← integral_div, ← integral_sub (by exact (hi.add hj).div_const 2) hk]
  apply integral_nonneg_of_ae
  filter_upwards [hf,hg] with x hx hy
  exact tf_midpoint_gap_nonneg hx hy
lemma tfLp_midpoint_gap [IsFiniteMeasure μ] {f g : TFLp μ}
    (hf : TFNonneg f) (hg : TFNonneg g) :
    ‖f-g‖^(5/3:ℝ) ≤
      ((36/5:ℝ)*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)))^(5/6:ℝ) *
        (‖f‖+‖g‖+‖(tfOne : TFLp μ)‖)^(5/18:ℝ) := by
  have H := tf_integrated_midpoint_gap (Lp.memLp f) (Lp.memLp g) hf hg
  rw [tfLp_nonneg_power hf, tfLp_nonneg_power hg, tfLp_midpoint_power hf hg] at H
  have he : (∫ x, ‖f x-g x‖^(5/3:ℝ) ∂μ) = ‖f-g‖^(5/3:ℝ) := by
    rw [tfLp_norm_power]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with x hx
    rw [hx]; rfl
  rw [he] at H
  have hi : (∫ x, (f x+g x+1)^(5/3:ℝ) ∂μ) = ‖f+g+tfOne‖^(5/3:ℝ) := by
    rw [← tfLp_nonneg_power ((hf.add hg).add tfNonneg_one)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (f+g) tfOne,Lp.coeFn_add f g,tfOne_coe (μ := μ)] with x hx hy hz
    simp only [hx,hy,hz,Pi.add_apply]
  rw [hi, ← Real.rpow_mul (norm_nonneg _)] at H
  have hnorm : ‖f+g+tfOne‖ ≤ ‖f‖+‖g‖+‖(tfOne : TFLp μ)‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le f g) le_rfl)
  have hnormp := Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num : (0:ℝ)≤5/18)
  have hg0 := tfLp_gap_nonneg hf hg
  have hp : 0 ≤ (36/5:ℝ)*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2-‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)) :=
    mul_nonneg (by norm_num) hg0
  have hb : (36/5:ℝ)*(‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2-(36/5:ℝ)*‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ) =
      (36/5:ℝ)*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2-‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)) := by ring
  rw [hb, show (5/3:ℝ)*(1/6)=5/18 by norm_num] at H
  exact H.trans (mul_le_mul_of_nonneg_left hnormp (Real.rpow_nonneg hp _))
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
noncomputable def tfFunctional (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f : TFLp μ) : ℝ :=
  c * ‖f‖^(5/3:ℝ) - L f + B f f / 2
lemma tfFunctional_continuous (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) : Continuous (tfFunctional c L B) := by
  unfold tfFunctional
  exact ((continuous_norm.rpow_const (fun _ => Or.inr (by norm_num : (0:ℝ) ≤ 5/3))).const_mul c).sub L.continuous |>.add
    ((B.continuous₂.comp (continuous_id.prodMk continuous_id)).div_const 2)
lemma tfFunctional_midpoint (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f g : TFLp μ) :
    (tfFunctional c L B f+tfFunctional c L B g)/2 - tfFunctional c L B ((1/2:ℝ) • (f+g)) =
      c*((‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)) + B (f-g) (f-g)/8 := by
  unfold tfFunctional
  simp only [map_add,map_smul,map_sub,_root_.add_apply,_root_.smul_apply,
    _root_.sub_apply,smul_eq_mul]
  ring
lemma tfFunctional_midpoint_nonneg {c : ℝ} (hc : 0 ≤ c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    tfFunctional c L B ((1/2:ℝ) • (f+g)) ≤ (tfFunctional c L B f+tfFunctional c L B g)/2 := by
  have H := tfFunctional_midpoint c L B f g
  have hn := add_nonneg (mul_nonneg hc (tfLp_gap_nonneg hf hg)) (div_nonneg (hB (f-g)) (by norm_num : (0:ℝ)≤8))
  linarith
lemma tfFunctional_lower {c : ℝ} (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) (f : TFLp μ) :
    c*‖f‖^(5/3:ℝ)-‖L‖*‖f‖ ≤ tfFunctional c L B f := by
  have HL : L f ≤ ‖L‖*‖f‖ := (le_abs_self _).trans (L.le_opNorm f)
  have HB := hB f
  unfold tfFunctional
  linarith
lemma tf_superlinear_bound {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℝ, R ≤ s → s ≤ c*s^(5/3:ℝ)-K*s := by
  let a := (K+1)/c
  have ha : 0 < a := div_pos (by linarith) hc
  refine ⟨a^(3/2:ℝ),Real.rpow_pos_of_pos ha _,?_⟩
  intro s hs
  have hs0 : 0 < s := (Real.rpow_pos_of_pos ha _).trans_le hs
  have H := Real.rpow_le_rpow (Real.rpow_nonneg ha.le _) hs (by norm_num : (0:ℝ)≤2/3)
  rw [← Real.rpow_mul ha.le] at H
  norm_num only [show (3/2:ℝ)*(2/3)=1 by norm_num,Real.rpow_one] at H
  have Hc : K+1 ≤ c*s^(2/3:ℝ) := by
    have := mul_le_mul_of_nonneg_left H hc.le
    dsimp [a] at this
    field_simp at this
    nlinarith
  have hp : s^(5/3:ℝ) = s*s^(2/3:ℝ) := by
    have H := Real.rpow_add hs0 (1:ℝ) (2/3:ℝ)
    norm_num at H ⊢
    exact H
  rw [hp]
  nlinarith
lemma tfFunctional_bddBelow {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) (S : Set (TFLp μ)) :
    BddBelow (tfFunctional c L B '' S) := by
  obtain ⟨R,hR,hRb⟩ := tf_superlinear_bound hc (norm_nonneg L)
  refine ⟨-‖L‖*R,?_⟩
  rintro a ⟨f,hf,rfl⟩
  have H := tfFunctional_lower (c := c) L B hB f
  by_cases hs : R ≤ ‖f‖
  · have HH := hRb ‖f‖ hs
    have hn : -‖L‖*R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg _)) hR.le
    linarith [norm_nonneg f]
  · have Hp := mul_nonneg hc.le (Real.rpow_nonneg (norm_nonneg f) (5/3:ℝ))
    have Hn := mul_le_mul_of_nonneg_left (le_of_not_ge hs) (norm_nonneg L)
    linarith
lemma tfFunctional_sublevel_bound {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) (a : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ f : TFLp μ, tfFunctional c L B f ≤ a → ‖f‖ ≤ R := by
  obtain ⟨R,hR,hRb⟩ := tf_superlinear_bound hc (norm_nonneg L)
  refine ⟨max R a,lt_of_lt_of_le hR (le_max_left _ _),?_⟩
  intro f hf
  by_cases hs : R ≤ ‖f‖
  · exact (hRb ‖f‖ hs |>.trans (tfFunctional_lower (c := c) L B hB f) |>.trans hf).trans (le_max_right _ _)
  · exact (le_of_not_ge hs).trans (le_max_left _ _)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctionalGapControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
lemma tfFunctional_gap_control {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f, TFNonneg f → ∀ g, TFNonneg g → ‖f‖ ≤ R → ‖g‖ ≤ R →
      ‖f-g‖^(5/3:ℝ) ≤ C * ((tfFunctional c L B f+tfFunctional c L B g)/2 -
        tfFunctional c L B ((1/2:ℝ) • (f+g)))^(5/6:ℝ) := by
  let A : ℝ := (36/5:ℝ)/c
  let U : ℝ := 2*R+‖(tfOne : TFLp μ)‖
  have hA : 0 < A := div_pos (by norm_num) hc
  have hU : 0 < U := by dsimp [U]; linarith [norm_nonneg (tfOne : TFLp μ)]
  refine ⟨A^(5/6:ℝ)*U^(5/18:ℝ),mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hU _),?_⟩
  intro f hf g hg hfR hgR
  let d := (‖f‖^(5/3:ℝ)+‖g‖^(5/3:ℝ))/2 - ‖(1/2:ℝ) • (f+g)‖^(5/3:ℝ)
  let e := (tfFunctional c L B f+tfFunctional c L B g)/2 - tfFunctional c L B ((1/2:ℝ) • (f+g))
  have hd : 0 ≤ d := tfLp_gap_nonneg hf hg
  have he : 0 ≤ e := sub_nonneg.mpr (tfFunctional_midpoint_nonneg hc.le L B hB hf hg)
  have hde : c*d ≤ e := by
    have H := tfFunctional_midpoint c L B f g
    have HB := hB (f-g)
    dsimp [d,e]
    linarith
  have hAc : A*c = 36/5 := by dsimp [A]; field_simp
  have hbase : (36/5:ℝ)*d ≤ A*e := by
    have H := mul_le_mul_of_nonneg_left hde hA.le
    nlinarith
  have hp := Real.rpow_le_rpow (mul_nonneg (by norm_num : (0:ℝ)≤36/5) hd) hbase
    (by norm_num : (0:ℝ)≤5/6)
  have hn : ‖f‖+‖g‖+‖(tfOne : TFLp μ)‖ ≤ U := by dsimp [U]; linarith
  have hnp := Real.rpow_le_rpow (by positivity : 0 ≤ ‖f‖+‖g‖+‖(tfOne : TFLp μ)‖) hn
    (by norm_num : (0:ℝ)≤5/18)
  calc
    _ ≤ ((36/5:ℝ)*d)^(5/6:ℝ)*(‖f‖+‖g‖+‖(tfOne : TFLp μ)‖)^(5/18:ℝ) := tfLp_midpoint_gap hf hg
    _ ≤ (A*e)^(5/6:ℝ)*U^(5/18:ℝ) := mul_le_mul hp hnp (by positivity) (by positivity)
    _ = _ := by rw [Real.mul_rpow hA.le he]; ring
lemma tfFunctional_exists_minimizer {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) :
    ∃ f : TFLp μ, TFNonneg f ∧ ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g := by
  apply exists_minimizer_of_midpoint_control tfNonneg_closed ⟨0,tfNonneg_zero⟩
    (fun f hf g hg => (hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))
    (tfFunctional_continuous c L B) (tfFunctional_bddBelow hc L B hB _)
    (fun f hf g hg => tfFunctional_midpoint_nonneg hc.le L B hB hf hg)
  · intro a
    obtain ⟨R,hR,hRb⟩ := tfFunctional_sublevel_bound hc L B hB a
    exact ⟨R,hR,fun f _ => hRb f⟩
  · exact fun R hR => tfFunctional_gap_control hc L B hB hR
lemma tfFunctional_minimizer_unique {c : ℝ} (hc : 0 < c) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g)
    (hfm : ∀ h, TFNonneg h → tfFunctional c L B f ≤ tfFunctional c L B h)
    (hgm : ∀ h, TFNonneg h → tfFunctional c L B g ≤ tfFunctional c L B h) : f = g := by
  have hfg : tfFunctional c L B f = tfFunctional c L B g := le_antisymm (hfm g hg) (hgm f hf)
  have hmid := hfm ((1/2:ℝ) • (f+g)) ((hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))
  have hmid' := tfFunctional_midpoint_nonneg hc.le L B hB hf hg
  have he : (tfFunctional c L B f+tfFunctional c L B g)/2 - tfFunctional c L B ((1/2:ℝ) • (f+g)) = 0 := by
    linarith
  obtain ⟨C,hC,hCb⟩ := tfFunctional_gap_control hc L B hB
    (show (0:ℝ)<‖f‖+‖g‖+1 by positivity)
  have H := hCb f hf g hg (by linarith [norm_nonneg g]) (by linarith [norm_nonneg f])
  rw [he,Real.zero_rpow (by norm_num : (5/6:ℝ) ≠ 0),mul_zero] at H
  have hz : ‖f-g‖^(5/3:ℝ) = 0 := le_antisymm H (Real.rpow_nonneg (norm_nonneg _) _)
  have hn : ‖f-g‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num : (5/3:ℝ)≠0)).mp hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable abbrev TFFieldExponent : ℝ≥0∞ := ENNReal.ofReal (5/2:ℝ)
instance instFactLeENNRealOfNatTFFieldExponent : Fact (1 ≤ TFFieldExponent) := ⟨by norm_num [TFFieldExponent]⟩
noncomputable abbrev TFLq {α : Type*} [MeasurableSpace α] (μ : Measure α) := Lp ℝ TFFieldExponent μ
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma tfLq_norm (W : TFLq μ) :
    ‖W‖ = (∫ x, ‖W x‖^(5/2:ℝ) ∂μ)^(2/5:ℝ) := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.memLp W).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num [TFFieldExponent]) (by simp)
      (Lp.memLp W).aestronglyMeasurable]
  norm_num [TFFieldExponent]
noncomputable def tfFieldPairing (W : TFLq μ) (f : TFLp μ) : ℝ := ∫ x, W x*f x ∂μ
lemma tfFieldPairing_integrable (W : TFLq μ) (f : TFLp μ) : Integrable (fun x => W x*f x) μ := by
  have : ENNReal.HolderConjugate TFFieldExponent TFExponent := coulomb_holder_exponents.ennrealOfReal
  exact (Lp.memLp W).integrable_mul (Lp.memLp f)
lemma tfFieldPairing_bound (W : TFLq μ) (f : TFLp μ) : ‖tfFieldPairing W f‖ ≤ ‖W‖*‖f‖ := by
  have H := integral_mul_norm_le_Lp_mul_Lq coulomb_holder_exponents (Lp.memLp W) (Lp.memLp f)
  rw [tfLq_norm,tfLp_norm]
  calc
    _ ≤ ∫ x, ‖W x*f x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖W x‖*‖f x‖ ∂μ := by simp only [norm_mul]
    _ ≤ _ := by convert H using 1; norm_num
lemma tfFieldPairing_add_left (U W : TFLq μ) (f : TFLp μ) :
    tfFieldPairing (U+W) f = tfFieldPairing U f+tfFieldPairing W f := by
  unfold tfFieldPairing
  rw [← integral_add (tfFieldPairing_integrable U f) (tfFieldPairing_integrable W f)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add U W] with x hx
  simp only [hx,Pi.add_apply,add_mul]
lemma tfFieldPairing_smul_left (c : ℝ) (W : TFLq μ) (f : TFLp μ) :
    tfFieldPairing (c • W) f = c*tfFieldPairing W f := by
  unfold tfFieldPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c W] with x hx
  simp only [hx,Pi.smul_apply,smul_eq_mul,mul_assoc]
lemma tfFieldPairing_add_right (W : TFLq μ) (f g : TFLp μ) :
    tfFieldPairing W (f+g) = tfFieldPairing W f+tfFieldPairing W g := by
  unfold tfFieldPairing
  rw [← integral_add (tfFieldPairing_integrable W f) (tfFieldPairing_integrable W g)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with x hx
  simp only [hx,Pi.add_apply,mul_add]
lemma tfFieldPairing_smul_right (c : ℝ) (W : TFLq μ) (f : TFLp μ) :
    tfFieldPairing W (c • f) = c*tfFieldPairing W f := by
  unfold tfFieldPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  ring
noncomputable def tfFieldLinear : TFLq μ →ₗ[ℝ] TFLp μ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ tfFieldPairing tfFieldPairing_add_left tfFieldPairing_smul_left
    tfFieldPairing_add_right tfFieldPairing_smul_right
noncomputable def tfFieldContinuous : TFLq μ →L[ℝ] TFLp μ →L[ℝ] ℝ :=
  tfFieldLinear.mkContinuous₂ 1 (fun W f => by
    change ‖tfFieldPairing W f‖ ≤ 1*‖W‖*‖f‖
    simpa only [one_mul] using tfFieldPairing_bound W f)
lemma tfFieldContinuous_apply (W : TFLq μ) (f : TFLp μ) :
    tfFieldContinuous W f = ∫ x, W x*f x ∂μ := rfl
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
noncomputable def tfIndicator (s : Set α) (hs : MeasurableSet s) : TFLp μ :=
  ((memLp_const (p := TFExponent) (μ := μ) (1:ℝ)).indicator hs).toLp (s.indicator (fun _ => 1))
lemma tfIndicator_coe (s : Set α) (hs : MeasurableSet s) :
    (tfIndicator s hs : TFLp μ) =ᵐ[μ] s.indicator (fun _ => 1) := MemLp.coeFn_toLp _
lemma tfIndicator_nonneg (s : Set α) (hs : MeasurableSet s) : TFNonneg (tfIndicator s hs : TFLp μ) := by
  filter_upwards [tfIndicator_coe (μ := μ) s hs] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
lemma tfIndicator_bound (s : Set α) (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, |(tfIndicator s hs : TFLp μ) x| ≤ 1 := by
  filter_upwards [tfIndicator_coe (μ := μ) s hs] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]
lemma tfField_indicator (W : TFLq μ) (s : Set α) (hs : MeasurableSet s) :
    tfFieldContinuous W (tfIndicator s hs) = ∫ x in s, W x ∂μ := by
  rw [tfFieldContinuous_apply,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [tfIndicator_coe (μ := μ) s hs] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]
lemma tfDual_nonneg (W : TFLq μ)
    (hW : ∀ h : TFLp μ, TFNonneg h → (∀ᵐ x ∂μ, |h x| ≤ 1) → 0 ≤ tfFieldContinuous W h) :
    ∀ᵐ x ∂μ, 0 ≤ W x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp W).integrable (by norm_num [TFFieldExponent]))
  intro s hs _
  rw [←tfField_indicator W s hs]
  exact hW _ (tfIndicator_nonneg s hs) (tfIndicator_bound s hs)
omit [IsFiniteMeasure μ] in
lemma tfKineticField_memLp (f : TFLp μ) :
    MemLp (fun x => ‖f x‖^(2/3:ℝ)) TFFieldExponent μ := by
  have H := (Lp.memLp f).norm_rpow_div (ENNReal.ofReal (2/3:ℝ))
  have he : TFExponent / ENNReal.ofReal (2/3:ℝ) = TFFieldExponent := by
    rw [TFExponent,TFFieldExponent,←ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2/3)]
    norm_num
  rw [he] at H
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤2/3)] at H
  exact H
noncomputable def tfKineticField (f : TFLp μ) : TFLq μ :=
  (tfKineticField_memLp f).toLp (fun x => ‖f x‖^(2/3:ℝ))
omit [IsFiniteMeasure μ] in
lemma tfKineticField_coe (f : TFLp μ) :
    tfKineticField f =ᵐ[μ] (fun x => ‖f x‖^(2/3:ℝ)) := MemLp.coeFn_toLp _
omit [IsFiniteMeasure μ] in
lemma tfKineticField_pair {f : TFLp μ} (hf : TFNonneg f) (h : TFLp μ) :
    tfFieldContinuous (tfKineticField f) h = ∫ x, (f x)^(2/3:ℝ)*h x ∂μ := by
  rw [tfFieldContinuous_apply]
  apply integral_congr_ae
  filter_upwards [tfKineticField_coe f,hf] with x hx hy
  rw [hx,Real.norm_of_nonneg hy]
omit [IsFiniteMeasure μ] in
lemma tfKineticField_self {f : TFLp μ} (hf : TFNonneg f) :
    tfFieldContinuous (tfKineticField f) f = ‖f‖^(5/3:ℝ) := by
  rw [tfKineticField_pair hf,←tfLp_nonneg_power hf]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  have H := Real.rpow_add_one' hx (by norm_num : (2/3:ℝ)+1≠0)
  norm_num at H
  exact H.symm
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
lemma tfPower_hasDerivAt {f h : α → ℝ} (hf : MemLp f TFExponent μ)
    (hh : AEStronglyMeasurable h μ) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) :
    HasDerivAt (fun t : ℝ => ∫ x, (f x+t*h x)^(5/3:ℝ) ∂μ)
      ((5/3:ℝ)*(∫ x, (f x)^(2/3:ℝ)*h x ∂μ)) 0 := by
  let F : ℝ → α → ℝ := fun t x => (f x+t*h x)^(5/3:ℝ)
  let F' : ℝ → α → ℝ := fun t x => (5/3:ℝ)*(f x+t*h x)^(2/3:ℝ)*h x
  let b : α → ℝ := fun x => (5/3:ℝ)*(|f x|+1)
  have hfi : Integrable f μ := hf.integrable (by norm_num [TFExponent])
  have hbi : Integrable b μ := (hfi.abs.add (integrable_const 1)).const_mul _
  have hFm : ∀ t, AEStronglyMeasurable (F t) μ := fun t => ((hf.aestronglyMeasurable.add (hh.const_mul t)).aemeasurable.pow_const _).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (F' 0) μ := by
    dsimp only [F']
    exact ((((hf.aestronglyMeasurable.add (hh.const_mul 0)).aemeasurable.pow_const _).aestronglyMeasurable).const_mul _).mul hh
  have hF0 : Integrable (F 0) μ := by
    have H := hf.integrable_norm_rpow (by norm_num [TFExponent]) (by simp)
    have H' : Integrable (fun x => |f x|^(5/3:ℝ)) μ := by
      norm_num [TFExponent] at H
      exact H
    refine H'.mono' (hFm 0) ?_
    filter_upwards [] with x
    simpa [F,Real.norm_eq_abs] using Real.abs_rpow_le_abs_rpow (f x) (5/3:ℝ)
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0:ℝ) 1, ‖F' t x‖ ≤ b x := by
    filter_upwards [hb] with x hx t ht
    have ht1 : |t| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using ht)
    have hv : |f x+t*h x| ≤ |f x|+1 :=
      (abs_add_le _ _).trans (by rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg (h x)])
    have hp : |(f x+t*h x)^(2/3:ℝ)| ≤ |f x|+1 :=
      (Real.abs_rpow_le_abs_rpow _ _).trans
        ((Real.rpow_le_rpow (abs_nonneg _) hv (by norm_num)).trans
          (Real.rpow_le_self_of_one_le (by linarith [abs_nonneg (f x)]) (by norm_num)))
    dsimp [F',b]
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<5/3)]
    calc
      _ ≤ (5/3:ℝ)*(|f x|+1)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hp (by norm_num)) hx (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0:ℝ) 1, HasDerivAt (F · x) (F' t x) t := by
    filter_upwards [] with x t _
    have H := ((hasDerivAt_const t (f x)).add ((hasDerivAt_id t).mul_const (h x))).rpow_const
      (p := (5/3:ℝ)) (Or.inr (by norm_num))
    convert H using 1 <;> norm_num [F,F',mul_comm,mul_left_comm]
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall hFm) hF0 hF'm hbound hbi hdiff
  simpa only [F,F',zero_mul,add_zero,mul_assoc,integral_const_mul] using H.2
lemma nonneg_deriv_of_min_on_right {F : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt F d 0)
    (hm : ∀ t : ℝ, 0 ≤ t → F 0 ≤ F t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [mem_Ioi] at ht
  simpa only [zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using div_nonneg (sub_nonneg.mpr (hm t ht.le)) ht.le
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfRawVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
noncomputable def tfRawVariation (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f h : TFLp μ) (t : ℝ) : ℝ :=
  c*(∫ x, (f x+t*h x)^(5/3:ℝ) ∂μ) - (L f+t*L h) +
    (B f f+t*(B f h+B h f)+t^2*B h h)/2
omit [IsFiniteMeasure μ] in
lemma tfRawVariation_eq (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f h : TFLp μ}
    (hf : TFNonneg f) (hh : TFNonneg h) {t : ℝ} (ht : 0 ≤ t) :
    tfRawVariation c L B f h t = tfFunctional c L B (f+t • h) := by
  have hK : (∫ x, (f x+t*h x)^(5/3:ℝ) ∂μ) = ‖f+t • h‖^(5/3:ℝ) := by
    rw [← tfLp_nonneg_power (hf.add (hh.smul ht))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • h), Lp.coeFn_smul t h] with x hx hy
    simp only [hx,Pi.add_apply,hy,Pi.smul_apply,smul_eq_mul]
  unfold tfRawVariation tfFunctional
  rw [hK]
  simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring
lemma tfRawVariation_hasDerivAt (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f h : TFLp μ)
    (hh : ∀ᵐ x ∂μ, |h x| ≤ 1) :
    HasDerivAt (tfRawVariation c L B f h)
      (c*(5/3:ℝ)*(∫ x, (f x)^(2/3:ℝ)*h x ∂μ) - L h + (B f h+B h f)/2) 0 := by
  have hK := tfPower_hasDerivAt (Lp.memLp f) (Lp.memLp h).aestronglyMeasurable hh
  have hid := hasDerivAt_id (0:ℝ)
  have hL := (hasDerivAt_const (0:ℝ) (L f)).add (hid.mul_const (L h))
  have hB := (((hasDerivAt_const (0:ℝ) (B f f)).add
    (hid.mul_const (B f h+B h f))).add ((hid.pow 2).mul_const (B h h))).div_const 2
  convert ((hK.const_mul c).sub hL).add hB using 1 <;>
    first | rfl | (norm_num [tfRawVariation]; ring)
lemma tfFunctional_tangent_nonneg (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f : TFLp μ} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g)
    {h : TFLp μ} (hh : TFNonneg h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) :
    0 ≤ c*(5/3:ℝ)*(∫ x, (f x)^(2/3:ℝ)*h x ∂μ) - L h + (B f h+B h f)/2 := by
  apply nonneg_deriv_of_min_on_right (tfRawVariation_hasDerivAt c L B f h hb)
  intro t ht
  rw [tfRawVariation_eq c L B hf hh (le_refl 0), zero_smul, add_zero,
    tfRawVariation_eq c L B hf hh ht]
  exact hm _ (hf.add (hh.smul ht))
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma tfFunctional_scaling_eq (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (f : TFLp μ) {t : ℝ} (ht : 0 ≤ t) :
    tfFunctional c L B (t • f) = c*t^(5/3:ℝ)*‖f‖^(5/3:ℝ) - t*L f + t^2*B f f/2 := by
  unfold tfFunctional
  rw [norm_smul,Real.norm_of_nonneg ht,Real.mul_rpow ht (norm_nonneg _)]
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
lemma tfFunctional_scaling_stationary (c : ℝ) (L : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f : TFLp μ} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g) :
    c*(5/3:ℝ)*‖f‖^(5/3:ℝ) - L f+B f f = 0 := by
  let J : ℝ → ℝ := fun t => c*t^(5/3:ℝ)*‖f‖^(5/3:ℝ) - t*L f+t^2*B f f/2
  have hj : IsLocalMin J 1 := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0:ℝ)<1)] with t ht
    have H := hm (t • f) (hf.smul ht.le)
    rw [tfFunctional_scaling_eq c L B f ht.le] at H
    simpa [J,tfFunctional] using H
  have hid := hasDerivAt_id (1:ℝ)
  have hpow := hid.rpow_const (p := (5/3:ℝ)) (Or.inl (by norm_num : (1:ℝ)≠0))
  have hd : HasDerivAt J (c*(5/3:ℝ)*‖f‖^(5/3:ℝ) - L f+B f f) 1 := by
    have H := (((hpow.const_mul c).mul_const (‖f‖^(5/3:ℝ))).sub (hid.mul_const (L f))).add
      (((hid.pow 2).mul_const (B f f)).div_const 2)
    convert H using 1 <;> first | rfl | norm_num [J]
  exact hj.hasDerivAt_eq_zero hd
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctionalUniformBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
omit [IsFiniteMeasure μ] in
lemma tfFunctional_uniform_bound {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f) :
    ∃ R : ℝ, 0 < R ∧ ∀ (L : TFLp μ →L[ℝ] ℝ), ‖L‖ ≤ K →
      ∀ f, tfFunctional c L B f ≤ 0 → ‖f‖ ≤ R := by
  obtain ⟨R,hR,hRb⟩ := tf_superlinear_bound hc hK
  refine ⟨R,hR,?_⟩
  intro L hL f hf
  by_contra! hn
  have H := hRb ‖f‖ hn.le
  have Hl := tfFunctional_lower (c := c) L B hB f
  have HK := mul_le_mul_of_nonneg_right hL (norm_nonneg f)
  linarith
omit [IsFiniteMeasure μ] in
lemma tfFunctional_minimizer_gap (c : ℝ) (L L' : TFLp μ →L[ℝ] ℝ)
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) {f g : TFLp μ}
    (hf : TFNonneg f) (hg : TFNonneg g)
    (hmf : ∀ h, TFNonneg h → tfFunctional c L B f ≤ tfFunctional c L B h)
    (hmg : ∀ h, TFNonneg h → tfFunctional c L' B g ≤ tfFunctional c L' B h)
    {R : ℝ} (hfR : ‖f‖ ≤ R) (hgR : ‖g‖ ≤ R) :
    (tfFunctional c L B f+tfFunctional c L B g)/2 -
      tfFunctional c L B ((1/2:ℝ) • (f+g)) ≤ R*‖L'-L‖ := by
  have Hm := hmf _ ((hf.add hg).smul (by norm_num : (0:ℝ)≤1/2))
  have Hg := hmg f hf
  have He : tfFunctional c L B g-tfFunctional c L B f =
      tfFunctional c L' B g-tfFunctional c L' B f+(L'-L) (g-f) := by
    simp only [tfFunctional,map_sub,_root_.sub_apply]
    ring
  have Hn : (L'-L) (g-f) ≤ ‖L'-L‖*(2*R) := by
    exact (le_abs_self _).trans ((L'-L).le_opNorm (g-f) |>.trans
      (mul_le_mul_of_nonneg_left ((norm_sub_le g f).trans (by linarith)) (norm_nonneg _)))
  nlinarith
lemma tfFunctional_minimizers_tendsto {ι : Type*} {l : Filter ι} {c : ℝ} (hc : 0 < c)
    {L : TFLp μ →L[ℝ] ℝ} {Ls : ι → TFLp μ →L[ℝ] ℝ} (hL : Tendsto Ls l (𝓝 L))
    (B : TFLp μ →L[ℝ] TFLp μ →L[ℝ] ℝ) (hB : ∀ f, 0 ≤ B f f)
    {f : TFLp μ} {fs : ι → TFLp μ} (hf : TFNonneg f) (hfs : ∀ i, TFNonneg (fs i))
    (hmf : ∀ g, TFNonneg g → tfFunctional c L B f ≤ tfFunctional c L B g)
    (hmfs : ∀ i g, TFNonneg g → tfFunctional c (Ls i) B (fs i) ≤ tfFunctional c (Ls i) B g) :
    Tendsto fs l (𝓝 f) := by
  let K := ‖L‖+1
  obtain ⟨R,hR,hRb⟩ := tfFunctional_uniform_bound hc
    (show (0:ℝ) ≤ K by dsimp [K]; positivity) B hB
  have hmin0 (L' : TFLp μ →L[ℝ] ℝ) (f' : TFLp μ)
      (hm : ∀ g, TFNonneg g → tfFunctional c L' B f' ≤ tfFunctional c L' B g) :
      tfFunctional c L' B f' ≤ 0 := by
    have H := hm 0 tfNonneg_zero
    simpa [tfFunctional] using H
  have hfR : ‖f‖ ≤ R := hRb L (by dsimp [K]; linarith) f (hmin0 _ _ hmf)
  have hev : ∀ᶠ i in l, ‖fs i‖ ≤ R := by
    filter_upwards [hL.norm.eventually (gt_mem_nhds (show ‖L‖ < K by dsimp [K]; linarith))] with i hi
    exact hRb (Ls i) hi.le (fs i) (hmin0 _ _ (hmfs i))
  obtain ⟨C,hC,hCb⟩ := tfFunctional_gap_control hc L B hB hR
  have hlimit : Tendsto (fun i => C*(R*‖Ls i-L‖)^(5/6:ℝ)) l (𝓝 0) := by
    have H := (hL.sub_const L).norm
    have H1 : Tendsto (fun i => R*‖Ls i-L‖) l (𝓝 (0:ℝ)) := by simpa using H.const_mul R
    simpa using (H1.rpow_const (p := (5/6:ℝ)) (Or.inr (by norm_num))).const_mul C
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεp := Real.rpow_pos_of_pos hε (5/3:ℝ)
  filter_upwards [hev,hlimit.eventually (gt_mem_nhds hεp)] with i hi hlim
  have H := hCb f hf (fs i) (hfs i) hfR hi
  have Hgap := tfFunctional_minimizer_gap c L (Ls i) B hf (hfs i) hmf (hmfs i) hfR hi
  have Hnon := sub_nonneg.mpr (tfFunctional_midpoint_nonneg hc.le L B hB hf (hfs i))
  have Hup := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow Hnon Hgap (by norm_num : (0:ℝ)≤5/6)) hC.le
  have Hd : ‖f-fs i‖ < ε := (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le (by norm_num : (0:ℝ)<5/3)).mp
    (H.trans Hup |>.trans_lt hlim)
  simpa only [dist_eq_norm,norm_sub_rev] using Hd
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_complementarity_solve {a r w : ℝ} (ha : 0 < a) (hr : 0 ≤ r)
    (hg : 0 ≤ a*r^(2/3:ℝ)-w) (hc : (a*r^(2/3:ℝ)-w)*r=0) :
    r = (max w 0/a)^(3/2:ℝ) ∧ a*r^(2/3:ℝ)-w = max (-w) 0 := by
  by_cases hz : r=0
  · subst r
    simp only [Real.zero_rpow (by norm_num : (2/3:ℝ)≠0),mul_zero,zero_sub] at hg ⊢
    have hw : w ≤ 0 := by linarith
    simp [max_eq_right hw,max_eq_left hg]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have he : a*r^(2/3:ℝ)-w=0 := (mul_eq_zero.mp hc).resolve_right hz
    have hw : 0 < w := by nlinarith [Real.rpow_pos_of_pos hrp (2/3:ℝ)]
    have hdiv : w/a=r^(2/3:ℝ) := (div_eq_iff ha.ne').mpr (by linarith [he])
    rw [max_eq_left hw.le,hdiv,←Real.rpow_mul hr]
    norm_num only [show (2/3:ℝ)*(3/2)=1 by norm_num,Real.rpow_one]
    exact ⟨True.intro,by rw [he,max_eq_right (by linarith)]⟩
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_power_tangent {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ s^(5/3:ℝ)-r^(5/3:ℝ)-(5/3:ℝ)*r^(2/3:ℝ)*(s-r) := by
  have H := Real.young_inequality_of_nonneg (Real.rpow_nonneg hr (2/3:ℝ)) hs coulomb_holder_exponents
  rw [←Real.rpow_mul hr] at H
  norm_num only [show (2/3:ℝ)*(5/2)=5/3 by norm_num] at H
  have he := Real.rpow_add_one' hr (by norm_num : (2/3:ℝ)+1≠0)
  norm_num at he
  nlinarith
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
noncomputable def tfBregman (f g : TFLp μ) : ℝ :=
  ‖g‖^(5/3:ℝ)-‖f‖^(5/3:ℝ)-(5/3:ℝ)*tfFieldContinuous (tfKineticField f) (g-f)
lemma tfKinetic_pair_integrable {f : TFLp μ} (hf : TFNonneg f) (g : TFLp μ) :
    Integrable (fun x => (f x)^(2/3:ℝ)*g x) μ := by
  apply (tfFieldPairing_integrable (tfKineticField f) g).congr
  filter_upwards [tfKineticField_coe f,hf] with x hx hy
  rw [hx,Real.norm_of_nonneg hy]
lemma tfBregman_formula {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    tfBregman f g = ∫ x, (g x)^(5/3:ℝ)-(f x)^(5/3:ℝ)-
      (5/3:ℝ)*(f x)^(2/3:ℝ)*(g x-f x) ∂μ := by
  have hi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp f) hf
  have hj := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) (Lp.memLp g) hg
  have hk := (tfKinetic_pair_integrable hf (g-f)).const_mul (5/3:ℝ)
  have hij : Integrable (fun x => (g x)^(5/3:ℝ)-(f x)^(5/3:ℝ)) μ := hj.sub hi
  unfold tfBregman
  rw [←tfLp_nonneg_power hf,←tfLp_nonneg_power hg,tfKineticField_pair hf,←integral_const_mul,
    ←integral_sub hj hi,←integral_sub hij hk]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub g f] with x hx
  simp only [hx,Pi.sub_apply,mul_assoc]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_InteriorBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

lemma second_deriv_general_quadratic_rpow {q b c p : ℝ} (hq : 0<q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+c*t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2+2*c*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+c*t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*c*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      (((hasDerivAt_id t).pow 2).const_mul c)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | dsimp [Q]; ring
  have hQ0 : Q 0=q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0:ℝ), Q t≠0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hd : deriv (fun t => Q t^p) =ᶠ[𝓝 0] fun t => p*Q t^(p-1)*(2*b+2*c*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hd.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
    (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul (2*c)))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*c*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*(2*c)) 0 := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv,show p-1-1=p-2 by ring]
  ring

def interiorBump (y : Position) (s A : ℝ) (x : Position) : ℝ :=
  A*(s^2-‖x-y‖^2)^(-4:ℝ)

lemma interiorBump_eq_div {y x : Position} {s A : ℝ}
    (h : 0 < s^2-‖x-y‖^2) : interiorBump y s A x=A/(s^2-‖x-y‖^2)^4 := by
  rw [interiorBump, Real.rpow_neg h.le]
  norm_num [div_eq_mul_inv]

lemma coordinateLaplacian_interiorBump {y x : Position} {s A : ℝ}
    (h : 0 < s^2-‖x-y‖^2) : coordinateLaplacian (interiorBump y s A) x =
      A*(80*‖x-y‖^2*(s^2-‖x-y‖^2)^(-6:ℝ)+24*(s^2-‖x-y‖^2)^(-5:ℝ)) := by
  unfold interiorBump
  rw [coordinateLaplacian_const_mul]
  unfold coordinateLaplacian
  have he (a : Fin 3) : (fun t : ℝ => (s^2-‖x+t • axis a-y‖^2)^(-4:ℝ))=
      (fun t : ℝ => ((s^2-‖x-y‖^2)+2*t*(-(x-y) a)+(-1)*t^2)^(-4:ℝ)) := by
    funext t
    rw [show x+t • axis a-y=(x-y)+t • axis a by module,norm_sq_axis_shift]
    congr 1
    ring
  simp_rw [he,second_deriv_general_quadratic_rpow h]
  congr 1
  norm_num
  have H : (∑ a : Fin 3, (y a-x a)^2)=‖x-y‖^2 := by
    have H := EuclideanSpace.real_norm_sq_eq (y-x)
    simpa only [PiLp.sub_apply,norm_sub_rev] using H.symm
  simp only [Finset.sum_add_distrib]
  rw [show (∑ a : Fin 3, 20*((s^2-‖x-y‖^2)^6)⁻¹*(2*(y a-x a))^2)=
      80*((s^2-‖x-y‖^2)^6)⁻¹*(∑ a : Fin 3, (y a-x a)^2) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring]
  rw [H]
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
  ring

lemma contDiffOn_interiorBump {y : Position} {s : ℝ} (hs : 0 < s) (A : ℝ) :
    ContDiffOn ℝ 2 (interiorBump y s A) (Metric.ball y s) := by
  apply contDiffOn_const.mul
  apply ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).contDiffOn).rpow_const_of_ne
  intro x hx
  have hx' : ‖x-y‖ < s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  exact ne_of_gt (sub_pos.mpr (sq_lt_sq₀ (norm_nonneg _) hs.le |>.mpr hx'))

lemma coordinateLaplacian_interiorBump_le {y x : Position} {s A : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hx : x∈Metric.ball y s) :
    coordinateLaplacian (interiorBump y s A) x ≤ 80*A*s^2/(s^2-‖x-y‖^2)^6 := by
  have hx' : ‖x-y‖ < s := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have h : 0 < s^2-‖x-y‖^2 := sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg _) hs.le).mpr hx')
  rw [coordinateLaplacian_interiorBump h]
  norm_num [Real.rpow_neg_natCast]
  have hid : ((s^2-‖x-y‖^2)^5)⁻¹=(s^2-‖x-y‖^2)*((s^2-‖x-y‖^2)^6)⁻¹ := by
    field_simp
  rw [hid,div_eq_mul_inv]
  calc
    _=(A*(80*‖x-y‖^2+24*(s^2-‖x-y‖^2)))*((s^2-‖x-y‖^2)^6)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (show A*(80*‖x-y‖^2+24*(s^2-‖x-y‖^2)) ≤ 80*A*s^2 by
      nlinarith [mul_nonneg hA h.le]) (inv_nonneg.mpr (pow_nonneg h.le 6))

lemma weighted_reaction_bound {A c s : ℝ} (hA : 0<A) (hc : 0 < c)
    (h : c*A^(3/2:ℝ) ≤ 80*A*s^2) : A ≤ (80/c)^2*s^4 := by
  have hp : A^(3/2:ℝ)=A*Real.sqrt A := by
    calc
      _=A^((1:ℝ)+(1/2:ℝ)) := by norm_num
      _=_ := by rw [Real.rpow_add hA,Real.rpow_one,←Real.sqrt_eq_rpow]
  rw [hp] at h
  have hsq : Real.sqrt A ≤ 80*s^2/c := by
    apply (le_div_iff₀ hc).mpr
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith [h]
  have H := pow_le_pow_left₀ (Real.sqrt_nonneg A) hsq 2
  rw [Real.sq_sqrt hA.le] at H
  calc
    A ≤ (80*s^2/c)^2 := H
    _=(80/c)^2*s^4 := by ring

theorem weak_power_interior_upper {F : Position → ℝ} {y : Position} {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hF : ContinuousOn F (Metric.closedBall y s))
    (hw : HasWeakLaplacian F (Metric.ball y s) (fun x => c*(max (F x) 0)^(3/2:ℝ)))
    {z : Position} (hz : z∈Metric.ball y s) :
    F z ≤ (80/c)^2*s^4/(s^2-‖z-y‖^2)^4 := by
  let g : Position → ℝ := fun x => (s^2-‖x-y‖^2)^4*F x
  have hg : ContinuousOn g (Metric.closedBall y s) :=
    (((continuous_const.sub ((continuous_id.sub continuous_const).norm.pow 2)).pow 4).continuousOn).mul hF
  obtain ⟨x,hx,hm⟩ := (isCompact_closedBall y s).exists_isMaxOn
    ⟨y,Metric.mem_closedBall_self hs.le⟩ hg
  have hzsq : 0 < s^2-‖z-y‖^2 := by
    apply sub_pos.mpr
    exact (sq_lt_sq₀ (norm_nonneg _) hs.le).mpr (by simpa only [Metric.mem_ball,dist_eq_norm] using hz)
  have hfinal : g z ≤ (80/c)^2*s^4 → F z ≤ (80/c)^2*s^4/(s^2-‖z-y‖^2)^4 := by
    intro H
    apply (le_div_iff₀ (pow_pos hzsq 4)).mpr
    simpa only [g,mul_comm] using H
  apply hfinal
  by_cases hpos : 0<g x
  · have hxi : x∈Metric.ball y s := by
      by_contra hn
      have hd : ‖x-y‖=s := le_antisymm
        (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
        (le_of_not_gt (by simpa only [Metric.mem_ball,dist_eq_norm] using hn))
      simp [g,hd] at hpos
    have hxq : 0 < s^2-‖x-y‖^2 := sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg _) hs.le).mpr
      (by simpa only [Metric.mem_ball,dist_eq_norm] using hxi))
    have hFx : 0<F x := (mul_pos_iff_of_pos_left (pow_pos hxq 4)).mp hpos
    have hbar (v : Position) (hv : v∈Metric.ball y s) : F v ≤ interiorBump y s (g x) v := by
      have hvq : 0 < s^2-‖v-y‖^2 := sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg _) hs.le).mpr
        (by simpa only [Metric.mem_ball,dist_eq_norm] using hv))
      rw [interiorBump_eq_div hvq]
      apply (le_div_iff₀ (pow_pos hvq 4)).mpr
      simpa only [g,mul_comm] using (show g v ≤ g x from hm (Metric.ball_subset_closedBall hv))
    have he : F x=interiorBump y s (g x) x := by
      rw [interiorBump_eq_div hxq]
      dsimp [g]
      field_simp
    have hmax : IsLocalMax (fun v => F v-interiorBump y s (g x) v) x := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxi] with v hv
      rw [he,sub_self]
      exact sub_nonpos.mpr (hbar v hv)
    have hq : ContinuousOn (fun v => c*(max (F v) 0)^(3/2:ℝ)) (Metric.ball y s) := by
      exact continuousOn_const.mul (((hF.mono Metric.ball_subset_closedBall).sup continuousOn_const).rpow_const
        (fun _ _ => Or.inr (by norm_num)))
    have HL := (weakLaplacian_le_at_local_max Metric.isOpen_ball hxi
      (hF.mono Metric.ball_subset_closedBall) hq (contDiffOn_interiorBump hs (g x)) hw hmax).trans
      (coordinateLaplacian_interiorBump_le hs hpos.le hxi)
    rw [max_eq_left hFx.le] at HL
    have hid : (g x)^(3/2:ℝ)=(s^2-‖x-y‖^2)^6*(F x)^(3/2:ℝ) := by
      dsimp [g]
      rw [Real.mul_rpow (pow_nonneg hxq.le 4) hFx.le]
      congr 1
      rw [←Real.rpow_natCast _ 4,←Real.rpow_mul hxq.le]
      norm_num
    have HR : c*(g x)^(3/2:ℝ) ≤ 80*(g x)*s^2 := by
      rw [hid]
      have H := (le_div_iff₀ (pow_pos hxq 6)).mp HL
      nlinarith [H]
    exact (hm (Metric.ball_subset_closedBall hz)).trans (weighted_reaction_bound hpos hc HR)
  · exact (hm (Metric.ball_subset_closedBall hz)).trans
      ((le_of_not_gt hpos).trans (by positivity))

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_ScaledProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def kTF : ℝ := (2:ℝ)^(3/2 : ℝ)/(3*Real.pi^2)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_CorrectionDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem coulombKernel_le_one {x : Position} (hx : 1 ≤ ‖x‖) : coulombKernel x ≤ 1 := by
  simpa only [coulombKernel, inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hx

theorem coulombKernel_sq_integrableOn_ball (r : ℝ) :
    IntegrableOn (fun x => (coulombKernel x)^2) (Metric.ball (0 : Position) r) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by simp : 1 ≤ Module.finrank ℝ Position)
    (C := 1) (α := 2) (by norm_num : (2:ℝ) < Module.finrank ℝ Position)
    _ (measurable_coulombKernel.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simp [coulombKernel, Real.rpow_neg (norm_nonneg x)])

theorem coulombKernel_sub_le {x y : Position} (hx : x ≠ 0) (hy : y ≠ 0) :
    |coulombKernel x-coulombKernel y| ≤
      ‖x-y‖/2*((coulombKernel x)^2+(coulombKernel y)^2) := by
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have he : |coulombKernel x-coulombKernel y| =
      |‖y‖-‖x‖| *(‖x‖⁻¹*‖y‖⁻¹) := by
    rw [coulombKernel, coulombKernel, inv_sub_inv hxp.ne' hyp.ne',
      abs_div, abs_mul, abs_of_pos hxp, abs_of_pos hyp]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_comm ‖x‖⁻¹ ‖y‖⁻¹]
  rw [he]
  calc
    |‖y‖-‖x‖| *(‖x‖⁻¹*‖y‖⁻¹) ≤ ‖x-y‖*(‖x‖⁻¹*‖y‖⁻¹) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
      · positivity
    _ ≤ _ := by
      have hb : 2*(‖x‖⁻¹*‖y‖⁻¹) ≤ (‖x‖⁻¹)^2+(‖y‖⁻¹)^2 := by
        nlinarith [sq_nonneg (‖x‖⁻¹-‖y‖⁻¹)]
      have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (x-y))
      dsimp [coulombKernel]
      nlinarith

theorem potentialOf_lipschitz_bound {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) (x x' : Position) :
    ‖potentialOf ρ x-potentialOf ρ x'‖ ≤
      (A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+(∫ y, ρ y))*‖x-x'‖ := by
  have hi (z : Position) : Integrable (fun y => coulombKernel (z-y)*ρ y) :=
    (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hpos hA z).1
  have hb (z : Position) := bounded_density_convolution
    (measurable_coulombKernel.pow_const 2) (fun y => sq_nonneg (coulombKernel y))
    (coulombKernel_sq_integrableOn_ball 1)
    (fun y hy => by nlinarith [coulombKernel_le_one hy, coulombKernel_nonneg y])
    hρ hpos hA z
  have hdomi : Integrable (fun y => ‖x-x'‖/2*
      ((coulombKernel (x-y))^2*ρ y+(coulombKernel (x'-y))^2*ρ y)) :=
    ((hb x).1.add (hb x').1).const_mul (‖x-x'‖/2)
  have hdom : ∀ᵐ y : Position ∂volume,
      ‖coulombKernel (x-y)*ρ y-coulombKernel (x'-y)*ρ y‖ ≤
        ‖x-x'‖/2*((coulombKernel (x-y))^2*ρ y+(coulombKernel (x'-y))^2*ρ y) := by
    filter_upwards [volume.ae_ne x, volume.ae_ne x'] with y hy hy'
    rw [← sub_mul, norm_mul, Real.norm_eq_abs (ρ y), abs_of_nonneg (hpos y)]
    have hh := mul_le_mul_of_nonneg_right
      (coulombKernel_sub_le (sub_ne_zero.mpr hy.symm) (sub_ne_zero.mpr hy'.symm)) (hpos y)
    simpa only [sub_sub_sub_cancel_right, Real.norm_eq_abs, mul_add, add_mul, mul_assoc] using hh
  have hh := norm_integral_le_of_norm_le hdomi hdom
  rw [integral_sub (hi x) (hi x'), integral_const_mul,
    integral_add (hb x).1 (hb x').1] at hh
  refine hh.trans ?_
  have hh' := add_le_add (hb x).2 (hb x').2
  nlinarith [mul_le_mul_of_nonneg_left hh' (norm_nonneg (x-x'))]

theorem potentialOf_lipschitz {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) :
    ∃ C : NNReal, LipschitzWith C (potentialOf ρ) := by
  let B := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+(∫ y, ρ y)
  have hB : 0 ≤ B := by
    exact add_nonneg (mul_nonneg ((hpos 0).trans (hA 0))
      (integral_nonneg (fun y => sq_nonneg _))) (integral_nonneg hpos)
  exact ⟨⟨B,hB⟩, lipschitzWith_iff_norm_sub_le.mpr (potentialOf_lipschitz_bound hρ hpos hA)⟩

theorem potentialOf_continuous {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) :
    Continuous (potentialOf ρ) :=
  (potentialOf_lipschitz hρ hpos hA).choose_spec.continuous

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology ContDiff
noncomputable section
namespace Coulomb

def tfInteriorConstant (c : ℝ) : ℝ :=
  256*(80/((4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ)))^2

lemma tfInteriorConstant_nonneg (c : ℝ) : 0≤tfInteriorConstant c := by
  unfold tfInteriorConstant; positivity

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PatchComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap
noncomputable section
namespace Coulomb

lemma weighted_cap_count_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w F N : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hF : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ x ∂μ, 0≤F x)
    (hFi : Integrable (fun x => w x*(F x)^2) μ)
    (hN : AEStronglyMeasurable N μ) {n : ℝ} (hn : 0≤n)
    (hN0 : ∀ᵐ x ∂μ, 0≤N x ∧ N x≤n) :
    Integrable (fun x => w x*(F x*N x)) μ := by
  apply ((hw.add hFi).const_mul n).mono' (hw.aestronglyMeasurable.mul (hF.mul hN))
  filter_upwards [hw0,hF0,hN0] with x hw hf hnn
  dsimp only [Pi.add_apply,Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg hw (mul_nonneg hf hnn.1))]
  have h1 := mul_le_mul_of_nonneg_left hnn.2 (mul_nonneg hw hf)
  have h2 := mul_nonneg (mul_nonneg hw hn) (sq_nonneg (F x-1/2))
  nlinarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_PatchErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma weighted_cap_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w F : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hF : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ x ∂μ, 0≤F x)
    (hFi : Integrable (fun x => w x*(F x)^2) μ) : Integrable (fun x => w x*F x) μ := by
  simpa only [mul_one] using weighted_cap_count_integrable hw hw0 hF hF0 hFi
    (aestronglyMeasurable_const (b := (1:ℝ))) zero_le_one (Eventually.of_forall (fun _ => ⟨zero_le_one,le_rfl⟩))

lemma ensemble_number_rpow {P : Type*} [Fintype P] (n : P → ℕ) (w : P → ℝ)
    (hw : ∀ p, 0≤w p) (hm : ∑ p, w p=1) :
    (∑ p, (n p:ℝ)^(4/3:ℝ)*w p) ≤ (∑ p, (n p:ℝ)^2*w p)^(2/3:ℝ) := by
  have H := (Real.concaveOn_rpow (by norm_num : (0:ℝ)≤2/3) (by norm_num : (2/3:ℝ)≤1)).le_map_sum
    (t := Finset.univ) (w := w) (p := fun p => (n p:ℝ)^2)
    (fun p _ => hw p) hm (fun p _ => by change 0 ≤ (n p:ℝ)^2; positivity)
  simp only [smul_eq_mul] at H
  have he (p : P) : ((n p:ℝ)^2)^(2/3:ℝ)=(n p:ℝ)^(4/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp only [he] at H
  simpa only [mul_comm] using H

lemma ensemble_number_mean {P : Type*} [Fintype P] (n : P → ℕ) (w : P → ℝ)
    (hw : ∀ p, 0≤w p) (hm : ∑ p, w p=1) :
    (∑ p, (n p:ℝ)*w p) ≤ Real.sqrt (∑ p, (n p:ℝ)^2*w p) := by
  apply Real.le_sqrt_of_sq_le
  have H := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p => (n p:ℝ)*Real.sqrt (w p)) (fun p => Real.sqrt (w p))
  simp only [mul_pow,Real.sq_sqrt (hw _)] at H
  have he : ∑ p, ↑(n p)*Real.sqrt (w p)*Real.sqrt (w p)=∑ p, ↑(n p)*w p :=
    Finset.sum_congr rfl (fun p _ => by rw [mul_assoc,←sq,Real.sq_sqrt (hw p)])
  rw [he,hm,mul_one] at H
  exact H

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ThinCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma transition_derivative_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (K:=Set.Icc (0:ℝ) 1) isCompact_Icc
  intro x hx
  rcases not_and_or.mp hx with h|h
  · have hx0 : x<0 := lt_of_not_ge h
    have H : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_lt_nhds hx0] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [H.deriv_eq]
    simp
  · have hx1 : 1<x := lt_of_not_ge h
    have H : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
      filter_upwards [eventually_gt_nhds hx1] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [H.deriv_eq]
    simp

lemma transition_derivative_bounded : ∃ C : ℝ, 0<C ∧ ∀ x, |deriv Real.smoothTransition x|≤C := by
  obtain ⟨B,hB⟩ := transition_derivative_compact.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff (n:=1)).continuous_deriv_one)
  exact ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x =>
    (by simpa only [Real.norm_eq_abs] using (hB x).trans (le_max_left B 1))⟩

def transitionDerivativeBound : ℝ := Classical.choose transition_derivative_bounded
lemma transitionDerivativeBound_pos : 0<transitionDerivativeBound :=
  (Classical.choose_spec transition_derivative_bounded).1
lemma transition_derivative_bound (x : ℝ) : |deriv Real.smoothTransition x|≤transitionDerivativeBound :=
  (Classical.choose_spec transition_derivative_bounded).2 x

def thinCutCoefficient : ℝ := Real.pi*transitionDerivativeBound
lemma thinCutCoefficient_pos : 0<thinCutCoefficient := mul_pos Real.pi_pos transitionDerivativeBound_pos

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_PhysicalEnsemble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma ensemble_fineLocalizationError {P : Type*} [Fintype P] (n : P → ℕ) (w : P → ℝ)
    (hw : ∀ p, 0≤w p) (hm : ∑ p, w p=1) {b : ℝ} (hb : 0<b) :
    (∑ p, fineLocalizationError (n p) b*w p)≤
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(∑ p, (n p:ℝ)^2*w p)^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (∑ p, (n p:ℝ)^2*w p) := by
  simp only [fineLocalizationError,add_mul,Finset.sum_add_distrib]
  simp_rw [show ∀ p, (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(n p:ℝ)^(4/3:ℝ)*w p =
    ((b⁻¹)^2*((Real.pi^2/2)*neumannBoundary))*((n p:ℝ)^(4/3:ℝ)*w p) by intro p; ring,
    show ∀ p, ((2*Real.pi+1)/(2*b))*(n p:ℝ)*w p=((2*Real.pi+1)/(2*b))*((n p:ℝ)*w p) by intro p; ring]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (ensemble_number_rpow n w hw hm) (by positivity [neumannBoundary_nonneg]))
    (mul_le_mul_of_nonneg_left (ensemble_number_mean n w hw hm) (by positivity [Real.pi_pos]))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicPatchCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma le_sqrt_sum_squares {C : Type*} [Fintype C] (f : C → ℝ) (c : C) :
    f c≤Real.sqrt (∑ v, (f v)^2) := by
  apply le_trans (le_abs_self _)
  apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mpr
  rw [sq_abs]
  exact Finset.single_le_sum (fun v _ => sq_nonneg (f v)) (Finset.mem_univ c)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma screenMass_inv_cube_le (δ : ℝ) (a : ℝ) : (a^3)⁻¹ ≤ screenMass δ a :=
  (le_max_left _ _).trans (screenMass_ge_base δ a)

lemma screenMass_square_ge (δ a : ℝ) : screenMass δ a ≤ (screenMass δ a)^2 := by
  nlinarith [screenMass_ge_one δ a]

lemma screenMass_pairscale (δ : ℝ) {a : ℝ} (ha : 0 < a) : screenMass δ a/a ≤ (screenMass δ a)^2 := by
  apply (div_le_iff₀ ha).mpr
  have H := mul_le_mul_of_nonneg_left (screenMass_scale δ ha) (screenMass_pos δ a).le
  nlinarith

lemma screenMass_kinetic_scale (δ : ℝ) {a : ℝ} (ha : 0 < a) :
    (screenMass δ a)^(4/3:ℝ)/a ≤ (screenMass δ a)^2 := by
  let m := screenMass δ a
  have hm : 0  <  m := screenMass_pos δ a
  have h13 : 1 ≤ a*m^(1/3:ℝ) := (screenBaseMass_cuberoot_scale ha).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (screenBaseMass_nonneg a) (screenMass_ge_base δ a) (by norm_num)) ha.le)
  have h23 : 1 ≤ a*m^(2/3:ℝ) := h13.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (screenMass_ge_one δ a) (by norm_num : (1/3:ℝ) ≤ 2/3)) ha.le)
  have H := mul_le_mul_of_nonneg_left h23 (Real.rpow_nonneg hm.le (4/3:ℝ))
  have he : m^(4/3:ℝ)*(a*m^(2/3:ℝ))=m^2*a := by
    calc
      _ = a*(m^(4/3:ℝ)*m^(2/3:ℝ)) := by ring
      _ = _ := by rw [←Real.rpow_add hm]; norm_num; ring
  rw [mul_one,he] at H
  exact (div_le_iff₀ ha).mpr H

lemma sqrt_cap_expression {C P m a : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hm : 0 ≤ m) (ha : 0 < a) :
    Real.sqrt (C*P*m^2/a^2)=Real.sqrt C*Real.sqrt P*m/a := by
  rw [Real.sqrt_div (mul_nonneg (mul_nonneg hC hP) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hC hP),Real.sqrt_mul hC,Real.sqrt_sq hm,Real.sqrt_sq ha.le]

lemma sqrt_deleted_expression {C D P m a β : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : 0 ≤ P) (hm : 0 ≤ m) (ha : 0 < a) (hβ : 0 ≤ β) :
    Real.sqrt ((C*P*m^2/a^2)*(18*D*(β*a/a)*P*m^2))=
      Real.sqrt (18*C*D)*Real.sqrt β*P*m^2/a := by
  have he : (C*P*m^2/a^2)*(18*D*(β*a/a)*P*m^2)=(18*C*D)*β*(P*m^2/a)^2 := by field_simp
  rw [he,Real.sqrt_mul (mul_nonneg (by positivity) hβ),Real.sqrt_mul (by positivity),
    Real.sqrt_sq (div_nonneg (mul_nonneg hP (pow_nonneg hm 2)) ha.le)]
  ring

lemma sqrt_out_expression {C P m : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hm : 0 ≤ m) :
    Real.sqrt (C*P*m^2)=Real.sqrt C*Real.sqrt P*m := by
  rw [Real.sqrt_mul (mul_nonneg hC hP),Real.sqrt_mul hC,Real.sqrt_sq hm]

lemma fine_count_expression {C P m : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hm : 0 ≤ m) :
    (C*P*m^2)^(2/3:ℝ)=C^(2/3:ℝ)*P^(2/3:ℝ)*m^(4/3:ℝ) := by
  rw [Real.mul_rpow (mul_nonneg hC hP) (sq_nonneg _),Real.mul_rpow hC hP,←Real.rpow_natCast,←Real.rpow_mul hm]
  norm_num

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end

end OAI
end


