-- Prove2me | Definitions.Def_OAIErdos3B1379
-- name    : OAIErdos3B1379
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T03:59:52.287369+00:00
-- url     : https://prove2.me/theorems/7d0d7765-1558-4d4d-965c-bc1bcb29397d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1380 of 1394
-- statement:
--   Definitions bundle 1380 of 1394 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1378`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1380 available.
--
--   Modules: `OAI.Erdos3.FiniteProbabilityWeights.complexMean_empty_tuple`, `OAI.Erdos3.FiniteProbabilityWeights.complexMean_pi_fin_cons`, `OAI.Erdos3.PolynomialPatch.value_mem_Icc`, `OAI.Erdos3.abs_sub_eq_add_sub_two_min`, `OAI.Erdos3.affineBoxAverage_eq`, `OAI.Erdos3.affineBoxAverage_mem_Icc`, `OAI.Erdos3.binaryDensity_cap`, `OAI.Erdos3.binaryDensity_lipschitz`, `OAI.Erdos3.booleanAffinePolynomial_eval`, `OAI.Erdos3.boxAverage_eq_translate`, `OAI.Erdos3.boxAverage_mem_Icc`, `OAI.Erdos3.boxProbabilityWindow_cap`, `OAI.Erdos3.boxProbabilityWindow_integrable`, `OAI.Erdos3.boxProbabilityWindow_mass`, `OAI.Erdos3.boxProbabilityWindow_measurable`, `OAI.Erdos3.boxProbabilityWindow_nonneg`, `OAI.Erdos3.boxProbabilityWindow_translate`, `OAI.Erdos3.densityMixture_cap`, `OAI.Erdos3.densityMixture_lipschitz`, `OAI.Erdos3.densityMixture_section_integrable`, `OAI.Erdos3.densityMixture_uniform_bound`, `OAI.Erdos3.density_overlap_mass`, `OAI.Erdos3.dependent_fin_cons_map`, `OAI.Erdos3.finiteNestedSiteExpansion_mass`, `OAI.Erdos3.finite_lipschitz_linear_combination`, `OAI.Erdos3.integerScalarCubePi_root_bounds`, `OAI.Erdos3.integerScalarCubeWeights_mean`, `OAI.Erdos3.integerScalarCubeWeights_root_bounds`, `OAI.Erdos3.integral_density_overlap`, `OAI.Erdos3.integral_intervalWindow`, `OAI.Erdos3.intervalWindow_integrable`, `OAI.Erdos3.intervalWindow_measurable`, `OAI.Erdos3.intervalWindow_mem_Icc`, `OAI.Erdos3.kernelAverage_cap`, `OAI.Erdos3.kernelAverage_lipschitz`, `OAI.Erdos3.kernelAverage_nonneg`, `OAI.Erdos3.linearBoxDensity_measurable`, `OAI.Erdos3.linearBoxDensity_mem_Icc`, `OAI.Erdos3.linearDensityPullback_measurable`, `OAI.Erdos3.linearDensityPullback_nonneg`, `OAI.Erdos3.normalizedIntervalWindow_integrable`, `OAI.Erdos3.normalizedIntervalWindow_le`, `OAI.Erdos3.normalizedIntervalWindow_mass`, `OAI.Erdos3.normalizedIntervalWindow_measurable`, `OAI.Erdos3.normalizedIntervalWindow_nonneg`, `OAI.Erdos3.normalizedIntervalWindow_translate`, `OAI.Erdos3.product_density_l1_le_sum`, `OAI.Erdos3.sum_dependent_fin_cons`, `OAI.Erdos3.twoBoxDifferenceDensity_mem_Icc`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

theorem finite_lipschitz_linear_combination {T X : Type*} [Fintype T] [PseudoMetricSpace X]
    (c : T → ℂ) (f : T → X → ℂ) {L B : ℝ≥0}
    (hf : ∀ t, LipschitzWith L (f t)) (hb : ∀ t x, ‖f t x‖ ≤ B) :
    (∀ x, ‖∑ t, c t * f t x‖ ≤ ((∑ t, ‖c t‖₊) * B : ℝ≥0)) ∧
      LipschitzWith ((∑ t, ‖c t‖₊) * L) (fun x => ∑ t, c t * f t x) := by
  constructor
  · intro x
    calc
      _ ≤ ∑ t, ‖c t * f t x‖ := norm_sum_le _ _
      _ ≤ ∑ t, ‖c t‖ * B := Finset.sum_le_sum (fun t _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb t x) (norm_nonneg _))
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ ∑ t, dist (c t * f t x) (c t * f t y) := dist_sum_sum_le _ _ _
      _ = ∑ t, ‖c t‖ * dist (f t x) (f t y) := by
        simp only [dist_eq_norm, ← mul_sub, norm_mul]
      _ ≤ ∑ t, ‖c t‖ * ((L : ℝ) * dist x y) := Finset.sum_le_sum (fun t _ =>
        mul_le_mul_of_nonneg_left ((hf t).dist_le_mul _ _) (norm_nonneg _))
      _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul, mul_assoc]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

theorem finiteNestedSiteExpansion_mass {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (c : ℂ) (a : A → B → ℂ) (b : C → ℂ) :
    (∑ i, ∑ j, ∑ k, ‖(c * a i j) * b k‖) =
      ‖c‖ * (∑ i, ∑ j, ‖a i j‖) * (∑ k, ‖b k‖) := by
  simp only [norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {S T U D : Type*} [Fintype S] [Fintype T]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d D E : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

end PolynomialSlots

namespace PolynomialPatch

variable {σ τ : Type*} {s d : ℕ}

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open _root_.MvPolynomial

variable {X : Type*} {s d : ℕ}

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d n D E : ℕ}

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3

namespace PolynomialPatch

variable {σ : Type*} {s D E : ℕ}

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3
namespace PolynomialPatch

open _root_.MvPolynomial

variable {σ τ : Type*} {s : ℕ}

end PolynomialPatch
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

theorem dependent_fin_cons_map {n : ℕ} {X E : Fin (n + 1) → Type*}
    (a : ∀ i, X i → E i) (x : X 0) (y : ∀ i : Fin n, X i.succ) :
    (fun i => a i (Fin.cons x y i)) = Fin.cons (a 0 x) (fun i => a i.succ (y i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem complexMean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (F : (∀ i, X i) → ℂ) :
    p.complexMean F = F (fun i => Fin.elim0 i) := by
  have hF : F = fun _ => F (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg F (Subsingleton.elim _ _)
  rw [hF, p.complexMean_const]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

theorem intervalWindow_mem_Icc (a b t : ℝ) : intervalWindow a b t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ioc a b <;> simp [intervalWindow, ht]

theorem intervalWindow_measurable (a b : ℝ) : Measurable (intervalWindow a b) :=
  measurable_const.indicator measurableSet_Ioc

theorem intervalWindow_integrable (a b : ℝ) : Integrable (intervalWindow a b) := by
  exact (integrableOn_const (s := Ioc a b) (μ := volume) (C := (1 : ℝ))
    (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
    measurableSet_Ioc

theorem integral_intervalWindow (a b : ℝ) :
    (∫ t, intervalWindow a b t) = max (b - a) 0 := by
  rw [intervalWindow, integral_indicator_const (1 : ℝ) measurableSet_Ioc, smul_eq_mul, mul_one,
    Real.volume_real_Ioc]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem normalizedIntervalWindow_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (x t : ℝ) :
    0 ≤ normalizedIntervalWindow ℓ x t := div_nonneg (intervalWindow_mem_Icc _ _ _).1 hℓ.le

theorem normalizedIntervalWindow_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x t : ℝ) :
    normalizedIntervalWindow ℓ x t ≤ 1 / ℓ :=
  div_le_div_of_nonneg_right (intervalWindow_mem_Icc _ _ _).2 hℓ.le

theorem normalizedIntervalWindow_integrable (ℓ x : ℝ) :
    Integrable (normalizedIntervalWindow ℓ x) := (intervalWindow_integrable _ _).div_const ℓ

theorem normalizedIntervalWindow_measurable (ℓ x : ℝ) :
    Measurable (normalizedIntervalWindow ℓ x) := (intervalWindow_measurable _ _).div_const ℓ

theorem normalizedIntervalWindow_mass {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    (∫ t, normalizedIntervalWindow ℓ x t) = 1 := by
  unfold normalizedIntervalWindow
  rw [integral_div, integral_intervalWindow]
  simp only [add_sub_cancel_left, max_eq_left hℓ.le, div_self hℓ.ne']

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelMixtureControl
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem kernelAverage_lipschitz {X T : Type*} [PseudoMetricSpace X] [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) (C D : ℝ≥0)
    (hK : ∀ x, Integrable (K x) μ) (hg : AEStronglyMeasurable g μ)
    (hgC : ∀ t, ‖g t‖ ≤ C)
    (hmove : ∀ x y, (∫ t, |K x t - K y t| ∂μ) ≤ D * dist x y) :
    LipschitzWith (C * D) (kernelAverage μ K g) := by
  have hint (x) : Integrable (fun t => K x t * g t) μ :=
    (hK x).mul_bdd hg (Filter.Eventually.of_forall hgC)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, K x t * g t ∂μ) - ∫ t, K y t * g t ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hd : Integrable (fun t => |K x t - K y t|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hK x).sub (hK y)).norm
  have hpoint (t) : ‖K x t * g t - K y t * g t‖ ≤ (C : ℝ) * |K x t - K y t| := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hgC t) (abs_nonneg (K x t - K y t))
  have h := norm_integral_le_of_norm_le (hd.const_mul (C : ℝ)) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at h
  rw [Real.norm_eq_abs] at h
  apply h.trans
  have hbound := mul_le_mul_of_nonneg_left (hmove x y) C.coe_nonneg
  simpa only [NNReal.coe_mul, mul_assoc] using hbound

theorem kernelAverage_nonneg {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ)
    (hK : ∀ x t, 0 ≤ K x t) (hg : ∀ t, 0 ≤ g t) (x : X) :
    0 ≤ kernelAverage μ K g x := integral_nonneg (fun t => mul_nonneg (hK x t) (hg t))

theorem kernelAverage_cap {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) {C : ℝ}
    (hK : ∀ x, Integrable (K x) μ) (hK0 : ∀ x t, 0 ≤ K x t)
    (hmass : ∀ x, (∫ t, K x t ∂μ) = 1) (hg : AEStronglyMeasurable g μ)
    (hgC : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : X) :
    kernelAverage μ K g x ≤ C := by
  have hnorm (t) : ‖g t‖ ≤ C := by simpa only [Real.norm_of_nonneg (hgC t).1] using (hgC t).2
  have hint : Integrable (fun t => K x t * g t) μ := (hK x).mul_bdd hg (Filter.Eventually.of_forall hnorm)
  have h := integral_mono hint ((hK x).mul_const C)
    (fun t => mul_le_mul_of_nonneg_left (hgC t).2 (hK0 x t))
  simpa only [kernelAverage, integral_mul_const, hmass, one_mul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem binaryDensity_cap {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (C D : ℝ≥0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) D) (p : X × Y) :
    binaryDensity f g p ∈ Set.Icc (0 : ℝ) (C * D) :=
  ⟨mul_nonneg (hf _).1 (hg _).1, mul_le_mul (hf _).2 (hg _).2 (hg _).1 C.coe_nonneg⟩

theorem binaryDensity_lipschitz {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℝ) (g : Y → ℝ) (C D L M : ℝ≥0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) D)
    (hL : LipschitzWith L f) (hM : LipschitzWith M g) :
    LipschitzWith (D * L + C * M) (binaryDensity f g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdx : dist x.1 y.1 ≤ dist x y := le_max_left _ _
  have hdy : dist x.2 y.2 ≤ dist x y := le_max_right _ _
  have hleft : |f x.1 - f y.1| ≤ (L : ℝ) * dist x y := by
    have h := hL.dist_le_mul x.1 y.1
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdx L.coe_nonneg)
  have hright : |g x.2 - g y.2| ≤ (M : ℝ) * dist x y := by
    have h := hM.dist_le_mul x.2 y.2
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdy M.coe_nonneg)
  rw [Real.dist_eq]
  change |f x.1 * g x.2 - f y.1 * g y.2| ≤ _
  calc
    |f x.1 * g x.2 - f y.1 * g y.2| =
        |(f x.1 - f y.1) * g x.2 + f y.1 * (g x.2 - g y.2)| := by congr 1; ring
    _ ≤ |(f x.1 - f y.1) * g x.2| + |f y.1 * (g x.2 - g y.2)| := abs_add_le _ _
    _ = |f x.1 - f y.1| * g x.2 + f y.1 * |g x.2 - g y.2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hg _).1, abs_of_nonneg (hf _).1]
    _ ≤ ((L : ℝ) * dist x y) * D + C * ((M : ℝ) * dist x y) :=
      add_le_add (mul_le_mul hleft (hg _).2 (hg _).1 (mul_nonneg L.coe_nonneg dist_nonneg))
        (mul_le_mul (hf _).2 hright (abs_nonneg _) C.coe_nonneg)
    _ = (D * L + C * M : ℝ≥0) * dist x y := by push_cast; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem integral_density_overlap (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hfmass : (∫ x, f x) = 1) (hgmass : (∫ x, g x) = 1) :
    (∫ x, |f x - g x|) = 2 - 2 * ∫ x, min (f x) (g x) := by
  have hm : Integrable (fun x => min (f x) (g x)) := hf.inf hg
  have hsum : Integrable (fun x => f x + g x) := hf.add hg
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [integral_sub hsum (hm.const_mul 2), integral_add hf hg, integral_const_mul,
    hfmass, hgmass]
  norm_num

theorem density_overlap_mass (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfmass : (∫ x, f x) = 1) :
    (∫ x, min (f x) (g x)) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun x => le_min (hf0 x) (hg0 x)), ?_⟩
  have hm : Integrable (fun x => min (f x) (g x)) := hf.inf hg
  exact (integral_mono hm hf (fun x => min_le_left _ _)).trans_eq hfmass

theorem product_density_l1_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hg : ∀ i, Integrable (g i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hfmass : ∀ i, (∫ x, f i x) = 1) (hgmass : ∀ i, (∫ x, g i x) = 1) :
    (∫ x : ι → ℝ, |(∏ i, f i (x i)) - ∏ i, g i (x i)|) ≤
      ∑ i, ∫ x, |f i x - g i x| := by
  let F : (ι → ℝ) → ℝ := fun x => ∏ i, f i (x i)
  let G : (ι → ℝ) → ℝ := fun x => ∏ i, g i (x i)
  let H : (ι → ℝ) → ℝ := fun x => ∏ i, min (f i (x i)) (g i (x i))
  let mass : ι → ℝ := fun i => ∫ x, min (f i x) (g i x)
  have hF : Integrable F := Integrable.fintype_prod hf
  have hG : Integrable G := Integrable.fintype_prod hg
  have hH : Integrable H := Integrable.fintype_prod (fun i => (hf i).inf (hg i))
  have hpoint (x : ι → ℝ) : |F x - G x| ≤ F x + G x - 2 * H x := by
    have hHF : H x ≤ F x := Finset.prod_le_prod
      (fun i _ => le_min (hf0 i _) (hg0 i _)) (fun i _ => min_le_left _ _)
    have hHG : H x ≤ G x := Finset.prod_le_prod
      (fun i _ => le_min (hf0 i _) (hg0 i _)) (fun i _ => min_le_right _ _)
    rw [abs_sub_eq_add_sub_two_min]
    have hmin := le_min hHF hHG
    linarith
  have hFmass : (∫ x, F x) = 1 := by
    dsimp only [F]
    rw [integral_fintype_prod_volume_eq_prod]
    simp only [hfmass, Finset.prod_const_one]
  have hGmass : (∫ x, G x) = 1 := by
    dsimp only [G]
    rw [integral_fintype_prod_volume_eq_prod]
    simp only [hgmass, Finset.prod_const_one]
  have hHmass : (∫ x, H x) = ∏ i, mass i := by
    exact integral_fintype_prod_volume_eq_prod (fun i x => min (f i x) (g i x))
  have hleft : Integrable (fun x => |F x - G x|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hF.sub hG).norm
  have hsum : Integrable (fun x => F x + G x) := hF.add hG
  have hright : Integrable (fun x => F x + G x - 2 * H x) := hsum.sub (hH.const_mul 2)
  have hbound := integral_mono hleft hright hpoint
  rw [integral_sub hsum (hH.const_mul 2), integral_add hF hG,
    integral_const_mul, hFmass, hGmass, hHmass] at hbound
  have hm (i) : mass i ∈ Set.Icc (0 : ℝ) 1 :=
    density_overlap_mass (f i) (g i) (hf i) (hg i) (hf0 i) (hg0 i) (hfmass i)
  have hprod := one_sub_sum_le_positive_prod Finset.univ mass (fun i => 1 - mass i)
    (fun i _ => (hm i).1) (fun i _ => ⟨by linarith [(hm i).2], by linarith [(hm i).1]⟩)
    (fun i _ => by linarith)
  have herr : (∑ i, ∫ x, |f i x - g i x|) = 2 * ∑ i, (1 - mass i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_density_overlap (f i) (g i) (hf i) (hg i) (hfmass i) (hgmass i)]
    dsimp only [mass]
    ring
  rw [herr]
  change (∫ x, |F x - G x|) ≤ _
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxWindowAveraging
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem boxProbabilityWindow_nonneg (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x t : ι → ℝ) :
    0 ≤ boxProbabilityWindow ℓ x t :=
  Finset.prod_nonneg (fun i _ => normalizedIntervalWindow_nonneg (hℓ i) _ _)

theorem boxProbabilityWindow_integrable (ℓ x : ι → ℝ) :
    Integrable (boxProbabilityWindow ℓ x) :=
  Integrable.fintype_prod (fun i => normalizedIntervalWindow_integrable (ℓ i) (x i))

theorem boxProbabilityWindow_measurable (ℓ x : ι → ℝ) : Measurable (boxProbabilityWindow ℓ x) := by
  apply Finset.measurable_prod
  intro i _
  exact (normalizedIntervalWindow_measurable _ _).comp (measurable_pi_apply i)

theorem boxProbabilityWindow_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x : ι → ℝ) :
    (∫ t, boxProbabilityWindow ℓ x t) = 1 := by
  unfold boxProbabilityWindow
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [normalizedIntervalWindow_mass (hℓ _), Finset.prod_const_one]

theorem boxProbabilityWindow_cap (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) (x t : ι → ℝ) :
    boxProbabilityWindow ℓ x t ≤ ∏ i, 1 / ℓ i :=
  Finset.prod_le_prod (fun i _ => normalizedIntervalWindow_nonneg (hℓ i) _ _)
    (fun i _ => normalizedIntervalWindow_le (hℓ i) _ _)

theorem boxAverage_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (g : (ι → ℝ) → ℝ) {C : ℝ} (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ι → ℝ) :
    kernelAverage volume (boxProbabilityWindow ℓ) g x ∈ Set.Icc (0 : ℝ) C :=
  ⟨kernelAverage_nonneg volume _ g (boxProbabilityWindow_nonneg ℓ hℓ) (fun t => (hbound t).1) x,
    kernelAverage_cap volume _ g (boxProbabilityWindow_integrable ℓ) (boxProbabilityWindow_nonneg ℓ hℓ)
      (boxProbabilityWindow_mass ℓ hℓ) hg hbound x⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBoxTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem normalizedIntervalWindow_translate (ℓ x t : ℝ) :
    normalizedIntervalWindow ℓ x t = normalizedIntervalWindow ℓ 0 (t - x) := by
  have hm : t ∈ Set.Ioc x (x + ℓ) ↔ t - x ∈ Set.Ioc 0 (0 + ℓ) := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [normalizedIntervalWindow, intervalWindow, Set.indicator, hm]

variable {ι : Type*} [Fintype ι]

theorem boxProbabilityWindow_translate (ℓ x t : ι → ℝ) :
    boxProbabilityWindow ℓ x t = boxProbabilityWindow ℓ 0 (t - x) := by
  apply Finset.prod_congr rfl
  intro i _
  exact normalizedIntervalWindow_translate _ _ _

theorem boxAverage_eq_translate (ℓ : ι → ℝ) (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    kernelAverage volume (boxProbabilityWindow ℓ) g x =
      ∫ u, boxProbabilityWindow ℓ 0 u * g (u + x) := by
  change (∫ t, boxProbabilityWindow ℓ x t * g t) = _
  rw [← integral_add_right_eq_self (fun t => boxProbabilityWindow ℓ x t * g t) x]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [boxProbabilityWindow_translate, add_sub_cancel_right]

theorem affineBoxAverage_eq (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x =
      kernelAverage volume (boxProbabilityWindow ℓ) (fun t => g (A t)) (A.symm x) := by
  rw [boxAverage_eq_translate]
  unfold affineBoxAverage
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [map_add, A.apply_symm_apply, ContinuousLinearEquiv.coe_coe, add_comm]

theorem affineBoxAverage_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (g : (ι → ℝ) → ℝ) {C : ℝ}
    (hg : Measurable g) (hbound : ∀ t, g t ∈ Set.Icc (0 : ℝ) C) (x : ι → ℝ) :
    affineBoxAverage ℓ A.toContinuousLinearMap g x ∈ Set.Icc (0 : ℝ) C := by
  rw [affineBoxAverage_eq]
  exact boxAverage_mem_Icc ℓ hℓ _ (hg.comp A.continuous.measurable).aestronglyMeasurable
    (fun t => hbound (A t)) _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

variable [Fintype ι]

theorem linearDensityPullback_measurable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (linearDensityPullback A f) :=
  measurable_const.mul (hf.comp A.symm.continuous.measurable)

omit [Fintype ι] in
theorem linearDensityPullback_nonneg (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ linearDensityPullback A f x := mul_nonneg (inverseJacobian_pos A).le (hf _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem linearBoxDensity_measurable (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measurable (linearBoxDensity ℓ A) :=
  linearDensityPullback_measurable A (boxProbabilityWindow_measurable ℓ 0)

theorem linearBoxDensity_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    linearBoxDensity ℓ A x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap ℓ hℓ A) :=
  ⟨linearDensityPullback_nonneg A (boxProbabilityWindow_nonneg ℓ hℓ 0) x,
    mul_le_mul_of_nonneg_left (boxProbabilityWindow_cap ℓ hℓ 0 (A.symm x))
      (inverseJacobian_pos A).le⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TwoBoxSmoothingComplex
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem twoBoxDifferenceDensity_mem_Icc (ℓ r : ι → ℝ)
    (hℓ : ∀ i, 0 < ℓ i) (hr : ∀ i, 0 < r i)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    twoBoxDifferenceDensity ℓ r A B x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap r hr B) :=
  affineBoxAverage_mem_Icc ℓ hℓ A _ (linearBoxDensity_measurable r B)
    (linearBoxDensity_mem_Icc r hr B) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_section_integrable {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ C t) (x : X) :
    Integrable (fun t => F t x) μ :=
  hC.mono' (hm x) (hbound.mono (fun _ ht => ht x))

theorem densityMixture_cap {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (C : T → ℝ) (hC : Integrable C μ)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hbound : ∀ᵐ t ∂μ, ∀ x, F t x ∈ Set.Icc (0 : ℝ) (C t)) (x : X) :
    densityMixture μ F x ∈ Set.Icc (0 : ℝ) (∫ t, C t ∂μ) := by
  have hb : ∀ᵐ t ∂μ, ∀ y, ‖F t y‖ ≤ C t := hbound.mono fun t ht y => by
    rw [Real.norm_of_nonneg (ht y).1]
    exact (ht y).2
  exact ⟨integral_nonneg_of_ae (hbound.mono (fun _ ht => (ht x).1)),
    integral_mono_ae (densityMixture_section_integrable μ F C hC hm hb x) hC
      (hbound.mono (fun _ ht => (ht x).2))⟩

theorem densityMixture_lipschitz {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) (F : T → X → ℝ) (L : T → ℝ≥0)
    (hL : Integrable (fun t => (L t : ℝ)) μ)
    (hint : ∀ x, Integrable (fun t => F t x) μ)
    (hLip : ∀ᵐ t ∂μ, LipschitzWith (L t) (F t)) :
    LipschitzWith ⟨∫ t, (L t : ℝ) ∂μ, integral_nonneg (fun t => (L t).coe_nonneg)⟩
      (densityMixture μ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ t, F t x ∂μ) - ∫ t, F t y ∂μ| ≤ _
  rw [← integral_sub (hint x) (hint y)]
  have hb : ∀ᵐ t ∂μ, ‖F t x - F t y‖ ≤ (L t : ℝ) * dist x y := by
    filter_upwards [hLip] with t ht
    simpa only [Real.dist_eq, Real.norm_eq_abs] using ht.dist_le_mul x y
  have h := norm_integral_le_of_norm_le (hL.mul_const (dist x y)) hb
  rw [Real.norm_eq_abs, integral_mul_const] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_uniform_bound {T X : Type*} [MeasurableSpace T] [PseudoMetricSpace X]
    (μ : Measure T) [IsProbabilityMeasure μ] (F : T → X → ℝ) (C L : ℝ≥0)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (hF : ∀ᵐ t ∂μ, (∀ x, F t x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (F t)) :
    (∀ x, densityMixture μ F x ∈ Set.Icc (0 : ℝ) C) ∧ LipschitzWith L (densityMixture μ F) := by
  have hb : ∀ᵐ t ∂μ, ∀ x, ‖F t x‖ ≤ (C : ℝ) := by
    filter_upwards [hF] with t ht
    intro x
    rw [Real.norm_of_nonneg (ht.1 x).1]
    exact (ht.1 x).2
  have hi := densityMixture_section_integrable μ F (fun _ => (C : ℝ)) (integrable_const _) hm hb
  constructor
  · intro x
    have h := densityMixture_cap μ F (fun _ => (C : ℝ)) (integrable_const _) hm
      (hF.mono (fun _ ht => ht.1)) x
    simpa only [integral_const, probReal_univ, one_smul] using h
  · have h := densityMixture_lipschitz μ F (fun _ => L) (integrable_const _) hi
      (hF.mono (fun _ ht => ht.2))
    have heq : (⟨∫ _ : T, (L : ℝ) ∂μ, integral_nonneg (fun _ => L.coe_nonneg)⟩ : ℝ≥0) = L := by
      apply Subtype.ext
      simp
    rw [heq] at h
    exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T : Type*} [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffinePolynomial_eval {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval a (booleanAffinePolynomial b v t) =
      ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, v, r) := by
  simp only [booleanAffinePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCubeWeights_root_bounds {α : Type*} [Fintype α] [DecidableEq α]
    {H : ℕ} (hH : 0 < H) (z : IntegerScalarCubeBox α H)
    (hz : (integerScalarCubeWeights α H hH).weight z ≠ 0) :
    0 ≤ (z none : ℤ) ∧ (z none : ℤ) ≤ ((H - 1 : ℕ) : ℤ) := by
  have hmem : z ∈ integerScalarCubeSet α H := by
    by_contra hn
    apply hz
    simp only [integerScalarCubeWeights, FiniteProbabilityWeights.condition,
      hn, ite_false, zero_div]
  have hr := ((mem_integerScalarCubeSet H z).mp hmem) ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hr
  exact ⟨hr.1, by omega⟩

theorem integerScalarCubePi_root_bounds {G : Type*} [Fintype G]
    (H : G → ℕ) (hH : ∀ g, 0 < H g)
    (z : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hz : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight z ≠ 0)
    (g : G) :
    0 ≤ (z g none : ℤ) ∧ (z g none : ℤ) ≤ ((H g - 1 : ℕ) : ℤ) := by
  apply integerScalarCubeWeights_root_bounds (hH g) (z g)
  change (∏ g, (integerScalarCubeWeights Empty (H g) (hH g)).weight (z g)) ≠ 0 at hz
  exact Finset.prod_ne_zero_iff.mp hz g (Finset.mem_univ g)

end Erdos3

namespace Erdos3

open scoped BigOperators

theorem integerScalarCubeWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (f : IntegerScalarCubeBox I L → ℝ) :
    (integerScalarCubeWeights I L hL).mean f = 𝔼 x : integerScalarCubeSet I L, f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) f

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

end OAI

end


