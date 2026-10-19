-- Prove2me | Definitions.Def_OAIE3v2B018
-- name    : OAIE3v2B018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:21.618162+00:00
-- url     : https://prove2.me/theorems/4b330cda-a241-486f-8f5d-136867e589f4
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 19 of 311
-- statement:
--   Definitions bundle 19 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CompatibleReducedFastReset.lean`, `Dynamics/FrozenCorrelationBudget.lean`, `Dynamics/RationalConstraintCountBudget.lean`, `Dynamics/SynchronizedCorrectionBudget.lean`, `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/CommonIntegralModelEquivalences.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/FrozenCosetVariation.lean`, `Estimates/InteriorIntervalCutoff.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeCorrelatedFactorFamily.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/UnitExpansionCorrelation.lean`, `Estimates/WeightedOverlapCorrelation.lean`, `Geometry/BoxOverlapSize.lean`, `Geometry/ConjugationCoordinates.lean`, `Geometry/QuantitativeMetricPartition.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/UnitIntervalBox.lean`, `Lattices/IntegerAbsInterval.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Linear/RescaledLieBasis.lean`, `Linear/SpanKernelGenerators.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/RankAdaptedNiltest.lean`, `Nilpotent/RealPolynomialBCH.lean`, `Nilpotent/RealifiedBCHFiniteAtlas.lean`, `Polynomial/IntegerPolynomialCongruence.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Polynomial/UniformPolynomialPeriodBudget.lean`, `Sampling/ConjugationGridBudget.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_weighted_term {I : Type*} [Fintype I] (c z : I → ℂ)
    {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : (∑ i, ‖c i‖) ≤ M) (hsum : delta ≤ ‖∑ i, c i * z i‖) :
    ∃ i, delta / M ≤ ‖z i‖ := by
  classical
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, norm_zero] at hsum
    linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) hI
  refine ⟨i, (div_le_iff₀ hM).mpr ?_⟩
  calc
    delta ≤ ‖∑ j, c j * z j‖ := hsum
    _ ≤ ∑ j, ‖c j * z j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * ‖z i‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * ‖z i‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ M * ‖z i‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖z i‖ * M := mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanKernelGenerators
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {K V W κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype κ]

noncomputable def finiteCombination (v : κ → V) : (κ → K) →ₗ[K] V :=
  (Pi.basisFun K κ).constr K v

theorem finiteCombination_apply (v : κ → V) (x : κ → K) :
    finiteCombination v x = ∑ i, x i • v i := by
  classical
  rw [finiteCombination, Basis.constr_apply_fintype]
  rfl

theorem finiteCombination_basis (v : κ → V) (i : κ) :
    finiteCombination v (Pi.basisFun K κ i) = v i :=
  Basis.constr_basis (Pi.basisFun K κ) K v i

theorem finiteCombination_range (v : κ → V) :
    LinearMap.range (finiteCombination (K := K) v) = Submodule.span K (Set.range v) :=
  Basis.constr_range (Pi.basisFun K κ) K

theorem finiteCombination_kernel_image (v : κ → V) (P : V →ₗ[K] W) :
    (LinearMap.ker (P.comp (finiteCombination v))).map (finiteCombination v) =
      Submodule.span K (Set.range v) ⊓ LinearMap.ker P := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(finiteCombination_range v).le ⟨x, rfl⟩, hx⟩
  · rintro ⟨hy, hP⟩
    obtain ⟨x, rfl⟩ := (finiteCombination_range v).ge hy
    exact ⟨x, hP, rfl⟩

section Rational

variable {V W ι η κ : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype κ] [Fintype η]

theorem finiteCombination_constraint_kernel (f : Basis η ℚ W) (P : V →ₗ[ℚ] W)
    (v : κ → V) :
    LinearMap.ker (Matrix.mulVecLin (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i)) =
      LinearMap.ker (P.comp (finiteCombination v)) := by
  classical
  ext x
  have he : (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i) *ᵥ x =
      f.equivFun (P (finiteCombination v x)) := by
    ext i
    simp only [finiteCombination_apply, map_sum, map_smul, Basis.equivFun_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  change (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i) *ᵥ x = 0 ↔
    P (finiteCombination v x) = 0
  rw [he, LinearEquiv.map_eq_zero_iff]

end Rational
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

theorem grid_box_count_le_exp (C d l : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p) :
    (((2 * ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ + 1) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + (C + 5)) ^ (C + 5)) := by
  let t := p + (C + 5 : ℕ)
  have ht : 5 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have ht1 : 1 ≤ t := by linarith
  have hpt : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have hshift : p + C ≤ t := by dsimp [t]; push_cast; linarith
  have hpT : p ≤ t ^ C := by
    apply hpt.trans
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (show 1 ≤ C by omega)
  have hprod : (l : ℝ) * Real.exp ((p + C) ^ C) ≤ Real.exp (t ^ (C + 1)) := by
    calc
      _ ≤ Real.exp (t ^ C) * Real.exp (t ^ C) :=
        mul_le_mul (hl.trans (Real.exp_le_exp.mpr hpT))
          (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift C))
          (by positivity) (by positivity)
      _ = Real.exp (2 * t ^ C) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ t ^ C)]
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ (l : ℝ) * Real.exp ((p + C) ^ C) by positivity)).le
  have hone : 1 ≤ Real.exp (t ^ (C + 1)) := Real.one_le_exp (by positivity)
  have hcount : ((2 * ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ + 1 : ℕ) : ℝ) ≤
      Real.exp (t ^ (C + 2)) := by
    have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc
      _ ≤ 5 * Real.exp (t ^ (C + 1)) := by push_cast; linarith
      _ ≤ Real.exp 4 * Real.exp (t ^ (C + 1)) :=
        mul_le_mul_of_nonneg_right hfive (by positivity)
      _ = Real.exp (4 + t ^ (C + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show C + 2 = (C + 1) + 1 by omega, pow_succ t (C + 1)]
        have hpow : 1 ≤ t ^ (C + 1) := one_le_pow₀ ht1
        nlinarith [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ t ^ (C + 1))]
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (t ^ (C + 2))) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount d
    _ = Real.exp ((d : ℝ) * t ^ (C + 2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t ^ (C + 3)) := by
      apply Real.exp_le_exp.mpr
      rw [show C + 3 = (C + 2) + 1 by omega, pow_succ' t (C + 2)]
      exact mul_le_mul_of_nonneg_right (hd.trans hpt) (by positivity)
    _ ≤ Real.exp (t ^ (C + 5)) := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht1 (by omega))
    _ = _ := by simp [t]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem metricPartition_constant_le_exp (n : ℕ) (r : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp p) (hr : 1 / (r : ℝ) ≤ Real.exp p) :
    (((2 * n + 1 : ℝ≥0) / r : ℝ≥0) : ℝ) ≤ Real.exp (2 * p + 2) := by
  have hnum : 2 * (n : ℝ) + 1 ≤ 3 * Real.exp p := by
    linarith [Real.one_le_exp_iff.mpr hp]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  change (2 * (n : ℝ) + 1) / r ≤ _
  calc
    _ = (2 * (n : ℝ) + 1) * (1 / r) := by ring
    _ ≤ (3 * Real.exp p) * Real.exp p :=
      mul_le_mul hnum hr (by positivity) (by positivity)
    _ = 3 * Real.exp (2 * p) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 2 * Real.exp (2 * p) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

noncomputable def polynomialDegreeGap (k d : ℕ) : Submodule ℚ (MvPolynomial σ ℚ) :=
  MvPolynomial.restrictSupport ℚ {α | Finsupp.weight (fun _ => 1) α + k ≤ d}

theorem polynomialDegreeGap_monomial (α : σ →₀ ℕ) (c : ℚ) :
    monomial α c ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) :=
  (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

theorem polynomialDegreeGap_mul {i j d e : ℕ} {p q : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap i d) (hq : q ∈ polynomialDegreeGap j e) :
    p * q ∈ polynomialDegreeGap (i + j) (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  have hb := hp hβ
  have hc := hq hγ
  change Finsupp.weight (fun _ : σ => 1) β + i ≤ d at hb
  change Finsupp.weight (fun _ : σ => 1) γ + j ≤ e at hc
  change Finsupp.weight (fun _ : σ => 1) (β + γ) + (i + j) ≤ d + e
  rw [map_add]
  omega

theorem polynomialDegreeGap_pderiv {k d : ℕ} {p : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap k d) (i : σ) :
    MvPolynomial.pderiv i p ∈ polynomialDegreeGap (k + 1) d := by
  classical
  intro α hα
  change α ∈ (MvPolynomial.pderiv i p).support at hα
  have hn : p.coeff (α + Finsupp.single i 1) ≠ 0 := by
    intro hz
    have hc : (MvPolynomial.pderiv i p).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul] at hc
    exact hc rfl
  have hh := hp (MvPolynomial.mem_support_iff.mpr hn)
  change Finsupp.weight (fun _ : σ => 1) (α + Finsupp.single i 1) + k ≤ d at hh
  simp only [map_add, Finsupp.weight_single, one_smul] at hh
  change Finsupp.weight (fun _ : σ => 1) α + (k + 1) ≤ d
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialCongruence
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem integer_polynomial_sub_dvd {σ : Type*} (P : MvPolynomial σ ℤ)
    (x y : σ → ℤ) (m : ℤ) (hxy : ∀ i, m ∣ x i - y i) :
    m ∣ eval x P - eval y P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    rw [eval_add, eval_add, add_sub_add_comm]
    exact dvd_add hP hQ
  | mul_X P i hP =>
    rw [eval_mul, eval_mul, eval_X, eval_X]
    have heq : eval x P * x i - eval y P * y i =
        (eval x P - eval y P) * x i + eval y P * (x i - y i) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left hP _) (dvd_mul_of_dvd_right (hxy i) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ConjugationGridBudget
namespace OAI

section

namespace Erdos3

theorem conjugation_grid_allowance_le_exp (K s l D q : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hD : (D : ℝ) ≤ Real.exp ((p + K) ^ K))
    (hq : (q : ℝ) ≤ Real.exp p) :
    ((l * D * q ^ s : ℕ) : ℝ) ≤
      Real.exp ((p + (K + s + 5)) ^ (K + s + 5)) := by
  let J := K + s + 5
  let t := p + J
  have ht : 2 ≤ t := by
    dsimp [t, J]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) s]
  have hp_le : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) J; linarith
  have hs_le : (s : ℝ) + 1 ≤ t := by dsimp [t, J]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hbig : (p + K) ^ K ≤ t ^ (J - 1) := by
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + K) (show p + K ≤ t by
      dsimp [t, J]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]) K).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [J]; omega)
  have hsmall : ((s : ℝ) + 1) * p ≤ t ^ (J - 1) := by
    apply (show ((s : ℝ) + 1) * p ≤ t ^ 2 by
      simpa only [pow_two] using mul_le_mul hs_le hp_le hp (by linarith : 0 ≤ t)).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [J]; omega)
  have hqpow : (q : ℝ) ^ s ≤ Real.exp ((s : ℝ) * p) := by
    simpa only [← Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg q) hq s
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp ((p + K) ^ K) * Real.exp ((s : ℝ) * p) :=
      mul_le_mul (mul_le_mul hl hD (by positivity) (by positivity)) hqpow (by positivity) (by positivity)
    _ = Real.exp ((p + K) ^ K + ((s : ℝ) + 1) * p) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ J) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 2 * t ^ (J - 1) := by linarith
        _ ≤ t * t ^ (J - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [J]; omega)]
    _ = _ := by simp [t, J]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAbsInterval
namespace OAI

section

namespace Erdos3

noncomputable def integerAbsInterval (B : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊B⌋) ⌊B⌋

theorem mem_integerAbsInterval (B : ℝ) (z : ℤ) :
    z ∈ integerAbsInterval B ↔ |(z : ℝ)| ≤ B := by
  rw [integerAbsInterval, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hn : -z ≤ ⌊B⌋ := by omega
    have hn' := Int.le_floor.mp hn
    have hp := Int.le_floor.mp hhi
    push_cast at hn'
    exact ⟨by linarith, hp⟩
  · rintro ⟨hlo, hhi⟩
    have hn : (-z : ℤ) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨by omega, Int.le_floor.mpr hhi⟩

theorem integerAbsInterval_card_le (B : ℝ) (hB : 0 ≤ B) :
    ((integerAbsInterval B).card : ℝ) ≤ 2 * B + 1 := by
  have hf : (0 : ℤ) ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hc : ((integerAbsInterval B).card : ℤ) = 2 * ⌊B⌋ + 1 := by
    rw [integerAbsInterval, Int.card_Icc]
    omega
  have hc' : ((integerAbsInterval B).card : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
    exact_mod_cast hc
  rw [hc']
  linarith [Int.floor_le B]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

def cubeDifferenceSupport (Q : Finset A) : Finset A :=
  (Q ×ˢ Q).image (fun p ↦ p.2 - p.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOverlapCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem weight_large_values_of_sum {ι : Type*} (I : Finset ι) (w a : ι → ℝ)
    {r B : ℝ} (hr : 0 ≤ r) (hB : 0 < B)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hsum : ∑ i ∈ I, w i = 1)
    (ha : ∀ i ∈ I, a i ≤ B) (hmean : r ≤ ∑ i ∈ I, w i * a i) :
    r / (2 * B) ≤ ∑ i ∈ I, w i * (if r / 2 ≤ a i then (1 : ℝ) else 0) := by
  classical
  have hp (i : ι) (hi : i ∈ I) : a i ≤ r / 2 + B * (if r / 2 ≤ a i then (1 : ℝ) else 0) := by
    split_ifs with h
    · simp only [mul_one]
      linarith [ha i hi]
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge h).le
  have hbound := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hp i hi) (hw i hi))
  have he : (∑ i ∈ I, w i * (r / 2 + B * (if r / 2 ≤ a i then (1 : ℝ) else 0))) =
      r / 2 * (∑ i ∈ I, w i) + B * (∑ i ∈ I, w i * (if r / 2 ≤ a i then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hsum, mul_one] at hbound
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

def frozenCosetMap (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (a r : H)
    (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ) : (G ⧸ Γ) → (H ⧸ Λ) :=
  Quotient.map (fun x => a * φ x * r) (fun {x y} hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    have heq : (a * φ x * r)⁻¹ * (a * φ y * r) = r⁻¹ * φ (x⁻¹ * y) * r := by
      rw [map_mul, map_inv]
      group
    rw [heq]
    exact h (x⁻¹ * y) (QuotientGroup.leftRel_apply.mp hxy))

@[simp] theorem frozenCosetMap_mk (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (a r : H)
    (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ) (x : G) :
    frozenCosetMap Γ Λ φ a r h (QuotientGroup.mk x) = QuotientGroup.mk (a * φ x * r) := rfl

open scoped NNReal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open scoped Matrix

section Algebra

variable {ι κ μ δ K : Type*} [Semiring K]

noncomputable def matrixBlockPart (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K) : Matrix ι κ K := by
  classical
  exact fun i j => if r i = c j then A i j else 0

theorem matrixBlockPart_eq (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) : matrixBlockPart r c A = A := by
  classical
  ext i j
  by_cases h : r i = c j
  · simp only [matrixBlockPart, h, ↓reduceIte]
  · simp only [matrixBlockPart, h, ↓reduceIte, hA i j h]

theorem matrixBlockPart_off_block (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K)
    (i : ι) (j : κ) (h : r i ≠ c j) : matrixBlockPart r c A i j = 0 := by
  classical
  simp only [matrixBlockPart, h, ↓reduceIte]

theorem matrix_mul_blockPart [Fintype κ] (r : ι → δ) (c : κ → δ) (d : μ → δ)
    (A : Matrix ι κ K) (B : Matrix κ μ K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) :
    A * matrixBlockPart c d B = matrixBlockPart r d (A * B) := by
  classical
  ext i k
  have hterm (j : κ) :
      A i j * (if c j = d k then B j k else 0) =
        if r i = d k then A i j * B j k else 0 := by
    by_cases hij : r i = c j
    · rw [hij]
      split_ifs <;> simp only [mul_zero]
    · rw [hA i j hij]
      split_ifs <;> simp only [zero_mul]
  simp only [Matrix.mul_apply, matrixBlockPart, hterm]
  by_cases h : r i = d k <;> simp only [h, ↓reduceIte, Finset.sum_const_zero]

theorem matrix_blockPart_mul [Fintype κ] (r : ι → δ) (c : κ → δ) (d : μ → δ)
    (A : Matrix ι κ K) (B : Matrix κ μ K)
    (hB : ∀ j k, c j ≠ d k → B j k = 0) :
    matrixBlockPart r c A * B = matrixBlockPart r d (A * B) := by
  classical
  ext i k
  have hterm (j : κ) :
      (if r i = c j then A i j else 0) * B j k =
        if r i = d k then A i j * B j k else 0 := by
    by_cases hjk : c j = d k
    · rw [hjk]
      split_ifs <;> simp only [zero_mul]
    · rw [hB j k hjk]
      split_ifs <;> simp only [mul_zero]
  simp only [Matrix.mul_apply, matrixBlockPart, hterm]
  by_cases h : r i = d k <;> simp only [h, ↓reduceIte, Finset.sum_const_zero]

theorem matrixBlockPart_image_section [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K) (S : Matrix κ ι K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) (hS : A * S * A = A) :
    A * matrixBlockPart c r S * A = A := by
  rw [matrix_mul_blockPart r c r A S hA, matrix_blockPart_mul r r c (A * S) A hA,
    hS, matrixBlockPart_eq r c A hA]

end Algebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

theorem weighted_matrix_mulVec_bound {ι κ δ : Type*} [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℝ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0)
    (H : ℝ≥0) (hA : ∀ i j, |A i j| ≤ H)
    (W : δ → ℝ) (hW : ∀ d, 0 < W d) {M : ℝ} (hM : 0 ≤ M)
    (x : κ → ℝ) (hx : ∀ j, |x j| ≤ M / W (c j)) (i : ι) :
    |(A *ᵥ x) i| ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * M / W (r i) := by
  classical
  have hdiv : 0 ≤ M / W (r i) := div_nonneg hM (hW _).le
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, (H : ℝ) * (M / W (r i)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : r i = c j
      · rw [abs_mul]
        exact mul_le_mul (hA i j) (by simpa only [h] using hx j) (abs_nonneg _) H.coe_nonneg
      · rw [hblock i j h, zero_mul, abs_zero]
        exact mul_nonneg H.coe_nonneg hdiv
    _ = (Fintype.card κ : ℝ) * H * (M / W (r i)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * (M / W (r i)) := by
      gcongr <;> linarith
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RescaledLieBasis
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℝ L]

noncomputable def inverseScaledBasis (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) : Basis ι ℝ L :=
  e.unitsSMul (fun i => (Units.mk0 (d i) (hd i).ne')⁻¹)

theorem inverseScaledBasis_apply (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (i : ι) :
    inverseScaledBasis e d hd i = (d i)⁻¹ • e i := by
  simp only [inverseScaledBasis, Basis.unitsSMul_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0]

theorem inverseScaledBasis_repr (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (x : L) (i : ι) :
    (inverseScaledBasis e d hd).repr x i = d i * e.repr x i := by
  simp only [inverseScaledBasis, Basis.repr_unitsSMul, inv_inv,
    Units.smul_def, Units.val_mk0, smul_eq_mul]

theorem inverseScaledBasis_bracket (e : Basis ι ℝ L) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hcompat : ∀ i j k, e.repr ⁅e i, e j⁆ k ≠ 0 → d k = d i * d j)
    (i j k : ι) :
    (inverseScaledBasis e d hd).repr
      ⁅inverseScaledBasis e d hd i, inverseScaledBasis e d hd j⁆ k =
        e.repr ⁅e i, e j⁆ k := by
  rw [inverseScaledBasis_repr, inverseScaledBasis_apply, inverseScaledBasis_apply]
  simp only [smul_lie, lie_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : e.repr ⁅e i, e j⁆ k = 0
  · simp only [h, mul_zero]
  · rw [hcompat i j k h]
    field_simp [(hd i).ne', (hd j).ne']

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ConjugationCoordinates
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

def conjugationInput {ι : Type*} (a b : ι → ℚ) : Fin 3 × ι → ℚ :=
  fun ji => ![a ji.2, b ji.2, -a ji.2] ji.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem symbol_dimension_bound_le_power (s d m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) :
    ((d * (s + 1) * (m + 1) ^ s : ℕ) : ℝ) ≤ (p + (s + 2)) ^ (s + 2) := by
  push_cast
  have ht : 0 ≤ p + ((s : ℝ) + 2) := by positivity
  calc
    (d : ℝ) * ((s : ℝ) + 1) * ((m : ℝ) + 1) ^ s ≤
        (p + ((s : ℝ) + 2)) * (p + ((s : ℝ) + 2)) * (p + ((s : ℝ) + 2)) ^ s := by
      apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (by linarith) s) (by positivity)
        (mul_nonneg ht ht)
      exact mul_le_mul (by linarith) (by linarith) (by positivity) ht
    _ = (p + ((s : ℝ) + 2)) ^ (s + 2) := by ring

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_abs_le_of_exceptional_set {X : Type*} [Fintype X] [Nonempty X]
    (E : Finset X) (f : X → ℝ) {M ε : ℝ} (hε : 0 ≤ ε)
    (hcap : ∀ x, |f x| ≤ M) (hgood : ∀ x, x ∉ E → |f x| ≤ ε) :
    (𝔼 x, |f x|) ≤ ε + M * (E.card : ℝ) / Fintype.card X := by
  classical
  have hbound (x : X) : |f x| ≤ ε + if x ∈ E then M else 0 := by
    by_cases hx : x ∈ E
    · simp only [hx, ↓reduceIte]
      exact (hcap x).trans (le_add_of_nonneg_left hε)
    · simpa only [hx, ↓reduceIte, add_zero] using hgood x hx
  calc
    _ ≤ (𝔼 x : X, (ε + if x ∈ E then M else 0)) := Finset.expect_le_expect (fun x _ => hbound x)
    _ = ε + M * (E.card : ℝ) / Fintype.card X := by
      rw [Finset.expect_add_distrib, Fintype.expect_const]
      congr 1
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHFiniteAtlas
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem shifted_center_power_bound (A B : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + A) + B) ^ B ≤ (p + (A + B + 2 : ℕ)) ^ (A + B + 2) := by
  have hbase : (p + A) + B ≤ p + (A + B + 2 : ℕ) := by push_cast; linarith
  apply (pow_le_pow_left₀ (by positivity) hbase B).trans
  exact pow_le_pow_right₀
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) A, Nat.cast_nonneg (α := ℝ) B]) (by omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

noncomputable def boundedRationalCandidates (H : ℕ) : Finset ℚ := by
  classical
  exact ((Finset.Icc (-(H : ℤ)) H) ×ˢ Finset.range (H + 1)).image
    (fun z : ℤ × ℕ => (z.1 : ℚ) / z.2)

theorem boundedRationalCandidates_card (H : ℕ) :
    (boundedRationalCandidates H).card ≤ (2 * H + 1) * (H + 1) := by
  classical
  have hcard : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    omega
  exact Finset.card_image_le.trans (by rw [Finset.card_product, hcard, Finset.card_range])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s : ℕ}

variable [Fintype ι]

theorem card_squareBasis_index_le (w : ι → ℕ) :
    Fintype.card (ι ⊕ {i // 2 ≤ w i}) ≤ 2 * Fintype.card ι := by
  rw [Fintype.card_sum]
  have h := Fintype.card_subtype_le (fun i => 2 ≤ w i)
  omega

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CompatibleReducedFastReset
namespace OAI

section

namespace Erdos3

def reducedResetParameter (a : ℕ) (p : ℝ) : ℝ :=
  ((p + 2) ^ 10 + 2) ^ 36 + (p + 2) ^ a + p + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem complex_prod_unit_interval {I : Type*} [Fintype I] (a : I → ℂ)
    (ha : ∀ i, (a i).im = 0 ∧ 0 ≤ (a i).re ∧ (a i).re ≤ 1) :
    (∏ i, a i).im = 0 ∧ 0 ≤ (∏ i, a i).re ∧ (∏ i, a i).re ≤ 1 := by
  have he (i : I) : a i = ((a i).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (ha i).1
  have hprod : (∏ i, a i) = ((∏ i, (a i).re : ℝ) : ℂ) := by
    calc
      _ = ∏ i, ((a i).re : ℂ) := Finset.prod_congr rfl (fun i _ => he i)
      _ = _ := by rw [Complex.ofReal_prod]
  rw [hprod]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact ⟨Finset.prod_nonneg (fun i _ => (ha i).2.1),
    Finset.prod_le_one (fun i _ => (ha i).2.1) (fun i _ => (ha i).2.2)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FrozenCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem frozen_correlation_precision_error (P D : ℝ) (hD : 0 ≤ D)
    {N : ℕ} (hN : 0 < N) (hlarge : Real.exp (D + 2 * P + 40) ≤ N) :
    Real.exp D * Real.exp (-(D + 2 * P + 40)) +
      12 * Real.exp (-(D + 2 * P + 40)) + 6 / N ≤ Real.exp (-(2 * P)) / 2 := by
  let ε := Real.exp (-(2 * P) - 40)
  have he : 0 < ε := Real.exp_pos _
  have hprod : Real.exp D * Real.exp (-(D + 2 * P + 40)) = ε := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrho : Real.exp (-(D + 2 * P + 40)) ≤ ε := by
    apply Real.exp_le_exp.mpr
    linarith
  have hinv : 1 / (N : ℝ) ≤ Real.exp (-(D + 2 * P + 40)) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    have h := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (-(D + 2 * P + 40))).le
    simpa only [← Real.exp_add, neg_add_cancel, Real.exp_zero] using h
  have h6 : 6 / (N : ℝ) ≤ 6 * Real.exp (-(D + 2 * P + 40)) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 6)
  have h38 : (38 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
  have hexp : Real.exp (-(2 * P)) = Real.exp 40 * ε := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hprod, hexp]
  nlinarith [mul_le_mul_of_nonneg_right h38 he.le]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix BigOperators

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (e : Basis κ ℚ V)

omit [Fintype κ] in
theorem real_basis_coordinates_transfer (x : ℝ ⊗[ℚ] V) :
    (fun i => (e.baseChange ℝ).repr x i) =
      (fun i j => (e.repr (b j) i : ℝ)) *ᵥ (fun j => (b.baseChange ℝ).repr x j) := by
  classical
  funext i
  conv_lhs => rw [← (b.baseChange ℝ).sum_repr x]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  change (∑ j, (b.baseChange ℝ).repr x j * (e.baseChange ℝ).repr ((b.baseChange ℝ) j) i) = _
  have he (j : ι) : (e.baseChange ℝ).repr ((b.baseChange ℝ) j) i = (e.repr (b j) i : ℝ) := by
    rw [Basis.baseChange_apply, Basis.baseChange_repr_tmul]
    simp
  simp only [he, Matrix.mulVec, dotProduct, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
namespace OAI

section

namespace Erdos3

open Module

theorem rational_height_count_le_cube (H : ℕ) : (2 * H + 1) * (H + 1) ≤ (H + 1) ^ 3 := by
  have h : 2 * H + 1 ≤ (H + 1) ^ 2 := by nlinarith
  calc
    _ ≤ (H + 1) ^ 2 * (H + 1) := Nat.mul_le_mul_right _ h
    _ = _ := by ring

theorem rational_height_count_exp_bound (H N : ℕ) {A : ℝ}
    (hA : 0 ≤ A) (hH : (H : ℝ) ≤ Real.exp A) :
    ((((2 * H + 1) * (H + 1)) ^ N : ℕ) : ℝ) ≤ Real.exp (3 * N * (A + 1)) := by
  have h1 : 1 ≤ Real.exp A := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hH1 : (H : ℝ) + 1 ≤ Real.exp (A + 1) := by
    calc
      _ ≤ Real.exp A + Real.exp A := add_le_add hH h1
      _ = 2 * Real.exp A := by ring
      _ ≤ Real.exp 1 * Real.exp A := mul_le_mul_of_nonneg_right htwo (Real.exp_pos A).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcount : (((2 * H + 1) * (H + 1) : ℕ) : ℝ) ≤ Real.exp (3 * (A + 1)) := by
    calc
      _ ≤ ((H + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast rational_height_count_le_cube H
      _ ≤ Real.exp (A + 1) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using hH1
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  rw [Nat.cast_pow]
  calc
    _ ≤ Real.exp (3 * (A + 1)) ^ N := pow_le_pow_left₀ (by positivity) hcount N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SynchronizedCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem exp_repeated_add_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.exp p + Real.exp p + Real.exp q ≤ Real.exp (p + q + 2) := by
  have hpq : Real.exp p ≤ Real.exp (p + q) := Real.exp_le_exp.mpr (le_add_of_nonneg_right hq)
  have hqp : Real.exp q ≤ Real.exp (p + q) := Real.exp_le_exp.mpr (le_add_of_nonneg_left hp)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ Real.exp (p + q) + Real.exp (p + q) + Real.exp (p + q) := add_le_add (add_le_add hpq hpq) hqp
    _ = 3 * Real.exp (p + q) := by ring
    _ ≤ Real.exp 2 * Real.exp (p + q) := mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_sub_positive_sum_le {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (t : ℂ) (error : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (herr : ∀ i, 0 < w i → ‖t - c i‖ ≤ error) :
    ‖t - ∑ i, (w i : ℂ) * c i‖ ≤ error := by
  have hsumC : (∑ i, (w i : ℂ)) = 1 := by exact_mod_cast hsum
  have hid : t - ∑ i, (w i : ℂ) * c i = ∑ i, (w i : ℂ) * (t - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumC, one_mul]
  rw [hid]
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * (t - c i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * error := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      rcases (hw i).eq_or_lt with hi | hi
      · rw [← hi, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (herr i hi) (hw i)
    _ = error := by rw [← Finset.sum_mul, hsum, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_positive_partition_sum_le_one {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖∑ i, (w i : ℂ) * c i‖ ≤ 1 := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * c i‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_of_le_one_right (hw i) (hc i)
    _ = 1 := hsum

theorem complex_partition_approximation_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w : I → X → ℝ) (c : I → X → ℂ) (T : X → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ 1)
    (hgood : ∀ i x, x ∉ E → 0 < w i x → ‖T x - c i x‖ ≤ ε) :
    (𝔼 x, ‖T x - ∑ i, (w i x : ℂ) * c i x‖) ≤
      ε + 2 * (E.card : ℝ) / Fintype.card X := by
  have hcap (x : X) : ‖T x - ∑ i, (w i x : ℂ) * c i x‖ ≤ 2 := by
    have hb := norm_positive_partition_sum_le_one (fun i => w i x) (fun i => c i x)
      (fun i => hw i x) (hsum x) (fun i => hc i x)
    exact (norm_sub_le _ _).trans (by linarith [hT x])
  have h := expect_abs_le_of_exceptional_set E
    (fun x => ‖T x - ∑ i, (w i x : ℂ) * c i x‖) hε
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hcap x)
    (fun x hx => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact norm_sub_positive_sum_le (fun i => w i x) (fun i => c i x) (T x) ε
        (fun i => hw i x) (hsum x) (fun i => hgood i x hx))
  simpa only [abs_of_nonneg (norm_nonneg _)] using h

theorem norm_correlation_sub_le_mean {X : Type*} [Fintype X]
    (f u v : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(𝔼 x, f x * star (u x)) - (𝔼 x, f x * star (v x))‖ ≤
      𝔼 x, ‖u x - v x‖ := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro x _
  rw [← mul_sub, ← star_sub, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (hf x)

theorem exists_correlating_summand_of_mean {X I : Type*} [Fintype X] [Fintype I]
    (f u : X → ℂ) (v : I → X → ℂ) {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : 0 < M) (hcard : (Fintype.card I : ℝ) ≤ M)
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (herr : (𝔼 x, ‖u x - ∑ i, v i x‖) ≤ ρ / 2)
    (hcorr : ρ ≤ ‖𝔼 x, f x * star (u x)‖) :
    ∃ i, ρ / (2 * M) ≤ ‖𝔼 x, f x * star (v i x)‖ := by
  have he := (norm_correlation_sub_le_mean f u (fun x => ∑ i, v i x) hf).trans herr
  have hsum : ρ / 2 ≤ ‖∑ i, 𝔼 x, f x * star (v i x)‖ := by
    have ht := norm_le_norm_add_norm_sub
      (𝔼 x, f x * star (∑ i, v i x)) (𝔼 x, f x * star (u x))
    have hm : (𝔼 x, f x * star (∑ i, v i x)) = ∑ i, 𝔼 x, f x * star (v i x) := by
      simp only [star_sum, Finset.mul_sum, Finset.expect_sum_comm]
    rw [norm_sub_rev] at ht
    rw [hm] at he ht
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun _ : I => (1 : ℂ))
    (fun i => 𝔼 x, f x * star (v i x)) (by linarith : 0 < ρ / 2) hM
    (by simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcard)
    (by simpa only [one_mul] using hsum)
  exact ⟨i, by simpa only [div_div] using hi⟩

theorem mean_error_mul_bounded {X : Type*} [Fintype X]
    (u v b : X → ℂ) {B ε : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖b x‖ ≤ B) (he : (𝔼 x, ‖u x - v x‖) ≤ ε) :
    (𝔼 x, ‖u x * b x - v x * b x‖) ≤ B * ε := by
  calc
    _ ≤ 𝔼 x, B * ‖u x - v x‖ := by
      apply Finset.expect_le_expect
      intro x _
      rw [← sub_mul, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = B * (𝔼 x, ‖u x - v x‖) := (Finset.mul_expect _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left he hB

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
namespace OAI

section

namespace Erdos3

open Module

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  (e : Basis ι ℚ L) (S : Finset α) (hS : S.Nonempty) (K : α → LieSubalgebra ℚ L)

theorem common_subalgebra_cost_le_budget (m d : ℕ) {A p : ℝ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hA : 0 ≤ A) (hAp : A ≤ p) :
    3 * (m : ℝ) * d * (A + 2) ≤ (p + 2) ^ 5 := by
  have hm' : (m : ℝ) ≤ p + 2 := by linarith
  have hd' : (d : ℝ) ≤ p + 2 := by linarith
  calc
    _ ≤ 3 * (p + 2) * (p + 2) * (p + 2) := by gcongr
    _ = 3 * (p + 2) ^ 3 := by ring
    _ ≤ (p + 2) ^ 2 * (p + 2) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = (p + 2) ^ 5 := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

def differenceInput {ι : Type*} (a b : ι → ℚ) : Fin 3 × ι → ℚ :=
  fun ji => ![-a ji.2, b ji.2, 0] ji.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem polynomial_period_cost_le_exp (K r s l D Q : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hD : (D : ℝ) ≤ Real.exp ((p + K) ^ K))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3))) :
    (((l * D * Q ^ s) * Q : ℕ) : ℝ) ≤
      Real.exp ((p + (K + r + s + 10)) ^ (K + r + s + 10)) := by
  let C := K + r + s + 10
  let t := p + C
  have ht : 3 ≤ t := by
    dsimp [t, C]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) s]
  have hC : 1 ≤ C := by dsimp [C]; omega
  have hpT : p ≤ t ^ (C - 1) := by
    apply (show p ≤ t by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) C; linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) (show 1 ≤ C - 1 by dsimp [C]; omega)
  have hDT : (p + K) ^ K ≤ t ^ (C - 1) := by
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + K) (show p + K ≤ t by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) s]) K).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hQT : ((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3) ≤ t ^ (C - 1) := by
    have hs : (s : ℝ) + 1 ≤ t := by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) r]
    have hr : p + (r + 3) ≤ t := by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) s]
    calc
      _ ≤ t * t ^ (r + 3) := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hr _) (by positivity) (by linarith)
      _ = t ^ (r + 4) := (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hQpow : (Q : ℝ) ^ (s + 1) ≤ Real.exp (((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ (s + 1)
  push_cast
  calc
    _ = (l : ℝ) * D * (Q : ℝ) ^ (s + 1) := by rw [pow_succ]; ring
    _ ≤ Real.exp p * Real.exp ((p + K) ^ K) *
        Real.exp (((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) :=
      mul_le_mul (mul_le_mul hl hD (by positivity) (by positivity)) hQpow (by positivity) (by positivity)
    _ = Real.exp (p + (p + K) ^ K + ((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (t ^ C) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 3 * t ^ (C - 1) := by linarith
        _ ≤ t * t ^ (C - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel hC]
    _ = _ := by simp [t, C]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitIntervalBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def scalarUnitEquiv (A : Type*) : A ≃ (Unit → A) where
  toFun a _ := a
  invFun f := f ()
  left_inv _ := rfl
  right_inv f := by
    funext u
    cases u
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest
namespace OAI

section

namespace Erdos3

def rankAdaptedNiltestBase (p : ℝ) : ℝ := (p + 3) ^ 11 + p + 2

def rankAdaptedNiltestBudget (p : ℝ) : ℝ :=
  rankAdaptedNiltestBase p + (rankAdaptedNiltestBase p + 2) ^ 2

theorem le_rankAdaptedNiltestBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ rankAdaptedNiltestBudget p := by
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  unfold rankAdaptedNiltestBudget rankAdaptedNiltestBase
  nlinarith [sq_nonneg ((p + 3) ^ 11 + p + 2 + 2)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxOverlapSize
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem side_gt_of_prod_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : ι → ℝ) (hS : ∀ i, 0 ≤ S i) (hT : ∀ i, 0 < T i)
    (hST : ∀ i, S i ≤ T i) {δ : ℝ}
    (hprod : δ * ∏ i, T i < ∏ i, S i) (i : ι) : δ * T i < S i := by
  have hrest : (∏ j ∈ Finset.univ.erase i, S j) ≤ ∏ j ∈ Finset.univ.erase i, T j :=
    Finset.prod_le_prod (fun j _ => hS j) (fun j _ => hST j)
  have hrestpos : 0 < ∏ j ∈ Finset.univ.erase i, T j := Finset.prod_pos (fun j _ => hT j)
  have hbound : (∏ j, S j) ≤ S i * ∏ j ∈ Finset.univ.erase i, T j := by
    rw [← Finset.mul_prod_erase Finset.univ S (Finset.mem_univ i)]
    exact mul_le_mul_of_nonneg_left hrest (hS i)
  have hlt := hprod.trans_le hbound
  rw [← Finset.mul_prod_erase Finset.univ T (Finset.mem_univ i), ← mul_assoc] at hlt
  exact (mul_lt_mul_iff_left₀ hrestpos).mp hlt

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCorrelatedFactorFamily
namespace OAI

section

namespace Erdos3

theorem right_lattice_factor_mk_eq {G : Type*} [Group G] (Γ : Subgroup G)
    (a x u δ : G) (hδ : δ ∈ Γ) :
    (QuotientGroup.mk (a * x * (u * δ)) : G ⧸ Γ) = QuotientGroup.mk (a * x * u) := by
  apply QuotientGroup.eq.mpr
  convert Γ.inv_mem hδ using 1
  group

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

noncomputable def properAffineVolumeLog (P : ℝ) (n : ℕ) : ℝ :=
  2 + 16 * (44 + 6 * max P 0 + 94 * n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedRootTensorExponent (s : ℕ) : ℕ := (s + 3) ^ (s + 2)

end Erdos3

end

end OAI
end


