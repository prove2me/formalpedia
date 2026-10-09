-- Prove2me | Definitions.Def_OAIErdos3B049
-- name    : OAIErdos3B049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T06:31:26.463842+00:00
-- url     : https://prove2.me/theorems/d436d4da-32be-46bb-8aa2-72b134d95966
-- title:
--   OpenAI Erdős-3 split, definitions bundle 50 of 132
-- statement:
--   Definitions bundle 50 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B048`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 50 available.
--
--   Modules: `OAI.Erdos3.NativeIntegerExpansion.constOne`, `OAI.Erdos3.NativeIntegerExpansion.exists_fin_prod_budget`, `OAI.Erdos3.NativeIntegerExpansion.exists_halving_expansion`, `OAI.Erdos3.NativeIntegerExpansion.exists_mul_budget`, `OAI.Erdos3.NativeIntegerExpansion.mul`, `OAI.Erdos3.NativeIntegerExpansion.ofProduct`, `OAI.Erdos3.NativeIntegerExpansion.tensorCrossProduct`, `OAI.Erdos3.NativeIntegerVectorEquivalence.exists_tensor_budget`, `OAI.Erdos3.NativeIntegerVectorEquivalence.exists_tensor_power_budget`, `OAI.Erdos3.NativeIntegerVectorEquivalence.exists_trans_budget`, `OAI.Erdos3.NativeIntegerVectorEquivalence.tensor`, `OAI.Erdos3.NativeIntegerVectorEquivalence.trans`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_of_unit_data`, `OAI.Erdos3.NativeMultidegreeNilcharacter.tensorPower`, `OAI.Erdos3.NativeMultidegreeNilcharacter.tensorPower_eval`, `OAI.Erdos3.NativeMultidegreeNilcharacter.tensorPower_tensor_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.AdaptedMapGeometryData.ordinaryResetGeometry`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData.eval`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData.eval_permute`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData.noConfusion`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonVerticalProduct`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.comparisonVerticalProduct_norm`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_symmetric_squarefree_unit`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.reindex`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.tensorPower`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_prescribed_scalar`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_prescribed_unit`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_unit_vertical_completion`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_unit_vertical_family`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_vertical_translate_frame`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_invariant_unit`, `OAI.Erdos3.RationalTorus.residueNiltest_eval`, `OAI.Erdos3.VectorPolynomial.CoveredJetChartSource`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetDensity`, `OAI.Erdos3.VectorPolynomial.coveredJetChart`, `OAI.Erdos3.VectorPolynomial.coveredJetChartSource_borel`, `OAI.Erdos3.VectorPolynomial.coveredJetSourceRegion`, `OAI.Erdos3.VectorPolynomial.coveredJetTargetRegion`, `OAI.Erdos3.arbitraryStep_prescribed_product_cast_le`, `OAI.Erdos3.arbitraryStep_prescribed_product_dvd`, `OAI.Erdos3.arbitraryStep_prescribed_product_exp_le`, `OAI.Erdos3.arbitraryStep_prescribed_product_le`, `OAI.Erdos3.badPrimeModulusEvent`, `OAI.Erdos3.card_product_le_exp_two`, `OAI.Erdos3.comparisonDescentBudget`, `OAI.Erdos3.comparisonEquivalenceBudget`, `OAI.Erdos3.comparisonEquivalenceBudget_bounds`, `OAI.Erdos3.comparisonProductCost`, `OAI.Erdos3.comparisonProductLip`, `OAI.Erdos3.comparisonProductLip_le_exp`, `OAI.Erdos3.complex_tensor_cross_product`, `OAI.Erdos3.exists_bounded_normalization_left_lipschitz`, `OAI.Erdos3.exists_comparisonEquivalence_cost`, `OAI.Erdos3.exists_complex_unit_completion`, `OAI.Erdos3.exists_coordinate_residue_expansion`, `OAI.Erdos3.exists_normalizedSquareComplexityBudget_bound`, `OAI.Erdos3.exists_pairParityIndicator_expansion`, `OAI.Erdos3.exists_positive_partition_integer_expansion`, `OAI.Erdos3.exists_positive_weighted_integer_expansion`, `OAI.Erdos3.largestTestedBadDepth`, `OAI.Erdos3.niltest_log_bound_of_exp`, `OAI.Erdos3.normalizedSquareComplexityBudget`, `OAI.Erdos3.normalizedSquareLeftBudget`, `OAI.Erdos3.normalizedSquareLeftBudget_nonneg`, `OAI.Erdos3.normalizedSquareObservableBudget`, `OAI.Erdos3.normalizedSquareObservableBudget_nonneg`, `OAI.Erdos3.normalizedSquareProjectionBudget`, `OAI.Erdos3.normalizedSquareProjectionBudget_nonneg`, `OAI.Erdos3.normalizedSquareReconstructionBudget`, `OAI.Erdos3.normalizedSquareReconstructionBudget_nonneg`, `OAI.Erdos3.pairParityIndicator`, `OAI.Erdos3.pairParityIndicator_product`, `OAI.Erdos3.physicalBadProductAccuracy`, `OAI.Erdos3.physicalBadProductGap`, `OAI.Erdos3.prescribedDeepBad`, `OAI.Erdos3.product_flatten`, `OAI.Erdos3.quantitativeBadPrimeRadius`, `OAI.Erdos3.quantitativeBadPrimeRadius_bounds`, `OAI.Erdos3.quantitativeBadPrimeRadius_witness_budget`, `OAI.Erdos3.rootTensorEquiv`, `OAI.Erdos3.rootTensorIndex`, `OAI.Erdos3.selectedResidueTiltedFiniteLaw`, `OAI.Erdos3.selectedResidueTiltedFiniteLaw_mean`, `OAI.Erdos3.selected_factorization_product_dvd`, `OAI.Erdos3.smallPrimePowerCorrection`, `OAI.Erdos3.sqrt_complement_lipschitz`, `OAI.Erdos3.squareObservableLipschitz_le_exp`, `OAI.Erdos3.tensorIndexEquiv`, `OAI.Erdos3.tensorPowerBudget`, `OAI.Erdos3.tensorPowerBudget_bounds`, `OAI.Erdos3.tensorVector`, `OAI.Erdos3.tensorVector_unit`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B042

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LargestBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def badPrimeModulusEvent {Ω : Type*} (S : Finset ℕ) (A : ℕ → ℕ) (Qs : ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (d : ℕ) (x : Ω) : Prop :=
  (∀ p ∈ d.primeFactors, p ∈ S ∧ 0 < d.factorization p ∧
    d.factorization p ≤ A p ∧ Qs ≤ p ^ d.factorization p) ∧
  (∀ p ∈ d.primeFactors, bad p (d.factorization p) x)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def largestTestedBadDepth {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) : ℕ :=
  ((Finset.Icc 1 (A p)).filter (fun a => bad p a x)).sup id

noncomputable def smallPrimePowerCorrection (Qs : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range Qs).filter Nat.Prime, p ^ Nat.log p (Qs - 1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

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

noncomputable def quantitativeBadPrimeRadius (E : ℝ) : ℕ := ⌈4 * Real.exp E⌉₊ + 1

theorem quantitativeBadPrimeRadius_bounds {E : ℝ} (hE : 0 ≤ E) :
    0 < quantitativeBadPrimeRadius E ∧
      (quantitativeBadPrimeRadius E : ℝ) ≤ Real.exp (E + 3) ∧
      2 / (9 * (quantitativeBadPrimeRadius E : ℝ) ^ 9) ≤ Real.exp (-E) / 2 := by
  let R := quantitativeBadPrimeRadius E
  have hR : 0 < R := Nat.succ_pos _
  have hexp : 1 ≤ Real.exp E := Real.one_le_exp hE
  have hlo : 4 * Real.exp E ≤ (R : ℝ) := by
    have hc := Nat.le_ceil (4 * Real.exp E)
    dsimp [R, quantitativeBadPrimeRadius]
    push_cast
    linarith
  have hhi : (R : ℝ) ≤ 4 * Real.exp E + 2 := by
    have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * Real.exp E)
    dsimp [R, quantitativeBadPrimeRadius]
    push_cast
    linarith
  have hexp3 : (6 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h2 : (4 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    have h3 : (8 : ℝ) ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
    have he : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [he]
    linarith
  have hbudget : (R : ℝ) ≤ Real.exp (E + 3) := by
    rw [Real.exp_add]
    have := mul_le_mul_of_nonneg_left hexp3 (Real.exp_pos E).le
    nlinarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRp : (R : ℝ) ≤ (R : ℝ) ^ 9 := by
    calc
      _ = (R : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hR1 (by omega)
  have hprod : 4 ≤ Real.exp (-E) * (R : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (-E)).le
    have he : Real.exp (-E) * Real.exp E = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have htail : 2 / (9 * (R : ℝ) ^ 9) ≤ Real.exp (-E) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 9 * (R : ℝ) ^ 9)).mpr
    have hh := mul_le_mul_of_nonneg_left hRp (Real.exp_pos (-E)).le
    nlinarith
  exact ⟨hR, hbudget, htail⟩

theorem quantitativeBadPrimeRadius_witness_budget {E V : ℝ}
    (hE : 0 ≤ E) (hV : 0 ≤ V) (Q : ℕ) (hQ : (Q : ℝ) ≤ Real.exp V) :
    let R := quantitativeBadPrimeRadius E
    (max Q (R ^ 2) : ℕ) ≤ Real.exp (V + 2 * E + 6) ∧
    1 / (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤
      Real.exp (V + 3 * E + 8) := by
  dsimp only
  let R := quantitativeBadPrimeRadius E
  have hR := (quantitativeBadPrimeRadius_bounds hE).2.1
  have hR2 : (R : ℝ) ^ 2 ≤ Real.exp (2 * E + 6) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ R) hR 2
    have he : (Real.exp (E + 3)) ^ 2 = Real.exp (2 * E + 6) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    exact hh.trans_eq he
  have hQbig : (Q : ℝ) ≤ Real.exp (V + 2 * E + 6) :=
    hQ.trans (Real.exp_le_exp.mpr (by linarith))
  have hRbig : (R : ℝ) ^ 2 ≤ Real.exp (V + 2 * E + 6) :=
    hR2.trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · rw [Nat.cast_max, Nat.cast_pow]
    exact max_le hQbig hRbig
  · have hne : Real.exp (-E) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hrec : 1 / (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) =
        2 * ((Q : ℝ) + (R : ℝ) ^ 2) * Real.exp E := by
      rw [one_div_div, Real.exp_neg, div_inv_eq_mul]
    rw [hrec]
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [he]
      nlinarith
    calc
      _ ≤ 4 * Real.exp (V + 2 * E + 6) * Real.exp E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos E).le
        linarith
      _ ≤ Real.exp 2 * Real.exp (V + 2 * E + 6) * Real.exp E := by
        gcongr
      _ = Real.exp (V + 3 * E + 8) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def selectedResidueTiltedFiniteLaw {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) :
    FiniteProbabilityWeights (rectangularWeightIndices 0 V 1) :=
  (selectedResidueFiniteLaw modulus G V hV hZ).reweightPositive (fun x => D x.val)
    (fun x => hD0 x.val) (by rw [selectedResidueFiniteLaw_densityMass]; exact hD)

theorem selectedResidueTiltedFiniteLaw_mean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℝ) :
    (selectedResidueTiltedFiniteLaw modulus G V hV hZ D hD0 hD).mean (fun x => f x.val) =
      ∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * f x := by
  rw [selectedResidueTiltedFiniteLaw, FiniteProbabilityWeights.reweightPositive_mean,
    selectedResidueFiniteLaw_densityMass,
    selectedResidueFiniteLaw_mean modulus G V hV hZ (fun x => D x * f x),
    selectedResidueDensityPMF_mean]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def prescribedDeepBad {Ω : Type*} (b : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p a : ℕ) (x : Ω) : Prop := b p < a ∧ bad p a x

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem selected_factorization_product_dvd (S : Finset ℕ) (n : ℕ) :
    (∏ p ∈ S, p ^ n.factorization p) ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  have he : (∏ p ∈ S ∩ n.factorization.support, p ^ n.factorization p) =
      ∏ p ∈ S, p ^ n.factorization p := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hp hnot
    have hzero : n.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun hs => hnot (Finset.mem_inter.mpr ⟨hp, hs⟩)
    simp [hzero]
  rw [← he]
  exact (Finset.prod_dvd_prod_of_subset (S ∩ n.factorization.support)
    n.factorization.support (fun p => p ^ n.factorization p) Finset.inter_subset_right).trans
      (dvd_of_eq (Nat.prod_factorization_pow_eq_self hn))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ArbitraryStepPrescribedBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem arbitraryStep_prescribed_product_dvd (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) (step : ℕ) :
    (∏ p : Pr, p.val ^ padicValNat p.val step) ∣ step := by
  rw [Finset.prod_coe_sort Pr (fun p : ℕ => p ^ padicValNat p step)]
  have hprod : (∏ p ∈ Pr, p ^ padicValNat p step) =
      ∏ p ∈ Pr, p ^ step.factorization p := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_def step (hprime p hp)]
  rw [hprod]
  exact selected_factorization_product_dvd Pr step

theorem arbitraryStep_prescribed_product_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step) :
    (∏ p : Pr, p.val ^ padicValNat p.val step) ≤ step :=
  Nat.le_of_dvd hstep (arbitraryStep_prescribed_product_dvd Pr hprime step)

theorem arbitraryStep_prescribed_product_cast_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step) :
    ((∏ p : Pr, p.val ^ padicValNat p.val step : ℕ) : ℝ) ≤ step := by
  exact_mod_cast arbitraryStep_prescribed_product_le Pr hprime hstep

theorem arbitraryStep_prescribed_product_exp_le (Pr : Finset ℕ)
    (hprime : ∀ p ∈ Pr, p.Prime) {step : ℕ} (hstep : 0 < step)
    {cost : ℝ} (hcost : (step : ℝ) ≤ 2 * Real.exp cost) :
    ((∏ p : Pr, p.val ^ padicValNat p.val step : ℕ) : ℝ) ≤
      Real.exp (cost + 1) := by
  calc
    _ ≤ (step : ℝ) := arbitraryStep_prescribed_product_cast_le Pr hprime hstep
    _ ≤ 2 * Real.exp cost := hcost
    _ ≤ Real.exp 1 * Real.exp cost :=
      mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1)
        (Real.exp_pos cost).le
    _ = Real.exp (cost + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDeckDensityLawCongruence
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def coefficientDeckJetDensity (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) : ℝ :=
  (Fintype.card (∀ j, O j → B j → ZMod d) : ℝ) *
    (((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d)) r).toReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def normalizedSquareProjectionBudget (p : ℝ) : ℝ :=
  (squareGeometryBudget p + p + 4) ^ 2

noncomputable def normalizedSquareLeftBudget (a b : ℕ) (p : ℝ) : ℝ :=
  (p + a + 2 + b) ^ b

noncomputable def normalizedSquareObservableBudget (a b : ℕ) (p : ℝ) : ℝ :=
  2 * p + normalizedSquareProjectionBudget p + normalizedSquareLeftBudget a b p + 1

noncomputable def normalizedSquareReconstructionBudget (a b : ℕ) (p : ℝ) : ℝ :=
  squareGeometryBudget p + 1 + normalizedSquareObservableBudget a b p + 2 * p

noncomputable def normalizedSquareComplexityBudget (a b c : ℕ) (p : ℝ) : ℝ :=
  squareGeometryBudget p + 2 * p + (normalizedSquareReconstructionBudget a b p + c) ^ c + 4

theorem normalizedSquareProjectionBudget_nonneg (p : ℝ) :
    0 ≤ normalizedSquareProjectionBudget p := sq_nonneg _

theorem normalizedSquareLeftBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareLeftBudget a b p := by
  unfold normalizedSquareLeftBudget
  positivity

theorem normalizedSquareObservableBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareObservableBudget a b p := by
  have h1 := normalizedSquareProjectionBudget_nonneg p
  have h2 := normalizedSquareLeftBudget_nonneg a b hp
  unfold normalizedSquareObservableBudget
  linarith

theorem normalizedSquareReconstructionBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareReconstructionBudget a b p := by
  have h1 := squareGeometryBudget_nonneg hp
  have h2 := normalizedSquareObservableBudget_nonneg a b hp
  unfold normalizedSquareReconstructionBudget
  linarith

theorem exists_normalizedSquareComplexityBudget_bound (a b c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → normalizedSquareComplexityBudget a b c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := ((X + 3) ^ 11 + 2 * X + 5) ^ 11
  let U := 2 * X + (Q + X + 4) ^ 2 + (X + Polynomial.C a + 2 + Polynomial.C b) ^ b + 1
  let R := Q + 1 + U + 2 * X
  let P := Q + 2 * X + (R + Polynomial.C c) ^ c + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, R, U, Q, X, Polynomial.eval₂_pow, normalizedSquareComplexityBudget, normalizedSquareReconstructionBudget,
    normalizedSquareObservableBudget, normalizedSquareProjectionBudget,
    normalizedSquareLeftBudget, squareGeometryBudget] using hbound p hp

theorem squareObservableLipschitz_le_exp (A B K J : ℝ≥0) {p q r : ℝ}
    (hr : 0 ≤ r) (hA : (A : ℝ) ≤ Real.exp r) (hB : (B : ℝ) ≤ Real.exp p)
    (hK : (K : ℝ) ≤ Real.exp p) (hJ : (J : ℝ) ≤ Real.exp q) :
    ((B * (K * J) + B * (K * (A * J)) : ℝ≥0) : ℝ) ≤ Real.exp (2 * p + q + r + 1) := by
  have hfirst : (B : ℝ) * (K * J) ≤ Real.exp (2 * p + q) := by
    calc
      _ ≤ Real.exp p * (Real.exp p * Real.exp q) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsecond : (B : ℝ) * (K * (A * J)) ≤ Real.exp (2 * p + q + r) := by
    calc
      _ ≤ Real.exp p * (Real.exp p * (Real.exp r * Real.exp q)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hfirst' := hfirst.trans (Real.exp_le_exp.mpr (by linarith : 2 * p + q ≤ 2 * p + q + r))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  change (B : ℝ) * (K * J) + B * (K * (A * J)) ≤ _
  calc
    _ ≤ 2 * Real.exp (2 * p + q + r) := by linarith
    _ ≤ Real.exp 1 * Real.exp (2 * p + q + r) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem niltest_log_bound_of_exp (x y : ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : (x : ℝ) ≤ Real.exp a) (hy : (y : ℝ) ≤ Real.exp b) :
    Real.log (2 + (x : ℝ) + y) ≤ a + b + 4 := by
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 2 + (x : ℝ) + y)).mpr
  have hx' := hx.trans (Real.exp_le_exp.mpr (by linarith : a ≤ a + b))
  have hy' := hy.trans (Real.exp_le_exp.mpr (by linarith : b ≤ a + b))
  have h1 : 1 ≤ Real.exp (a + b) := Real.one_le_exp (by linarith)
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (a + b) := by linarith
    _ ≤ Real.exp 4 * Real.exp (a + b) := mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_bounded_normalization_left_lipschitz (s a : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ A : ℝ≥0, 0 < A ∧ (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p) ∧
        ∀ ε : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + a) ^ a)) →
          letI := D.metricSpace
          LipschitzWith A (fun x : D.Space => ε • x) := by
  obtain ⟨b, hb, hleft⟩ := exists_uniform_quotient_left_lipschitz_exp_bound s a
  refine ⟨b, hb, ?_⟩
  intro L _ _ d _ _ _ _ D p hp hD
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  let q := p + a + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  obtain ⟨A, hA, hAp, hLip⟩ := hleft (D.basis.baseChange ℝ)
    (lieStructureConstants D.basis) ⌈Real.exp p⌉₊ q
    D.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hq
    (by simpa only [Fintype.card_fin] using hD.1.trans hpq) hH
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  refine ⟨A, hA, hAp, ?_⟩
  intro ε hε
  apply hLip D.realLattice (D.realLattice_closed_discrete).1 ε
  intro i
  apply (hε i).trans (Real.exp_le_exp.mpr _)
  apply pow_le_pow_left₀ (by positivity)
  dsimp [q]
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def comparisonProductLip (c : ℕ) (K L A : ℝ≥0) (p : ℝ) : ℝ≥0 :=
  c * K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩) +
    L * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩

theorem comparisonProductLip_le_exp (c : ℕ) (K L A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hc : (c : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hL : (L : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp p) :
    (comparisonProductLip c K L A p : ℝ) ≤ Real.exp ((p + 3) ^ 2 + 3 * p + 1) := by
  have hleft : (c : ℝ) * K * A ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul hc hK K.coe_nonneg (Real.exp_pos _).le) hA
          A.coe_nonneg (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hright : (L : ℝ) ≤ Real.exp (3 * p) :=
    hL.trans (Real.exp_le_exp.mpr (by linarith))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  change (c : ℝ) * K * (A * Real.exp ((p + 3) ^ 2)) + L * Real.exp ((p + 3) ^ 2) ≤ _
  calc
    _ = ((c : ℝ) * K * A + L) * Real.exp ((p + 3) ^ 2) := by ring
    _ ≤ (2 * Real.exp (3 * p)) * Real.exp ((p + 3) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (Real.exp 1 * Real.exp (3 * p)) * Real.exp ((p + 3) ^ 2) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

noncomputable def comparisonProductCost (p : ℝ) : ℝ := (p + 3) ^ 2 + 3 * p + 5

noncomputable def comparisonDescentBudget (s : ℕ) (p : ℝ) : ℝ :=
  (comparisonProductCost p + RationalFilteredNilmanifold.topInvariantIntegerExponent s) ^
    RationalFilteredNilmanifold.topInvariantIntegerExponent s

end Erdos3

end

section

namespace Erdos3

noncomputable def comparisonEquivalenceBudget (s : ℕ) (p : ℝ) : ℝ :=
  comparisonDescentBudget s p + ((s + 1).factorial + 1 : ℝ) * (p + 1)

theorem comparisonEquivalenceBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    comparisonDescentBudget s p ≤ comparisonEquivalenceBudget s p ∧
    p ≤ comparisonEquivalenceBudget s p ∧
    ((s + 1).factorial : ℝ) * p ≤ comparisonEquivalenceBudget s p := by
  have hdescent : 0 ≤ comparisonDescentBudget s p := by
    dsimp [comparisonDescentBudget, comparisonProductCost]
    positivity
  have hf : 0 ≤ ((s + 1).factorial : ℝ) := Nat.cast_nonneg _
  dsimp [comparisonEquivalenceBudget]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exists_comparisonEquivalence_cost (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → comparisonEquivalenceBudget s p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let a := RationalFilteredNilmanifold.topInvariantIntegerExponent s
  let P := ((X + 3) ^ 2 + 3 * X + 5 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + Polynomial.C ((s + 1).factorial + 1) * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [comparisonEquivalenceBudget, comparisonDescentBudget, comparisonProductCost,
    a, X, P, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeAdaptedOrdinaryResetGeometry
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L QL ML : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing QL] [LieAlgebra ℚ QL] [LieRing ML] [LieAlgebra ℚ ML]
    {s t r d e f : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {Q : RationalFilteredNilmanifold QL t e}
    {Mmark : RationalFilteredNilmanifold ML r f}
    {ψ : L →ₗ⁅ℚ⁆ QL} {φ : QL →ₗ⁅ℚ⁆ ML}
    {pg qg pm qm p0 : ℝ}

namespace AdaptedMapGeometryData

theorem ordinaryResetGeometry
    (geometry : D.AdaptedMapGeometryData Q ψ pg qg)
    (markGeometry : Q.FixedSourceAdaptedMarkGeometryData Mmark geometry.target φ pm qm)
    (hp0 : 0 ≤ p0) (hgeom : qg ≤ p0) (hmark : qm ≤ p0) (hgen : pg ≤ p0) :
    geometry.target.model.GeometryComplexityLE p0 ∧
    markGeometry.target.model.GeometryComplexityLE p0 ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.model.basis.repr (markGeometry.target.basis j) i) ≤ p0) ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.basis.repr (φ (geometry.target.basis j)) i) ≤ p0) ∧
    (∀ i j, rationalLogHeight
      (markGeometry.target.model.basis.repr (φ (geometry.target.model.basis j)) i) ≤ p0) ∧
    (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p0 ∧
    (Fintype.card (Fin (finrank ℚ QL)) : ℝ) ≤ p0 ∧
    (Fintype.card (Fin (finrank ℚ ML)) : ℝ) ≤ p0 := by
  have hsourceGeometry := geometry.target_geometry.mono geometry.target.model hgeom
  have hmarkedGeometry := markGeometry.target_geometry.mono markGeometry.target.model hmark
  refine ⟨hsourceGeometry, hmarkedGeometry, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change rationalLogHeight (markGeometry.target.basis.repr
      (markGeometry.target.basis j) i) ≤ p0
    rw [Basis.repr_self]
    simp only [Finsupp.single_apply]
    split_ifs <;> simpa [rationalLogHeight] using hp0
  · exact fun i j => (markGeometry.entries_logHeight i j).trans hmark
  · exact fun i j => (markGeometry.entries_logHeight i j).trans hmark
  · simpa only [Fintype.card_fin] using geometry.source_dimension.trans hgen
  · simpa only [Fintype.card_fin] using geometry.target_dimension.trans hgen
  · simpa only [Fintype.card_fin] using hmarkedGeometry.1

end AdaptedMapGeometryData
end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def physicalBadProductAccuracy (E Vlog : ℝ) : ℝ :=
  Real.exp (-(Vlog + 3 * E + 16))

noncomputable def physicalBadProductGap (N : ℕ) (E Vlog : ℝ) (Q : ℕ) : ℝ :=
  (2 * (N : ℝ) + 1) * (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) /
    physicalBadProductAccuracy E Vlog

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeVerticalTranslateFrame
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_native_vertical_translate_frame (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ u : Fin n → D.Space → ℂ,
        (∀ i x, ‖u i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (u i)) ∧
        (∀ x, ∃ i, Real.exp (-(p + 1)) ≤ ‖u i x‖) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          u i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * u i x := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  obtain ⟨c, _, hcover⟩ := exists_native_quotient_parameter_cover s
  let X : Polynomial ℕ := Polynomial.X
  let Q := 2 * X + 2 * (X + Polynomial.C a + 2 + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + Q + (Q + Polynomial.C c) ^ c + 1)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let l := normalizedSquareLeftBudget a b p
  let q := 2 * p + 2 * l + 2
  have hl : 0 ≤ l := normalizedSquareLeftBudget_nonneg a b hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have htotal : p + q + (q + c) ^ c + 1 ≤ (p + C) ^ C := by
    simpa [X, Q, q, l, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hcp : 0 ≤ (q + c) ^ c := by positivity
  have hqp : q ≤ (p + C) ^ C := by linarith
  have hcount : (q + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hT.1
  have hrepresentatives : ∀ x : D.Space, ∃ r : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + 1 + a) ^ a)) ∧
      QuotientGroup.mk r = x := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      obtain ⟨r, hr, γ, hγ, hg⟩ :=
        hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
          ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
          (fun i j k => rationalHeightLE_ceil_exp (hT.1.2.2.1 i j k))
          (by linarith)
          (by simpa only [Fintype.card_fin] using hT.1.1.trans (show p ≤ p + 1 by linarith))
          (ceil_exp_le_exp_add_one hp) (hT.1.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
      refine ⟨r, hr, ?_⟩
      change (QuotientGroup.mk r : D.Space) = QuotientGroup.mk g
      rw [hg]
      exact (QuotientGroup.mk_mul_of_mem r (show γ ∈ D.realLattice from hγ)).symm
  choose r hr hrc using hrepresentatives
  have hInv (x : D.Space) : ∀ i,
      |(D.basis.baseChange ℝ).repr (r x)⁻¹.coord i| ≤ Real.exp ((p + 1 + a) ^ a) := by
    intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hr x i
  let ε := Real.exp (-q)
  have hε : 0 < ε := Real.exp_pos _
  have hεinv : 1 / ε ≤ Real.exp q := by
    simp only [ε, Real.exp_neg, one_div, inv_inv, le_refl]
  obtain ⟨n, hn, hnc, centers, hcenters⟩ :=
    hcover D hq (hT.1.mono D hpq) hε hεinv
  let K := T.lipBound * (A * A)
  let u (i : Fin n) (x : D.Space) := T.observable (r y • ((r (centers i))⁻¹ • x))
  have hK : (K : ℝ) ≤ Real.exp (p + 2 * l) := by
    have hTlip : (T.lipBound : ℝ) ≤ Real.exp p := by
      linarith [Niltest.observable_budget hT, T.normBound.coe_nonneg]
    calc
      _ ≤ Real.exp p * (Real.exp l * Real.exp l) := by
        dsimp [K]
        exact mul_le_mul hTlip (mul_le_mul hA hA A.coe_nonneg (Real.exp_nonneg _))
          (mul_nonneg A.coe_nonneg A.coe_nonneg) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have huLip (i : Fin n) : LipschitzWith K (u i) :=
    T.lipschitz.comp ((hLip (r y) (hr y)).comp (hLip ((r (centers i))⁻¹) (hInv _)))
  have hcenter (i : Fin n) : u i (centers i) = T.observable y := by
    change T.observable (r y • ((r (centers i))⁻¹ • centers i)) = T.observable y
    have heq : (r (centers i))⁻¹ • centers i = (QuotientGroup.mk (1 : D.RealGroup) : D.Space) := by
      calc
        _ = (r (centers i))⁻¹ • QuotientGroup.mk (r (centers i)) :=
          congrArg (fun x : D.Space => (r (centers i))⁻¹ • x) (hrc _).symm
        _ = _ := by simp only [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    rw [heq]
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hrc]
  have herror : (K : ℝ) * ε ≤ Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp (p + 2 * l) * Real.exp (-q) := mul_le_mul_of_nonneg_right hK hε.le
      _ = Real.exp (-p - 2) := by rw [← Real.exp_add]; congr 1; dsimp [q]; ring
      _ ≤ Real.exp (-p - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := exp_sub_one_le_half_exp (-p)
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr hcount), K,
    hK.trans (Real.exp_le_exp.mpr (by dsimp [q] at hqp; linarith)), u, ?_, huLip, ?_, ?_⟩
  · intro i x
    have hnorm' : (T.normBound : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hnorm
    exact (T.norm_le _).trans hnorm'
  · intro x
    obtain ⟨i, hi⟩ := hcenters x
    have hdist := (huLip i).dist_le_mul x (centers i)
    have herr : ‖u i (centers i) - u i x‖ ≤ Real.exp (-p) / 2 := by
      have h := hdist.trans ((mul_le_mul_of_nonneg_left hi K.coe_nonneg).trans herror)
      simpa only [dist_eq_norm, norm_sub_rev] using h
    have ht := norm_sub_norm_le (u i (centers i)) (u i x)
    rw [hcenter] at ht herr
    refine ⟨i, ?_⟩
    have hh : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
      simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
    linarith
  · intro i z hz x
    exact D.vertical_left_translate (fun x => T.observable (r y • x)) eta
      (fun z hz x => D.vertical_left_translate T.observable eta hvertical (r y) z hz x)
      ((r (centers i))⁻¹) z hz x

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem sqrt_complement_lipschitz {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hrhalf : r ≤ 1 / 2) (hthalf : t ≤ 1 / 2) :
    |Real.sqrt (1 - r ^ 2) - Real.sqrt (1 - t ^ 2)| ≤ |r - t| := by
  let a := Real.sqrt (1 - r ^ 2)
  let b := Real.sqrt (1 - t ^ 2)
  have hrq : 0 ≤ 1 - r ^ 2 := by nlinarith
  have htq : 0 ≤ 1 - t ^ 2 := by nlinarith
  have ha : 1 / 2 ≤ a := Real.le_sqrt_of_sq_le (by nlinarith)
  have hb : 1 / 2 ≤ b := Real.le_sqrt_of_sq_le (by nlinarith)
  have ha2 : a ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hrq
  have hb2 : b ^ 2 = 1 - t ^ 2 := Real.sq_sqrt htq
  have heq : |a - b| * (a + b) = |r - t| * (r + t) := by
    calc
      _ = |(a - b) * (a + b)| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ a + b)]
      _ = |(t - r) * (r + t)| := congrArg abs (by nlinarith)
      _ = _ := by rw [abs_mul, abs_sub_comm t r, abs_of_nonneg (by linarith : 0 ≤ r + t)]
  calc
    _ ≤ |a - b| * (a + b) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |r - t| * (r + t) := heq
    _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) (by linarith)

theorem exists_complex_unit_completion {X : Type*} [PseudoMetricSpace X] {n : ℕ}
    (f : X → ℂ) (v : Fin n → X → ℂ) {K J : ℝ≥0}
    (hf : ∀ x, ‖f x‖ ≤ 1 / 2) (hfLip : LipschitzWith K f)
    (hv : ∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) (hvnorm : ∀ i x, ‖v i x‖ ≤ 1)
    (hvLip : ∀ i, LipschitzWith J (v i)) :
    ∃ u : Fin (n + 1) → X → ℂ,
      (∀ x, u 0 x = f x) ∧
      (∀ x, ∑ i, ‖u i x‖ ^ 2 = 1) ∧
      (∀ i x, ‖u i x‖ ≤ 1) ∧
      (∀ i, LipschitzWith (K + J) (u i)) ∧
      ∀ x y c, ‖c‖ = 1 → f x = c * f y → (∀ i, v i x = c * v i y) →
        ∀ i, u i x = c * u i y := by
  let t (x : X) : ℂ := Real.sqrt (1 - ‖f x‖ ^ 2)
  have ht (x : X) : ‖t x‖ = Real.sqrt (1 - ‖f x‖ ^ 2) := by
    exact (Complex.norm_real _).trans (Real.norm_of_nonneg (Real.sqrt_nonneg _))
  have htbound (x : X) : ‖t x‖ ≤ 1 := by
    rw [ht]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ‖f x‖])
  have htsq (x : X) : ‖t x‖ ^ 2 = 1 - ‖f x‖ ^ 2 := by
    rw [ht]
    exact Real.sq_sqrt (by nlinarith [hf x, norm_nonneg (f x)])
  have htLip : LipschitzWith K t := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    change ‖(Real.sqrt (1 - ‖f x‖ ^ 2) : ℂ) - (Real.sqrt (1 - ‖f y‖ ^ 2) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (sqrt_complement_lipschitz (norm_nonneg _) (norm_nonneg _) (hf x) (hf y)).trans
      ((abs_norm_sub_norm_le (f x) (f y)).trans (by
        simpa only [dist_eq_norm] using hfLip.dist_le_mul x y))
  let u : Fin (n + 1) → X → ℂ := Fin.cases f (fun i x => t x * v i x)
  have htailLip (i : Fin n) : LipschitzWith (K + J) (fun x => t x * v i x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    calc
      _ = ‖(t x - t y) * v i x + t y * (v i x - v i y)‖ := by congr 1; ring
      _ ≤ ‖(t x - t y) * v i x‖ + ‖t y * (v i x - v i y)‖ := norm_add_le _ _
      _ ≤ ‖t x - t y‖ + ‖v i x - v i y‖ := by
        simp only [norm_mul]
        exact add_le_add
          (mul_le_of_le_one_right (norm_nonneg _) (hvnorm i x))
          (mul_le_of_le_one_left (norm_nonneg _) (htbound y))
      _ ≤ (K : ℝ) * dist x y + (J : ℝ) * dist x y := add_le_add
        (by simpa only [dist_eq_norm] using htLip.dist_le_mul x y)
        (by simpa only [dist_eq_norm] using (hvLip i).dist_le_mul x y)
      _ = _ := by push_cast; ring
  refine ⟨u, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [Fin.sum_univ_succ, u, Fin.cases_zero, Fin.cases_succ, norm_mul, mul_pow]
    rw [← Finset.mul_sum, hv, mul_one, htsq]
    ring
  · intro i x
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hf x).trans (by norm_num)
    · change ‖t x * v j x‖ ≤ 1
      rw [norm_mul]
      exact (mul_le_mul (htbound x) (hvnorm j x) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  · intro i
    refine Fin.cases ?_ htailLip i
    exact hfLip.weaken (le_add_of_nonneg_right (show 0 ≤ J by positivity))
  · intro x y c hc hfc hvc i
    have htx : t x = t y := by
      dsimp [t]
      rw [hfc, norm_mul, hc, one_mul]
    refine Fin.cases hfc (fun j => ?_) i
    change t x * v j x = c * (t y * v j y)
    rw [htx, hvc]
    ring

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_prescribed_scalar (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ f : D.Space → ℂ, (letI := D.metricSpace; LipschitzWith K f) ∧
        (∀ x, ‖f x‖ ≤ 2) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
          f (z • x) = logCharacter (realifyFunctional η) z * f x) ∧
        f (QuotientGroup.mk (1 : D.RealGroup)) = 1 := by
  obtain ⟨C, hC, hseed⟩ := exists_native_central_seed s
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  obtain ⟨K, hK, f, hf, hb, hcentral⟩ := hseed D hp hD η hη hint
  obtain ⟨g, hg, hgb, hvertical, hone⟩ :=
    D.exists_native_prescribed_projection hp hD η f hf hb hcentral
  exact ⟨K, hK, g, hg, hgb, hvertical, hone⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct NNReal BigOperators

theorem exists_native_unit_vertical_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ v : Fin n → D.Space → ℂ,
        (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
        (∀ i x, ‖v i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (v i)) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          v i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * v i x := by
  obtain ⟨a, _, hframe⟩ := exists_native_vertical_translate_frame s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 2 * (X + Polynomial.C a) ^ a + 3)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have htotal : p + 2 * P + 3 ≤ (p + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨n, hn, hnc, K, hK, u, _, hLip, hlower, hphase⟩ :=
    hframe D T hp hT hnorm eta hvertical y hy
  let rho : ℝ≥0 := ⟨Real.exp (-(p + 1)), (Real.exp_pos _).le⟩
  have hrho : 0 < rho := Real.exp_pos _
  obtain ⟨v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    exists_normalized_complex_family u hrho hLip hlower
  let B : ℝ≥0 := 2 / rho * ((n + 1 : ℝ≥0) * K)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hnplus : (n : ℝ) + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hscale : 2 / (rho : ℝ) ≤ Real.exp (p + 2) := by
    calc
      _ = 2 * Real.exp (p + 1) := by
        change 2 / Real.exp (-(p + 1)) = _
        rw [Real.exp_neg, div_inv_eq_mul]
      _ ≤ Real.exp 1 * Real.exp (p + 1) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hB : (B : ℝ) ≤ Real.exp (p + 2 * P + 3) := by
    calc
      _ ≤ Real.exp (p + 2) * (Real.exp (P + 1) * Real.exp P) := by
        dsimp [B]
        push_cast
        exact mul_le_mul hscale (mul_le_mul hnplus hK K.coe_nonneg (Real.exp_nonneg _))
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr (by dsimp [P] at *; linarith)),
    B, hB.trans (Real.exp_le_exp.mpr htotal), v, hvunit, hvnorm, ?_, ?_⟩
  · intro i
    simpa only [Fintype.card_fin] using hvLip i
  · intro i z hz x
    exact hvphase (z • x) x _ (norm_character _) (fun j => hphase j z hz x) i

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_prescribed_unit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) (Fin n)
        ((p + C) ^ C), V.frequency = η := by
  obtain ⟨a, _, hscalar⟩ := exists_native_prescribed_scalar s
  obtain ⟨b, _, hfamily⟩ := exists_native_unit_vertical_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + (X + Polynomial.C a) ^ a + 4 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  obtain ⟨K, hK, f, hf, hb, hvertical, hone⟩ := hscalar D hp hD η hη hint
  let P := (p + a) ^ a
  let q := p + P + 4
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have htwoNorm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  let T : D.Niltest (fun _ : Unit => 1) := {
    orbit := 1
    observable := fun x => f x / 2
    normBound := 1
    lipBound := K
    norm_le := fun x => by
      rw [norm_div, htwoNorm]
      simpa only [NNReal.coe_one, div_self (by norm_num : (2 : ℝ) ≠ 0)] using
        div_le_div_of_nonneg_right (hb x) (by norm_num : (0 : ℝ) ≤ 2)
    lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, ← sub_div, norm_div, htwoNorm]
      have h := hf.dist_le_mul x y
      rw [dist_eq_norm] at h
      linarith [norm_nonneg (f x - f y)] }
  have hT : T.ComplexityLE q := by
    refine ⟨hD.mono D hpq, ?_⟩
    have h := niltest_log_bound_of_exp (1 : ℝ≥0) K (a := 0) (b := P)
      (by norm_num) hP (by simp) hK
    simp only [NNReal.coe_one, zero_add] at h
    change Real.log (2 + ((1 : ℝ≥0) : ℝ) + K) ≤ q
    dsimp [q]
    linarith
  have hphase : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x := by
    intro z hz x
    change f (z • x) / 2 = _ * (f x / 2)
    rw [hvertical z hz]
    exact mul_div_assoc _ _ _
  have hy : Real.exp (-q) ≤ ‖T.observable (QuotientGroup.mk (1 : D.RealGroup))‖ := by
    change Real.exp (-q) ≤ ‖f (QuotientGroup.mk (1 : D.RealGroup)) / 2‖
    rw [hone, norm_div, norm_one, htwoNorm]
    have htwo : (2 : ℝ) ≤ Real.exp q := by
      have he := Real.add_one_le_exp q
      dsimp [q] at *
      linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) htwo
  obtain ⟨n, hn, hnc, K', hK', v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    hfamily D T hq hT (by exact le_rfl) η hphase
      (QuotientGroup.mk (1 : D.RealGroup)) hy
  have htotal : p + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, P, Polynomial.eval₂_pow] using hbudget p hp
  have hqb : (q + b) ^ b ≤ (p + C) ^ C := by linarith
  have hpc : p ≤ (p + C) ^ C := by
    have : 0 ≤ (q + b) ^ b := by positivity
    linarith
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr hqb), ?_⟩
  exact ⟨{
    observable := v
    unit := hvunit
    norm := hvnorm
    lipBound := K'
    lip_bound := hK'.trans (Real.exp_le_exp.mpr hqb)
    lipschitz := hvLip
    frequency := η
    height := fun i => (hη i).trans hpc
    vertical := hvphase
    integral := fun z _ hz => hint z hz }, rfl⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct NNReal BigOperators

theorem exists_native_unit_vertical_completion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ v : Fin (n + 1) → D.Space → ℂ,
        (∀ x, v 0 x = T.observable x / 2) ∧
        (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
        (∀ i x, ‖v i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (v i)) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          v i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * v i x := by
  obtain ⟨a, _, hfamily⟩ := exists_native_unit_vertical_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C a) ^ a + 1)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have htotal : p + P + 1 ≤ (p + C) ^ C := by
    simpa [X, P, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨n, hn, hnc, K, hK, v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    hfamily D T hp hT hnorm eta hvertical y hy
  let f (x : D.Space) := T.observable x / 2
  have htwoNorm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have hf (x : D.Space) : ‖f x‖ ≤ 1 / 2 := by
    have hn' : (T.normBound : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hnorm
    dsimp [f]
    rw [norm_div, htwoNorm]
    exact div_le_div_of_nonneg_right ((T.norm_le x).trans hn') (by norm_num)
  have hfLip : LipschitzWith T.lipBound f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (T.observable x / 2) (T.observable y / 2) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div, htwoNorm]
    have h := T.lipschitz.dist_le_mul x y
    rw [dist_eq_norm] at h
    linarith [norm_nonneg (T.observable x - T.observable y)]
  obtain ⟨u, hu0, huunit, hunorm, huLip, huphase⟩ :=
    exists_complex_unit_completion f v hf hfLip hvunit hvnorm hvLip
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hcount : (n : ℝ) + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hsum : ((T.lipBound + K : ℝ≥0) : ℝ) ≤ Real.exp (p + P + 1) := by
    have hTlip : (T.lipBound : ℝ) ≤ Real.exp p := by
      linarith [Niltest.observable_budget hT, T.normBound.coe_nonneg]
    have ht := hTlip.trans (Real.exp_le_exp.mpr (show p ≤ p + P by linarith))
    have hk := hK.trans (Real.exp_le_exp.mpr (show (p + a) ^ a ≤ p + P by dsimp [P]; linarith))
    calc
      _ ≤ 2 * Real.exp (p + P) := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp (p + P) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨n, hn, hcount.trans (Real.exp_le_exp.mpr (by linarith)),
    T.lipBound + K, hsum.trans (Real.exp_le_exp.mpr htotal), u, hu0, huunit, hunorm, huLip, ?_⟩
  intro i z hz x
  apply huphase (z • x) x _ (norm_character _) ?_ (fun j => hvphase j z hz x) i
  dsimp [f]
  rw [hvertical z hz]
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_prescribed_invariant_unit (s M : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Γ L : Type*} [Group Γ] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) [MulAction Γ D.Space],
      Fintype.card Γ ≤ M → ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (letI := D.metricSpace; ∀ a : Γ,
        LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (fun x : D.Space => a • x)) →
      (∀ (a : Γ) (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x : D.Space,
        a • (z • x) = z • (a • x)) →
      ∀ η : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ n : ℕ, 0 < n ∧
        (Fintype.card (SymmetricEvaluationIndex (Fintype.card Γ) (Fin n)) : ℝ) ≤
          Real.exp ((p + C) ^ C) ∧
      ∃ W : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
          (SymmetricEvaluationIndex (Fintype.card Γ) (Fin n)) ((p + C) ^ C),
        W.frequency = Fintype.card Γ • η ∧
        ∀ (a : Γ) k x, W.observable k (a • x) = W.observable k x := by
  obtain ⟨a, _, hunit⟩ := exists_native_prescribed_unit s
  obtain ⟨b, _, hcost⟩ := exists_uniform_invariantVertical_cost M
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C a) ^ a + (X + 3) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro Γ L _ _ _ _ _ _ _ _ d D _ hM p hp hD hact hcomm η hη hint
  let := D.metricSpace
  obtain ⟨n, hn, hnc, V, hV⟩ := hunit D hp hD η hη hint
  let P := (p + a) ^ a
  let r := p + P + (p + 3) ^ 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hPr : P ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 3)]
  have hAr : (p + 3) ^ 2 ≤ r := by dsimp [r]; linarith
  let V' := V.mono hPr
  have hn' : (Fintype.card (Fin n) : ℝ) ≤ Real.exp r := by
    simpa only [Fintype.card_fin] using hnc.trans (Real.exp_le_exp.mpr hPr)
  obtain ⟨W, hW, hWinv, hWcard⟩ := V'.exists_invariant hr hn'
    ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ (Real.exp_le_exp.mpr hAr) hact hcomm
  have htotal : invariantVerticalBudget (Fintype.card Γ) r ≤ (p + C) ^ C := by
    apply (hcost (Fintype.card Γ) hM r hr).trans
    simpa [R, X, r, P, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hWcard.trans (Real.exp_le_exp.mpr htotal), W.mono htotal, ?_, hWinv⟩
  change W.frequency = _
  rw [hW]
  change Fintype.card Γ • V.frequency = _
  rw [hV]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}

noncomputable def tensorPower (V : D.UnitVerticalObservable T I p) (n : ℕ) :
    D.UnitVerticalObservable T (Fin n → I) (p + n + 1) where
  observable a x := ∏ j, V.observable (a j) x
  unit x := by
    simp only [norm_prod, ← Finset.prod_pow]
    calc
      _ = ∏ _j : Fin n, ∑ a : I, ‖V.observable a x‖ ^ 2 := (Fintype.prod_sum _).symm
      _ = 1 := by simp only [V.unit, Finset.prod_const_one]
  norm a x := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => V.norm (a j) x)
  lipBound := n * V.lipBound
  lip_bound := by
    change (n : ℝ) * V.lipBound ≤ Real.exp (p + n + 1)
    calc
      _ ≤ Real.exp ((n : ℝ) + 1) * Real.exp p :=
        mul_le_mul (by linarith [Real.add_one_le_exp ((n : ℝ) + 1)]) V.lip_bound
          V.lipBound.coe_nonneg (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  lipschitz := by
    let := D.metricSpace
    intro a
    have h := bounded_lipschitz_fintype_prod (fun j x => V.observable (a j) x)
      (B := 1) le_rfl (fun j => V.lipschitz (a j)) (fun j x => V.norm (a j) x)
    simpa only [Fintype.card_fin, one_pow, mul_one] using h.2
  frequency := n • V.frequency
  height i := by
    simpa only [LinearMap.smul_apply, nsmul_eq_mul] using rationalLogHeight_nat_mul n (V.height i)
  vertical a z hz x := by
    simp only [V.vertical _ z hz x, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, realifyFunctional_nsmul, AddCircle.coe_nsmul, character_nsmul]
  integral z hz hL := by
    obtain ⟨m, hm⟩ := V.integral z hz hL
    refine ⟨(n : ℤ) * m, ?_⟩
    rw [realifyFunctional_nsmul, hm]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

noncomputable def reindex {J : Type*} [Fintype J]
    (V : D.UnitVerticalObservable T I p) (e : I ≃ J) : D.UnitVerticalObservable T J p where
  observable j := V.observable (e.symm j)
  unit x := (e.symm.sum_comp (fun i => ‖V.observable i x‖ ^ 2)).trans (V.unit x)
  norm j := V.norm (e.symm j)
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := fun j => V.lipschitz (e.symm j)
  frequency := V.frequency
  height := V.height
  vertical j := V.vertical (e.symm j)
  integral := V.integral

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

theorem exists_of_unit_data {σ I : Type*} {L : Type}
    [Fintype σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
    (M : D.MultidegreeStructure bound) (hstep : t = ∑ i, bound i)
    {p : ℝ} (hM : M.ComplexityLE p)
    (g : M.filtration.realification.PolynomialOrbit)
    (V : D.UnitVerticalObservable (D.filtration.realification.subgroup t) I p)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp p) :
    ∃ W : NativeMultidegreeNilcharacter bound p, ∃ e : I ≃ Fin W.outputDim,
      W.dim = d ∧ ∀ i x, W.eval (e i) x = V.observable i
        (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) := by
  classical
  subst hstep
  let V' : D.UnitVerticalObservable (M.realSubgroup bound) I p :=
    { V with
      vertical := fun i z hz x => V.vertical i z (M.realSubgroup_top ▸ hz) x
      integral := fun z hz hL => V.integral z (M.realSubgroup_top ▸ hz) hL }
  obtain ⟨i, _⟩ := exists_large_unit_coordinate
    (fun i => V.observable i (QuotientGroup.mk 1)) (V.unit _)
  let W : NativeMultidegreeNilcharacter bound p :=
    { L := L
      dim := d
      model := D
      multi := M
      complexity := hM
      orbit := g
      outputDim := Fintype.card I
      output_pos := Fintype.card_pos_iff.mpr ⟨i⟩
      output_bound := hI
      vertical := V'.reindex (Fintype.equivFin I) }
  refine ⟨W, Fintype.equivFin I, rfl, ?_⟩
  intro i x
  change V.observable ((Fintype.equivFin I).symm ((Fintype.equivFin I) i)) _ = _
  rw [Equiv.symm_apply_apply]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def tensorIndexEquiv (d n : ℕ) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_fun, Fintype.card_fin])

noncomputable def tensorPowerBudget (n : ℕ) (p : ℝ) : ℝ := (n + 1) * (p + 1)

theorem tensorPowerBudget_bounds (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ tensorPowerBudget n p ∧ p + n + 1 ≤ tensorPowerBudget n p ∧
      (n : ℝ) * p ≤ tensorPowerBudget n p := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  unfold tensorPowerBudget
  constructor
  · nlinarith [mul_nonneg hn hp]
  constructor <;> nlinarith [mul_nonneg hn hp]

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def tensorPower (n : ℕ) : NativeMultidegreeNilcharacter bound (tensorPowerBudget n p) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hb := tensorPowerBudget_bounds n hp
  exact {
    L := W.L
    dim := W.dim
    model := W.model
    multi := W.multi
    complexity := W.complexity.mono W.multi hb.1
    orbit := W.orbit
    outputDim := W.outputDim ^ n
    output_pos := pow_pos W.output_pos n
    output_bound := by
      simpa only [Nat.cast_pow] using
        (pow_le_pow_left₀ (Nat.cast_nonneg W.outputDim) W.output_bound n).trans
          (by rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr hb.2.2)
    vertical := ((W.vertical.tensorPower n).reindex (tensorIndexEquiv W.outputDim n)).mono hb.2.1 }

theorem tensorPower_eval (n : ℕ) (a : Fin (W.outputDim ^ n)) (x : σ → ℤ) :
    (W.tensorPower n).eval a x = ∏ j, W.eval ((tensorIndexEquiv W.outputDim n).symm a j) x := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def tensorVector {σ I : Type*} (f : I → (σ → ℤ) → ℂ)
    (n : ℕ) (a : Fin n → I) (x : σ → ℤ) : ℂ := ∏ j, f (a j) x

theorem product_flatten {q n N : ℕ} (e : (Fin q × Fin n) ≃ Fin N)
    (f : Fin q → Fin n → ℂ) :
    (∏ i, ∏ j, f i j) = ∏ k, f (e.symm k).1 (e.symm k).2 := by
  calc
    _ = ∏ a : Fin q × Fin n, f a.1 a.2 := (Fintype.prod_prod_type (fun a => f a.1 a.2)).symm
    _ = _ := (e.symm.prod_comp (fun a => f a.1 a.2)).symm

noncomputable def rootTensorEquiv (q t : ℕ) (ht : 1 ≤ t) :
    (Fin q × Fin (q ^ (t - 1))) ≃ Fin (((q : ℤ) ^ t).natAbs) :=
  finProdFinEquiv.trans (finCongr (by
    have h : q * q ^ (t - 1) = q ^ t := by rw [← pow_succ', Nat.sub_add_cancel ht]
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using h))

noncomputable def rootTensorIndex (d q t : ℕ) (ht : 1 ≤ t)
    (a : Fin q → Fin (d ^ (q ^ (t - 1)))) : Fin (((q : ℤ) ^ t).natAbs) → Fin d :=
  fun k => (tensorIndexEquiv d (q ^ (t - 1))).symm
    (a ((rootTensorEquiv q t ht).symm k).1) ((rootTensorEquiv q t ht).symm k).2

theorem NativeMultidegreeNilcharacter.tensorPower_tensor_eval
    {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter bound p) (q t : ℕ) (ht : 1 ≤ t)
    (a : Fin q → Fin (W.outputDim ^ (q ^ (t - 1)))) (x : σ → ℤ) :
    tensorVector (W.tensorPower (q ^ (t - 1))).eval q a x =
      signedTensorVector W.eval ((q : ℤ) ^ t) (rootTensorIndex W.outputDim q t ht a) x := by
  unfold tensorVector
  simp_rw [W.tensorPower_eval]
  have hnonneg : 0 ≤ (q : ℤ) ^ t := pow_nonneg (Int.natCast_nonneg q) _
  simp only [signedTensorVector, signedTensorProduct, if_neg (not_lt.mpr hnonneg)]
  exact product_flatten (rootTensorEquiv q t ht) _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem tensorVector_unit {σ I : Type*} [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hunit : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (n : ℕ) (x : σ → ℤ) :
    ∑ a : Fin n → I, ‖tensorVector f n a x‖ ^ 2 = 1 := by
  simp only [tensorVector, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ _j : Fin n, ∑ i : I, ‖f i x‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [hunit, Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

structure SymmetricSquarefreeUnitData (p : ℝ) (η : L →ₗ[ℚ] ℚ) (q : ℝ) where
  grid : ℕ
  grid_pos : 0 < grid
  stable : M.SquarefreeGridStable p grid
  complexity : (M.squarefreeModelMultidegree p grid grid_pos stable).ComplexityLE q
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  observable : (M.squarefreeModel p grid grid_pos stable).UnitVerticalObservable
    ((M.squarefreeModel p grid grid_pos stable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound)))
    (SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin coordinateCount)) q
  frequency : observable.frequency = M.filtration.replicatedFrequency η
  invariant : ∀ (e : ReplicatedPermutation bound) k x,
    observable.observable k (M.squarefreeSpacePermute p grid grid_pos stable e x) =
      observable.observable k x
  dimension :
    (Fintype.card (SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound))
      (Fin coordinateCount)) : ℝ) ≤ Real.exp q

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators NNReal

variable {σ : Type} {L I : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] [Fintype I]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (M : D.MultidegreeStructure bound) {p q v : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (V : D.UnitVerticalObservable (D.filtration.realification.subgroup s) I v)
  (U : M.SymmetricSquarefreeUnitData p V.frequency q)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p U.grid U.grid_pos U.stable)

noncomputable def comparisonVerticalProduct (ε : D.RealGroup)
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : E.Space) : ℂ :=
  (V.tensorPower (multidegreeFactorial bound)).observable a
    (ε • M.comparisonFirstSpace p U.grid U.grid_pos U.stable E hEL x) *
  star (U.observable.observable k (M.comparisonSecondSpace p U.grid U.grid_pos U.stable E hEL x))

theorem comparisonVerticalProduct_norm (ε : D.RealGroup)
    (a : Fin (multidegreeFactorial bound) → I)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : E.Space) : ‖M.comparisonVerticalProduct V U E hEL ε a k x‖ ≤ 1 := by
  unfold comparisonVerticalProduct
  rw [norm_mul, norm_star]
  simpa only [mul_one] using mul_le_mul
    ((V.tensorPower (multidegreeFactorial bound)).norm a _) (U.observable.norm k _)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct BigOperators

theorem exists_controlled_symmetric_squarefree_unit (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound), (∑ i, bound i) = t →
      ∀ [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
        {p : ℝ}, M.ComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      Nonempty (M.SymmetricSquarefreeUnitData (p + t.factorial + 1) η ((p + C) ^ C)) := by
  obtain ⟨a, _, hinvariant⟩ := exists_prescribed_invariant_unit t t.factorial
  obtain ⟨b, _, hfrequency⟩ := exists_squarefreeFrequency_cost t
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + Polynomial.C t.factorial + 1
  let R := (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ s d D bound M ht _ _ _ _ p hM η hη
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let q := p + t.factorial + 1
  let m := Fintype.card (ReplicatedPermutation bound)
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨1⟩
  have hmle : m ≤ t.factorial := by
    simpa only [ht] using replicatedPermutation_card_le bound
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) t.factorial]
  have hηdiv (i) : rationalLogHeight (dividedFrequency m η (D.basis i)) ≤ q := by
    apply (dividedFrequency_height m hm η (D.basis i) (hη i)).trans
    have hmr : (m : ℝ) ≤ t.factorial := by exact_mod_cast hmle
    dsimp [q]
    linarith
  obtain ⟨B, hB, hstable, hE, hηE, hint⟩ :=
    M.exists_controlled_replicated_frequency (hM.mono M hpq) (dividedFrequency m η) hηdiv
  rw [ht] at hE hηE
  let r := (q + b) ^ b
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : squarefreeFrequencyModelBudget t q ≤ r := hfrequency q hq
  have hEr := hE.mono (M.squarefreeModelMultidegree q B hB hstable) hqr
  let E := M.squarefreeModel q B hB hstable
  let := M.squarefreeSpaceAction q B hB hstable
  have hstep : Fintype.card (ReplicatedIndex bound) = t := (replicatedIndex_card bound).trans ht
  rw [← hstep] at hinvariant
  obtain ⟨n, hn, hdim, W, hW, hWinv⟩ := hinvariant (Γ := ReplicatedPermutation bound) E
    (by simpa only [hstep] using hmle) hr hEr.1
    (fun e => M.squarefreeSpacePermute_lipschitz q B hB hstable hr hEr.1 e)
    (fun e z hz x => M.squarefreeSpacePermute_commutes_top q B hB hstable e z hz x)
    (M.filtration.replicatedFrequency (dividedFrequency m η)) (fun i => (hηE i).trans hqr) hint
  have htotal : q + r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, R, X, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hra : 0 ≤ (r + a) ^ a := by positivity
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hWC : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  refine ⟨{
    grid := B
    grid_pos := hB
    stable := hstable
    complexity := hEr.mono (M.squarefreeModelMultidegree q B hB hstable) hrC
    coordinateCount := n
    coordinateCount_pos := hn
    observable := W.mono hWC
    frequency := ?_
    invariant := hWinv
    dimension := hdim.trans (Real.exp_le_exp.mpr hWC) }⟩
  change W.frequency = M.filtration.replicatedFrequency η
  rw [hW]
  ext x
  simp only [LinearMap.smul_apply, nsmul_eq_mul, MultidegreeLieFiltration.replicatedFrequency_apply,
    dividedFrequency, smul_eq_mul]
  change (m : ℚ) * ((m : ℚ)⁻¹ * η _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0), one_mul]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  {M : D.MultidegreeStructure bound} {p q : ℝ} {η : L →ₗ[ℚ] ℚ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  (U : M.SymmetricSquarefreeUnitData p η q)

noncomputable def eval (g : M.filtration.realification.PolynomialOrbit)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) : ℂ :=
  U.observable.observable k (QuotientGroup.mk
    ((M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).realification.polynomialOrbitEval
      x (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g)))

theorem eval_permute (g : M.filtration.realification.PolynomialOrbit)
    (e : ReplicatedPermutation bound)
    (k : SymmetricEvaluationIndex (Fintype.card (ReplicatedPermutation bound)) (Fin U.coordinateCount))
    (x : ReplicatedIndex bound → ℤ) :
    U.eval g k (fun j => x ((replicatedPermutation bound e).symm j)) = U.eval g k x := by
  unfold eval
  rw [← M.filtration.polarizeRealOrbit_permute (fun j : ReplicatedIndex bound => j.1)
    g (replicatedPermutation bound e) (replicatedPermutation_block bound e) x]
  change U.observable.observable k (QuotientGroup.mk
    (M.squarefreeRealPermute p U.grid U.grid_pos U.stable e _)) = _
  rw [← M.squarefreeSpacePermute_mk]
  exact U.invariant e k _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  {M : D.MultidegreeStructure bound} {p q r : ℝ} {η : L →ₗ[ℚ] ℚ}
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

noncomputable def mono (U : M.SymmetricSquarefreeUnitData p η q) (hqr : q ≤ r) :
    M.SymmetricSquarefreeUnitData p η r := {
  U with
  complexity := U.complexity.mono _ hqr
  observable := U.observable.mono hqr
  dimension := U.dimension.trans (Real.exp_le_exp.mpr hqr) }

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.SymmetricSquarefreeUnitData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev CoveredJetChartSource (O B : Fin m → Type*) (n : Fin m → ℕ) (d : ℕ) :=
  ∀ j, O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)

instance coveredJetChartSource_borel [∀ j, Fintype (O j)] (d : ℕ) [NeZero d] :
    BorelSpace (CoveredJetChartSource U O B n d) := by
  let : ∀ j, BorelSpace ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => inferInstance
  let : ∀ j, BorelSpace (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def coveredJetChart : CoveredJetChartSource U O B n d → EuclideanJetLayers U O :=
  fun x j t => normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d (x j t)

def coveredJetSourceRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (CoveredJetChartSource U O B n d) :=
  Set.univ.pi (fun j => Set.univ.pi (fun t =>
    (normalizedLatticePoint (euclideanSubspace (U j)) (b j) ⁻¹' Ω j t) ×ˢ Set.univ))

def coveredJetTargetRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (EuclideanJetLayers U O) :=
  Set.univ.pi (fun j => Set.univ.pi (fun t =>
    quotientIntegerCover
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d ⁻¹'
        normalizedChartRegion (euclideanSubspace (U j)) (b j) (hb j) (Ω j t)))

variable [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def ofProduct {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {σ : Type*} {w : σ → ℕ} {s d e : ℕ} {p : ℝ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (T : D.Niltest w) (U : E.Niltest w)
    (hp : 2 ≤ p) (hT : T.ComplexityLE p) (hU : U.ComplexityLE p) :
    NativeIntegerExpansion w s (productNiltestBudget p)
      (fun x => T.eval x * U.eval x) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L M
  let dims : Bool → ℕ := fun b => Bool.rec e d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact E
    · exact D
  let tests : ∀ b, (models b).Niltest w := fun b => by
    cases b
    · exact U
    · exact T
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact hU
    · exact hT
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : σ → ℤ) : S.eval x =
      T.eval x * U.eval x := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      x = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  exact ofTest S
    (RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests)
    (fun x => (heval x).symm)

noncomputable def mul {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ} {f g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p f) (F : NativeIntegerExpansion w s p g)
    (hp : 2 ≤ p) :
    NativeIntegerExpansion w s (productNiltestBudget p + 2 * p) (fun x => f x * g x) := by
  let c : Fin E.count × Fin F.count → ℂ := fun ij => E.coefficient ij.1 * F.coefficient ij.2
  let v : Fin E.count × Fin F.count → (σ → ℤ) → ℂ := fun ij x =>
    (E.test ij.1).eval x * (F.test ij.2).eval x
  let R : ∀ ij, NativeIntegerExpansion w s (productNiltestBudget p) (v ij) :=
    fun ij => ofProduct (E.model ij.1) (F.model ij.2) (E.test ij.1) (F.test ij.2)
      hp (E.complexity ij.1) (F.complexity ij.2)
  have hexp : Real.exp p * Real.exp p = Real.exp (2 * p) := by
    rw [← Real.exp_add, two_mul]
  have hcard : (Fintype.card (Fin E.count × Fin F.count) : ℝ) ≤ Real.exp (2 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul E.count_bound F.count_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq hexp
  have hc : (∑ ij, ‖c ij‖) ≤ Real.exp (2 * p) := by
    calc
      _ = (∑ i, ‖E.coefficient i‖) * (∑ j, ‖F.coefficient j‖) := by
        simp only [c, norm_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.cost F.cost (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Real.exp_nonneg _)
      _ = _ := hexp
  have heq : (fun x => ∑ ij, c ij * v ij x) = (fun x => f x * g x) := by
    funext x
    rw [E.eval x, F.eval x]
    simp only [c, v, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact heq ▸ weightedSum R c (by linarith) hcard hc

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem trans {σ J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
    {s : ℕ} {p : ℝ}
    {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ} {psi : M → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p chi eta) (F : NativeIntegerVectorEquivalence s p eta psi)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (hp : 2 ≤ p) :
    NativeIntegerVectorEquivalence s (productNiltestBudget p + 2 * p + p) chi psi := by
  classical
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hpq : p ≤ productNiltestBudget p + 2 * p + p := by linarith
  refine {
    left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
    right_dimension := F.right_dimension.trans (Real.exp_le_exp.mpr hpq)
    expansion := ?_
  }
  intro j l
  let A : ∀ k, NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => chi j x * star (eta k x)) :=
    fun k => Classical.choice (E.expansion j k)
  let B : ∀ k, NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => eta k x * star (psi l x)) :=
    fun k => Classical.choice (F.expansion k l)
  let R := fun k => (A k).mul (B k) hp
  have hc : (∑ _ : K, ‖(1 : ℂ)‖) ≤ Real.exp p := by
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using E.right_dimension
  let S := NativeIntegerExpansion.weightedSum R (fun _ => 1) hp0 E.right_dimension hc
  have heq : (fun x => ∑ k, (1 : ℂ) *
      ((chi j x * star (eta k x)) * (eta k x * star (psi l x)))) =
      (fun x => chi j x * star (psi l x)) := by
    funext x
    calc
      _ = ∑ k, ((chi j x * star (psi l x)) * star (eta k x)) * eta k x := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := (complex_unit_vector_resolution (fun k => eta k x) (hunit x) _).symm
  exact ⟨heq ▸ S⟩

theorem exists_trans_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
      {s : ℕ} {p : ℝ}
      {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ} {psi : M → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p chi eta → NativeIntegerVectorEquivalence s p eta psi →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) → NativeIntegerVectorEquivalence s ((p + C) ^ C) chi psi := by
  let Y : Polynomial ℕ := Polynomial.X + 2
  let P := (Y + 2) ^ 2 + Y + (Y + (Y ^ 2 + Y + 3) ^ 2) + Y ^ 2 + 4 + 2 * Y + Y
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J K M _ _ _ s p chi eta psi hp E F hunit
  have hpq : p ≤ p + 2 := by linarith
  have hbudget : productNiltestBudget (p + 2) + 2 * (p + 2) + (p + 2) ≤ (p + C) ^ C := by
    simpa [P, Y, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget]
      using hbound p hp
  exact ((E.mono hpq).trans (F.mono hpq) hunit (by linarith)).mono hbudget

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerExpansion

noncomputable def constOne {σ : Type*} (w : σ → ℕ) (s : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    NativeIntegerExpansion w s p (fun _ => 1) :=
  ofTest (RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold s) w 1)
    (RationalTorus.trivialNilmanifold_const_one_complexity s w hp) (fun _ => rfl)

theorem exists_mul_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
      {f g : (σ → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion w s p f → NativeIntegerExpansion w s p g →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => f x * g x)) := by
  obtain ⟨a, _, ha⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2 + Polynomial.C a) ^ a + 2 * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro σ w s p f g hp E F
  have hpq : p ≤ p + 2 := by linarith
  have hcost : (p + 2 + a) ^ a + 2 * (p + 2) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : productNiltestBudget (p + 2) + 2 * (p + 2) ≤ (p + C) ^ C :=
    (add_le_add (ha _ (by linarith)) (le_refl _)).trans hcost
  exact ⟨(((E.mono hpq).mul (F.mono hpq) (by linarith)).mono hbound)⟩

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

theorem card_product_le_exp_two {A B : Type*} [Fintype A] [Fintype B] {p : ℝ}
    (ha : (Fintype.card A : ℝ) ≤ Real.exp p) (hb : (Fintype.card B : ℝ) ≤ Real.exp p) :
    (Fintype.card (A × B) : ℝ) ≤ Real.exp (2 * p) := by
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact (mul_le_mul ha hb (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    (by rw [← Real.exp_add, two_mul])

theorem complex_tensor_cross_product (a b c d : ℂ) :
    (a * star b) * (c * star d) = (a * c) * star (b * d) := by
  simp only [star_mul]
  ring

noncomputable def NativeIntegerExpansion.tensorCrossProduct {σ : Type*} {s : ℕ} {p : ℝ}
    {f g h k : (σ → ℤ) → ℂ}
    (A : NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => f x * star (h x)))
    (B : NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => g x * star (k x)))
    (hp : 2 ≤ p) :
    NativeIntegerExpansion (fun _ : σ => 1) s (productNiltestBudget p + 2 * p)
      (fun x => (f x * g x) * star (h x * k x)) := by
  have heq : (fun x => (f x * star (h x)) * (g x * star (k x))) =
      (fun x => (f x * g x) * star (h x * k x)) :=
    funext (fun x => complex_tensor_cross_product (f x) (h x) (g x) (k x))
  exact heq ▸ A.mul B hp

namespace NativeIntegerVectorEquivalence

theorem tensor {σ J K L M : Type*} [Fintype J] [Fintype K] [Fintype L] [Fintype M]
    {s : ℕ} {p : ℝ} {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
    {psi : L → (σ → ℤ) → ℂ} {phi : M → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p chi eta)
    (F : NativeIntegerVectorEquivalence s p psi phi) (hp : 2 ≤ p) :
    NativeIntegerVectorEquivalence s (productNiltestBudget p + 2 * p)
      (fun jl : J × L => fun x => chi jl.1 x * psi jl.2 x)
      (fun km : K × M => fun x => eta km.1 x * phi km.2 x) := by
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hcost : Real.exp (2 * p) ≤ Real.exp (productNiltestBudget p + 2 * p) :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_left hB)
  refine ⟨(card_product_le_exp_two E.left_dimension F.left_dimension).trans hcost,
    (card_product_le_exp_two E.right_dimension F.right_dimension).trans hcost, ?_⟩
  intro jl km
  obtain ⟨A⟩ := E.expansion jl.1 km.1
  obtain ⟨B⟩ := F.expansion jl.2 km.2
  exact ⟨A.tensorCrossProduct B hp⟩

theorem exists_tensor_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K L M : Type*}
      [Fintype J] [Fintype K] [Fintype L] [Fintype M] {s : ℕ} {p : ℝ}
      {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
      {psi : L → (σ → ℤ) → ℂ} {phi : M → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p chi eta →
      NativeIntegerVectorEquivalence s p psi phi →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun jl : J × L => fun x => chi jl.1 x * psi jl.2 x)
        (fun km : K × M => fun x => eta km.1 x * phi km.2 x) := by
  obtain ⟨a, _, ha⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2 + Polynomial.C a) ^ a + 2 * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro σ J K L M _ _ _ _ s p chi eta psi phi hp E F
  have hpq : p ≤ p + 2 := by linarith
  have hcost : (p + 2 + a) ^ a + 2 * (p + 2) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : productNiltestBudget (p + 2) + 2 * (p + 2) ≤ (p + C) ^ C :=
    (add_le_add (ha _ (by linarith)) (le_refl _)).trans hcost
  exact ((E.mono hpq).tensor (F.mono hpq) (by linarith)).mono hbound

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

theorem exists_fin_prod_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
      (f : Fin n → (σ → ℤ) → ℂ), 0 ≤ p →
      (∀ i, Nonempty (NativeIntegerExpansion w s p (f i))) →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => ∏ i, f i x)) := by
  induction n with
  | zero =>
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.X + 2)
    refine ⟨C, hC, ?_⟩
    intro σ w s p f hp _
    have hcost : p + 2 ≤ (p + C) ^ C := by simpa using hbudget p hp
    exact ⟨by simpa using (constOne w s (by linarith : 2 ≤ p + 2)).mono hcost⟩
  | succ n ih =>
    obtain ⟨A, _, hprod⟩ := ih
    obtain ⟨B, _, hmul⟩ := exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    let T := X + (X + Polynomial.C A) ^ A
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
    refine ⟨C, hC, ?_⟩
    intro σ w s p f hp hf
    let t := p + (p + A) ^ A
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
    have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
    obtain ⟨tail⟩ := hprod (fun i => f i.succ) hp (fun i => hf i.succ)
    obtain ⟨H⟩ := hmul ht ((Classical.choice (hf 0)).mono hpt) (tail.mono hAt)
    have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
    exact ⟨by simpa only [Fin.prod_univ_succ] using H.mono hcost⟩

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem RationalTorus.residueNiltest_eval {q : ℕ} [NeZero q] (j : ZMod q) (n : ℤ) :
    (residueNiltest j).eval (fun _ : Unit => n) = if (n : ZMod q) = j then 1 else 0 := by
  classical
  unfold residueNiltest realAffineNiltest
  rw [affineNiltest_eval]
  simp only [reindexedRealObservable, Equiv.refl_apply,
    Finset.univ_unique, Finset.sum_singleton, Pi.add_apply, Pi.smul_apply,
    zero_add, smul_eq_mul, mul_one_div]
  rw [← ZMod.toAddCircle_intCast, CircleFourier.residueCutoff_at_grid]
  split_ifs <;> rfl

theorem exists_coordinate_residue_expansion {σ : Type*} [Fintype σ]
    {q : ℕ} [NeZero q] (k : σ) (j : ZMod q) {p : ℝ}
    (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    Nonempty (NativeIntegerExpansion (fun _ : σ => 1) 1 (p + 2)
      (fun x => if (x k : ZMod q) = j then 1 else 0)) := by
  let T := RationalTorus.residueNiltest j
  let a : (σ → ℤ) →+ ℤ := { toFun := fun x => x k, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom (fun _ : Unit => a)
  refine ⟨NativeIntegerExpansion.ofTest U (RationalTorus.residueNiltest_complexity j hp hq) ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
  exact (RationalTorus.residueNiltest_eval j (x k)).symm

noncomputable def pairParityIndicator (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) : ℂ :=
  if (fun i => (x i : ZMod 2)) = r then 1 else 0

theorem pairParityIndicator_product (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) :
    pairParityIndicator r x =
      (if (x 0 : ZMod 2) = r 0 then 1 else 0) *
        (if (x 1 : ZMod 2) = r 1 then 1 else 0) := by
  classical
  have heq : (fun i => (x i : ZMod 2)) = r ↔ (x 0 : ZMod 2) = r 0 ∧ (x 1 : ZMod 2) = r 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
  unfold pairParityIndicator
  simp only [heq]
  split_ifs <;> simp_all

theorem exists_pairParityIndicator_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ r : Fin 2 → ZMod 2,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (C : ℝ) (pairParityIndicator r)) := by
  obtain ⟨A, hA, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨(4 + A) ^ A + 2, by omega, ?_⟩
  intro r
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  obtain ⟨E0⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 0 (r 0) (by norm_num : (0 : ℝ) ≤ 2) htwo
  obtain ⟨E1⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 1 (r 1) (by norm_num : (0 : ℝ) ≤ 2) htwo
  obtain ⟨E⟩ := hmul (by norm_num : (0 : ℝ) ≤ 2 + 2) E0 E1
  have hb : ((2 : ℝ) + 2 + A) ^ A ≤ (((4 + A) ^ A + 2 : ℕ) : ℝ) := by
    push_cast
    norm_num
  have heq : (fun x => (if (x 0 : ZMod 2) = r 0 then (1 : ℂ) else 0) *
      (if (x 1 : ZMod 2) = r 1 then 1 else 0)) = pairParityIndicator r := by
    funext x
    exact (pairParityIndicator_product r x).symm
  rw [heq] at E
  exact ⟨E.mono hb⟩

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_tensor_power_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p f g →
      NativeIntegerVectorEquivalence s ((p + C) ^ C) (tensorVector f n) (tensorVector g n) := by
  obtain ⟨A, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C n * X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp E
  have hsum : (p + A) ^ A + n * p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by
    have hn : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
    linarith
  have hnp : (n : ℝ) * p ≤ (p + C) ^ C := by
    have ha : 0 ≤ (p + A) ^ A := by positivity
    linarith
  have hI : (Fintype.card (Fin n → I) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) E.left_dimension n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  have hJ : (Fintype.card (Fin n → J) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) E.right_dimension n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  refine ⟨hI, hJ, ?_⟩
  intro a b
  obtain ⟨F⟩ := hprod (fun k x => f (a k) x * star (g (b k) x)) hp
    (fun k => E.expansion (a k) (b k))
  have heq : (fun x => ∏ k, f (a k) x * star (g (b k) x)) =
      (fun x => tensorVector f n a x * star (tensorVector g n b x)) := by
    funext x
    simp only [tensorVector, Finset.prod_mul_distrib, star_prod]
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

theorem exists_halving_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} {f : (Fin 2 → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 p f →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (fun x => f (fun i => x i / 2))) := by
  obtain ⟨A, hA, hparity⟩ := exists_pairParityIndicator_expansion
  obtain ⟨B, _, hmul⟩ := exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A + 2 + Polynomial.C B) ^ B + 2)
  refine ⟨C, hC, ?_⟩
  intro p f hp E
  classical
  let t : ℝ := p + A + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hAt : (A : ℝ) ≤ t := by dsimp [t]; linarith
  let P (r : Fin 2 → ZMod 2) := halvingPolynomial (fun i => ((r i).val : ℤ))
  have hP (r : Fin 2 → ZMod 2) (i : Fin 2) :
      P r i ∈ weightedSupportLE (fun _ : Fin 2 => 1) 1 := halvingPolynomial_support _ i
  let F (r : Fin 2 → ZMod 2) := E.substitutedValue (P r) (hP r)
  have hF (r : Fin 2 → ZMod 2) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((t + B) ^ B) (fun x => pairParityIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hparity r)).mono hAt)
      ((E.substituteExpansion (P r) (hP r)).mono hpt)
  have hc : (Fintype.card (Fin 2 → ZMod 2) : ℝ) ≤ Real.exp 2 := by
    norm_num only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hcost : (∑ _ : Fin 2 → ZMod 2, ‖(1 : ℂ)‖) ≤ Real.exp 2 := by simpa using hc
  let S := weightedSum (fun r => Classical.choice (hF r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 2) hc hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod 2, (1 : ℂ) * (pairParityIndicator r x * F r x)) =
      (fun x => f (fun i => x i / 2)) := by
    funext x
    let r : Fin 2 → ZMod 2 := fun i => (x i : ZMod 2)
    rw [Finset.sum_eq_single r]
    · simp only [pairParityIndicator, r, ite_true, one_mul]
      apply E.substitutedValue_eq (P r) (hP r) x (fun i => x i / 2)
      exact halvingPolynomial_eval _ x (fun i => (ZMod.val_intCast (x i)).symm)
    · intro a _ ha
      have hne : (fun i => (x i : ZMod 2)) ≠ a := fun h => ha h.symm
      simp only [pairParityIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  have hb : (t + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [t, X, Polynomial.eval₂_pow] using hbudget p hp
  rw [heq] at S
  exact ⟨S.mono hb⟩

end Erdos3.NativeIntegerExpansion

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PositivePartitionIntegerExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_weighted_integer_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] {s N : ℕ} [NeZero N]
      {p : ℝ} {f : (σ → ℤ) → ℂ}
      (_E : NativeIntegerExpansion (fun _ : σ => 1) s p f),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → ∀ w : σ → ZMod N → ℝ,
      (∀ i, PositiveCyclicNiltest.{0} s N p (w i)) →
      ∃ g : (σ → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) g) ∧
        ∀ x : σ → ZMod N, g (fun i => ((x i).val : ℤ)) =
          (∏ i, (w i (x i) : ℂ)) * f (fun i => ((x i).val : ℤ)) := by
  obtain ⟨A, _, hprod⟩ := exists_productNiltestBudget_bound
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 2) ^ 2 + 3
  let Q := (Y + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ _ s N _ p f E hp hσ w hw
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  let q := (raisedNiltestBudget p + A) ^ A + p + 2
  have hpower : 0 ≤ (raisedNiltestBudget p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p ≤ q := by dsimp only [q]; linarith only [hpower]
  have hweight : productNiltestBudget (raisedNiltestBudget p) ≤ q :=
    (hprod _ hp').trans (by dsimp only [q]; linarith only [hp])
  have hqC : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [Q, Y, X, q, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨g, ⟨W⟩, he⟩ := exists_positive_coordinate_product hp hσ hw
  obtain ⟨G⟩ := hmul hq (W.mono hweight) (E.mono hpq)
  refine ⟨fun x => g x * f x, ⟨G.mono hqC⟩, ?_⟩
  intro x
  exact congrArg (fun z : ℂ => z * f (fun i => ((x i).val : ℤ))) (he x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_partition_integer_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} {I J : Type*} [Fintype σ] [Fintype I]
      {s N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ (w : I → σ → ZMod N → ℝ) (v : I → J → (σ → ℤ) → ℂ),
        (∀ i k, PositiveCyclicNiltest.{0} s N p (w i k)) →
        (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p (v i j))) →
        ∃ F : J → (σ → ℤ) → ℂ,
          (∀ j, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j))) ∧
          ∀ j (x : σ → ZMod N), F j (fun k => ((x k).val : ℤ)) =
            ∑ i, ((∏ k, w i k (x k) : ℝ) : ℂ) * v i j (fun k => ((x k).val : ℤ)) := by
  obtain ⟨A, _, hweighted⟩ := exists_positive_weighted_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s N _ p hp hσ hI w v hw hv
  classical
  have hfamily (i : I) (j : J) : ∃ g : (σ → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + A) ^ A) g) ∧
      ∀ x : σ → ZMod N, g (fun k => ((x k).val : ℤ)) =
        ((∏ k, w i k (x k) : ℝ) : ℂ) * v i j (fun k => ((x k).val : ℤ)) := by
    obtain ⟨g, hg, he⟩ := hweighted (Classical.choice (hv i j)) hp hσ (w i) (hw i)
    exact ⟨g, hg, fun x => by simpa only [Complex.ofReal_prod] using he x⟩
  choose g hg he using hfamily
  let F := fun (j : J) (x : σ → ℤ) => ∑ i, g i j x
  have hcost : (p + A) ^ A + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨F, ?_, ?_⟩
  · intro j
    have hc : (∑ _i : I, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hI
    exact ⟨by simpa only [F, one_mul] using
      ((NativeIntegerExpansion.weightedSum (fun i => Classical.choice (hg i j))
        (fun _ => 1) hp hI hc).mono hcost)⟩
  · intro j x
    exact Finset.sum_congr rfl (fun i _ => he i j x)

end Erdos3

end

end OAI

end


