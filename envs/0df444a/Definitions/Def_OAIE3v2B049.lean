-- Prove2me | Definitions.Def_OAIE3v2B049
-- name    : OAIE3v2B049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:14:12.179256+00:00
-- url     : https://prove2.me/theorems/5c31c298-826c-46c0-a0f9-e519cd3df1b2
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 50 of 311
-- statement:
--   Definitions bundle 50 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B007`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017` of this split.
--
--   Modules: `Dynamics/CoefficientProfileBudget.lean`, `Dynamics/IntervalSplitBudget.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/DenseCorrelationPairs.lean`, `Estimates/InactiveAxisScale.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/LocalMomentScale.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/PeelingDecomposition.lean`, `Estimates/PowerIndexFromOrderedGenerators.lean`, `Estimates/PowerSubgroup.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/RealifiedDilationMultidegree.lean`, `Estimates/ShiftTestingGowers.lean`, `Estimates/SquarefreeExponents.lean`, `Estimates/SquarefreeStructureHeight.lean`, `Estimates/WeightedSummandCorrelation.lean`, `Geometry/CoordinateSubstitutionAlgebra.lean`, `Geometry/EmbeddingCoordinateHeight.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Geometry/RealSupportedQuotientCoordinates.lean`, `Geometry/RealifiedPairCoordinates.lean`, `Geometry/RealifiedTripleCoordinates.lean`, `Geometry/SupportedCorrelationPairs.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/EuclideanShortLatticeBasis.lean`, `Lattices/IntegerAffineSubstitution.lean`, `Lattices/IntegerAxisPrincipalLaw.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/PrimeCoordinateCells.lean`, `Linear/BoundedAdaptedBasis.lean`, `Linear/MahlerBasis.lean`, `Linear/ProperCyclicKernelBasis.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Nilpotent/NiltestComplement.lean`, `Nilpotent/SquarefreeBracketHeight.lean`, `Polynomial/RealPositivePolynomialEvaluation.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Probability/InactivePrincipalLaw.lean`, `Probability/ScalarCubeBoundaryMass.lean`, `Probability/ScalarCubeDomainDensity.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientProfileBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coefficientProfile_budget {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {ρ γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 ≤ ε) :
    (∑ j, (|coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j)) ≤
      ρ + 2 * γ * P.card + ε * Fintype.card J := by
  classical
  have hpoint (j : J) : |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j ≤
      (if j = j₀ then ρ else 0) + (if j ∈ P then 2 * γ else 0) + ε := by
    by_cases hj : j = j₀
    · subst j
      simp [coefficientProfileCenter, coefficientProfileWidth, hj₀, hε]
    · by_cases hP : j ∈ P
      · have hpos : 0 ≤ 3 * γ / 2 := by positivity
        simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hP,
          ↓reduceIte, abs_of_nonneg hpos]
        linarith
      · simp [coefficientProfileCenter, coefficientProfileWidth, hj, hP]
  calc
    _ ≤ ∑ j, ((if j = j₀ then ρ else 0) + (if j ∈ P then 2 * γ else 0) + ε) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite_mem]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem finiteCorrelation_sub_right {Ω : Type*} (Q : Finset Ω) (f u v : Ω → ℂ) :
    finiteCorrelation Q f (fun x => u x - v x) =
      finiteCorrelation Q f u - finiteCorrelation Q f v := by
  simp only [finiteCorrelation, star_sub, mul_sub, Finset.expect_sub_distrib]

theorem finiteCorrelation_sum_right {Ω J : Type*} [Fintype J]
    (Q : Finset Ω) (f : Ω → ℂ) (u : J → Ω → ℂ) :
    finiteCorrelation Q f (fun x => ∑ j, u j x) = ∑ j, finiteCorrelation Q f (u j) := by
  simp only [finiteCorrelation, star_sum, Finset.mul_sum, Finset.expect_sum_comm]

theorem norm_finiteCorrelation_le {Ω : Type*} {Q : Finset Ω} (hQ : Q.Nonempty)
    (f u : Ω → ℂ) {B : ℝ} (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B) :
    ‖finiteCorrelation Q f u‖ ≤ B := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const hQ B)
  intro x hx
  simpa only [norm_mul, norm_star, one_mul] using
    mul_le_mul (hf x hx) (hu x hx) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

theorem mem_denominatorGrid_iff (L : ℕ) (hL : 0 < L) (x : ι → ℚ) :
    x ∈ denominatorGrid L ↔ ∃ z : ι → ℤ, ∀ i, x i = (z i : ℚ) / L := by
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    apply (eq_div_iff hLq).mpr
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hz i
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    change (L : ℚ) * x i = (z i : ℚ)
    rw [hz i, mul_div_cancel₀ _ hLq]

end Erdos3

end

section

namespace Erdos3

theorem rational_grid_height_le_exp (n d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((H ^ (n * d) * rationalSolveHeight d H ^ (d * n) : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
  have hsolve := rationalSolveHeight_le_budget d H hp hd hH
  have hA := pow_le_pow_left₀ (Nat.cast_nonneg H) hH (n * d)
  have hC := pow_le_pow_left₀ (Nat.cast_nonneg (rationalSolveHeight d H)) hsolve (d * n)
  rw [← Real.exp_nat_mul] at hA hC
  have hlog : p + (p + 2) ^ 5 ≤ (p + 2) ^ 6 := by
    have hp5 := le_power_budget hp (by decide : 1 ≤ 5)
    calc
      _ ≤ 2 * (p + 2) ^ 5 := by linarith
      _ ≤ (p + 2) * (p + 2) ^ 5 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  push_cast
  calc
    _ ≤ Real.exp ((n * d : ℕ) * p) * Real.exp ((d * n : ℕ) * (p + 2) ^ 5) :=
      mul_le_mul hA hC (by positivity) (by positivity)
    _ = Real.exp ((n : ℝ) * d * (p + (p + 2) ^ 5)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    _ ≤ Real.exp ((p + 2) ^ 2 * (p + 2) ^ 6) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul _ hlog (by positivity) (by positivity)
      calc
        (n : ℝ) * d ≤ (p + 2) * (p + 2) := by gcongr <;> linarith
        _ = (p + 2) ^ 2 := by ring
    _ = _ := by rw [← pow_add]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem scaled_grid_mulVec (B : Matrix ι κ ℚ) (l : ℕ) (x : κ → ℚ)
    (hx : IntegralVector (B *ᵥ x)) : B *ᵥ ((l : ℚ) • x) ∈ scaledIntegerGrid l := by
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, by rw [Matrix.mulVec_smul, funext hz]⟩

theorem grid_allowance_mul_le_exp {p : ℝ} (hp : 0 ≤ p) {l K : ℕ}
    (hl : (l : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp ((p + 2) ^ 8)) :
    ((l * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 8) := by
      rw [Nat.cast_mul]
      exact mul_le_mul hl hK (Nat.cast_nonneg _) (by positivity)
    _ = Real.exp (p + (p + 2) ^ 8) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ 9) := by
      apply Real.exp_le_exp.mpr
      have hp8 := le_power_budget hp (by decide : 1 ≤ 8)
      calc
        _ ≤ 2 * (p + 2) ^ 8 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 8 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeExponents
namespace OAI

section

namespace Erdos3

theorem card_squarefreeIndex (ι : Type*) [Fintype ι] :
    Fintype.card (SquarefreeIndex ι) = 2 ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (squarefreeIndexEquiv ι), Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftTestingGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_absolute_cauchy_schwarz {H Ω : Type*} [Fintype H] [Fintype Ω]
    [Nonempty Ω] (B : Ω → ℂ) (v : H → Ω → ℂ) {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, B x * v h x‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k, ‖𝔼 x, v h x * star (v k x)‖) := by
  choose a ha hphase using fun h => exists_complex_unit_phase (𝔼 x, B x * v h x)
  have havg : (𝔼 x, B x * (𝔼 h, a h * v h x)) =
      ((𝔼 h, ‖𝔼 x, B x * v h x‖) : ℝ) := by
    calc
      _ = 𝔼 h, a h * (𝔼 x, B x * v h x) := by
        simp_rw [Finset.mul_expect]
        rw [Finset.expect_comm]
        apply Finset.expect_congr rfl
        intro h _
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = _ := by simp_rw [hphase]; simp [Fintype.expect_eq_sum_div_card]
  have hcross (h k : H) :
      ‖𝔼 x, (a h * v h x) * star (a k * v k x)‖ =
        ‖𝔼 x, v h x * star (v k x)‖ := by
    have hid : (𝔼 x, (a h * v h x) * star (a k * v k x)) =
        (a h * star (a k)) * (𝔼 x, v h x * star (v k x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [star_mul]
      ring
    rw [hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]
  have hcs := finite_family_cauchy_schwarz B (fun h x => a h * v h x) hB
  rw [havg, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [hcross] using hcs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_correlation_pairs {I X : Type*} [Fintype I] [Nonempty I]
    [Fintype X] [Nonempty X] (B : X → ℂ) (v : I → X → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hB : ∀ x, ‖B x‖ ≤ 1) (hv : ∀ i x, ‖v i x‖ ≤ 1)
    (hcorr : ∀ i, δ ≤ ‖𝔼 x, B x * v i x‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, δ ^ 2 / 2 ≤ ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
  have hmean : δ ≤ 𝔼 i, ‖𝔼 x, B x * v i x‖ := by
    simpa only [Fintype.expect_const] using
      Finset.expect_le_expect (s := Finset.univ) (fun i _ => hcorr i)
  have hcs := finite_absolute_cauchy_schwarz B v hB
  have hcross : δ ^ 2 ≤ 𝔼 t : I × I, ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
    have h := (pow_le_pow_left₀ hδ.le hmean 2).trans hcs
    simpa only [one_pow, one_mul, ← Finset.univ_product_univ, Finset.expect_product] using h
  have hunit (t : I × I) : ‖𝔼 x, v t.1 x * star (v t.2 x)‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect _).trans_eq (Fintype.expect_const _)
    intro x _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv t.1 x)).trans (hv t.2 x)
  obtain ⟨P, hsize, hP⟩ := exists_dense_level_set
    (fun t : I × I => ‖𝔼 x, v t.1 x * star (v t.2 x)‖) (sq_nonneg δ) hunit hcross
  have hsize' : δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hsize
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hsize'
  exact ⟨P, Finset.card_pos.mp (by exact_mod_cast hpos), hsize', hP⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem multiplicativeDerivative_norm_le_one (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (h x : G) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
  simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
    mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem integerBox_nonempty : (integerBox T).Nonempty := by
  refine ⟨0, (mem_integerBox T 0).mpr ?_⟩
  intro i
  change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < T i
  exact ⟨le_rfl, by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (T i))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeDomainDensity (α : Type*) [Fintype α] [DecidableEq α] : ℝ :=
  (volume.real (scalarCubeDomain α))⁻¹

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeBoundaryConstant (α : Type*) [Fintype α] [DecidableEq α] : ℝ :=
  4 * scalarCubeDomainDensity α * ((2 : ℝ) ^ Fintype.card α) ^ 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem multidegreeWeight_mono {σ : Type*} [Fintype σ] (c : σ → ℕ) {a b : σ → ℕ}
    (hab : a ≤ b) : multidegreeWeight c a ≤ multidegreeWeight c b :=
  Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (c i) (hab i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedTripleCoordinates
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def realTripleEquiv :
    (ℝ ⊗[ℚ] (L × L × L)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) :=
  (TensorProduct.prodRight ℚ ℝ ℝ L (L × L)).trans
    ((LinearEquiv.refl ℝ (ℝ ⊗[ℚ] L)).prodCongr (TensorProduct.prodRight ℚ ℝ ℝ L L))

@[simp] theorem realTripleEquiv_tmul (r : ℝ) (x : L × L × L) :
    realTripleEquiv (r ⊗ₜ[ℚ] x) = (r ⊗ₜ[ℚ] x.1, r ⊗ₜ[ℚ] x.2.1, r ⊗ₜ[ℚ] x.2.2) := rfl

theorem realTripleEquiv_neutral (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleNeutral (realTripleEquiv x) =
      (tripleNeutral : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.2.1 + r ⊗ₜ[ℚ] x.2.2 - r ⊗ₜ[ℚ] x.1 =
      r ⊗ₜ[ℚ] (x.2.1 + x.2.2 - x.1)
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realTripleEquiv_left (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleLeft (realTripleEquiv x) =
      (tripleLeft : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.1 - r ⊗ₜ[ℚ] x.2.2 = r ⊗ₜ[ℚ] (x.1 - x.2.2)
    rw [TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realTripleEquiv_right (x : ℝ ⊗[ℚ] (L × L × L)) :
    tripleRight (realTripleEquiv x) =
      (tripleRight : (L × L × L) →ₗ[ℚ] L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realTripleEquiv_tmul, LinearMap.baseChange_tmul]
    change r ⊗ₜ[ℚ] x.1 - r ⊗ₜ[ℚ] x.2.1 = r ⊗ₜ[ℚ] (x.1 - x.2.1)
    rw [TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

abbrev LieTreeOccurrences : FreeMagma I → Type
  | .of _ => Unit
  | .mul a b => LieTreeOccurrences a ⊕ LieTreeOccurrences b

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realification_inf {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P Q : Submodule ℚ V) :
    (P ⊓ Q).baseChange ℝ = P.baseChange ℝ ⊓ Q.baseChange ℝ := by
  have hker : LinearMap.ker (P.mkQ.prod Q.mkQ) = P ⊓ Q := by
    ext v
    change (P.mkQ v, Q.mkQ v) = (0, 0) ↔ v ∈ P ∧ v ∈ Q
    rw [Prod.mk.injEq]
    exact and_congr (Submodule.Quotient.mk_eq_zero P) (Submodule.Quotient.mk_eq_zero Q)
  rw [← hker, realification_ker]
  ext v
  rw [LinearMap.mem_ker, realification_prod_eq_zero_iff,
    realification_mkQ_eq_zero_iff, realification_mkQ_eq_zero_iff, Submodule.mem_inf]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateSubstitutionAlgebra
namespace OAI

section

namespace Erdos3

variable {σ R S : Type*} [DecidableEq σ] [CommRing R] [CommRing S] [Algebra R S]

theorem aeval_monomial_update (f : σ → S) (i : σ) (u : S) (a : σ →₀ ℕ) :
    MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) =
      u ^ a i * (a.erase i).prod (fun j n => f j ^ n) := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    ← Finsupp.mul_prod_erase' a i (fun j n => Function.update f i u j ^ n) (fun _ => pow_zero _)]
  rw [Function.update_self]
  congr 1
  apply Finsupp.prod_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    simp only [Finsupp.mem_support_iff, Finsupp.erase_same, ne_eq, not_true_eq_false] at hj
  rw [Function.update_of_ne hji]

theorem aeval_monomial_update_eq_of_zero (f : σ → S) (i : σ) (u v : S)
    (a : σ →₀ ℕ) (ha : a i = 0) :
    MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) =
      MvPolynomial.aeval (R := R) (Function.update f i v) (MvPolynomial.monomial a 1) := by
  simp only [aeval_monomial_update, ha, pow_zero]

theorem aeval_monomial_update_add (f : σ → S) (i : σ) (u v : S)
    (a : σ →₀ ℕ) (ha : a i ≤ 1) :
    MvPolynomial.aeval (R := R) (Function.update f i (u + v)) (MvPolynomial.monomial a 1) =
      MvPolynomial.aeval (R := R) (Function.update f i u) (MvPolynomial.monomial a 1) +
      MvPolynomial.aeval (R := R) (Function.update f i v) (MvPolynomial.monomial a 1) -
      MvPolynomial.aeval (R := R) (Function.update f i 0) (MvPolynomial.monomial a 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h <;>
    simp only [aeval_monomial_update, h, pow_zero, pow_one] <;> ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

theorem omittedCoordinateWeight_total [Fintype σ] (i : σ) (bound : σ → ℕ) :
    multidegreeWeight (omittedCoordinateWeight i) bound + bound i = ∑ j, bound j := by
  have h (j : σ) : omittedCoordinateWeight i j * bound j + (if j = i then bound i else 0) = bound j := by
    by_cases hj : j = i <;> simp [omittedCoordinateWeight, hj]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => h j)
  simpa [Finset.sum_add_distrib, multidegreeWeight] using hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3

open Module
open scoped NNReal

theorem coordinateLipschitzBound_power_budget (d D : ℕ) (hD : 2 ≤ D) (B : ℝ≥0)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hB : (B : ℝ) ≤ Real.exp ((p + D) ^ D)) :
    (coordinateLipschitzBound d d B : ℝ) ≤
      Real.exp ((p + ((D + 2) * 2 : ℕ)) ^ ((D + 2) * 2)) := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hq : 0 ≤ (p + D) ^ D := by positivity
  have hpq : p ≤ (p + D) ^ D := by
    calc
      p ≤ p + D := by linarith
      _ ≤ (p + D) ^ D := by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + D)
          (by omega : 1 ≤ D)
  apply (coordinateLipschitzBound_le_exp d d B hq (hd.trans hpq) (hd.trans hpq) hB).trans
  apply Real.exp_le_exp.mpr
  have hshift := shifted_power_budget_le (p := p + D - 2) (by linarith) D 2
  rw [show p + D - 2 + 2 = p + D by ring] at hshift
  apply hshift.trans
  apply pow_le_pow_left₀ (by positivity)
  have hDE : D ≤ (D + 2) * 2 := by omega
  exact add_le_add le_rfl (Nat.cast_le.mpr hDE)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

open scoped BigOperators

noncomputable def integerScalarCubeSet (I : Type*) [Fintype I] (L : ℕ) :
    Finset (IntegerScalarCubeBox I L) := by
  classical
  exact Finset.univ.filter (fun x => IntegerScalarCube L (fun i => (x i : ℤ)))

theorem mem_integerScalarCubeSet {I : Type*} [Fintype I] (L : ℕ)
    (x : IntegerScalarCubeBox I L) :
    x ∈ integerScalarCubeSet I L ↔ IntegerScalarCube L (fun i => (x i : ℤ)) := by
  classical
  simp [integerScalarCubeSet]

end Erdos3


namespace Erdos3

def integerScalarCubeBoxZero (I : Type*) (L : ℕ) (hL : 0 < L) : IntegerScalarCubeBox I L :=
  fun _ => ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast hL⟩⟩

theorem integerScalarCubeSet_nonempty (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L) :
    (integerScalarCubeSet I L).Nonempty := by
  refine ⟨integerScalarCubeBoxZero I L hL, (mem_integerScalarCubeSet L _).mpr ?_⟩
  intro t
  simp only [integerScalarCubeValue, integerScalarCubeBoxZero, Finset.sum_const_zero, add_zero]
  exact ⟨le_rfl, by exact_mod_cast hL⟩

theorem integerScalarCubeBox_card (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) :
    Fintype.card (IntegerScalarCubeBox I L) = (2 * L) ^ (Fintype.card I + 1) := by
  change Fintype.card (Option I → Finset.Ico (-(L : ℤ)) (L : ℤ)) = _
  rw [Fintype.card_fun, Fintype.card_option, Fintype.card_coe, Int.card_Ico]
  congr 1
  omega


noncomputable def scalarCubeResidueSet (I : Type*) [Fintype I] (L : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) : Finset (IntegerScalarCubeBox I L) := by
  classical
  exact Finset.univ.filter (fun x => ∀ i, ((x i : ℤ) : ZMod (m i)) = r i)

theorem mem_scalarCubeResidueSet {I : Type*} [Fintype I] (L : ℕ)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (x : IntegerScalarCubeBox I L) :
    x ∈ scalarCubeResidueSet I L m r ↔ ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  simp only [scalarCubeResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem scalarCubeResidueSet_card_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L M H : ℕ) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hH : 0 < H)
    (hbudget : (Fintype.card I + 1) * (M * H) ≤ L) :
    H ^ (Fintype.card I + 1) ≤ ((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r).card := by
  classical
  have hM : 0 < M := (hm none).trans_le (hmM none)
  have hML : M * H ≤ L := by nlinarith
  let point (x : Option I → Fin H) (i : Option I) : Fin (M * H) :=
    ⟨(r i).val + m i * (x i).val,
      (scalarResiduePoint_bound (m i) H (hm i) (r i) (x i)).trans_le (Nat.mul_le_mul_right H (hmM i))⟩
  let tuple (x : Option I → Fin H) : IntegerScalarCubeBox I L := fun i =>
    ⟨((point x i).val : ℤ), Finset.mem_Ico.mpr
      ⟨by omega, by have := (point x i).isLt; omega⟩⟩
  have hmem (x : Option I → Fin H) :
      tuple x ∈ (integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (mem_integerScalarCubeSet L _).mpr
        (integerScalarCube_small_positive (Nat.mul_pos hM hH) hbudget (point x))
    · apply (mem_scalarCubeResidueSet L m r _).mpr
      intro i
      change ((((r i).val + m i * (x i).val : ℕ) : ℤ) : ZMod (m i)) = r i
      simpa only [Int.cast_natCast] using scalarResiduePoint_cast (m i) (hm i) (r i) (x i).val
  let e : (Option I → Fin H) → ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) :=
    fun x => ⟨tuple x, hmem x⟩
  have he : Function.Injective e := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrArg (fun z : ↥((integerScalarCubeSet I L) ∩ scalarCubeResidueSet I L m r) =>
      (z.val i : ℤ)) h
    change (((r i).val + m i * (x i).val : ℕ) : ℤ) = (((r i).val + m i * (y i).val : ℕ) : ℤ) at hi
    have hi' : (r i).val + m i * (x i).val = (r i).val + m i * (y i).val := by exact_mod_cast hi
    exact mul_left_cancel₀ (hm i).ne' (Nat.add_left_cancel hi')
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe] using hc


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem remainder_nonneg (C : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    0 ≤ remainder C f x := by
  by_cases hx : x ∈ C <;> simp [remainder, hx, hf x]

omit [Fintype G] in
theorem remainder_le (C : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    remainder C f x ≤ f x := by
  by_cases hx : x ∈ C <;> simp [remainder, hx, hf x]

end Erdos3.Peeling


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

inductive Chain (B : Finset G) (Admissible : Finset G → Prop) (K kappa : ℝ) :
    (G → ℝ) → (G → ℝ) → List (Finset G) → Prop
  | nil (f : G → ℝ) : Chain B Admissible K kappa f f []
  | step {f g : G → ℝ} {cs : List (Finset G)} (C : Finset G)
      (active : kappa ≤ 𝔼 x ∈ B, f x)
      (admissible : Admissible C)
      (concentrated : K * (𝔼 x ∈ B, f x) < 𝔼 x ∈ C, f x)
      (tail : Chain B Admissible K kappa (remainder C f) g cs) :
      Chain B Admissible K kappa f g (C :: cs)

namespace Chain

variable {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
  {f g : G → ℝ} {cs : List (Finset G)}

omit [Fintype G] in
theorem bounds (h : Chain B Admissible K kappa f g cs) :
    (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ g x ∧ g x ≤ f x := by
  induction h with
  | nil f => intro hf x; exact ⟨hf x, le_rfl⟩
  | @step f g cs C _ _ _ _ ih =>
    intro hf x
    obtain ⟨hg, hgf⟩ := ih (remainder_nonneg C f hf) x
    exact ⟨hg, hgf.trans (remainder_le C f hf x)⟩

omit [Fintype G] in
theorem supported (h : Chain B Admissible K kappa f g cs)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    ∀ x, x ∉ B → g x = 0 := by
  intro x hx
  have hb := h.bounds hf x
  have hz := hsupport x hx
  linarith

end Chain
end Erdos3.Peeling


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerSubgroup
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

theorem powerSubgroup_map_le (f : G →* G) (m : ℕ) :
    (powerSubgroup G m).map f ≤ powerSubgroup G m := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨g, rfl⟩
  change f (g ^ m) ∈ powerSubgroup G m
  rw [map_pow]
  exact pow_mem_powerSubgroup _ _

instance powerSubgroup_characteristic (m : ℕ) : (powerSubgroup G m).Characteristic :=
  Subgroup.characteristic_iff_map_le.mpr (fun f => powerSubgroup_map_le f.toMonoidHom m)

theorem subgroupPowerCover_subgroupOf (Γ : Subgroup G) (m : ℕ) :
    (subgroupPowerCover Γ m).subgroupOf Γ = powerSubgroup Γ m := by
  change ((powerSubgroup Γ m).map Γ.subtype).comap Γ.subtype = _
  exact Subgroup.comap_map_eq_self_of_injective (f := Γ.subtype) Subtype.val_injective _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

theorem basisTail_antitone (e : Basis (Fin d) ℚ L) : Antitone (basisTail e) :=
  fun _ _ hij _ hx k hk => hx k (lt_of_lt_of_le hk hij)

theorem basisTail_zero (e : Basis (Fin d) ℚ L) : basisTail e 0 = ⊤ := by
  apply top_unique
  intro x _ j hj
  omega

theorem basisTail_terminal (e : Basis (Fin d) ℚ L) : basisTail e d = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply e.repr.injective
  ext j
  simpa only [map_zero, Finsupp.zero_apply] using hx j j.isLt

theorem mem_basisTail_succ_iff (e : Basis (Fin d) ℚ L) (j : Fin d) (x : L) :
    x ∈ basisTail e (j.val + 1) ↔ x ∈ basisTail e j.val ∧ e.repr x j = 0 := by
  constructor
  · intro hx
    exact ⟨basisTail_antitone e (Nat.le_succ j.val) hx, hx j (Nat.lt_succ_self j.val)⟩
  · rintro ⟨hx, hj⟩ k hk
    by_cases hkj : k = j
    · simpa only [hkj] using hj
    · apply hx k
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega

namespace IsCentralLieBasis

variable {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
include he

theorem lie_mem_tail_succ (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i) :
    ⁅a, b⁆ ∈ basisTail e (i + 1) := by
  classical
  rw [← e.sum_repr b, lie_sum]
  apply Submodule.sum_mem
  intro j _
  rw [lie_smul]
  by_cases hj : j.val < i
  · rw [hb j hj, zero_smul]
    exact (basisTail e (i + 1)).zero_mem
  · exact (basisTail e (i + 1)).smul_mem _
      (basisTail_antitone e (Nat.add_le_add_right (Nat.le_of_not_gt hj) 1) (he j a))

def tailIdeal (i : ℕ) : LieIdeal ℚ L :=
  { basisTail e i with
    lie_mem := by
      intro a b hb
      exact basisTail_antitone e (Nat.le_succ i) (he.lie_mem_tail_succ i a hb) }

end IsCentralLieBasis

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {d : ℕ}

namespace IsRealCentralLieBasis

variable {e : Basis (Fin d) ℝ L} (he : IsRealCentralLieBasis e)
include he

noncomputable def tailIdeal [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L] (i : ℕ) : LieIdeal ℚ L :=
  { (realBasisTail e i).restrictScalars ℚ with
    lie_mem := by
      intro a b hb
      exact realBasisTail_antitone e (Nat.le_succ i) (he.lie_mem_tail_succ i a hb) }

end IsRealCentralLieBasis

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerIndexFromOrderedGenerators
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G] {d : ℕ}

theorem powerSubgroup_index_le_of_ordered_generators (a : Fin d → G)
    (hgen : Function.Surjective (orderedZpowProduct a)) (m : ℕ) (hm : 0 < m) :
    (powerSubgroup G m).FiniteIndex ∧ (powerSubgroup G m).index ≤ m ^ d := by
  let Q := G ⧸ powerSubgroup G m
  let q : G →* Q := QuotientGroup.mk' _
  let f : (Fin d → Fin m) → Q := fun r => orderedGroupProduct (fun j => q (a j) ^ (r j).val)
  have hpow (j : Fin d) : q (a j) ^ m = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (pow_mem_powerSubgroup (a j) m)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, rfl⟩ := hgen g
    obtain ⟨r, hr⟩ := exists_bounded_ordered_exponents (fun j => q (a j)) m hm hpow z
    refine ⟨r, ?_⟩
    change orderedGroupProduct (fun j => q (a j) ^ (r j).val) = q (orderedZpowProduct a z)
    rw [orderedZpowProduct_map]
    exact hr
  let : Finite Q := Finite.of_surjective f hf
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  change Nat.card Q ≤ m ^ d
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using
    Nat.card_le_card_of_surjective f hf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeStructureHeight
namespace OAI

section

namespace Erdos3

open Module

def squarefreeStructureHeight (n H : ℕ) : ℕ :=
  (n + 1) * (rationalSolveHeight n H * squarefreeBracketHeight n H) ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem integerAffinePolynomial_eval (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) (i : σ) :
    MvPolynomial.aeval (fun j => (x j : ℚ)) (integerAffinePolynomial A b i) =
      (integerAffineMap A b x i : ℚ) := by
  simp [integerAffinePolynomial, integerAffineMap]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmbeddingCoordinateHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem embedding_coordinate_height_budget (n d H K : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    (((n + 1) * (rationalSolveHeight d H * K) ^ n : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
  have hproduct : ((rationalSolveHeight d H * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 6) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 5) * Real.exp p :=
        mul_le_mul (rationalSolveHeight_le_budget d H hp hd hH) hK (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((p + 2) ^ 5 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hpp : p ≤ (p + 2) ^ 5 := le_power_budget hp (by decide)
        calc
          _ ≤ 2 * (p + 2) ^ 5 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 5 := by gcongr; linarith
          _ = (p + 2) ^ 6 := by ring
  exact rational_sum_cost_le_exp n _ hp 6 1 hproduct (by simpa only [pow_one] using hn.trans (by linarith))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MahlerBasis
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

@[simp]
theorem integralEmbed_add {n : ℕ} (x y : IntegralPoint n) :
    integralEmbed (x + y) = integralEmbed x + integralEmbed y := by
  ext i
  simp [integralEmbed]

@[simp]
theorem integralEmbed_zsmul {n : ℕ} (a : ℤ) (x : IntegralPoint n) :
    integralEmbed (a • x) = (a : ℝ) • integralEmbed x := by
  ext i
  simp [integralEmbed]

end Erdos3.IntegerBasisReduction.Mahler

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProperCyclicKernelBasis
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

def IsCenteredReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (a : Fin n → Fin n → ℝ) : Prop :=
  ∀ i,
    integralEmbed (b i) = ∑ j, a i j • integralEmbed (x j) ∧
    (∀ j, i < j → a i j = 0) ∧
    ((|a i i| = 1 ∧ ∀ j, j < i → a i j = 0) ∨
      ∀ j, j ≤ i → |a i j| ≤ (1 : ℝ) / 2)

def IsRawFlagReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
  (u : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, integralEmbed (b i) = ∑ j, u i j • integralEmbed (x j)) ∧
  (∀ i j, i < j → u i j = 0) ∧
  (∀ i j, i < j → b.repr (x i) j = 0) ∧
  ∀ i, b.repr (x i) i ≠ 0 ∧
    ((b.repr (x i) i : ℝ) * u i i = 1)

theorem exists_rawFlagReduction_of_linearIndependent {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i))) :
    ∃ (b : Basis (Fin n) ℤ (IntegralPoint n))
      (u : Fin n → Fin n → ℝ), IsRawFlagReduction x b u := by
  classical
  have hrealEmbed (z : IntegralPoint n) :
      SaturatedFlag.realEmbed n z = integralEmbed z := by
    ext j
    rfl
  have hli' : LinearIndependent ℝ
      (fun i ↦ SaturatedFlag.realEmbed n (x i)) := by
    simpa only [hrealEmbed] using hli
  obtain ⟨b, hprefix, hxrepr, hxdiag⟩ :=
    SaturatedFlag.exists_prefix_adapted_basis_realPrefixLattice x hli'
  let xb : Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun i ↦ integralEmbed (x i)) hli (by simp)
  let u : Fin n → Fin n → ℝ :=
    fun i j ↦ xb.repr (integralEmbed (b i)) j
  have hxb (i : Fin n) : xb i = integralEmbed (x i) := by
    simp [xb]
  have hexpand (i : Fin n) :
      integralEmbed (b i) = ∑ j, u i j • integralEmbed (x j) := by
    simpa only [hxb] using (xb.sum_repr (integralEmbed (b i))).symm
  have htri : ∀ i j, i < j → u i j = 0 := by
    intro i j hij
    have hbi : b i ∈ SaturatedFlag.realPrefixLattice x i := by
      rw [hprefix i]
      apply Submodule.subset_span
      exact ⟨i, Set.mem_Iic.mpr le_rfl, rfl⟩
    have hbispan : integralEmbed (b i) ∈
        Submodule.span ℝ (xb '' Set.Iic i) := by
      have hm := SaturatedFlag.mem_realPrefixLattice.mp hbi
      have himage : SaturatedFlag.realEmbed n '' (x '' Set.Iic i) =
          xb '' Set.Iic i := by
        ext y
        constructor
        · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
          exact ⟨k, hk, (hxb k).trans (hrealEmbed (x k)).symm⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨x k, ⟨k, hk, rfl⟩,
            (hrealEmbed (x k)).trans (hxb k).symm⟩
      rw [himage] at hm
      rw [hrealEmbed] at hm
      exact hm
    have hsupp := xb.repr_support_subset_of_mem_span (Set.Iic i) hbispan
    by_contra hne
    have hjmem : j ∈ Set.Iic i :=
      hsupp (Finsupp.mem_support_iff.mpr hne)
    exact (not_le_of_gt hij) (Set.mem_Iic.mp hjmem)
  refine ⟨b, u, hexpand, htri, hxrepr, ?_⟩
  intro i
  have hxreal :
      ∑ j, (b.repr (x i) j : ℝ) • integralEmbed (b j) =
        integralEmbed (x i) := by
    calc
      (∑ j, (b.repr (x i) j : ℝ) • integralEmbed (b j)) =
          integralEmbed (∑ j, b.repr (x i) j • b j) := by
        ext k
        simp [integralEmbed]
      _ = integralEmbed (x i) := congrArg integralEmbed (b.sum_repr (x i))
  have hcoord := congrArg (fun y : Fin n → ℝ ↦ xb.repr y i) hxreal
  have hrhs : xb.repr (integralEmbed (x i)) i = 1 := by
    rw [← hxb]
    simp
  rw [hrhs] at hcoord
  have hcoord' :
      ∑ j, (b.repr (x i) j : ℝ) * u j i = 1 := by
    simpa [u, hxb] using hcoord
  have hsingle :
      (∑ j, (b.repr (x i) j : ℝ) * u j i) =
        (b.repr (x i) i : ℝ) * u i i := by
    apply Finset.sum_eq_single i
    · intro j _hj hji
      rcases lt_or_gt_of_ne hji with hji | hij
      · rw [htri j i hji]
        simp
      · rw [hxrepr i j hij]
        simp
    · simp
  have hrecip : (b.repr (x i) i : ℝ) * u i i = 1 := by
    rw [← hsingle]
    exact hcoord'
  exact ⟨hxdiag i, hrecip⟩

theorem rawFlagReduction_diag_abs_le_one {n : ℕ}
    {x : Fin n → IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegralPoint n)}
    {u : Fin n → Fin n → ℝ}
    (hraw : IsRawFlagReduction x b u) (i : Fin n) :
    |u i i| ≤ 1 := by
  have hcne := (hraw.2.2.2 i).1
  have hrecip := (hraw.2.2.2 i).2
  have hcabsZ : (1 : ℤ) ≤ |b.repr (x i) i| := by
    have hpos : (0 : ℤ) < |b.repr (x i) i| := abs_pos.mpr hcne
    omega
  have hcabs : (1 : ℝ) ≤ |(b.repr (x i) i : ℝ)| := by
    exact_mod_cast hcabsZ
  have habsprod : |(b.repr (x i) i : ℝ)| * |u i i| = 1 := by
    rw [← abs_mul, hrecip, abs_one]
  nlinarith [abs_nonneg (u i i)]

theorem rawFlagReduction_diag_abs_le_half_of_not_unit {n : ℕ}
    {x : Fin n → IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegralPoint n)}
    {u : Fin n → Fin n → ℝ}
    (hraw : IsRawFlagReduction x b u) (i : Fin n)
    (hnot : |b.repr (x i) i| ≠ 1) :
    |u i i| ≤ (1 : ℝ) / 2 := by
  have hcne := (hraw.2.2.2 i).1
  have hrecip := (hraw.2.2.2 i).2
  have hcabsZ : (2 : ℤ) ≤ |b.repr (x i) i| := by
    have hpos : (0 : ℤ) < |b.repr (x i) i| := abs_pos.mpr hcne
    omega
  have hcabs : (2 : ℝ) ≤ |(b.repr (x i) i : ℝ)| := by
    exact_mod_cast hcabsZ
  have habsprod : |(b.repr (x i) i : ℝ)| * |u i i| = 1 := by
    rw [← abs_mul, hrecip, abs_one]
  nlinarith [abs_nonneg (u i i)]

@[simp] theorem prefixIndex_val {n : ℕ} (i : Fin n) (j : Fin i.val) :
    (prefixIndex i j).val = j.val := rfl

theorem prefixIndex_lt {n : ℕ} (i : Fin n) (j : Fin i.val) :
    prefixIndex i j < i := j.isLt

theorem exists_prefix_integerCombination_abs_le_half {n : ℕ}
    (u : Fin n → Fin n → ℝ)
    (htri : ∀ j h, j < h → u j h = 0)
    (hne : ∀ j, u j j ≠ 0)
    (hle : ∀ j, |u j j| ≤ (1 : ℝ))
    (r : Fin n → ℝ) (i : Fin n) :
    ∃ t : Fin i.val → ℤ, ∀ h : Fin i.val,
      |r (prefixIndex i h) +
        ∑ j, (t j : ℝ) * u (prefixIndex i j) (prefixIndex i h)| ≤
          (1 : ℝ) / 2 := by
  let up : Fin i.val → Fin i.val → ℝ :=
    fun j h ↦ u (prefixIndex i j) (prefixIndex i h)
  have htrip : ∀ j h, j < h → up j h = 0 := by
    intro j h hjh
    exact htri (prefixIndex i j) (prefixIndex i h) hjh
  have hnep : ∀ j, up j j ≠ 0 := fun j ↦ hne (prefixIndex i j)
  have hlep : ∀ j, |up j j| ≤ (1 : ℝ) := fun j ↦ hle (prefixIndex i j)
  simpa [up] using exists_integerCombination_abs_le_half up htrip hnep hlep
    (fun h ↦ r (prefixIndex i h))

@[simp]
theorem extendPrefix_prefixIndex {n : ℕ} (i : Fin n)
    (t : Fin i.val → ℤ) (j : Fin i.val) :
    extendPrefix i t (prefixIndex i j) = t j := by
  simp [extendPrefix, prefixIndex_lt]

def prefixIndexEquivIio {n : ℕ} (i : Fin n) :
    Fin i.val ≃ {j : Fin n // j ∈ Finset.Iio i} where
  toFun j := ⟨prefixIndex i j, Finset.mem_Iio.mpr (prefixIndex_lt i j)⟩
  invFun j :=
    { val := j.1.val
      isLt := by
        have hji : j.1 < i := Finset.mem_Iio.mp j.2
        exact hji }
  left_inv j := by ext; rfl
  right_inv j := by ext; rfl

theorem sum_extendPrefix_mul {n : ℕ} (i : Fin n) (t : Fin i.val → ℤ)
    (f : Fin n → ℝ) :
    (∑ j, (extendPrefix i t j : ℝ) * f j) =
      ∑ j : Fin i.val, (t j : ℝ) * f (prefixIndex i j) := by
  classical
  calc
    (∑ j, (extendPrefix i t j : ℝ) * f j) =
        ∑ j ∈ Finset.Iio i, (extendPrefix i t j : ℝ) * f j := by
      symm
      apply Finset.sum_subset (by intro j hj; simp)
      intro j _hj hjnot
      have hnlt : ¬j < i := by simpa using hjnot
      simp [extendPrefix, hnlt]
    _ = ∑ j : {j : Fin n // j ∈ Finset.Iio i},
          (extendPrefix i t j : ℝ) * f j := by
      rw [← Finset.sum_attach]
      simp
    _ = ∑ j : Fin i.val, (t j : ℝ) * f (prefixIndex i j) := by
      symm
      refine Fintype.sum_equiv (prefixIndexEquivIio i) _ _ ?_
      intro j
      simp [prefixIndexEquivIio]

noncomputable def centeredReductionMatrix {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun j i ↦
    if |b.repr (x i) i| = 1 then
      b.repr (x i) i * b.repr (x i) j
    else if j = i then 1 else extendPrefix i (t i) j

theorem centeredReductionMatrix_isUpperTriangular {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ)
    (hupper : ∀ i j, i < j → b.repr (x i) j = 0) :
    (centeredReductionMatrix x b t).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  change centeredReductionMatrix x b t i j = 0
  by_cases hunit : |b.repr (x j) j| = 1
  · simp [centeredReductionMatrix, hunit, hupper j i hji]
  · have hne : i ≠ j := hji.ne'
    have hnlt : ¬i < j := hji.asymm
    simp [centeredReductionMatrix, hunit, hne, extendPrefix, hnlt]

@[simp]
theorem centeredReductionMatrix_apply_self {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) (i : Fin n) :
    centeredReductionMatrix x b t i i = 1 := by
  by_cases hunit : |b.repr (x i) i| = 1
  · have hsquare : b.repr (x i) i * b.repr (x i) i = 1 := by
      by_cases hnonneg : 0 ≤ b.repr (x i) i
      · rw [abs_of_nonneg hnonneg] at hunit
        simp [hunit]
      · have hnonpos : b.repr (x i) i ≤ 0 := le_of_not_ge hnonneg
        rw [abs_of_nonpos hnonpos] at hunit
        have hminus : b.repr (x i) i = -1 := by omega
        simp [hminus]
    simp [centeredReductionMatrix, hunit, hsquare]
  · simp [centeredReductionMatrix, hunit]

theorem centeredReductionMatrix_isUnit_diagonal {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (t : (i : Fin n) → Fin i.val → ℤ) :
    ∀ i, IsUnit (centeredReductionMatrix x b t i i) := by
  intro i
  rw [centeredReductionMatrix_apply_self]
  exact isUnit_one

theorem exists_centeredReduction_of_rawFlagReduction {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i)))
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (u : Fin n → Fin n → ℝ)
    (hraw : IsRawFlagReduction x b u) :
    ∃ (e : Basis (Fin n) ℤ (IntegralPoint n))
      (a : Fin n → Fin n → ℝ), IsCenteredReduction x e a := by
  classical
  have hudiag_ne : ∀ i, u i i ≠ 0 := by
    intro i hui
    have hrecip := (hraw.2.2.2 i).2
    rw [hui] at hrecip
    norm_num at hrecip
  have hudiag_le : ∀ i, |u i i| ≤ (1 : ℝ) :=
    fun i ↦ rawFlagReduction_diag_abs_le_one hraw i
  have hround : ∀ i, ∃ t : Fin i.val → ℤ, ∀ h : Fin i.val,
      |u i (prefixIndex i h) +
        ∑ j, (t j : ℝ) * u (prefixIndex i j) (prefixIndex i h)| ≤
          (1 : ℝ) / 2 := by
    intro i
    exact exists_prefix_integerCombination_abs_le_half u hraw.2.1
      hudiag_ne hudiag_le (u i) i
  choose t ht using hround
  let A : Matrix (Fin n) (Fin n) ℤ := centeredReductionMatrix x b t
  have hAupper : A.IsUpperTriangular :=
    centeredReductionMatrix_isUpperTriangular x b t hraw.2.2.1
  have hAdiag : ∀ i, IsUnit (A i i) :=
    centeredReductionMatrix_isUnit_diagonal x b t
  let e : Basis (Fin n) ℤ (IntegralPoint n) :=
    basisOfUpperTriangularUnits b A hAupper hAdiag
  let xb : Basis (Fin n) ℝ (Fin n → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun i ↦ integralEmbed (x i)) hli (by simp)
  have hxb (i : Fin n) : xb i = integralEmbed (x i) := by
    simp [xb]
  let a : Fin n → Fin n → ℝ :=
    fun i h ↦ xb.repr (integralEmbed (e i)) h
  have hurepr (j h : Fin n) :
      xb.repr (integralEmbed (b j)) h = u j h := by
    rw [hraw.1 j]
    simp_rw [← hxb]
    simp [Finsupp.single_apply]
  have he_apply (i : Fin n) : e i = ∑ j, A j i • b j :=
    basisOfUpperTriangularUnits_apply b A hAupper hAdiag i
  have hembed (i : Fin n) :
      integralEmbed (e i) = ∑ j, (A j i : ℝ) • integralEmbed (b j) := by
    rw [he_apply]
    ext k
    simp [integralEmbed]
  have haformula (i h : Fin n) :
      a i h = ∑ j, (A j i : ℝ) * u j h := by
    change xb.repr (integralEmbed (e i)) h = _
    rw [hembed]
    simp [hurepr]
  have hexpand (i : Fin n) :
      integralEmbed (e i) = ∑ j, a i j • integralEmbed (x j) := by
    simpa only [hxb] using (xb.sum_repr (integralEmbed (e i))).symm
  refine ⟨e, a, ?_⟩
  intro i
  refine ⟨hexpand i, ?_⟩
  by_cases hunit : |b.repr (x i) i| = 1
  · have heprim : e i = b.repr (x i) i • x i := by
      rw [he_apply]
      simp only [A, centeredReductionMatrix, hunit, ite_true]
      simp_rw [mul_smul]
      rw [← Finset.smul_sum, b.sum_repr]
    have hembedprim : integralEmbed (e i) =
        (b.repr (x i) i : ℝ) • xb i := by
      rw [heprim]
      ext k
      simp [integralEmbed, hxb]
    have haprim (h : Fin n) : a i h =
        (b.repr (x i) i : ℝ) * (if i = h then 1 else 0) := by
      change xb.repr (integralEmbed (e i)) h = _
      rw [hembedprim]
      simp [Finsupp.single_apply]
    have habove : ∀ j, i < j → a i j = 0 := by
      intro j hij
      rw [haprim]
      simp [hij.ne]
    refine ⟨habove, Or.inl ⟨?_, ?_⟩⟩
    · rw [haprim]
      have hcabs : |(b.repr (x i) i : ℝ)| = 1 := by
        exact_mod_cast hunit
      simpa using hcabs
    · intro j hji
      rw [haprim]
      simp [hji.ne']
  · have hainon (h : Fin n) : a i h =
        u i h + ∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) h := by
      rw [haformula]
      calc
        (∑ j, (A j i : ℝ) * u j h) =
            ∑ j, ((if j = i then 1 else 0) +
              (extendPrefix i (t i) j : ℤ) : ℤ) * u j h := by
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hji : j = i
          · subst j
            simp [A, extendPrefix]
          · simp [A, centeredReductionMatrix, hunit, hji]
        _ = u i h + ∑ j, (extendPrefix i (t i) j : ℝ) * u j h := by
          simp_rw [Int.cast_add, add_mul]
          rw [Finset.sum_add_distrib]
          simp
        _ = u i h + ∑ j : Fin i.val,
              (t i j : ℝ) * u (prefixIndex i j) h := by
          rw [sum_extendPrefix_mul]
    have habove : ∀ h, i < h → a i h = 0 := by
      intro h hih
      rw [hainon, hraw.2.1 i h hih]
      have hsum : (∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) h) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        rw [hraw.2.1 (prefixIndex i j) h
          (lt_trans (prefixIndex_lt i j) hih)]
        simp
      rw [hsum, add_zero]
    refine ⟨habove, Or.inr ?_⟩
    intro h hhi
    rcases lt_or_eq_of_le hhi with hlt | heq
    · let h' : Fin i.val := ⟨h.val, hlt⟩
      have hp : prefixIndex i h' = h := by
        apply Fin.ext
        rfl
      rw [hainon]
      simpa only [hp] using ht i h'
    · subst h
      rw [hainon]
      have hsum : (∑ j : Fin i.val,
          (t i j : ℝ) * u (prefixIndex i j) i) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        rw [hraw.2.1 (prefixIndex i j) i (prefixIndex_lt i j)]
        simp
      rw [hsum, add_zero]
      exact rawFlagReduction_diag_abs_le_half_of_not_unit hraw i hunit

theorem exists_centeredReduction_of_linearIndependent {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i))) :
    ∃ (b : Basis (Fin n) ℤ (IntegralPoint n))
      (a : Fin n → Fin n → ℝ), IsCenteredReduction x b a := by
  obtain ⟨b, u, hraw⟩ := exists_rawFlagReduction_of_linearIndependent x hli
  exact exists_centeredReduction_of_rawFlagReduction x hli b u hraw

end Erdos3.IntegerBasisReduction.Mahler

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem IntegerBasisReduction.Mahler.IsCenteredReduction.abs_coefficient_le_one
    {n : ℕ} {x : Fin n → IntegerBasisReduction.Mahler.IntegralPoint n}
    {b : Basis (Fin n) ℤ (IntegerBasisReduction.Mahler.IntegralPoint n)}
    {a : Fin n → Fin n → ℝ}
    (h : IntegerBasisReduction.Mahler.IsCenteredReduction x b a) (i j : Fin n) :
    |a i j| ≤ 1 := by
  obtain ⟨_, habove, hprim | hhalf⟩ := h i
  · rcases lt_trichotomy j i with hlt | rfl | hgt
    · simp [hprim.2 j hlt]
    · exact hprim.1.le
    · simp [habove j hgt]
  · rcases le_or_gt j i with hle | hgt
    · exact (hhalf j hle).trans (by norm_num)
    · simp [habove j hgt]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

noncomputable def properCyclicKernelBasisBound (r : ℕ) (δ : ℝ) : ℝ :=
  (r : ℝ) * BohrLattice.MinkowskiSecondBox.minkowskiSecondConstant r * 2 ^ r / δ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanShortLatticeBasis
namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem orthonormalChart_norm_le (b : OrthonormalBasis I ℝ E) (x : I → ℝ) :
    ‖orthonormalChart b x‖ ≤ (Fintype.card I : ℝ) * ‖x‖ := by
  change ‖b.repr.symm ((EuclideanSpace.equiv I ℝ).symm x)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ∑ i, |x i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : I, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactivePrincipal_small {K q : ℕ} (hsmall : K < 2 * q) :
    inactivePrincipalCoefficient K q = 0 := by
  simp [inactivePrincipalCoefficient, not_le.mpr hsmall]

theorem inactivePrincipal_large {K q : ℕ} (hlarge : 2 * q ≤ K) :
    inactivePrincipalCoefficient K q = 1 := by
  simp [inactivePrincipalCoefficient, hlarge]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.InactivePrincipalLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem inactivePrincipalPMF_support {K q : ℕ} {k : ℤ}
    (hk : k ∈ (inactivePrincipalPMF K q).support) : k = inactivePrincipalCoefficient K q := by
  simpa only [inactivePrincipalPMF, PMF.support_pure, Set.mem_singleton_iff] using hk

theorem inactivePrincipal_scaled_upper {h K q : ℕ} (hh : 0 < h) (hK : 0 < K) (hq : 0 < q) :
    |(inactivePrincipalCoefficient K q : ℝ)| * (inactiveSideLength h K q : ℝ) ^ h / K ≤ 1 / (q : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hlarge : 2 * q ≤ K
  · rw [inactivePrincipal_large hlarge, Int.cast_one, abs_one, one_mul]
    have hb : q * inactiveSideLength h K q ^ h ≤ K := by
      calc
        _ ≤ q * (K / q) := Nat.mul_le_mul_left q (inactiveSideLength_power hh hlarge)
        _ ≤ K := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self K q
    have hbr : (q : ℝ) * (inactiveSideLength h K q : ℝ) ^ h ≤ K := by exact_mod_cast hb
    apply (div_le_div_iff₀ hKr hqr).mpr
    nlinarith
  · rw [inactivePrincipal_small (lt_of_not_ge hlarge), Int.cast_zero, abs_zero, zero_mul, zero_div]
    positivity

theorem inactiveDenominator_bound {γ : ℝ} (hγ : 0 < γ) : 1 / (inactiveDenominator γ : ℝ) ≤ γ := by
  have hq : (0 : ℝ) < inactiveDenominator γ := by exact_mod_cast inactiveDenominator_pos γ
  have hceil : γ⁻¹ ≤ (inactiveDenominator γ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈γ⁻¹⌉₊))
  have hb := mul_le_mul_of_nonneg_left hceil hγ.le
  rw [mul_inv_cancel₀ hγ.ne'] at hb
  exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hb)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAxisPrincipalLaw
namespace OAI

section

namespace Erdos3

theorem integerAxisPrincipalPMF_inactive {h K L : ℕ} (hh : 0 < h) (hK : 0 < K)
    (hL : 0 < L) {γ : ℝ} (hγ : 0 < γ)
    (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K) (ha : K ≤ L ^ h) :
    integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap =
      inactivePrincipalPMF K (inactiveDenominator γ) := by
  simp [integerAxisPrincipalPMF, Nat.not_lt.mpr ha]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

theorem le_raisedNiltestBudget (p : ℝ) : p ≤ raisedNiltestBudget p := by
  unfold raisedNiltestBudget
  nlinarith [sq_nonneg (p + 2)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedPairCoordinates
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem realPairEquiv_difference (q : ℚ) (x : ℝ ⊗[ℚ] (L × L)) :
    scaledPairDifference q (realPairEquiv x) =
      (scaledPairDifference (L := L) q).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realPairEquiv_tmul, LinearMap.baseChange_tmul, scaledPairDifference_apply,
      TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedDilationMultidegree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem scaledPairLayer_eq_inf (P Q : Submodule ℚ L) (q : ℚ) :
    scaledPairLayer P Q q = P.comap (LinearMap.fst ℚ L L) ⊓
      (P.comap (LinearMap.snd ℚ L L) ⊓ Q.comap (scaledPairDifference q)) := by
  ext x
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSupportedQuotientCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (P : Submodule ℚ V) (S : Set ι)
  (hP : P = Submodule.span ℚ (b '' S))

theorem realSupportedQuotientBasis_repr_mk (x : ℝ ⊗[ℚ] V) (i : {i // i ∉ S}) :
    ((supportedQuotientBasis b P S hP).baseChange ℝ).repr (P.mkQ.baseChange ℝ x) i =
      (b.baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, supportedQuotientBasis_repr_mk]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ}

noncomputable def boxedDegreeMonomial (a : BoxedDegreeIndex bound) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

@[simp] theorem boxedDegreeMonomial_apply (a : BoxedDegreeIndex bound) (i : σ) :
    boxedDegreeMonomial a i = (a i).val := by
  classical
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (fun i => (a i).val)) i

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {bound : σ → ℕ}

theorem boxedDegreeMonomial_injective : Function.Injective (@boxedDegreeMonomial σ _ bound) := by
  intro a b h
  funext i
  apply Fin.ext
  simpa only [boxedDegreeMonomial_apply] using congrArg (fun c : σ →₀ ℕ => c i) h

theorem boxedDegreeMonomial_le (a : BoxedDegreeIndex bound) :
    (fun i => boxedDegreeMonomial a i) ≤ bound := by
  intro i
  change boxedDegreeMonomial a i ≤ bound i
  rw [boxedDegreeMonomial_apply]
  exact Nat.le_of_lt_succ (a i).isLt

theorem exists_boxedDegreeMonomial (a : σ →₀ ℕ) (ha : (fun i => a i) ≤ bound) :
    ∃ b : BoxedDegreeIndex bound, boxedDegreeMonomial b = a := by
  refine ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, ?_⟩
  ext i
  exact boxedDegreeMonomial_apply _ i

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ]

noncomputable def coordinateTranslationExpansion (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → BinaryTensorIndex I l.length → (Option σ → ℤ) → ℂ
  | [], a, x => f a (fun j => x (some j))
  | i :: l, a, x => coordinateTranslationExpansion f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

variable {σ I : Type*} [DecidableEq σ]

noncomputable def firstTranslationCoordinate : (l : List σ) → BinaryTensorIndex I l.length → I
  | [], a => a
  | _ :: l, a => firstTranslationCoordinate l a.1

noncomputable def translationExpansionRemainder (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → BinaryTensorIndex I l.length → (Option σ → ℤ) → ℂ
  | [], _, _ => 1
  | i :: l, a, x => translationExpansionRemainder f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCorrelationPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_supported_correlation_pairs {I X : Type*} [Fintype I] [Nonempty I] [DecidableEq X]
    (A : Finset X) (hA : A.Nonempty) (S : I → Finset X) (hSA : ∀ i, S i ⊆ A)
    (B : X → ℂ) (v : I → X → ℂ) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hB : ∀ x ∈ A, ‖B x‖ ≤ 1) (hv : ∀ i x, x ∈ S i → ‖v i x‖ ≤ 1)
    (hsize : ∀ i, α ≤ (S i).card / (A.card : ℝ))
    (hcorr : ∀ i, δ ≤ ‖𝔼 x ∈ S i, B x * v i x‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      (α * δ) ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, (S t.1 ∩ S t.2).Nonempty ∧
        (α * δ) ^ 2 / 2 ≤ ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ ∧
        (α * δ) ^ 2 / 2 ≤ (S t.1 ∩ S t.2).card / (A.card : ℝ) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hA
  have hA : A.Nonempty := ⟨x₀, hx₀⟩
  let : Nonempty A := ⟨⟨x₀, hx₀⟩⟩
  let u (i : I) (x : A) := zeroExtendFinset (S i) (v i) x.val
  have huc (i : I) : α * δ ≤ ‖𝔼 x : A, B x.val * u i x‖ := by
    have heq : ‖𝔼 x : A, B x.val * u i x‖ =
        ((S i).card / (A.card : ℝ)) * ‖𝔼 x ∈ S i, B x * v i x‖ := by
      change ‖𝔼 x : A, B x.val * zeroExtendFinset (S i) (v i) x.val‖ = _
      rw [expect_finset_subtype A (fun x => B x * zeroExtendFinset (S i) (v i) x)]
      simp_rw [zeroExtendFinset_mul_left]
      exact norm_expect_zeroExtendFinset A (S i) (hSA i) _
    rw [heq]
    exact mul_le_mul (hsize i) (hcorr i) hδ.le (by positivity)
  obtain ⟨P, hP, hPsize, hPcor⟩ := exists_dense_correlation_pairs
    (fun x : A => B x.val) u (mul_pos hα hδ) (fun x => hB x.val x.property)
    (fun i x => zeroExtendFinset_norm_le_one (S i) (v i) (hv i) x.val) huc
  refine ⟨P, hP, hPsize, ?_⟩
  intro t ht
  have hJA : S t.1 ∩ S t.2 ⊆ A := Finset.Subset.trans Finset.inter_subset_left (hSA t.1)
  have heq : ‖𝔼 x : A, u t.1 x * star (u t.2 x)‖ =
      ((S t.1 ∩ S t.2).card / (A.card : ℝ)) *
        ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ := by
    change ‖𝔼 x : A, zeroExtendFinset (S t.1) (v t.1) x.val *
      star (zeroExtendFinset (S t.2) (v t.2) x.val)‖ = _
    rw [expect_finset_subtype A (fun x => zeroExtendFinset (S t.1) (v t.1) x *
      star (zeroExtendFinset (S t.2) (v t.2) x))]
    simp_rw [zeroExtendFinset_mul_star]
    exact norm_expect_zeroExtendFinset A (S t.1 ∩ S t.2) hJA _
  have hp := hPcor t ht
  rw [heq] at hp
  have hpos : 0 < (α * δ) ^ 2 / 2 := by positivity
  have hJ : (S t.1 ∩ S t.2).Nonempty := by
    by_contra hempty
    have he : S t.1 ∩ S t.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul] at hp
    exact (not_le_of_gt hpos) hp
  have hnorm : ‖𝔼 x ∈ S t.1 ∩ S t.2, v t.1 x * star (v t.2 x)‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const hJ 1)
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_inter.mp hx
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv t.1 x hx₁)).trans (hv t.2 x hx₂)
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hratio : ((S t.1 ∩ S t.2).card / (A.card : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hApos).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (Finset.card_le_card hJA) :
      ((S t.1 ∩ S t.2).card : ℝ) ≤ A.card)
  refine ⟨hJ, ?_, ?_⟩
  · exact hp.trans ((mul_le_mul_of_nonneg_right hratio (norm_nonneg _)).trans_eq (one_mul _))
  · exact hp.trans ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (mul_one _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

def mixedErrorPairBudget (p : ℝ) : ℝ := productNiltestBudget p + 2 * p

def mixedErrorBudget (p : ℝ) : ℝ :=
  productNiltestBudget (mixedErrorPairBudget p) + 2 * mixedErrorPairBudget p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.IntervalSplitBudget
namespace OAI

section

namespace Erdos3

def intervalErrorBaseBudget (p : ℝ) : ℝ := mixedErrorBudget (p + 2) + p + 2

def intervalErrorBudget (p : ℝ) : ℝ := mixedErrorPairBudget (intervalErrorBaseBudget p)

end Erdos3

end

section

namespace Erdos3

def intervalSplitInput (K : ℝ) : ℝ := 2 * K + 2 * intervalErrorBudget K + 2

def intervalSplitTermBudget (c : ℕ) (K : ℝ) : ℝ := (intervalSplitInput K + c) ^ c

def intervalSplitLocalBudget (c : ℕ) (K : ℝ) : ℝ :=
  mixedErrorPairBudget (intervalErrorBudget K + intervalSplitTermBudget c K + 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

noncomputable def balancedFunction (L : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  f x - realFinsetIndicator L x

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

noncomputable def localMomentExponentFactor (delta : ℝ) : ℕ :=
  momentAmplificationFactor (delta ^ 2 / 8)

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

def antisymmetricPairBudget (p q : ℝ) : ℝ := p + q + raisedNiltestBudget (p + q) + 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    Finset (σ → ℤ) := by
  classical
  exact (translatedIntegerBox lo N).filter (fun z => ∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i)

@[simp] theorem mem_primeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) (z : σ → ℤ) :
    z ∈ primeCoordinateCell lo N q I x ↔
      z ∈ translatedIntegerBox lo N ∧ ∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i := by
  classical
  simp only [primeCoordinateCell, Finset.mem_filter]

end Erdos3

end

end OAI
end


