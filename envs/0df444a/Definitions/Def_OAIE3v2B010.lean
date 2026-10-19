-- Prove2me | Definitions.Def_OAIE3v2B010
-- name    : OAIE3v2B010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:22.052872+00:00
-- url     : https://prove2.me/theorems/d63ea9c1-4e06-46d7-9b43-a6239d1138b9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 11 of 311
-- statement:
--   Definitions bundle 11 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/CubeModeUniformBudget.lean`, `Dynamics/ModeThresholdLogBudget.lean`, `Dynamics/RationalHeightBudget.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/BoundedCommonSiteResidual.lean`, `Estimates/BoundedExtendedSiteSection.lean`, `Estimates/ContinuousImageFactor.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/LinearQuotientCoverAverage.lean`, `Estimates/MixedArrayReference.lean`, `Estimates/MixedBooleanSiteValues.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/NativePhysicalHaarExpansion.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/RationalImageIntersections.lean`, `Estimates/RationalRowReduction.lean`, `Estimates/ResidualErrorAllocation.lean`, `Estimates/ScaledLinearResidual.lean`, `Estimates/SmoothedImageTest.lean`, `Fourier/AnchoredCoefficientFourierNormalization.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Geometry/GeometricRetainedCommonCover.lean`, `Geometry/IndependentProductTransport.lean`, `Geometry/IndexedComparableScalarParameterBox.lean`, `Geometry/LieTreeSupport.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AffineCoefficientCoverTilt.lean`, `Lattices/IntegerAffineResidues.lean`, `Lattices/IntegerColumnMinor.lean`, `Lattices/RoundedAffineLifts.lean`, `Linear/BasisSurjectionSection.lean`, `Linear/BoundedAdaptedBasis.lean`, `Linear/FixedKernelEuclideanDensity.lean`, `Linear/FixedKernelSiteImage.lean`, `Linear/FurstenbergWeissProjection.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/RankIntervalFactorization.lean`, `Linear/RationalKernelBudget.lean`, `Linear/SpanKernelGenerators.lean`, `Linear/WeightedPatchKernel.lean`, `Polynomial/BoundedRealPolynomialBasis.lean`, `Polynomial/MeasureDegreeZeroTwistTransfer.lean`, `Polynomial/PolynomialDensityBudget.lean`, `Probability/CommonSectionAmbientDensityMultiple.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/FiniteArrayMeasure.lean`, `Probability/FiniteDensityMassBound.lean`, `Probability/PairedProductDensity.lean`, `Probability/ProbabilityIntegralApproximation.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontSourceLossBudget
namespace OAI

section

namespace Erdos3

theorem le_power_budget {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 1 ≤ a) :
    p ≤ (p + 2) ^ a := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  calc
    p ≤ p + 2 := by linarith
    _ ≤ (p + 2) ^ a := by simpa only [pow_one] using pow_le_pow_right₀ hbase ha

theorem shifted_power_budget_le {p : ℝ} (hp : 0 ≤ p) (a b : ℕ) :
    ((p + 2) ^ a + 2) ^ b ≤ (p + 2) ^ ((a + 2) * b) := by
  have hbase : (1 : ℝ) ≤ p + 2 := by linarith
  have hpow : (1 : ℝ) ≤ (p + 2) ^ a := one_le_pow₀ hbase
  have hsq : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have hstep : (p + 2) ^ a + 2 ≤ (p + 2) ^ (a + 2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (p + 2) ^ a)]
  calc
    _ ≤ ((p + 2) ^ (a + 2)) ^ b := pow_le_pow_left₀ (by positivity) hstep b
    _ = _ := (pow_mul _ _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

def conjugationPower : ℕ → (ℂ →+* ℂ)
  | 0 => RingHom.id ℂ
  | n + 1 => (starRingEnd ℂ).comp (conjugationPower n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
namespace OAI

section

namespace Erdos3

theorem natPolynomial_eval_nonneg (P : Polynomial ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))

theorem exists_natPolynomial_eval_budget (P : Polynomial ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + N) ^ N := by
  let N := P.eval 1 + P.natDegree + 2
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro p hp
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  have ht : 1 ≤ p + N := by linarith
  have hcoeff : ((P.eval 1 : ℕ) : ℝ) ≤ p + N := by
    have h : P.eval 1 ≤ N := by dsimp [N]; omega
    exact (Nat.cast_le.mpr h).trans (le_add_of_nonneg_left hp)
  have hsum : (∑ n ∈ P.support, (P.coeff n : ℝ)) = ((P.eval 1 : ℕ) : ℝ) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [one_pow, mul_one, Nat.cast_sum]
  calc
    P.eval₂ (Nat.castRingHom ℝ) p = ∑ n ∈ P.support, (P.coeff n : ℝ) * p ^ n := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      rfl
    _ ≤ ∑ n ∈ P.support, (P.coeff n : ℝ) * (p + N) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (pow_le_pow_left₀ hp (le_add_of_nonneg_right (Nat.cast_nonneg N)) n).trans
      exact pow_le_pow_right₀ ht (Polynomial.le_natDegree_of_mem_supp n hn)
    _ = ((P.eval 1 : ℕ) : ℝ) * (p + N) ^ P.natDegree := by rw [← Finset.sum_mul, hsum]
    _ ≤ (p + N) * (p + N) ^ P.natDegree :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by linarith) _)
    _ = (p + N) ^ (P.natDegree + 1) := (pow_succ' _ _).symm
    _ ≤ (p + N) ^ N := pow_le_pow_right₀ ht (by dsimp [N]; omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

def booleanWeight {j : ℕ} (ω : Fin j → Bool) : ℕ :=
  ∑ i, if ω i then 1 else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem conjugationPower_norm (n : ℕ) (z : ℂ) : ‖conjugationPower n z‖ = ‖z‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ‖star (conjugationPower n z)‖ = ‖z‖
    rw [norm_star, ih]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerColumnMinor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integer_det_natAbs_le (A : Matrix ι ι ℤ) {H : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ H) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  have h := Matrix.det_le (A := A) (abv := AbsoluteValue.abs) (x := (H : ℤ))
    (fun i j => show |A i j| ≤ (H : ℤ) from by
      simpa only [← Int.natCast_natAbs] using (show
        ((A i j).natAbs : ℤ) ≤ (H : ℤ) from by exact_mod_cast hA i j))
  change |A.det| ≤ (Fintype.card ι).factorial • (H : ℤ) ^ Fintype.card ι at h
  rw [← Int.natCast_natAbs, nsmul_eq_mul] at h
  exact_mod_cast h

theorem integer_cramer_natAbs_le (A : Matrix ι ι ℤ) (b : ι → ℤ) {H : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H) (i : ι) :
    (A.cramer b i).natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  rw [Matrix.cramer_apply]
  apply integer_det_natAbs_le
  intro j k
  rw [Matrix.updateCol_apply]
  split
  · exact hb j
  · exact hA j k

def rationalCramerSolution (A : Matrix ι ι ℚ) (b : ι → ℚ) : ι → ℚ :=
  A.det⁻¹ • A.cramer b

theorem rationalCramerSolution_solves (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hA : A.det ≠ 0) : A *ᵥ rationalCramerSolution A b = b := by
  rw [rationalCramerSolution, Matrix.mulVec_smul, Matrix.mulVec_cramer,
    smul_smul, inv_mul_cancel₀ hA, one_smul]

theorem rationalCramerSolution_unique (A : Matrix ι ι ℚ) (b x : ι → ℚ)
    (hA : A.det ≠ 0) (hx : A *ᵥ x = b) : x = rationalCramerSolution A b := by
  apply Matrix.mulVec_injective_of_isUnit (A.isUnit_iff_isUnit_det.mpr
    (isUnit_iff_ne_zero.mpr hA))
  exact hx.trans (rationalCramerSolution_solves A b hA).symm

theorem integerCramerSolution_apply (A : Matrix ι ι ℤ) (b : ι → ℤ) (i : ι) :
    rationalCramerSolution (A.map (Int.castRingHom ℚ)) (fun j => (b j : ℚ)) i =
      (A.cramer b i : ℚ) / (A.det : ℚ) := by
  have hdet : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det A).symm
  have hnum : (A.map (Int.castRingHom ℚ)).cramer (fun j => (b j : ℚ)) i =
      (A.cramer b i : ℚ) := by
    rw [Matrix.cramer_apply, Matrix.cramer_apply]
    have h := ((Int.castRingHom ℚ).map_det (A.updateCol i b)).symm
    change ((A.updateCol i b).map (Int.castRingHom ℚ)).det = _ at h
    rw [Matrix.map_updateCol] at h
    exact h
  simp only [rationalCramerSolution, Pi.smul_apply, smul_eq_mul, hdet, hnum,
    div_eq_mul_inv, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def rationalSolveHeight (r H : ℕ) : ℕ :=
  r.factorial * (H ^ (r * r + r)) ^ r

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in

theorem exists_nonsingular_columns (A : Matrix ι κ ℚ)
    (hA : Function.Surjective A.mulVec) :
    ∃ c : ι → κ, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  classical
  have hspan : Submodule.span ℚ (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    exact hA
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
  rw [hspan, finrank_top, Module.finrank_pi] at hex
  obtain ⟨v, hv, _, hli⟩ := hex
  choose f hf using hv
  let e := Fintype.equivFin ι
  let c : ι → κ := fun i => f (e i)
  have hcol : (A.submatrix id c).col = fun i => v (e i) := by
    funext i
    exact hf (e i)
  have hcols : LinearIndependent ℚ (A.submatrix id c).col := by
    rw [hcol]
    exact hli.comp e e.injective
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    apply hcols.injective
    change A.col (c i) = A.col (c j)
    rw [hij]
  · exact (isUnit_iff_ne_zero.mp
      ((A.submatrix id c).isUnit_iff_isUnit_det.mp
        (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)))

def extendRows (c : ι → κ) (B : Matrix ι ι ℚ) : Matrix κ ι ℚ :=
  fun k j => ∑ i, if c i = k then B i j else 0

omit [Fintype κ] in
theorem extendRows_apply (c : ι → κ) (hc : Function.Injective c)
    (B : Matrix ι ι ℚ) (i j : ι) : extendRows c B (c i) j = B i j := by
  simp only [extendRows, hc.eq_iff]
  simp

omit [DecidableEq ι] [Fintype κ] in
theorem extendRows_apply_of_not_mem (c : ι → κ) (B : Matrix ι ι ℚ)
    (k : κ) (hk : k ∉ Set.range c) (j : ι) : extendRows c B k j = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun h => hk ⟨i, h⟩)

omit [DecidableEq ι] in
theorem mul_extendRows (A : Matrix ι κ ℚ) (c : ι → κ) (B : Matrix ι ι ℚ) :
    A * extendRows c B = A.submatrix id c * B := by
  ext r j
  change (∑ k, A r k * ∑ i, if c i = k then B i j else 0) =
    ∑ i, A r (c i) * B i j
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero]
  simp

theorem rationalSolveHeight_pos (r : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < rationalSolveHeight r H := by
  have hHpos : 0 < H := Nat.zero_lt_one.trans_le hH
  unfold rationalSolveHeight
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem mulVec_eq_zero_iff_row_span (A : Matrix ι κ ℚ) (x : κ → ℚ) :
    A *ᵥ x = 0 ↔ ∀ v ∈ Submodule.span ℚ (Set.range A.row), v ⬝ᵥ x = 0 := by
  constructor
  · intro hx v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact congrFun hx i
    | zero => exact zero_dotProduct x
    | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_dotProduct, hy, smul_zero]
  · intro hx
    funext i
    exact hx (A.row i) (Submodule.subset_span ⟨i, rfl⟩)

theorem mulVec_surjective_of_independent_rows (A : Matrix ι κ ℚ)
    (hA : LinearIndependent ℚ A.row) : Function.Surjective A.mulVec := by
  change Function.Surjective A.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change A.rank = Module.finrank ℚ (ι → ℚ)
  rw [hA.rank_matrix, Module.finrank_pi]

theorem exists_independent_defining_rows (A : Matrix ι κ ℚ) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ rows : Fin r → ι,
      Function.Injective rows ∧ Function.Surjective (A.submatrix rows id).mulVec ∧
      LinearMap.ker (A.submatrix rows id).mulVecLin = LinearMap.ker A.mulVecLin := by
  classical
  let r := Module.finrank ℚ (Submodule.span ℚ (Set.range A.row))
  obtain ⟨v, hv, hspan, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.row)
  choose rows hrows using hv
  have hrow : (A.submatrix rows id).row = v := by
    funext i
    exact hrows i
  have hind : LinearIndependent ℚ (A.submatrix rows id).row := by
    rw [hrow]
    exact hli
  refine ⟨r, ?_, rows, ?_, mulVec_surjective_of_independent_rows _ hind, ?_⟩
  · change Module.finrank ℚ (Submodule.span ℚ (Set.range A.row)) ≤ Fintype.card ι
    rw [← A.rank_eq_finrank_span_row]
    exact A.rank_le_card_height
  · intro i j hij
    apply hind.injective
    change A.row (rows i) = A.row (rows j)
    rw [hij]
  · ext x
    change (A.submatrix rows id) *ᵥ x = 0 ↔ A *ᵥ x = 0
    rw [mulVec_eq_zero_iff_row_span, mulVec_eq_zero_iff_row_span, hrow, hspan]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalHeightBudget
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem factorial_le_exp_sq (r : ℕ) :
    (r.factorial : ℝ) ≤ Real.exp ((r : ℝ) ^ 2) := by
  calc
    (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
    _ ≤ (Real.exp r) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _)
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp r)) r
    _ = Real.exp ((r : ℝ) ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem rationalSolveHeight_le_exp (r H : ℕ) {p : ℝ} (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight r H : ℝ) ≤
      Real.exp ((r : ℝ) ^ 2 + p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) := by
  have hpower : (((H : ℝ) ^ (r * r + r)) ^ r) ≤
      Real.exp (p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) := by
    calc
      _ ≤ ((Real.exp p) ^ (r * r + r)) ^ r := by gcongr
      _ = _ := by rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold rationalSolveHeight
  push_cast
  calc
    _ ≤ Real.exp ((r : ℝ) ^ 2) *
        Real.exp (p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2)) :=
      mul_le_mul (factorial_le_exp_sq r) hpower (by positivity) (by positivity)
    _ = _ := (Real.exp_add _ _).symm

theorem rationalSolveHeight_le_budget (r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalSolveHeight r H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  apply (rationalSolveHeight_le_exp r H hH).trans
  apply Real.exp_le_exp.mpr
  calc
    (r : ℝ) ^ 2 + p * ((r : ℝ) ^ 3 + (r : ℝ) ^ 2) ≤
        p ^ 2 + p * (p ^ 3 + p ^ 2) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 9 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 80 * p + 32 := by
        positivity
      nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanKernelGenerators
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def rationalKernelHeight (r H : ℕ) : ℕ :=
  2 * (r + 1) * (rationalSolveHeight r H * H) ^ r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalKernelBudget
namespace OAI

section

namespace Erdos3

theorem rationalKernelHeight_le_budget (r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalKernelHeight r H : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  have hsolve := rationalSolveHeight_le_budget r H hp hr hH
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfront : (2 : ℝ) * (r + 1) ≤ Real.exp (1 + (r : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul htwo (Real.add_one_le_exp r) (by positivity) (by positivity)
  have hbase : (rationalSolveHeight r H : ℝ) * H ≤
      Real.exp ((p + 2) ^ 5 + p) := by
    rw [Real.exp_add]
    exact mul_le_mul hsolve hH (Nat.cast_nonneg _) (by positivity)
  have hpower := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hbase r
  rw [← Real.exp_nat_mul] at hpower
  have hbound : (rationalKernelHeight r H : ℝ) ≤
      Real.exp (1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p)) := by
    unfold rationalKernelHeight
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul hfront hpower (by positivity) (by positivity)
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  calc
    1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p) ≤
        1 + p + p * ((p + 2) ^ 5 + p) := by gcongr
    _ ≤ (p + 2) ^ 7 := by
      have h : 0 ≤ p ^ 7 + 13 * p ^ 6 + 74 * p ^ 5 + 240 * p ^ 4 +
          480 * p ^ 3 + 591 * p ^ 2 + 415 * p + 127 := by positivity
      nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalImageIntersections
namespace OAI

section

namespace Erdos3

theorem rationalSolveHeight_mono {r s H : ℕ} (hH : 1 ≤ H) (hrs : r ≤ s) :
    rationalSolveHeight r H ≤ rationalSolveHeight s H := by
  unfold rationalSolveHeight
  apply Nat.mul_le_mul (Nat.factorial_le hrs)
  have he : r * r + r ≤ s * s + s := Nat.add_le_add (Nat.mul_le_mul hrs hrs) hrs
  have hbase := pow_le_pow_right₀ hH he
  calc
    _ ≤ (H ^ (s * s + s)) ^ r := pow_le_pow_left₀ (Nat.zero_le _) hbase r
    _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ hH) hrs

theorem rationalKernelHeight_mono {r s H : ℕ} (hH : 1 ≤ H) (hrs : r ≤ s) :
    rationalKernelHeight r H ≤ rationalKernelHeight s H := by
  unfold rationalKernelHeight
  apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hrs))
  have hbase := Nat.mul_le_mul_right H (rationalSolveHeight_mono hH hrs)
  have hpos : 1 ≤ rationalSolveHeight s H * H :=
    Nat.mul_pos (rationalSolveHeight_pos s hH) (Nat.zero_lt_one.trans_le hH)
  calc
    _ ≤ (rationalSolveHeight s H * H) ^ r := pow_le_pow_left₀ (Nat.zero_le _) hbase r
    _ ≤ _ := pow_le_pow_right₀ hpos hrs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IndependentProductTransport
namespace OAI

section

namespace Erdos3

theorem pmf_map_injective_at {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (x : X) : p.map f (f x) = p x := by
  classical
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro y hy
    have hne : f x ≠ f y := fun h => hy (hf h).symm
    simp only [hne, ite_false]

theorem pmf_map_zero_off_range {X Y : Type*} (p : PMF X) (f : X → Y) (y : Y)
    (hy : y ∉ Set.range f) : p.map f y = 0 := by
  classical
  have hne (x) : y ≠ f x := fun h => hy ⟨x, h.symm⟩
  simp only [PMF.map_apply, hne, ite_false, tsum_zero]

theorem pmf_map_injective_expectation {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (φ : Y → ℂ) :
    (∑' y, ((p.map f y).toReal : ℂ) * φ y) =
      ∑' x, ((p x).toReal : ℂ) * φ (f x) := by
  have hs : Function.support (fun y => ((p.map f y).toReal : ℂ) * φ y) ⊆ Set.range f := by
    intro y hy
    by_contra hn
    have hz := pmf_map_zero_off_range p f y hn
    exact hy (by simp only [hz, ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul])
  have he := hf.tsum_eq hs
  simpa only [pmf_map_injective_at p f hf] using he.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
namespace OAI

section

namespace Erdos3

noncomputable def paddedExponentWord {K : Type*} (m : K →₀ ℕ) (h : ℕ)
    (hm : m.sum (fun _ n => n) ≤ h) : List.Vector (Option K) h :=
  ⟨(m.toMultiset.map some + Multiset.replicate (h - m.sum (fun _ n => n)) none).toList, by
    rw [Multiset.length_toList, Multiset.card_add, Multiset.card_map, Multiset.card_replicate,
      Finsupp.card_toMultiset]
    exact Nat.add_sub_of_le hm⟩

theorem paddedExponentWord_count {K : Type*} [DecidableEq K] (m : K →₀ ℕ) (h : ℕ)
    (hm : m.sum (fun _ n => n) ≤ h) (k : K) :
    ((paddedExponentWord m h hm).val : Multiset (Option K)).count (some k) = m k := by
  change Multiset.count (some k)
    ((m.toMultiset.map some + Multiset.replicate (h - m.sum (fun _ n => n)) none).toList :
      Multiset (Option K)) = m k
  rw [Multiset.coe_toList, Multiset.count_add,
    Multiset.count_map_eq_count' _ _ (Option.some_injective _)]
  simp [Multiset.mem_replicate]

open scoped BigOperators

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerBooleanInterpolant {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) : MvPolynomial K ℤ :=
  MvPolynomial.C (a ^ (h - s.card)) * ∏ r ∈ s, q r

theorem integerBooleanInterpolant_eval {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (vertices : Finset α → K → ℤ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then a else 0)
    (t : Finset α) :
    MvPolynomial.eval (vertices t) (integerBooleanInterpolant q a h s) =
      a ^ h * if s ⊆ t then 1 else 0 := by
  have hprod : (∏ r ∈ s, MvPolynomial.eval (vertices t) (q r)) =
      if s ⊆ t then a ^ s.card else 0 := by
    by_cases hst : s ⊆ t
    · rw [if_pos hst]
      calc
        _ = ∏ _r ∈ s, a := Finset.prod_congr rfl (fun r hr => by rw [hq r t, if_pos (hst hr)])
        _ = _ := by simp
    · rw [if_neg hst]
      obtain ⟨r, hrs, hrt⟩ := Finset.not_subset.mp hst
      exact Finset.prod_eq_zero hrs (by rw [hq r t, if_neg hrt])
  rw [integerBooleanInterpolant, map_mul, MvPolynomial.eval_C, map_prod, hprod]
  by_cases hst : s ⊆ t
  · simp only [if_pos hst, mul_one]
    rw [← pow_add, Nat.sub_add_cancel hs]
  · simp only [if_neg hst, mul_zero]

theorem integerBooleanInterpolant_degree {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (hq : ∀ r ∈ s, (q r).totalDegree ≤ 1) :
    (integerBooleanInterpolant q a h s).totalDegree ≤ h := by
  unfold integerBooleanInterpolant
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd s q).trans
  calc
    _ ≤ ∑ _r ∈ s, 1 := Finset.sum_le_sum hq
    _ = s.card := by simp
    _ ≤ h := hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerAffineNumerator {K : Type*} [Fintype K]
    (root n : K → ℤ) : MvPolynomial K ℤ :=
  ∑ k, MvPolynomial.C (n k) * (MvPolynomial.X k - MvPolynomial.C (root k))

theorem integerAffineNumerator_degree {K : Type*} [Fintype K] (root n : K → ℤ) :
    (integerAffineNumerator root n).totalDegree ≤ 1 := by
  unfold integerAffineNumerator
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothedImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def mappedTest {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → X) (φ : X → ℝ) : ℝ := ∫ a, φ (U a) ∂μ

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

noncomputable def densityMixture {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (x : X) : ℝ := ∫ t, F t x ∂μ

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_test_integral {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite μ] [SFinite ν]
    (F : T → X → ℝ) (hF : Integrable (Function.uncurry F) (μ.prod ν))
    (φ : X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, densityMixture μ F x * φ x ∂ν) = ∫ t, ∫ x, F t x * φ x ∂ν ∂μ := by
  have hi : Integrable (Function.uncurry (fun t x => F t x * φ x)) (μ.prod ν) :=
    hF.mul_bdd (hφ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.2))
  calc
    (∫ x, densityMixture μ F x * φ x ∂ν) = ∫ x, ∫ t, F t x * φ x ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, F t x * φ x ∂ν ∂μ := (integral_integral_swap hi).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def haarShiftDensity {T G : Type*} [MeasurableSpace T] [Sub G]
    (ν : Measure T) (z : T → G) (f : G → ℝ) (y : G) : ℝ :=
  densityMixture ν (fun t x => f (x - z t)) y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem inv_min_le_of_inv_le {a b M : ℝ} (ha : a⁻¹ ≤ M) (hb : b⁻¹ ≤ M) :
    (min a b)⁻¹ ≤ M := by
  rcases le_total a b with h | h
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right h] using hb

theorem one_add_le_exp_succ {x P : ℝ} (hP : 0 ≤ P) (hx : x ≤ Real.exp P) :
    1+x ≤ Real.exp (P+1) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2*Real.exp P := by linarith
    _ ≤ Real.exp 1*Real.exp P := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteArrayMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def finiteArrayTranspose (I J X : Type*) [MeasurableSpace X] : (I → J → X) ≃ᵐ (J → I → X) :=
  ((MeasurableEquiv.curry I J X).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : J × I => X) (Equiv.prodComm I J))).trans
      (MeasurableEquiv.curry J I X)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteMeasure_eq_of_integrals {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X → ℝ, Measurable f → (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi := h (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs)
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteDensityMassBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_supported_weight_sum_tsum {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0) :
    (∑' x, ∑ r, w r x) = ∑ r, ∑' x, w r x := by
  have hcut (v : X → ℝ) (hv : ∀ x ∉ S, v x = 0) : (∑' x, v x) = ∑ x ∈ S, v x :=
    (hasSum_sum_of_ne_finset_zero hv).tsum_eq
  have hsum (x : X) (hx : x ∉ S) : (∑ r, w r x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact hw r x hx
  have hcutEach (r : R) := hcut (w r) (hw r)
  rw [hcut (fun x => ∑ r, w r x) hsum]
  simp_rw [hcutEach]
  exact Finset.sum_comm

theorem finite_normalized_test_sum {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (Z : ℝ) (φ : X → ℂ) :
    (∑' x, ((w x / Z : ℝ) : ℂ) * φ x) = ∑ x ∈ S, ((w x / Z : ℝ) : ℂ) * φ x := by
  apply (hasSum_sum_of_ne_finset_zero (s := S) _).tsum_eq
  intro x hx
  simp only [hw x hx, zero_div, Complex.ofReal_zero, zero_mul]

theorem finite_supported_normalized_mixture {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0)
    (hZr : ∀ r, 0 < ∑' x, w r x) (hZ : 0 < ∑ r, ∑' x, w r x) (φ : X → ℂ) :
    (∑' x, (((∑ r, w r x) / (∑ r, ∑' y, w r y) : ℝ) : ℂ) * φ x) =
      ∑ r, (((∑' y, w r y) / (∑ s, ∑' y, w s y) : ℝ) : ℂ) *
        (∑' x, ((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x) := by
  have hsum (x : X) (hx : x ∉ S) : (∑ r, w r x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact hw r x hx
  have hcut := finite_normalized_test_sum (fun x => ∑ r, w r x) S hsum
    (∑ r, ∑' y, w r y) φ
  rw [hcut]
  simp_rw [finite_normalized_test_sum _ S (hw _) _ φ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hc r : (((∑' y, w r y) / (∑ s, ∑' y, w s y) : ℝ) : ℂ) *
      (((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x) =
      ((w r x / (∑ s, ∑' y, w s y) : ℝ) : ℂ) * φ x := by
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp [hZ.ne', (hZr r).ne']
  simp_rw [hc]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_div]

theorem finite_supported_normalized_mixture_bound {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0)
    (hZr : ∀ r, 0 < ∑' x, w r x) (hZ : 0 < ∑ r, ∑' x, w r x)
    (φ : X → ℂ) {ε : ℝ}
    (hφ : ∀ r, ‖∑' x, ((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x‖ ≤ ε) :
    ‖∑' x, (((∑ r, w r x) / (∑ r, ∑' y, w r y) : ℝ) : ℂ) * φ x‖ ≤ ε := by
  rw [finite_supported_normalized_mixture w S hw hZr hZ φ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, ((∑' y, w r y) / (∑ s, ∑' y, w s y)) * ε := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos (hZr r) hZ).le]
      exact mul_le_mul_of_nonneg_left (hφ r) (div_pos (hZr r) hZ).le
    _ = ε := by rw [← Finset.sum_mul, ← Finset.sum_div, div_self hZ.ne', one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteDensityMass {X : Type*} (w D : X → ℝ) : ℝ :=
  ∑' x, (w x / ∑' y, w y) * D x

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

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def multidegreeTotalLayer (P : (σ → ℕ) → Submodule ℚ L) (n : ℕ) : Submodule ℚ L :=
  ⨆ a : {a : σ → ℕ // n ≤ ∑ i, a i}, P a.val

theorem layer_le_multidegreeTotalLayer (P : (σ → ℕ) → Submodule ℚ L) (a : σ → ℕ) (n : ℕ)
    (ha : n ≤ ∑ i, a i) : P a ≤ multidegreeTotalLayer P n :=
  le_iSup (fun b : {b : σ → ℕ // n ≤ ∑ i, b i} => P b.val) ⟨a, ha⟩

theorem multidegreeTotalLayer_antitone (P : (σ → ℕ) → Submodule ℚ L) :
    Antitone (multidegreeTotalLayer P) := by
  intro i j hij
  apply iSup_le
  intro a
  exact layer_le_multidegreeTotalLayer P a.val i (hij.trans a.property)

theorem multidegreeTotalLayer_eq (P : (σ → ℕ) → Submodule ℚ L) (n : ℕ) :
    multidegreeTotalLayer P n = ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), P a := by
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup_of_le a.val (le_iSup_of_le a.property le_rfl)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact layer_le_multidegreeTotalLayer P a n ha

theorem multidegreeTotalLayer_lie_mem (P : (σ → ℕ) → Submodule ℚ L)
    (hP : ∀ {a b : σ → ℕ} {x y : L}, x ∈ P a → y ∈ P b → ⁅x, y⁆ ∈ P (a + b))
    {i j : ℕ} {x y : L} (hx : x ∈ multidegreeTotalLayer P i) (hy : y ∈ multidegreeTotalLayer P j) :
    ⁅x, y⁆ ∈ multidegreeTotalLayer P (i + j) := by
  refine Submodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ multidegreeTotalLayer P (i + j)) ?_ ?_ ?_
  · intro a u hu
    refine Submodule.iSup_induction _ hy
      (motive := fun z => ⁅u, z⁆ ∈ multidegreeTotalLayer P (i + j)) ?_ ?_ ?_
    · intro b v hv
      apply layer_le_multidegreeTotalLayer P (a.val + b.val) (i + j) _ (hP hu hv)
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using Nat.add_le_add a.property b.property
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro u v hu hv
      rw [lie_add]
      exact Submodule.add_mem _ hu hv
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro u v hu hv
    rw [add_lie]
    exact Submodule.add_mem _ hu hv

theorem multidegreeTotalLayer_terminal (P : (σ → ℕ) → Submodule ℚ L) (bound : σ → ℕ)
    (hP : ∀ a, ¬a ≤ bound → P a = ⊥) (s : ℕ) (hs : (∑ i, bound i) ≤ s) :
    multidegreeTotalLayer P (s + 1) = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro a
  have ha : ¬a.val ≤ bound := by
    intro h
    have hsum : (∑ i, a.val i) ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => h i)
    have hn := a.property
    omega
  rw [hP a.val ha]

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

def basisTail (e : Basis (Fin d) ℚ L) (i : ℕ) : Submodule ℚ L where
  carrier := {x | ∀ j : Fin d, j.val < i → e.repr x j = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro j hj
    simp only [map_add, Finsupp.add_apply, hx j hj, hy j hj, zero_add]
  smul_mem' c x hx := by
    intro j hj
    simp only [map_smul, Finsupp.smul_apply, hx j hj, smul_zero]

theorem basisTail_eq_span (e : Basis (Fin d) ℚ L) (i : ℕ) :
    basisTail e i = Submodule.span ℚ (e '' {j : Fin d | i ≤ j.val}) := by
  ext x
  rw [e.mem_span_image]
  constructor
  · intro hx j hj
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hx j (Nat.lt_of_not_ge h))
  · intro hx j hj
    by_contra h
    exact (not_le_of_gt hj) (hx (Finsupp.mem_support_iff.mpr h))

def IsCentralLieBasis (e : Basis (Fin d) ℚ L) : Prop :=
  ∀ (j : Fin d) (a : L), ⁅a, e j⁆ ∈ basisTail e (j.val + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

theorem fejer_error_le_of_cutoff {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    {N : ℕ} (hN : 0 < N) (hcut : (L + 1) ^ 3 / δ ^ 3 ≤ (N : ℝ)) :
    L * (δ / (2 * (L + 1)) + 1 / (8 * N * (δ / (2 * (L + 1))) ^ 2)) ≤ δ := by
  have hS : 0 < L + 1 := by linarith
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (L + 1) ^ 3 ≤ (N : ℝ) * δ ^ 3 :=
    (div_le_iff₀ (pow_pos hδ 3)).mp hcut
  have hfirst : L * δ / (2 * (L + 1)) ≤ δ / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hsecond : L * (L + 1) ^ 2 / (2 * N * δ ^ 2) ≤ δ / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      L * (L + 1) ^ 2 ≤ (L + 1) ^ 3 := by nlinarith [sq_nonneg (L + 1)]
      _ ≤ (N : ℝ) * δ ^ 3 := hpow
      _ = δ / 2 * (2 * N * δ ^ 2) := by ring
  have heq : L * (δ / (2 * (L + 1)) + 1 / (8 * N * (δ / (2 * (L + 1))) ^ 2)) =
      L * δ / (2 * (L + 1)) + L * (L + 1) ^ 2 / (2 * N * δ ^ 2) := by
    field_simp [ne_of_gt hS, ne_of_gt hδ, ne_of_gt hNr]
    ring
  rw [heq]
  linarith

theorem exists_fejer_cutoff {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ (L + 1) ^ 3 / δ ^ 3 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (L + 1) ^ 3 / δ ^ 3 + 2 := by
  let R := (L + 1) ^ 3 / δ ^ 3
  refine ⟨⌈R⌉₊ + 1, by omega, ?_, ?_⟩
  · have h := Nat.le_ceil R
    push_cast
    linarith
  · have h := Nat.ceil_lt_add_one (show 0 ≤ R by dsimp [R]; positivity)
    push_cast
    linarith

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieTreeSupport
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

def lieTreeSupport : FreeMagma I → Set I
  | .of i => {i}
  | .mul a b => lieTreeSupport a ∪ lieTreeSupport b

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FurstenbergWeissProjection
namespace OAI

section

namespace Erdos3

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def fourCoordinateKernel (S : Finset (Fin 4)) : Submodule ℚ (Fin 4 → V) :=
  ⨅ k ∈ S, LinearMap.ker (LinearMap.proj k)

def fourFirstProjection (J : Submodule ℚ (Fin 4 → V)) : Submodule ℚ V :=
  J.map (LinearMap.proj 0)

def fourSparseFirstProjection (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) : Submodule ℚ V :=
  (J ⊓ fourCoordinateKernel S).map (LinearMap.proj 0)

def fourDependentProjection (J : Submodule ℚ (Fin 4 → V)) : Submodule ℚ V :=
  fourSparseFirstProjection J {1, 2} ⊓ fourSparseFirstProjection J {1, 3}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

open scoped Matrix

namespace Erdos3

theorem real_matrix_image_section {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ) (hS : A * S * A = A) :
    Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) *
      Matrix.of (fun i j => (A i j : ℝ)) = Matrix.of (fun i j => (A i j : ℝ)) := by
  ext i j
  have he := congrArg (fun q : ℚ => (q : ℝ)) (congrFun (congrFun hS i) j)
  simpa only [Matrix.mul_apply, Matrix.of_apply, Rat.cast_sum, Rat.cast_mul] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem add_le_exp_add_one {x y P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hx : x ≤ Real.exp P) (hy : y ≤ Real.exp Q) : x+y ≤ Real.exp (P+Q+1) := by
  have hx' := hx.trans (Real.exp_le_exp.mpr (show P ≤ P+Q by linarith))
  have hy' := hy.trans (Real.exp_le_exp.mpr (show Q ≤ P+Q by linarith))
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2*Real.exp (P+Q) := by linarith
    _ ≤ Real.exp 1*Real.exp (P+Q) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem sum_le_exp_card_add_sum {I : Type*} [Fintype I]
    (x P : I → ℝ) (hP : ∀ i, 0 ≤ P i) (hx : ∀ i, x i ≤ Real.exp (P i)) :
    (∑ i, x i) ≤ Real.exp ((Fintype.card I : ℝ)+∑ i, P i) := by
  have hi (i) : P i ≤ ∑ j, P j := Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)
  have hcard : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  calc
    _ ≤ ∑ _i : I, Real.exp (∑ j, P j) :=
      Finset.sum_le_sum (fun i _ => (hx i).trans (Real.exp_le_exp.mpr (hi i)))
    _ = (Fintype.card I : ℝ)*Real.exp (∑ j, P j) := by simp
    _ ≤ Real.exp (Fintype.card I)*Real.exp (∑ j, P j) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CubeModeUniformBudget
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

noncomputable def cubeInputLogPolynomial (q : ℕ) : Polynomial ℕ :=
  X + C q.factorial + C (2 + q * (q + 1)) + C (q + 2) * (X + 4)

theorem cubeInputLogPolynomial_ge (q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ (cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P := by
  have hrest := natPolynomial_eval_nonneg
    (C q.factorial + C (2 + q * (q + 1)) + C (q + 2) * (X + 4)) hP
  simpa [cubeInputLogPolynomial, add_assoc] using le_add_of_nonneg_right hrest (a := P)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledLinearResidual
namespace OAI

section

namespace Erdos3

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

noncomputable def scaledLinearResidual (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ) :
    V →ₗ[ℝ] V := q • LinearMap.id - T.comp E

theorem scaledLinearResidual_apply (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ) (x : V) :
    scaledLinearResidual E T q x = q • x - T (E x) := rfl

theorem scaledLinearResidual_evaluation (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V) (q : ℝ)
    (hT : ∀ x, E (T (E x)) = q • E x) (x : V) :
    E (scaledLinearResidual E T q x) = 0 := by
  rw [scaledLinearResidual_apply, map_sub, map_smul, hT, sub_self]

theorem scaledLinearResidual_factor_iff (E : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] V)
    {q : ℝ} (hq : q ≠ 0) (hT : ∀ x, E (T (E x)) = q • E x) (L : V →ₗ[ℝ] ℝ) :
    L.comp (scaledLinearResidual E T q) = 0 ↔ ∃ M : W →ₗ[ℝ] ℝ, L = M.comp E := by
  constructor
  · intro h
    refine ⟨q⁻¹ • L.comp T, ?_⟩
    ext x
    have hx := DFunLike.congr_fun h x
    simp only [LinearMap.comp_apply, scaledLinearResidual_apply, map_sub, map_smul,
      smul_eq_mul, LinearMap.zero_apply, sub_eq_zero] at hx
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← hx, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  · rintro ⟨M, rfl⟩
    ext x
    simp only [LinearMap.comp_apply, scaledLinearResidual_evaluation E T q hT,
      map_zero, LinearMap.zero_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

noncomputable def linearQuotientEndomorphism : (V ⧸ Γ) →+ (V ⧸ Γ) :=
  QuotientAddGroup.map Γ Γ R.toAddMonoidHom hR

noncomputable def linearQuotientAverage [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) (f : (V ⧸ Γ) → W) (x : V ⧸ Γ) : W :=
  ∫ y, f (x + linearQuotientEndomorphism Γ R hR y) ∂μ

theorem linearQuotientAverage_bound [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] (f : (V ⧸ Γ) → W)
    {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : V ⧸ Γ) :
    ‖linearQuotientAverage Γ R hR μ f x‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (integrable_const B (μ := μ))
    (ae_of_all μ (fun y => hf (x + linearQuotientEndomorphism Γ R hR y)))
  simpa only [linearQuotientAverage, integral_const, probReal_univ, one_smul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

theorem linearQuotientEndomorphism_continuous [TopologicalSpace V] (hRc : Continuous R) :
    Continuous (linearQuotientEndomorphism Γ R hR) := by
  apply (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp hRc

theorem linearQuotientAverage_invariant [MeasurableSpace (V ⧸ Γ)] [MeasurableAdd₂ (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] (f : (V ⧸ Γ) → W) (x z : V ⧸ Γ) :
    linearQuotientAverage Γ R hR μ f (x + linearQuotientEndomorphism Γ R hR z) =
      linearQuotientAverage Γ R hR μ f x := by
  have h := integral_add_left_eq_self (μ := μ)
    (fun y => f (x + linearQuotientEndomorphism Γ R hR y)) z
  simpa only [linearQuotientAverage, map_add, add_assoc] using h

theorem linearQuotientAverage_approx [MeasurableSpace (V ⧸ Γ)]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] (f g : (V ⧸ Γ) → W)
    {ε : ℝ} (hε : ∀ x, ‖f x - g x‖ ≤ ε) (x : V ⧸ Γ)
    (hf : Integrable (fun y => f (x + linearQuotientEndomorphism Γ R hR y)) μ)
    (hg : Integrable (fun y => g (x + linearQuotientEndomorphism Γ R hR y)) μ) :
    ‖linearQuotientAverage Γ R hR μ f x - linearQuotientAverage Γ R hR μ g x‖ ≤ ε := by
  unfold linearQuotientAverage
  rw [← integral_sub hf hg]
  exact linearQuotientAverage_bound Γ R hR μ (fun x => f x - g x) hε x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisSurjectionSection
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I : Type*} [CommSemiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F]

noncomputable def basisSurjectionSection (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (b : Basis I R F) : F →ₗ[R] E :=
  b.constr R (fun i => (hq (b i)).choose)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

def arrayCoordinateLinear {I J : Type*} (U : Submodule ℝ (J → ℝ)) (i : I) :
    (I → U) →ₗ[ℝ] (Unit → U) where
  toFun x _ := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCommonSiteResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def complementaryPeriod {I : Type*} [Fintype I] (q : I → ℕ) (i : I) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, q j

theorem period_mul_complementary {I : Type*} [Fintype I] (q : I → ℕ) (i : I) :
    q i * complementaryPeriod q i = ∏ j, q j :=
  Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)

theorem complementaryPeriod_le_product {I : Type*} [Fintype I] (q : I → ℕ)
    (hq : ∀ i, 0 < q i) (i : I) : complementaryPeriod q i ≤ ∏ j, q j := by
  rw [← period_mul_complementary q i]
  exact Nat.le_mul_of_pos_left _ (hq i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedExtendedSiteSection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def columnInclusionMatrix {I K : Type*} [DecidableEq I] (e : K → I) : Matrix I K ℝ :=
  fun i k => if e k = i then 1 else 0

theorem matrix_mul_columnInclusion {I K S : Type*} [Fintype I] [DecidableEq I]
    (E : Matrix S I ℝ) (e : K → I) : E * columnInclusionMatrix e = E.submatrix id e := by
  ext s k
  simp [Matrix.mul_apply, columnInclusionMatrix]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def extendIntegerSiteSection {K I S : Type*} [Fintype K] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) : Matrix I S ℤ :=
  fun i s => ∑ k, if e k = i then T k s else 0

theorem extendIntegerSiteSection_cast {K I S : Type*} [Fintype K] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) :
    Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ)) =
      columnInclusionMatrix e * Matrix.of (fun k s => (T k s : ℝ)) := by
  ext i s
  simp [extendIntegerSiteSection, columnInclusionMatrix, Matrix.mul_apply]

theorem integerPeriod_range_le_of_columns {O K I : Type*}
    [Fintype O] [DecidableEq O] [Fintype K] [Fintype I]
    (A₀ : Matrix O K ℤ) (A : Matrix O I ℤ) (e : K → I)
    (he : ∀ i k, A i (e k) = A₀ i k) : A₀.mulVecLin.range ≤ A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro v ⟨k, rfl⟩
  exact ⟨e k, funext (fun i => he i k)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem extendIntegerSiteSection_column_sum {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) (s : S) :
    (∑ i, |(extendIntegerSiteSection e T i s : ℝ)|) ≤ ∑ k, |(T k s : ℝ)| := by
  classical
  calc
    _ ≤ ∑ i : I, ∑ k : K, if e k = i then |(T k s : ℝ)| else 0 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [extendIntegerSiteSection, Int.cast_sum]
      apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    _ = ∑ k : K, ∑ i : I, if e k = i then |(T k s : ℝ)| else 0 := Finset.sum_comm
    _ = _ := by simp

theorem extendIntegerSiteSection_column_sum_bound {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (e : K → I) (T : Matrix K S ℤ) {B : ℝ} (hT : ∀ k s, |(T k s : ℝ)| ≤ B) (s : S) :
    (∑ i, |(extendIntegerSiteSection e T i s : ℝ)|) ≤ Fintype.card K * B := by
  apply (extendIntegerSiteSection_column_sum e T s).trans
  calc
    _ ≤ ∑ _k : K, B := Finset.sum_le_sum (fun k _ => hT k s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContinuousImageFactor
namespace OAI

section

namespace Erdos3

open Topology

theorem exists_continuous_image_factor {X Y Z : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Z] (E : X → Y) (hE : Continuous E) (f : X → Z) (hf : Continuous f)
    (hfactor : ∀ x y, E x = E y → f x = f y) :
    ∃ g : Set.range E → Z, Continuous g ∧ ∀ x, g (Set.rangeFactorization E x) = f x := by
  let e : C(X, Set.range E) := ⟨Set.rangeFactorization E, hE.rangeFactorization⟩
  have hq : IsQuotientMap e :=
    IsQuotientMap.of_surjective_continuous Set.rangeFactorization_surjective hE.rangeFactorization
  have hfac : Function.FactorsThrough (⟨f, hf⟩ : C(X, Z)) e :=
    fun x y hxy => hfactor x y (congrArg Subtype.val hxy)
  let g := hq.lift ⟨f, hf⟩ hfac
  refine ⟨g, g.continuous, ?_⟩
  intro x
  exact DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

def mixedArrayRegroup (I Z J : Type*) :
    ((I → J → ℝ) × (Z → J → ℤ)) ≃ᵐ (J → (I → ℝ) × (Z → ℤ)) :=
  ((finiteArrayTranspose I J ℝ).prodCongr (finiteArrayTranspose Z J ℤ)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

abbrev BoundedBooleanJet (α : Type*) (h : ℕ) := {s : Finset α // s.card ≤ h}

noncomputable def booleanReconstructionMatrix (α : Type*) [DecidableEq α] :
    Matrix (Finset α) (Finset α) ℤ := fun s r => if r ⊆ s then 1 else 0

noncomputable def boundedBooleanReconstructionMatrix (α : Type*) [DecidableEq α] (h : ℕ) :
    Matrix (Finset α) (BoundedBooleanJet α h) ℤ := fun s r => if r.val ⊆ s then 1 else 0

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def boundedBooleanJetRows (α : Type*) [Fintype α] (h : ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun s => s.card ≤ h)

theorem mem_boundedBooleanJetRows {α : Type*} [Fintype α] (h : ℕ) (s : Finset α) :
    s ∈ boundedBooleanJetRows α h ↔ s.card ≤ h := by
  simp only [boundedBooleanJetRows, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def boundedBooleanJetRowsEquiv (α : Type*) [Fintype α] (h : ℕ) :
    {s : Finset α // s ∈ boundedBooleanJetRows α h} ≃ BoundedBooleanJet α h where
  toFun s := ⟨s.val, (mem_boundedBooleanJetRows h s.val).mp s.property⟩
  invFun s := ⟨s.val, (mem_boundedBooleanJetRows h s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelSiteImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem exists_matrix_factor_of_common_reconstruction {S J K I : Type*}
    [Fintype S] [Fintype J] [Fintype K] [Fintype I]
    (E₀ : Matrix S K ℝ) (E : Matrix S I ℝ) (B : Matrix S J ℝ) (T : Matrix J S ℝ)
    (h₀ : B * T * E₀ = E₀) (hE : B * T * E = E)
    (hs : Function.Surjective (Matrix.mulVec (T * E₀))) :
    ∃ R : Matrix K I ℝ, E₀ * R = E := by
  choose v hv using fun i : I => hs (fun j => (T * E) j i)
  let R : Matrix K I ℝ := fun k i => v i k
  have hr : (T * E₀) * R = T * E := by
    ext j i
    exact congrFun (hv i) j
  refine ⟨R, ?_⟩
  calc
    E₀ * R = (B * (T * E₀)) * R := by rw [← Matrix.mul_assoc, h₀]
    _ = B * ((T * E₀) * R) := Matrix.mul_assoc _ _ _
    _ = B * (T * E) := by rw [hr]
    _ = E := by rw [← Matrix.mul_assoc, hE]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
namespace OAI

section

namespace Erdos3

open Polynomial

noncomputable def fourierModeError (B ε : ℝ) : ℝ := ε / (B + 1)

theorem fourierModeError_pos {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < fourierModeError B ε := div_pos hε (by linarith)

theorem fourierModeError_cost_le {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    B * fourierModeError B ε ≤ ε := by
  have h := mul_le_mul_of_nonneg_right (show B ≤ B + 1 by linarith) (fourierModeError_pos hB hε).le
  have he : (B + 1) * fourierModeError B ε = ε := by
    unfold fourierModeError
    field_simp
  exact h.trans_eq he

theorem fourierModeError_inv_le_exp {P B ε : ℝ} (hP : 0 ≤ P) (_hB : 0 ≤ B)
    (hBP : B ≤ Real.exp P) (hε : 0 < ε) (hεP : 1 / ε ≤ Real.exp P) :
    1 / fourierModeError B ε ≤ Real.exp (2 * P + 2) := by
  have hb : B + 1 ≤ Real.exp (P + 1) := by
    simpa only [add_comm B 1] using one_add_le_exp_succ hP hBP
  rw [fourierModeError, one_div, inv_div]
  calc
    _ = (B + 1) * (1 / ε) := by ring
    _ ≤ Real.exp (P + 1) * Real.exp P :=
      mul_le_mul hb hεP (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (2 * P + 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProbabilityIntegralApproximation
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem probability_integral_approximation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : X → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) {η : ℝ}
    (he : ∀ x, ‖f x - g x‖ ≤ η) :
    ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ η := by
  rw [← integral_sub hf hg]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all μ he)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt
namespace OAI

section

namespace Erdos3

open Polynomial

theorem exists_integer_cover_threshold (A₀ : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp ((P + A₀) ^ A₀) ≤ Real.exp ((P + A) ^ A) ∧
      Real.exp P * Real.exp ((P + A₀) ^ A₀) ≤ Real.exp ((P + A) ^ A) := by
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget (X + (X + C A₀) ^ A₀ + 1)
  refine ⟨A, hA, ?_⟩
  intro P hP
  have he : P + (P + A₀) ^ A₀ + 1 ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hpoly P hP
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

def geometricSiteBudget (m q : ℕ) (P : ℝ) : ℝ :=
  ((m : ℝ) + 1) * (P + 1) ^ (m + 1) + 2 ^ q

theorem geometricSiteBudget_nonneg (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ geometricSiteBudget m q P := by
  unfold geometricSiteBudget
  positivity

theorem degree_mul_le_geometricSiteBudget (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (m : ℝ) * (P + 1) ≤ geometricSiteBudget m q P := by
  have hp : P + 1 ≤ (P + 1) ^ (m + 1) := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ P + 1) (show 1 ≤ m + 1 by omega)
  calc
    _ ≤ ((m : ℝ) + 1) * (P + 1) ^ (m + 1) :=
      mul_le_mul (by linarith) hp (by linarith) (by positivity)
    _ ≤ geometricSiteBudget m q P := le_add_of_nonneg_right (by positivity)

theorem cubeSites_card_le_geometricSiteBudget (m q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (Fintype.card (Finset (Fin q)) : ℝ) ≤ geometricSiteBudget m q P := by
  simp only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact le_add_of_nonneg_left (by positivity)

noncomputable def exponentialSiteHeight (m : ℕ) (P : ℝ) : ℕ := ⌈Real.exp P⌉₊ ^ m

theorem exponentialSiteHeight_pos (m : ℕ) (P : ℝ) : 0 < exponentialSiteHeight m P := by
  exact pow_pos (Nat.ceil_pos.mpr (Real.exp_pos _)) _

theorem exponentialSiteHeight_le (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (exponentialSiteHeight m P : ℝ) ≤ Real.exp ((m : ℝ) * (P + 1)) := by
  have hceil : (⌈Real.exp P⌉₊ : ℝ) ≤ Real.exp (P + 1) := by
    calc
      _ ≤ Real.exp P + 1 := (Nat.ceil_lt_add_one (Real.exp_pos P).le).le
      _ ≤ Real.exp P * 2 := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp P * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos P).le
      _ = Real.exp (P + 1) := (Real.exp_add _ _).symm
  simpa only [exponentialSiteHeight, Nat.cast_pow, Real.exp_nat_mul] using
    pow_le_pow_left₀ (Nat.cast_nonneg _) hceil m

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def spatialTrimMargin {I : Type*} (τ : ℝ) (N : I → ℕ) : I → ℕ :=
  fun i => ⌈τ * (N i : ℝ) / 4⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

def standardPhysicalCubeOutput {X : Type*} {q : ℕ}
    (z : Option (Fin q) × X → ℤ) : X → (Unit ⊕ Fin q) → ℤ :=
  fun x => Sum.elim (fun _ => z (none,x)) (fun i => z (some i,x))

def standardPhysicalCubeFrame {X : Type*} {q : ℕ}
    (v : X → (Unit ⊕ Fin q) → ℤ) : Option (Fin q) × X → ℤ :=
  fun z => Option.elim' (v z.2 (.inl ())) (fun i => v z.2 (.inr i)) z.1

theorem standardPhysicalCubeOutput_frame {X : Type*} {q : ℕ}
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    standardPhysicalCubeOutput (standardPhysicalCubeFrame v) = v := by
  funext x i
  rcases i with i | i
  · cases i; rfl
  · rfl

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RoundedAffineLifts
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def jointIntegerFrame {K I : Type*}
    (z : (I → ℤ) × (Option K × I → ℤ)) : Option K → I → ℤ :=
  fun k i => match k with
    | none => z.1 i + z.2 (none,i)
    | some k => z.2 (some k,i)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelEuclideanDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Polynomial

theorem exists_bounded_residual_cover_budget (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      geometricSiteBudget m q P + ((m : ℝ) + 2) * (geometricSiteBudget m q P + 2) ^ 36 ≤
        (P + A) ^ A := by
  let G : Polynomial ℕ := C (m + 1) * (X + 1) ^ (m + 1) + C (2 ^ q)
  obtain ⟨A, hA, h⟩ := exists_natPolynomial_eval_budget (G + C (m + 2) * (G + 2) ^ 36)
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [G, geometricSiteBudget, Polynomial.eval₂_pow, Nat.cast_add] using h P hP

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedPatchKernel
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_mul_unit_interval {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {L M : ℝ≥0} (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (hfI : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hgI : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    LipschitzWith (L + M) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h₁ : dist (f x * g x) (f y * g x) ≤ dist (f x) (f y) := by
    rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (hgI x).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hgI x).2
  have h₂ : dist (f y * g x) (f y * g y) ≤ dist (g x) (g y) := by
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (hfI y).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hfI y).2
  exact (dist_triangle _ (f y * g x) _).trans
    ((add_le_add (h₁.trans (hf.dist_le_mul _ _)) (h₂.trans (hg.dist_le_mul _ _))).trans_eq
      (by simp [add_mul]))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical NNReal

structure NormalizedPolynomialTwist (X : Type*) [Fintype X]
    (Y : Type*) [Fintype Y] (periodCap coverCap : ℝ) (L : ℝ≥0) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  modulus_bound : (modulus : ℝ) ≤ periodCap
  cover : ℕ
  cover_pos : 0 < cover
  cover_bound : (cover : ℝ) ≤ coverCap
  mask : (X → ZMod modulus) → ℂ
  mask_bound : ∀ z, ‖mask z‖ ≤ 1
  smooth : (X → ℝ) × (Y → UnitAddCircle) → ℂ
  smooth_bound : ∀ z, ‖smooth z‖ ≤ 1
  smooth_lipschitz : LipschitzWith L smooth

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def mono {Y : Type*} [Fintype Y]
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    {periodCap' coverCap' : ℝ} {L' : ℝ≥0}
    (hp : periodCap ≤ periodCap') (hc : coverCap ≤ coverCap') (hL : L ≤ L') :
    NormalizedPolynomialTwist X Y periodCap' coverCap' L' :=
  { W with
    modulus_bound := W.modulus_bound.trans hp
    cover_bound := W.cover_bound.trans hc
    smooth_lipschitz := W.smooth_lipschitz.weaken hL }

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def rankQuadrupleParameters {N : ℕ} (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ZMod N :=
  ![t.2.1, t.2.1 - t.1, t.2.2, t.2.2 - t.1]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem torus_nsmul_reindex_lipschitz {A B : Type*} [Fintype A] [Fintype B]
    (r : B → A) (n : ℕ) : LipschitzWith (n : ℝ≥0)
      (fun z : A → UnitAddCircle => fun i : B => n • z (r i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  calc
    _ = ‖n • (x (r i) - y (r i))‖ := by rw [dist_eq_norm, nsmul_sub]
    _ ≤ n * ‖x (r i) - y (r i)‖ := norm_nsmul_le
    _ ≤ (n : ℝ≥0) * dist x y := by
      rw [← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y (r i)) (Nat.cast_nonneg _)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators Classical NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {pw cw pv cv : ℝ} {Lw Lv : ℝ≥0}

theorem complex_dist_product (a b c d : ℂ) :
    dist (a * b) (c * d) ≤ ‖a‖ * dist b d + dist a c * ‖d‖ := by
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  calc
    _ = ‖a * (b - d) + (a - c) * d‖ := by congr 1; ring
    _ ≤ ‖a * (b - d)‖ + ‖(a - c) * d‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IndexedComparableScalarParameterBox
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def comparableScalarParameterRadius (r L : ℝ) : ℕ := ⌈r * L⌉₊

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CommonSectionAmbientDensityMultiple
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

theorem unitAddCircle_coe_sum {A : Type*} [Fintype A] (a : A → ℝ) :
    ((∑ t, a t : ℝ) : UnitAddCircle) = ∑ t, (a t : UnitAddCircle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) a Finset.univ

end Erdos3.VectorPolynomial

end

end OAI
end


