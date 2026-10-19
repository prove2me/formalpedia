-- Prove2me | Definitions.Def_OAIE3v2B001
-- name    : OAIE3v2B001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:39.918288+00:00
-- url     : https://prove2.me/theorems/33e18e73-8509-4884-93d4-3a4adb812657
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 2 of 311
-- statement:
--   Definitions bundle 2 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CoefficientProfileBudget.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/DynkinTrees.lean`, `Estimates/FormalExpLog.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/FreePrimitiveCriterion.lean`, `Estimates/LinearQuotientCoverAverage.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/PhysicalSliceCost.lean`, `Estimates/TensorContraction.lean`, `Estimates/TruncatedSeries.lean`, `FixedDensity/BoundaryBernoulli.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/RectangularGridCharacter.lean`, `Fourier/TorusCircleActions.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Lattices/CoverBasisResidues.lean`, `Lattices/EuclideanShortLatticeBasis.lean`, `Lattices/IntegerKernelCoordinates.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/DynkinProjection.lean`, `Linear/LieWordProjection.lean`, `Linear/OrthogonalBasisChart.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/LieBCHContinuity.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/LayerTailDegree.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Probability/OrthonormalMixedLaw.lean`, `Probability/RestrictedComplexChartDensityComparison.lean`, `Probability/SampledWeightCellLaw.lean`, `Sampling/FrozenPartitionScore.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientProfileBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coefficientProfileWidth {J : Type*} (P : Finset J) (j₀ : J)
    (ρ γ ε : ℝ) (j : J) : ℝ := by
  classical
  exact if j = j₀ then ρ else if j ∈ P then γ / 2 else ε

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure FiniteProbabilityWeights (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

noncomputable def pi (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    FiniteProbabilityWeights (∀ j, Ω j) := by
  classical
  exact {
    weight := fun x => ∏ j, (p j).weight (x j)
    nonneg := fun x => Finset.prod_nonneg (fun j _ => (p j).nonneg (x j))
    total := by
      calc
        _ = ∏ j, ∑ x, (p j).weight x := (Fintype.prod_sum _).symm
        _ = ∏ _j : J, (1 : ℝ) := Finset.prod_congr rfl (fun j _ => (p j).total)
        _ = 1 := by simp }

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DynkinTrees
namespace OAI

section

namespace Erdos3

abbrev WordPolynomial (X : Type*) := MonoidAlgebra ℚ (FreeSemigroup X)

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def rightBracket (x : L) : Module.End ℚ L where
  toFun z := ⁅z, x⁆
  map_add' z w := add_lie z w x
  map_smul' c z := smul_lie c z x

@[simp] theorem rightBracket_apply (x z : L) : rightBracket x z = ⁅z, x⁆ := rfl

def rightBracketList (f : X → L) : List X → Module.End ℚ L
  | [] => 1
  | x :: xs => rightBracketList f xs * rightBracket (f x)

@[simp] theorem rightBracketList_nil (f : X → L) : rightBracketList f [] = 1 := rfl
@[simp] theorem rightBracketList_cons (f : X → L) (x : X) (xs : List X) :
    rightBracketList f (x :: xs) = rightBracketList f xs * rightBracket (f x) := rfl

def rightBracketWord (f : X → L) (w : FreeSemigroup X) : Module.End ℚ L :=
  rightBracketList f (w.head :: w.tail)

def dynkinWord (f : X → L) (w : FreeSemigroup X) : L :=
  rightBracketList f w.tail (f w.head)

noncomputable def wordLinearMap {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeSemigroup X → M) : WordPolynomial X →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ v).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem wordLinearMap_single {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeSemigroup X → M) (w : FreeSemigroup X) (r : ℚ) :
    wordLinearMap v (MonoidAlgebra.single w r) = r • v w := by
  simp [wordLinearMap]

noncomputable def dynkinMap (f : X → L) : WordPolynomial X →ₗ[ℚ] L :=
  wordLinearMap (dynkinWord f)

noncomputable def rightAction (f : X → L) : WordPolynomial X →ₗ[ℚ] Module.End ℚ L :=
  wordLinearMap (rightBracketWord f)

@[simp] theorem dynkinMap_single (f : X → L) (w : FreeSemigroup X) (r : ℚ) :
    dynkinMap f (MonoidAlgebra.single w r) = r • dynkinWord f w := wordLinearMap_single _ _ _

@[simp] theorem rightAction_single (f : X → L) (w : FreeSemigroup X) (r : ℚ) :
    rightAction f (MonoidAlgebra.single w r) = r • rightBracketWord f w :=
  wordLinearMap_single _ _ _

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def lieTreeEval (f : X → L) : FreeMagma X → L
  | .of x => f x
  | .mul u v => ⁅lieTreeEval f u, lieTreeEval f v⁆

noncomputable def commutatorTree : FreeMagma X → WordPolynomial X
  | .of x => MonoidAlgebra.single (FreeSemigroup.of x) 1
  | .mul u v => commutatorTree u * commutatorTree v - commutatorTree v * commutatorTree u

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalExpLog
namespace OAI

section

namespace Erdos3

open PowerSeries

theorem formalSeries_eq_of_derivative_eq {f g : PowerSeries ℚ}
    (hd : derivative ℚ f = derivative ℚ g) (hc : constantCoeff f = constantCoeff g) :
    f = g := by
  ext n
  cases n with
  | zero => simpa only [coeff_zero_eq_constantCoeff] using hc
  | succ n =>
    have h := congrArg (coeff n) hd
    simp only [coeff_derivative] at h
    exact mul_right_cancel₀ (by positivity : (n : ℚ) + 1 ≠ 0) h

theorem formal_log_derivative_mul : derivative ℚ (log ℚ) * (1 + X) = (1 : PowerSeries ℚ) := by
  rw [deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_add, coeff_succ_mul_X, coeff_mk, coeff_one, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, pow_succ]
    simp

theorem formal_log_derivative_subst {f : PowerSeries ℚ} (hf : HasSubst f) :
    (derivative ℚ (log ℚ)).subst f * (1 + f) = 1 := by
  have h := congrArg (substAlgHom hf) formal_log_derivative_mul
  simpa only [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom] using h

theorem formal_log_exp : (log ℚ).subst (exp ℚ - 1) = (X : PowerSeries ℚ) := by
  apply formalSeries_eq_of_derivative_eq
  · rw [derivative_subst HasSubst.exp_sub_one, derivative_X]
    have hd : derivative ℚ (exp ℚ - 1) = exp ℚ := by simp [derivative_exp]
    rw [hd]
    have hadd : (1 : PowerSeries ℚ) + (exp ℚ - 1) = exp ℚ := by abel
    simpa only [hadd] using
      formal_log_derivative_subst (f := exp ℚ - 1) HasSubst.exp_sub_one
  · have h := constantCoeff_logOf (f := exp ℚ) constantCoeff_exp
    simpa only [logOf_eq, constantCoeff_X] using h

theorem formal_exp_sub_one_log : (exp ℚ - 1).subst (log ℚ) = (X : PowerSeries ℚ) := by
  have hP' : IsUnit (coeff 1 (log ℚ)) := by rw [coeff_one_log]; exact isUnit_one
  have hQ : exp ℚ - 1 = (log ℚ).substInvOfIsUnit hP' := calc
    _ = PowerSeries.subst (exp ℚ - 1) X := (subst_X HasSubst.exp_sub_one).symm
    _ = _ := by
      rw [← (log ℚ).subst_substInvOfIsUnit_left constantCoeff_log hP',
        subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' constantCoeff_log)
          HasSubst.exp_sub_one _, formal_log_exp, X_subst _]
  rw [hQ, (log ℚ).subst_substInvOfIsUnit_left constantCoeff_log hP']

theorem formal_exp_log : (exp ℚ).subst (log ℚ) = (1 + X : PowerSeries ℚ) := by
  have h := formal_exp_sub_one_log
  rw [subst_sub HasSubst.log] at h
  have hone : (1 : PowerSeries ℚ).subst (log ℚ) = 1 := by
    rw [← coe_substAlgHom HasSubst.log, map_one]
  rw [hone] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TruncatedSeries
namespace OAI

section

namespace Erdos3
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

def truncatedSeriesCon (A : Type*) [Ring A] (s : ℕ) : RingCon (PowerSeries A) where
  r f g := ∀ n, n ≤ s → PowerSeries.coeff n f = PowerSeries.coeff n g
  iseqv := ⟨fun _ _ _ => rfl, fun h n hn => (h n hn).symm,
    fun h₁ h₂ n hn => (h₁ n hn).trans (h₂ n hn)⟩
  add' hf hg n hn := by rw [map_add, map_add, hf n hn, hg n hn]
  mul' hf hg n hn := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [hf ij.1 (by omega), hg ij.2 (by omega)]

abbrev TruncatedSeries (A : Type*) [Ring A] (s : ℕ) := (truncatedSeriesCon A s).Quotient

noncomputable def truncatedSeriesMk (s : ℕ) : PowerSeries A →ₐ[ℚ] TruncatedSeries A s :=
  (truncatedSeriesCon A s).mkₐ ℚ

theorem truncatedSeriesMk_surjective (s : ℕ) :
    Function.Surjective (truncatedSeriesMk (A := A) s) :=
  (truncatedSeriesCon A s).mkₐ_surjective

theorem truncatedSeriesMk_eq_iff (s : ℕ) (f g : PowerSeries A) :
    truncatedSeriesMk s f = truncatedSeriesMk s g ↔
      ∀ n, n ≤ s → PowerSeries.coeff n f = PowerSeries.coeff n g :=
  (truncatedSeriesCon A s).eq

noncomputable def truncatedSeriesCoeff (s n : ℕ) (hn : n ≤ s) :
    TruncatedSeries A s →ₗ[ℚ] A where
  toFun := Quotient.lift (PowerSeries.coeff n) (fun _ _ h => h n hn)
  map_add' p q := by
    obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
    obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
    exact map_add (PowerSeries.coeff n) f g
  map_smul' r p := by
    obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
    exact PowerSeries.coeff_smul n f r

@[simp] theorem truncatedSeriesCoeff_mk (s n : ℕ) (hn : n ≤ s) (f : PowerSeries A) :
    truncatedSeriesCoeff s n hn (truncatedSeriesMk s f) = PowerSeries.coeff n f := rfl

theorem truncatedSeries_ext {s : ℕ} {p q : TruncatedSeries A s}
    (h : ∀ n (hn : n ≤ s), truncatedSeriesCoeff s n hn p = truncatedSeriesCoeff s n hn q) :
    p = q := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  exact (truncatedSeriesMk_eq_iff s f g).mpr h

noncomputable def seriesConstantCoeff : PowerSeries A →ₐ[ℚ] A :=
  { PowerSeries.constantCoeff with
    commutes' r := by
      change PowerSeries.constantCoeff (PowerSeries.C (algebraMap ℚ A r)) = _
      exact PowerSeries.constantCoeff_C _ }

noncomputable def truncatedSeriesConstantCoeff (s : ℕ) : TruncatedSeries A s →ₐ[ℚ] A :=
  (truncatedSeriesCon A s).liftₐ seriesConstantCoeff (by
    intro f g h
    change PowerSeries.constantCoeff f = PowerSeries.constantCoeff g
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h 0 (Nat.zero_le s))

@[simp] theorem truncatedSeriesConstantCoeff_mk (s : ℕ) (f : PowerSeries A) :
    truncatedSeriesConstantCoeff s (truncatedSeriesMk s f) = PowerSeries.constantCoeff f := rfl

noncomputable def truncatedSeriesMap (s : ℕ) (φ : A →ₐ[ℚ] B) :
    TruncatedSeries A s →ₐ[ℚ] TruncatedSeries B s :=
  (truncatedSeriesCon A s).liftₐ ((truncatedSeriesMk s).comp (PowerSeries.mapAlgHom φ)) (by
    intro f g h
    apply (truncatedSeriesMk_eq_iff s _ _).mpr
    intro n hn
    change φ (PowerSeries.coeff n f) = φ (PowerSeries.coeff n g)
    rw [h n hn])

@[simp] theorem truncatedSeriesMap_mk (s : ℕ) (φ : A →ₐ[ℚ] B) (f : PowerSeries A) :
    truncatedSeriesMap s φ (truncatedSeriesMk s f) =
      truncatedSeriesMk s (PowerSeries.mapAlgHom φ f) := rfl

@[simp] theorem truncatedSeriesCoeff_map (s n : ℕ) (hn : n ≤ s) (φ : A →ₐ[ℚ] B)
    (p : TruncatedSeries A s) :
    truncatedSeriesCoeff s n hn (truncatedSeriesMap s φ p) =
      φ (truncatedSeriesCoeff s n hn p) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  simp [PowerSeries.mapAlgHom_apply]

@[simp] theorem truncatedSeriesConstantCoeff_map (s : ℕ) (φ : A →ₐ[ℚ] B)
    (p : TruncatedSeries A s) :
    truncatedSeriesConstantCoeff s (truncatedSeriesMap s φ p) =
      φ (truncatedSeriesConstantCoeff s p) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  change PowerSeries.constantCoeff (PowerSeries.map φ.toRingHom f) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff]
  rfl

noncomputable def truncatedSeriesPositive (s : ℕ) : NonUnitalSubalgebra ℚ (TruncatedSeries A s) where
  carrier := {p | truncatedSeriesConstantCoeff s p = 0}
  zero_mem' := map_zero _
  add_mem' hp hq := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp hq ⊢
    rw [map_add, hp, hq, zero_add]
  smul_mem' r p hp := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp ⊢
    rw [map_smul, hp, smul_zero]
  mul_mem' hp hq := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp hq ⊢
    rw [map_mul, hp, hq, zero_mul]

@[simp] theorem mem_truncatedSeriesPositive {s : ℕ} {p : TruncatedSeries A s} :
    p ∈ truncatedSeriesPositive s ↔ truncatedSeriesConstantCoeff s p = 0 := Iff.rfl

theorem truncatedSeriesPositive_pow {s : ℕ} {p : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesPositive s) : p ^ (s + 1) = 0 := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  change PowerSeries.constantCoeff f = 0 at hp
  rw [← map_pow, ← map_zero (truncatedSeriesMk s)]
  apply (truncatedSeriesMk_eq_iff s _ _).mpr
  intro n hn
  rw [map_zero]
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast (Nat.lt_succ_of_le hn))
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (s + 1) hp)

theorem truncatedSeriesPositive_nilpotent {s : ℕ} {p : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesPositive s) : IsNilpotent p :=
  ⟨s + 1, truncatedSeriesPositive_pow hp⟩

theorem truncatedSeriesMap_positive (s : ℕ) (φ : A →ₐ[ℚ] B)
    {p : TruncatedSeries A s} (hp : p ∈ truncatedSeriesPositive s) :
    truncatedSeriesMap s φ p ∈ truncatedSeriesPositive s := by
  rw [mem_truncatedSeriesPositive, truncatedSeriesConstantCoeff_map,
    mem_truncatedSeriesPositive.mp hp, map_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorContraction
namespace OAI

section

namespace Erdos3
open TensorProduct
variable {A : Type*} [Ring A] [Algebra ℚ A]

noncomputable def tensorContract (S T : A →ₗ[ℚ] A) : A ⊗[ℚ] A →ₗ[ℚ] A :=
  (LinearMap.mul' ℚ A).comp (TensorProduct.map S T)

@[simp] theorem tensorContract_tmul (S T : A →ₗ[ℚ] A) (a b : A) :
    tensorContract S T (a ⊗ₜ[ℚ] b) = S a * T b := by
  simp [tensorContract]

theorem tensorContract_mul_left (S T : A →ₗ[ℚ] A)
    (hS : ∀ a b, S (a * b) = S b * S a) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S T (t * (a ⊗ₜ[ℚ] 1)) = S a * tensorContract S T t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, hS, mul_assoc]
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, mul_add]

theorem tensorContract_id_mul_right (S : A →ₗ[ℚ] A) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S LinearMap.id (t * (1 ⊗ₜ[ℚ] a)) =
      tensorContract S LinearMap.id t * a := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc]
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]

theorem tensorContract_derivation_mul_right (S T : A →ₗ[ℚ] A)
    (hT : ∀ a b, T (a * b) = T a * b + a * T b) (t : A ⊗[ℚ] A) (a : A) :
    tensorContract S T (t * (1 ⊗ₜ[ℚ] a)) =
      tensorContract S T t * a + tensorContract S LinearMap.id t * T a := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [Algebra.TensorProduct.tmul_mul_tmul, hT, mul_add, mul_assoc]
  | add p q hp hq =>
    simp only [add_mul, map_add, hp, hq]
    abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DynkinProjection
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

def WordHomogeneous (n : ℕ) (p : WordPolynomial X) : Prop :=
  ∀ w, p.coeff w ≠ 0 → w.length = n

theorem WordHomogeneous.mul {n m : ℕ} {p q : WordPolynomial X}
    (hp : WordHomogeneous n p) (hq : WordHomogeneous m q) : WordHomogeneous (n + m) (p * q) := by
  classical
  intro w hw
  by_contra hlen
  apply hw
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have hu' := hp u (Finsupp.mem_support_iff.mp hu)
  have hv' := hq v (Finsupp.mem_support_iff.mp hv)
  have hne : u * v ≠ w := by
    intro he
    apply hlen
    rw [← he, FreeSemigroup.length_mul, hu', hv']
  simp only [hne, ite_false]

noncomputable def dynkinProjection (f : X → L) : WordPolynomial X →ₗ[ℚ] L :=
  wordLinearMap (fun w => (w.length : ℚ)⁻¹ • dynkinWord f w)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3

variable {X : Type*}

noncomputable instance wordPolynomialLieRing : LieRing (WordPolynomial X) where
  bracket p q := p * q - q * p
  add_lie p q r := by change (p + q) * r - r * (p + q) = _; simp [add_mul, mul_add]; abel
  lie_add p q r := by change p * (q + r) - (q + r) * p = _; simp [add_mul, mul_add]; abel
  lie_self p := by change p * p - p * p = 0; exact sub_self _
  leibniz_lie p q r := by
    change p * (q * r - r * q) - (q * r - r * q) * p =
      (p * q - q * p) * r - r * (p * q - q * p) +
        (q * (p * r - r * p) - (p * r - r * p) * q)
    noncomm_ring

noncomputable instance wordPolynomialLieAlgebra : LieAlgebra ℚ (WordPolynomial X) where
  lie_smul c p q := by
    change p * (c • q) - (c • q) * p = c • (p * q - q * p)
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]

@[simp] theorem wordPolynomial_lie (p q : WordPolynomial X) : ⁅p, q⁆ = p * q - q * p := rfl

noncomputable def freeLieWordExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ WordPolynomial X :=
  FreeLieAlgebra.lift ℚ (fun x => MonoidAlgebra.single (FreeSemigroup.of x) 1)

@[simp] theorem freeLieWordExpansion_of (x : X) :
    freeLieWordExpansion (FreeLieAlgebra.of ℚ x) = MonoidAlgebra.single (FreeSemigroup.of x) 1 :=
  FreeLieAlgebra.lift_of_apply _ _

theorem freeLieWordExpansion_tree (t : FreeMagma X) :
    freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) t) = commutatorTree t := by
  induction t using FreeMagma.rec with
  | of x => exact freeLieWordExpansion_of x
  | mul u v hu hv =>
    change freeLieWordExpansion ⁅lieTreeEval (FreeLieAlgebra.of ℚ) u,
      lieTreeEval (FreeLieAlgebra.of ℚ) v⁆ = _
    rw [LieHom.map_lie, hu, hv]
    rfl

theorem freeLie_mk_single_tree (t : FreeMagma X) :
    (FreeLieAlgebra.mk ℚ (MonoidAlgebra.single t 1) : FreeLieAlgebra ℚ X) =
      lieTreeEval (FreeLieAlgebra.of ℚ) t := by
  induction t using FreeMagma.rec with
  | of x => rfl
  | mul u v hu hv =>
    have hs := MonoidAlgebra.single_mul_single u v (1 : ℚ) 1
    simp only [one_mul] at hs
    change FreeLieAlgebra.mk ℚ (MonoidAlgebra.single (u * v) 1) = _
    rw [← hs, map_mul]
    change ⁅(FreeLieAlgebra.mk ℚ (MonoidAlgebra.single u 1) : FreeLieAlgebra ℚ X),
      (FreeLieAlgebra.mk ℚ (MonoidAlgebra.single v 1) : FreeLieAlgebra ℚ X)⁆ = _
    rw [hu, hv]
    rfl

theorem freeLie_linear_induction (P : FreeLieAlgebra ℚ X → Prop)
    (hz : P 0) (ha : ∀ x y, P x → P y → P (x + y))
    (hs : ∀ (r : ℚ) x, P x → P (r • x))
    (ht : ∀ t : FreeMagma X, P (lieTreeEval (FreeLieAlgebra.of ℚ) t))
    (x : FreeLieAlgebra ℚ X) : P x := by
  refine Quot.inductionOn x ?_
  intro q
  change P (FreeLieAlgebra.mk ℚ q)
  induction q using MonoidAlgebra.induction_linear with
  | zero =>
    change P (0 : FreeLieAlgebra ℚ X)
    exact hz
  | add p q hp hq =>
    change P ((FreeLieAlgebra.mk ℚ p : FreeLieAlgebra ℚ X) +
      (FreeLieAlgebra.mk ℚ q : FreeLieAlgebra ℚ X))
    exact ha _ _ hp hq
  | single t r =>
    have he : MonoidAlgebra.single t r = r • MonoidAlgebra.single t (1 : ℚ) := by simp
    rw [he, map_smul, freeLie_mk_single_tree]
    exact hs r _ (ht t)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def wordPolynomialEmbedding : WordPolynomial X →ₙₐ[ℚ] FreeAlgebra ℚ X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.toNonUnitalAlgHom).comp
    (MonoidAlgebra.mapDomainNonUnitalAlgHom ℚ ℚ FreeSemigroup.toFreeMonoid)

@[simp] theorem wordPolynomialEmbedding_generator (x : X) :
    wordPolynomialEmbedding (MonoidAlgebra.single (FreeSemigroup.of x) 1) = FreeAlgebra.ι ℚ x := by
  let e : FreeAlgebra ℚ X ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid X) :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid
  change e.symm (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid
    (MonoidAlgebra.single (FreeSemigroup.of x) 1)) = _
  rw [MonoidAlgebra.mapDomain_single, FreeSemigroup.toFreeMonoid_of]
  apply e.injective
  rw [e.apply_symm_apply]
  change MonoidAlgebra.single (FreeMonoid.of x) 1 =
    FreeAlgebra.lift ℚ (fun x => MonoidAlgebra.of ℚ (FreeMonoid X) (FreeMonoid.of x))
      (FreeAlgebra.ι ℚ x)
  rw [FreeAlgebra.lift_ι_apply]
  rfl

noncomputable def wordPolynomialEmbeddingLie : WordPolynomial X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X where
  toFun := wordPolynomialEmbedding
  map_add' := map_add wordPolynomialEmbedding
  map_smul' := map_smul wordPolynomialEmbedding
  map_lie' {p q} := by
    change wordPolynomialEmbedding (p * q - q * p) =
      wordPolynomialEmbedding p * wordPolynomialEmbedding q -
        wordPolynomialEmbedding q * wordPolynomialEmbedding p
    rw [map_sub, map_mul, map_mul]

noncomputable def freeLieAssociativeExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X :=
  FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ)

theorem wordPolynomialEmbedding_comp_freeLie :
    wordPolynomialEmbeddingLie.comp freeLieWordExpansion =
      (freeLieAssociativeExpansion : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeAlgebra ℚ X) := by
  apply FreeLieAlgebra.hom_ext
  intro x
  change wordPolynomialEmbedding (freeLieWordExpansion (FreeLieAlgebra.of ℚ x)) =
    freeLieAssociativeExpansion (FreeLieAlgebra.of ℚ x)
  rw [freeLieWordExpansion_of, wordPolynomialEmbedding_generator]
  exact (FreeLieAlgebra.lift_of_apply _ _).symm

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

noncomputable def freeWordLinearMap {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeMonoid X → M) : FreeAlgebra ℚ X →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ v).comp
    ((MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap)

theorem freeMonoid_induction_right (P : FreeMonoid X → Prop) (h1 : P 1)
    (hstep : ∀ w x, P w → P (w * FreeMonoid.of x)) (w : FreeMonoid X) : P w := by
  have h : ∀ xs : List X, P (FreeMonoid.ofList xs) := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil => exact h1
    | append_singleton xs x ih =>
      rw [FreeMonoid.ofList_append, FreeMonoid.ofList_singleton]
      exact hstep _ _ ih
  exact h w.toList

end Erdos3

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem map_lieTreeEval (φ : L →ₗ⁅ℚ⁆ M) (f : X → L) (t : FreeMagma X) :
    φ (lieTreeEval f t) = lieTreeEval (fun x => φ (f x)) t := by
  induction t using FreeMagma.rec with
  | of x => rfl
  | mul u v hu hv => simp only [lieTreeEval, LieHom.map_lie, hu, hv]

theorem lift_lieTreeEval (f : X → L) (t : FreeMagma X) :
    FreeLieAlgebra.lift ℚ f (lieTreeEval (FreeLieAlgebra.of ℚ) t) = lieTreeEval f t := by
  rw [map_lieTreeEval]
  simp only [FreeLieAlgebra.lift_of_apply]

theorem rightBracketList_mem_lowerCentralSeries (f : X → L) (xs : List X)
    {n : ℕ} {z : L} (hz : z ∈ LieModule.lowerCentralSeries ℚ L L n) :
    rightBracketList f xs z ∈ LieModule.lowerCentralSeries ℚ L L (n + xs.length) := by
  induction xs generalizing n z with
  | nil => simpa only [rightBracketList_nil, Module.End.one_apply, List.length_nil, Nat.add_zero] using hz
  | cons x xs ih =>
    have hleft : ⁅f x, z⁆ ∈ LieModule.lowerCentralSeries ℚ L L (n + 1) := by
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hz
    have hright : ⁅z, f x⁆ ∈ LieModule.lowerCentralSeries ℚ L L (n + 1) := by
      rw [← lie_skew z (f x)]
      exact (LieModule.lowerCentralSeries ℚ L L (n + 1)).neg_mem hleft
    have h := ih hright
    simpa only [rightBracketList_cons, Module.End.mul_apply, rightBracket_apply,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1 xs.length] using h

theorem dynkinWord_mem_lowerCentralSeries (f : X → L) (w : FreeSemigroup X) :
    dynkinWord f w ∈ LieModule.lowerCentralSeries ℚ L L w.tail.length := by
  have h : f w.head ∈ LieModule.lowerCentralSeries ℚ L L 0 := by
    rw [LieModule.lowerCentralSeries_zero]
    exact LieSubmodule.mem_top _
  simpa only [dynkinWord, Nat.zero_add] using rightBracketList_mem_lowerCentralSeries f w.tail h

theorem dynkinWord_eq_zero_of_length_gt (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {w : FreeSemigroup X}
    (hw : s < w.length) : dynkinWord f w = 0 := by
  have hle : s ≤ w.tail.length := by change s < w.tail.length + 1 at hw; omega
  have h := LieModule.antitone_lowerCentralSeries ℚ L L hle
    (dynkinWord_mem_lowerCentralSeries f w)
  simpa only [hnil, LieSubmodule.mem_bot] using h

theorem dynkinProjection_eq_zero_of_low_coeff_zero (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p : WordPolynomial X}
    (hp : ∀ w, w.length ≤ s → p.coeff w = 0) : dynkinProjection f p = 0 := by
  classical
  change p.coeff.sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) = 0
  apply Finset.sum_eq_zero
  intro w hw
  have hgt : s < w.length := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hw) (hp w (Nat.le_of_not_gt hn))
  dsimp only
  rw [dynkinWord_eq_zero_of_length_gt f hnil hgt, smul_zero, smul_zero]

theorem dynkinProjection_eq_of_low_coeff_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : WordPolynomial X}
    (hpq : ∀ w, w.length ≤ s → p.coeff w = q.coeff w) :
    dynkinProjection f p = dynkinProjection f q := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply dynkinProjection_eq_zero_of_low_coeff_zero f hnil
  intro w hw
  change p.coeff w - q.coeff w = 0
  rw [hpq w hw, sub_self]

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}

noncomputable def freeCoproduct : FreeAlgebra ℚ X →ₐ[ℚ]
    FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X :=
  FreeAlgebra.lift ℚ (fun x => FreeAlgebra.ι ℚ x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] FreeAlgebra.ι ℚ x)

@[simp] theorem freeCoproduct_generator (x : X) :
    freeCoproduct (FreeAlgebra.ι ℚ x) =
      FreeAlgebra.ι ℚ x ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] FreeAlgebra.ι ℚ x :=
  FreeAlgebra.lift_ι_apply _ _

noncomputable def freeAugmentation : FreeAlgebra ℚ X →ₐ[ℚ] ℚ :=
  FreeAlgebra.lift ℚ (fun _ => 0)

@[simp] theorem freeAugmentation_generator (x : X) : freeAugmentation (FreeAlgebra.ι ℚ x) = 0 :=
  FreeAlgebra.lift_ι_apply _ _

noncomputable def freeAntipodeOp : FreeAlgebra ℚ X →ₐ[ℚ] (FreeAlgebra ℚ X)ᵐᵒᵖ :=
  FreeAlgebra.lift ℚ (fun x => MulOpposite.op (-FreeAlgebra.ι ℚ x))

noncomputable def freeAntipode : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap.comp freeAntipodeOp.toLinearMap

@[simp] theorem freeAntipode_generator (x : X) : freeAntipode (FreeAlgebra.ι ℚ x) = -FreeAlgebra.ι ℚ x := by
  change MulOpposite.unop (freeAntipodeOp (FreeAlgebra.ι ℚ x)) = _
  rw [freeAntipodeOp, FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem freeAntipode_one : freeAntipode (1 : FreeAlgebra ℚ X) = 1 := by
  change MulOpposite.unop (freeAntipodeOp 1) = 1
  rw [map_one, MulOpposite.unop_one]

theorem freeAntipode_mul (p q : FreeAlgebra ℚ X) :
    freeAntipode (p * q) = freeAntipode q * freeAntipode p := by
  change MulOpposite.unop (freeAntipodeOp (p * q)) = _
  rw [map_mul, MulOpposite.unop_mul]
  rfl

def FreePrimitive (p : FreeAlgebra ℚ X) : Prop :=
  freeCoproduct p = p ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] p

theorem freePrimitive_generator (x : X) : FreePrimitive (FreeAlgebra.ι ℚ x) :=
  freeCoproduct_generator x

theorem FreePrimitive.commutator {p q : FreeAlgebra ℚ X}
    (hp : FreePrimitive p) (hq : FreePrimitive q) : FreePrimitive (p * q - q * p) := by
  unfold FreePrimitive at hp hq ⊢
  simp only [map_sub, map_mul, hp, hq, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, sub_tmul, tmul_sub]
  abel

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

noncomputable def freeScaleSeries : FreeAlgebra ℚ X →ₐ[ℚ] PowerSeries (FreeAlgebra ℚ X) :=
  FreeAlgebra.lift ℚ (fun x => PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x))

@[simp] theorem freeScaleSeries_generator (x : X) :
    freeScaleSeries (FreeAlgebra.ι ℚ x) = PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x) :=
  FreeAlgebra.lift_ι_apply _ _

noncomputable def freeHomogeneousPart (n : ℕ) : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  ((PowerSeries.coeff n).restrictScalars ℚ).comp freeScaleSeries.toLinearMap

theorem freeHomogeneousPart_apply (n : ℕ) (p : FreeAlgebra ℚ X) :
    freeHomogeneousPart n p = PowerSeries.coeff n (freeScaleSeries p) := rfl

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def wordTruncation (s : ℕ) : WordPolynomial X →ₗ[ℚ] WordPolynomial X :=
  wordLinearMap (fun w => if w.length ≤ s then MonoidAlgebra.single w 1 else 0)

@[simp] theorem wordTruncation_single (s : ℕ) (w : FreeSemigroup X) (r : ℚ) :
    wordTruncation s (MonoidAlgebra.single w r) =
      if w.length ≤ s then MonoidAlgebra.single w r else 0 := by
  simp only [wordTruncation, wordLinearMap_single]
  split_ifs <;> simp

theorem wordTruncation_coeff (s : ℕ) (p : WordPolynomial X) (w : FreeSemigroup X) :
    (wordTruncation s p).coeff w = if w.length ≤ s then p.coeff w else 0 := by
  classical
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  | single u r =>
    rw [wordTruncation_single]
    by_cases he : u = w
    · subst u
      split_ifs <;> simp
    · split_ifs <;> simp [he]

theorem wordTruncation_eq_iff (s : ℕ) (p q : WordPolynomial X) :
    wordTruncation s p = wordTruncation s q ↔
      ∀ w, w.length ≤ s → p.coeff w = q.coeff w := by
  constructor
  · intro h w hw
    have he := congrArg (fun p : WordPolynomial X => p.coeff w) h
    simpa only [wordTruncation_coeff, hw, ite_true] using he
  · intro h
    ext w
    simp only [wordTruncation_coeff]
    split_ifs with hw
    · exact h w hw
    · rfl

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def freeAssociativeLieSubalgebra : LieSubalgebra ℚ (FreeAlgebra ℚ X) :=
  freeLieAssociativeExpansion.range

theorem freeAssociativeLieSubalgebra_generator (x : X) :
    FreeAlgebra.ι ℚ x ∈ freeAssociativeLieSubalgebra := by
  exact ⟨FreeLieAlgebra.of ℚ x, FreeLieAlgebra.lift_of_apply _ _⟩

noncomputable def freeAntipodeConvolution : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (tensorContract freeAntipode LinearMap.id).comp freeCoproduct.toLinearMap

@[simp] theorem freeAntipodeConvolution_one :
    freeAntipodeConvolution (1 : FreeAlgebra ℚ X) = 1 := by
  simp [freeAntipodeConvolution, Algebra.TensorProduct.one_def]

theorem freeAntipodeConvolution_mul_generator (p : FreeAlgebra ℚ X) (x : X) :
    freeAntipodeConvolution (p * FreeAlgebra.ι ℚ x) =
      -FreeAlgebra.ι ℚ x * freeAntipodeConvolution p +
        freeAntipodeConvolution p * FreeAlgebra.ι ℚ x := by
  change tensorContract freeAntipode LinearMap.id (freeCoproduct (p * FreeAlgebra.ι ℚ x)) = _
  rw [map_mul, freeCoproduct_generator, mul_add, map_add,
    tensorContract_mul_left _ _ freeAntipode_mul, tensorContract_id_mul_right,
    freeAntipode_generator]
  rfl

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem freePrimitive_lieTree (t : FreeMagma X) :
    FreePrimitive (lieTreeEval (FreeAlgebra.ι ℚ) t) := by
  induction t using FreeMagma.rec with
  | of x => exact freePrimitive_generator x
  | mul u v hu hv => exact hu.commutator hv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LieWordProjection
namespace OAI

section

namespace Erdos3

variable {X : Type*}

noncomputable def lieWordProjection : WordPolynomial X →ₗ[ℚ] WordPolynomial X :=
  freeLieWordExpansion.toLinearMap.comp (dynkinProjection (FreeLieAlgebra.of ℚ))

@[simp] theorem lieWordProjection_apply (p : WordPolynomial X) :
    lieWordProjection p = freeLieWordExpansion (dynkinProjection (FreeLieAlgebra.of ℚ) p) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem wordPolynomialEmbedding_freeLieExpansion (p : FreeLieAlgebra ℚ X) :
    wordPolynomialEmbedding (freeLieWordExpansion p) = freeLieAssociativeExpansion p :=
  DFunLike.congr_fun wordPolynomialEmbedding_comp_freeLie p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

abbrev Circle := UnitAddCircle

def integerDistance (x : Circle) : ℝ := ‖x‖

@[simp]
theorem integerDistance_zero : integerDistance (0 : Circle) = 0 := by
  simp [integerDistance]

@[simp]
theorem integerDistance_neg (x : Circle) : integerDistance (-x) = integerDistance x := by
  simp [integerDistance]

@[simp]
theorem integerDistance_coe (x : ℝ) :
    integerDistance (x : Circle) = |x - round x| := by
  simp [integerDistance, UnitAddCircle.norm_eq]

def character (x : Circle) : ℂ := AddCircle.toCircle x

@[simp]
theorem character_zero : character 0 = 1 := by
  simp [character]

@[simp]
theorem character_add (x y : Circle) : character (x + y) = character x * character y := by
  unfold character
  rw [AddCircle.toCircle_add]
  rfl

@[simp]
theorem character_neg (x : Circle) : character (-x) = star (character x) := by
  unfold character
  rw [AddCircle.toCircle_neg, _root_.Circle.coe_inv, Complex.inv_def,
    _root_.Circle.normSq_coe]
  simp

@[simp]
theorem character_nsmul (n : ℕ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_nsmul]
  rfl

@[simp]
theorem character_zsmul (n : ℤ) (x : Circle) : character (n • x) = character x ^ n := by
  unfold character
  rw [AddCircle.toCircle_zsmul]
  rfl

@[simp]
theorem character_finset_sum {I : Type*} (s : Finset I) (f : I → Circle) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, character_add]

@[simp]
theorem character_fintype_sum {I : Type*} [Fintype I] (f : I → Circle) :
    character (∑ i, f i) = ∏ i, character (f i) := by
  simp

@[simp]
theorem norm_character (x : Circle) : ‖character x‖ = 1 := by
  exact Circle.norm_coe _

end
end Erdos3.CircleFourier

end

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def linearCircleHom (L : E →ₗ[ℝ] ℝ) : E →+ CircleFourier.Circle :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp L.toAddMonoidHom

theorem integral_subgroup_le_linearCircleHom_ker (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) : Γ ≤ (linearCircleHom L).ker := by
  intro x hx
  change (L x : CircleFourier.Circle) = 0
  obtain ⟨n, hn⟩ := hint x hx
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simp [hn]⟩

noncomputable def quotientLinearPhase (Γ : AddSubgroup E) (L : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) : (E ⧸ Γ) →+ CircleFourier.Circle :=
  QuotientAddGroup.lift Γ (linearCircleHom L) (integral_subgroup_le_linearCircleHom_ker Γ L hint)

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
open scoped BigOperators

noncomputable def realDensityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : Measure X := μ.withDensity (fun x => ENNReal.ofReal (f x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

def quotientIntegerCover {E : Type*} [AddCommGroup E] (Γ : AddSubgroup E) (q : ℕ) :
    (E ⧸ Γ) →+ (E ⧸ Γ) := nsmulAddMonoidHom q

theorem quotientIntegerCover_mk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) (q : ℕ) (x : E) :
    quotientIntegerCover Γ q (QuotientAddGroup.mk' Γ x) =
      QuotientAddGroup.mk' Γ ((q : ℝ) • x) := by
  change q • QuotientAddGroup.mk' Γ x = _
  rw [Nat.cast_smul_eq_nsmul, map_nsmul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal BigOperators

structure IsometricCircleAction (X : Type*) [PseudoMetricSpace X] where
  act : Circle → X → X
  zero_act : ∀ x, act 0 x = x
  add_act : ∀ t u x, act (t + u) x = act t (act u x)
  continuous_act : Continuous (fun p : Circle × X => act p.1 p.2)
  isometry_act : ∀ t, Isometry (act t)

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

@[instance_reducible] def toAddAction (A : IsometricCircleAction X) : AddAction Circle X where
  vadd := A.act
  zero_vadd := A.zero_act
  add_vadd := A.add_act

end IsometricCircleAction
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSliceCost
namespace OAI

section

namespace Erdos3

def PhysicalSubbox {σ : Type*} (parent : σ → ℤ) (H : σ → ℕ)
    (lo : σ → ℤ) (N : σ → ℕ) : Prop :=
  ∀ j, parent j ≤ lo j ∧ lo j + N j ≤ parent j + H j

theorem PhysicalSubbox.refl {σ : Type*} (lo : σ → ℤ) (N : σ → ℕ) :
    PhysicalSubbox lo N lo N := fun _ => ⟨le_rfl, le_rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BoundaryBernoulli
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev BoundaryBooleanCutAssignment
    (G : Type*) (j : ℕ) :=
  (i : Fin (j + 1)) → (Fin j → G) → Bool

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

def integerScalarLattice (J : Type*) [Fintype J] (m : ℤ) : Submodule ℤ (J → ℤ) :=
  (m • (LinearMap.id : (J → ℤ) →ₗ[ℤ] (J → ℤ))).range

theorem integerScalarLattice_mem {J : Type*} [Fintype J] (m : ℤ) (y : J → ℤ) :
    y ∈ integerScalarLattice J m ↔ ∃ z : J → ℤ, m • z = y := Iff.rfl

end Erdos3

end

section

namespace Erdos3

def integerResidueMap (I : Type*) (m : ℕ) : (I → ℤ) →ₗ[ℤ] (I → ZMod m) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

theorem integerResidueMap_surjective (I : Type*) (m : ℕ) :
    Function.Surjective (integerResidueMap I m) := by
  intro v
  choose z hz using fun i => ZMod.intCast_surjective (v i)
  exact ⟨z, funext hz⟩

theorem integerResidueMap_ker (I : Type*) [Fintype I] (m : ℕ) :
    LinearMap.ker (integerResidueMap I m) = integerScalarLattice I (m : ℤ) := by
  ext v
  rw [LinearMap.mem_ker, integerScalarLattice_mem]
  constructor
  · intro hv
    have hd : ∀ i, (m : ℤ) ∣ v i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) m).mp (congrFun hv i)
    choose z hz using hd
    exact ⟨z, funext fun i => (hz i).symm⟩
  · rintro ⟨z, rfl⟩
    ext i
    change (((m : ℤ) * z i : ℤ) : ZMod m) = 0
    simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

open PowerSeries _root_.Finset

section Ring
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def nilpotentSeries (f : PowerSeries ℚ) (a : A) : A :=
  ∑ i ∈ range (nilpotencyClass a), coeff i f • a ^ i

theorem nilpotentSeries_eq_sum (f : PowerSeries ℚ) {a : A} {k : ℕ} (h : a ^ k = 0) :
    nilpotentSeries f a = ∑ i ∈ range k, coeff i f • a ^ i := by
  unfold nilpotentSeries
  have hle : nilpotencyClass a ≤ k := csInf_le' h
  apply sum_subset (range_mono hle)
  intro i hi hnot
  rw [pow_eq_zero_of_le (Nat.le_of_not_gt (by simpa using hnot))
    (pow_nilpotencyClass ⟨k, h⟩), smul_zero]

theorem nilpotentSeries_eq_finsum (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a) :
    nilpotentSeries f a = ∑ᶠ i : ℕ, coeff i f • a ^ i := by
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hn
  have he : a ^ i = 0 := pow_eq_zero_of_le
    (Nat.le_of_not_gt (by simpa using hn)) (pow_nilpotencyClass ha)
  exact hi (by simp [he])

theorem map_nilpotentSeries (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a)
    (φ : A →ₐ[ℚ] B) : φ (nilpotentSeries f a) = nilpotentSeries f (φ a) := by
  obtain ⟨k, hk⟩ := ha
  have hk' : (φ a) ^ k = 0 := by rw [← map_pow, hk, map_zero]
  simp [nilpotentSeries_eq_sum f hk, nilpotentSeries_eq_sum f hk']

theorem nilpotentSeries_exp (a : A) :
    nilpotentSeries (PowerSeries.exp ℚ) a = IsNilpotent.exp a := by
  simp [nilpotentSeries, IsNilpotent.exp, coeff_exp, one_div]

end Ring

section CommRing
variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
theorem hasSubst_C_nilpotent {a : A} (ha : IsNilpotent a) :
    HasSubst (C a : PowerSeries A) := by
  change IsNilpotent (constantCoeff (C a))
  simpa only [constantCoeff_C] using ha

theorem subst_C_nilpotent_eq (f : PowerSeries ℚ) {a : A} (ha : IsNilpotent a) :
    f.subst (C a : PowerSeries A) = C (nilpotentSeries f a) := by
  ext n
  rw [coeff_subst' (hasSubst_C_nilpotent ha)]
  simp only [← map_pow, coeff_C]
  cases n with
  | zero => simp only [ite_true, nilpotentSeries_eq_finsum f ha]
  | succ n => simp

noncomputable def nilpotentSeriesHom {a : A} (ha : IsNilpotent a) :
    PowerSeries ℚ →ₐ[ℚ] A :=
  constantCoeff.toRatAlgHom.comp (substAlgHom (hasSubst_C_nilpotent ha))

theorem nilpotentSeriesHom_apply {a : A} (ha : IsNilpotent a) (f : PowerSeries ℚ) :
    nilpotentSeriesHom ha f = nilpotentSeries f a := by
  simp only [nilpotentSeriesHom, AlgHom.comp_apply, RingHom.toRatAlgHom_apply,
    coe_substAlgHom, subst_C_nilpotent_eq f ha, constantCoeff_C]

theorem nilpotentSeries_X {a : A} (ha : IsNilpotent a) :
    nilpotentSeries X a = a := by
  have h := subst_X (R := ℚ) (hasSubst_C_nilpotent ha)
  rw [subst_C_nilpotent_eq _ ha] at h
  exact C_injective h

theorem isNilpotent_nilpotentSeries {a : A} (ha : IsNilpotent a)
    {g : PowerSeries ℚ} (hg : constantCoeff g = 0) :
    IsNilpotent (nilpotentSeries g a) := by
  have h := (HasSubst.of_constantCoeff_zero' hg).comp (hasSubst_C_nilpotent ha)
  change IsNilpotent (nilpotentSeriesHom ha g) at h
  rwa [nilpotentSeriesHom_apply] at h

theorem nilpotentSeries_subst {a : A} (ha : IsNilpotent a)
    (f : PowerSeries ℚ) {g : PowerSeries ℚ} (hg : constantCoeff g = 0) :
    nilpotentSeries (f.subst g) a = nilpotentSeries f (nilpotentSeries g a) := by
  have h := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg)
    (hasSubst_C_nilpotent ha) f
  rw [subst_C_nilpotent_eq _ ha, subst_C_nilpotent_eq _ ha,
    subst_C_nilpotent_eq _ (isNilpotent_nilpotentSeries ha hg)] at h
  exact C_injective h

end CommRing
end Erdos3

end

section

namespace Erdos3

open PowerSeries

section Ring
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def nilpotentLog (a : A) : A := nilpotentSeries (log ℚ) a

theorem nilpotentLog_eq_sum {a : A} {k : ℕ} (h : a ^ k = 0) :
    nilpotentLog a = ∑ i ∈ Finset.range k, ((-1 : ℚ) ^ (i + 1) / i) • a ^ i := by
  rw [nilpotentLog, nilpotentSeries_eq_sum _ h]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hzero : i = 0
  · simp [hzero]
  · simp [coeff_log, hzero]

theorem map_nilpotentLog {a : A} (ha : IsNilpotent a) (φ : A →ₐ[ℚ] B) :
    φ (nilpotentLog a) = nilpotentLog (φ a) := map_nilpotentSeries _ ha φ

end Ring

section CommRing
variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem isNilpotent_nilpotentLog_comm {a : A} (ha : IsNilpotent a) :
    IsNilpotent (nilpotentLog a) := isNilpotent_nilpotentSeries ha constantCoeff_log

theorem exp_nilpotentLog_comm {a : A} (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  have h := nilpotentSeries_subst ha (exp ℚ) (g := log ℚ) constantCoeff_log
  rw [formal_exp_log, ← nilpotentSeriesHom_apply ha, map_add, map_one,
    nilpotentSeriesHom_apply, nilpotentSeries_X ha, nilpotentSeries_exp] at h
  exact h.symm

theorem nilpotentLog_exp_sub_one_comm {a : A} (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  have h := nilpotentSeries_subst ha (log ℚ) (g := exp ℚ - 1)
    (by simp [constantCoeff_exp])
  rw [formal_log_exp, nilpotentSeries_X ha, ← nilpotentSeriesHom_apply ha,
    map_sub, map_one, nilpotentSeriesHom_apply, nilpotentSeries_exp] at h
  exact h.symm

end CommRing

section Ring
variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem exp_nilpotentLog {a : A} (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := congrArg S.val (exp_nilpotentLog_comm hx)
  rw [IsNilpotent.map_exp (isNilpotent_nilpotentLog_comm hx),
    map_nilpotentLog hx, map_add, map_one] at h
  exact h

theorem nilpotentLog_exp_sub_one {a : A} (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  let S := Algebra.adjoin ℚ ({a} : Set A)
  let x : S := ⟨a, Algebra.self_mem_adjoin_singleton ℚ a⟩
  have hx : IsNilpotent x :=
    (IsNilpotent.map_iff (f := S.val) Subtype.val_injective).mp ha
  have h := congrArg S.val (nilpotentLog_exp_sub_one_comm hx)
  rw [map_nilpotentLog (IsNilpotent.isNilpotent_exp_sub_one hx), map_sub, map_one,
    IsNilpotent.map_exp hx] at h
  exact h

theorem exp_injective_on_nilpotents {a b : A} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  rw [← nilpotentLog_exp_sub_one ha, ← nilpotentLog_exp_sub_one hb, h]

end Ring
end Erdos3

end

section

namespace Erdos3

open PowerSeries _root_.Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nonUnitalSubalgebra_pow_mem (I : NonUnitalSubalgebra ℚ A) {a : A}
    (ha : a ∈ I) {n : ℕ} (hn : 0 < n) : a ^ n ∈ I := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  clear hn
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ]
    exact mul_mem ih ha

theorem nilpotentSeries_sub (f g : PowerSeries ℚ) (a : A) :
    nilpotentSeries (f - g) a = nilpotentSeries f a - nilpotentSeries g a := by
  simp [nilpotentSeries, sub_smul, sum_sub_distrib]

theorem nilpotentSeries_one {a : A} (ha : IsNilpotent a) :
    nilpotentSeries 1 a = 1 := by
  obtain ⟨k, hk⟩ := ha
  rw [nilpotentSeries_eq_sum _ (pow_eq_zero_of_le (Nat.le_succ k) hk)]
  simp [coeff_one]

theorem nilpotentSeries_mem (I : NonUnitalSubalgebra ℚ A) {a : A} (ha : a ∈ I)
    {f : PowerSeries ℚ} (hf : constantCoeff f = 0) : nilpotentSeries f a ∈ I := by
  apply I.sum_mem
  intro i hi
  by_cases hzero : i = 0
  · simp [hzero, coeff_zero_eq_constantCoeff, hf]
  · exact I.smul_mem _ (nonUnitalSubalgebra_pow_mem I ha (Nat.pos_of_ne_zero hzero))

theorem nilpotentLog_mem (I : NonUnitalSubalgebra ℚ A) {a : A} (ha : a ∈ I) :
    nilpotentLog a ∈ I := nilpotentSeries_mem I ha constantCoeff_log

theorem exp_sub_one_mem (I : NonUnitalSubalgebra ℚ A) {a : A}
    (ha : a ∈ I) (hna : IsNilpotent a) : IsNilpotent.exp a - 1 ∈ I := by
  rw [← nilpotentSeries_exp a, ← nilpotentSeries_one hna, ← nilpotentSeries_sub]
  exact nilpotentSeries_mem I ha (by simp [constantCoeff_exp])

theorem exp_mul_exp_sub_one_mem (I : NonUnitalSubalgebra ℚ A) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) (hna : IsNilpotent a) (hnb : IsNilpotent b) :
    IsNilpotent.exp a * IsNilpotent.exp b - 1 ∈ I := by
  have hpa := exp_sub_one_mem I ha hna
  have hpb := exp_sub_one_mem I hb hnb
  have hid : IsNilpotent.exp a * IsNilpotent.exp b - 1 =
      (IsNilpotent.exp a - 1) * (IsNilpotent.exp b - 1) +
        (IsNilpotent.exp a - 1) + (IsNilpotent.exp b - 1) := by noncomm_ring
  rw [hid]
  exact I.add_mem (I.add_mem (I.mul_mem hpa hpb) hpa) hpb

noncomputable def nilpotentBCH (a b : A) : A :=
  nilpotentLog (IsNilpotent.exp a * IsNilpotent.exp b - 1)

theorem nilpotentBCH_mem (I : NonUnitalSubalgebra ℚ A) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) (hna : IsNilpotent a) (hnb : IsNilpotent b) :
    nilpotentBCH a b ∈ I :=
  nilpotentLog_mem I (exp_mul_exp_sub_one_mem I ha hb hna hnb)

section NilAlgebra
variable (I : NonUnitalSubalgebra ℚ A) (hI : ∀ a ∈ I, IsNilpotent a)
include hI

theorem exp_nilpotentBCH {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    IsNilpotent.exp (nilpotentBCH a b) = IsNilpotent.exp a * IsNilpotent.exp b := by
  have hn := hI _ (exp_mul_exp_sub_one_mem I ha hb (hI _ ha) (hI _ hb))
  rw [nilpotentBCH, exp_nilpotentLog hn]
  abel

end NilAlgebra

end Erdos3

end

section

namespace Erdos3

variable {A : Type*} [Ring A] [Algebra ℚ A]

structure NilpotentBCHGroup (I : NonUnitalSubalgebra ℚ A)
    (_hI : ∀ a ∈ I, IsNilpotent a) where
  coord : A
  mem_coord : coord ∈ I

namespace NilpotentBCHGroup
variable {I : NonUnitalSubalgebra ℚ A} {hI : ∀ a ∈ I, IsNilpotent a}

@[ext]
theorem ext {a b : NilpotentBCHGroup I hI} (h : a.coord = b.coord) : a = b := by
  cases a
  cases b
  cases h
  rfl

noncomputable instance instMul : Mul (NilpotentBCHGroup I hI) where
  mul a b := ⟨nilpotentBCH a.coord b.coord,
    nilpotentBCH_mem I a.mem_coord b.mem_coord (hI _ a.mem_coord) (hI _ b.mem_coord)⟩

instance instOne : One (NilpotentBCHGroup I hI) where
  one := ⟨0, I.zero_mem⟩

instance instInv : Inv (NilpotentBCHGroup I hI) where
  inv a := ⟨-a.coord, I.neg_mem a.mem_coord⟩

@[simp] theorem coord_mul (a b : NilpotentBCHGroup I hI) :
    (a * b).coord = nilpotentBCH a.coord b.coord := rfl
@[simp] theorem coord_one : (1 : NilpotentBCHGroup I hI).coord = 0 := rfl
@[simp] theorem coord_inv (a : NilpotentBCHGroup I hI) : (a⁻¹).coord = -a.coord := rfl

end NilpotentBCHGroup
end Erdos3

end

section

namespace Erdos3

open _root_.Finset

variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

noncomputable def finiteExp (k : ℕ) (a : A) : A :=
  ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • a ^ i

noncomputable def finiteLog (k : ℕ) (a : A) : A :=
  ∑ i ∈ range k, ((-1 : ℚ) ^ (i + 1) / i) • a ^ i

theorem map_finiteExp (φ : A →ₐ[ℚ] B) (k : ℕ) (a : A) :
    φ (finiteExp k a) = finiteExp k (φ a) := by simp [finiteExp]

theorem map_finiteLog (φ : A →ₐ[ℚ] B) (k : ℕ) (a : A) :
    φ (finiteLog k a) = finiteLog k (φ a) := by simp [finiteLog]

theorem finiteExp_eq_exp {a : A} {k : ℕ} (h : a ^ k = 0) :
    finiteExp k a = IsNilpotent.exp a := (IsNilpotent.exp_eq_sum h).symm

theorem finiteLog_eq_log {a : A} {k : ℕ} (h : a ^ k = 0) :
    finiteLog k a = nilpotentLog a := (nilpotentLog_eq_sum h).symm

noncomputable def bchPolynomial (k : ℕ) : FreeAlgebra ℚ (Fin 2) :=
  finiteLog k (finiteExp k (FreeAlgebra.ι ℚ 0) * finiteExp k (FreeAlgebra.ι ℚ 1) - 1)

noncomputable def bchPolynomialEval (a b : A) : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] A :=
  FreeAlgebra.lift ℚ ![a, b]

theorem bchPolynomialEval_formula (k : ℕ) (a b : A) :
    bchPolynomialEval a b (bchPolynomial k) =
      finiteLog k (finiteExp k a * finiteExp k b - 1) := by
  simp [bchPolynomial, bchPolynomialEval, map_finiteLog, map_finiteExp]

theorem bchPolynomialEval_eq (I : NonUnitalSubalgebra ℚ A) {k : ℕ}
    (hI : ∀ a ∈ I, a ^ k = 0) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    bchPolynomialEval a b (bchPolynomial k) = nilpotentBCH a b := by
  have hna : IsNilpotent a := ⟨k, hI a ha⟩
  have hnb : IsNilpotent b := ⟨k, hI b hb⟩
  rw [bchPolynomialEval_formula, finiteExp_eq_exp (hI a ha), finiteExp_eq_exp (hI b hb),
    finiteLog_eq_log (hI _ (exp_mul_exp_sub_one_mem I ha hb hna hnb))]
  rfl

theorem map_nilpotentBCH (I : NonUnitalSubalgebra ℚ A)
    (hI : ∀ a ∈ I, IsNilpotent a) (φ : A →ₐ[ℚ] B) {a b : A}
    (ha : a ∈ I) (hb : b ∈ I) : φ (nilpotentBCH a b) = nilpotentBCH (φ a) (φ b) := by
  rw [nilpotentBCH, map_nilpotentLog (hI _
    (exp_mul_exp_sub_one_mem I ha hb (hI _ ha) (hI _ hb))), map_sub, map_mul, map_one,
    IsNilpotent.map_exp (hI _ ha), IsNilpotent.map_exp (hI _ hb), nilpotentBCH]

end Erdos3

end

section

namespace Erdos3
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem nilpotentBCH_commuting_maps
    (I : NonUnitalSubalgebra ℚ A) (hI : ∀ a ∈ I, IsNilpotent a)
    (J : NonUnitalSubalgebra ℚ B) (hJ : ∀ b ∈ J, IsNilpotent b)
    (L R : A →ₐ[ℚ] B) (hL : ∀ a ∈ I, L a ∈ J) (hR : ∀ a ∈ I, R a ∈ J)
    (hcomm : ∀ a b, Commute (L a) (R b)) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    nilpotentBCH (L a + R a) (L b + R b) = L (nilpotentBCH a b) + R (nilpotentBCH a b) := by
  have hc := nilpotentBCH_mem I ha hb (hI _ ha) (hI _ hb)
  have hca := J.add_mem (hL _ ha) (hR _ ha)
  have hcb := J.add_mem (hL _ hb) (hR _ hb)
  apply exp_injective_on_nilpotents
    (hJ _ (nilpotentBCH_mem J hca hcb (hJ _ hca) (hJ _ hcb)))
    (hJ _ (J.add_mem (hL _ hc) (hR _ hc)))
  rw [exp_nilpotentBCH J hJ hca hcb,
    IsNilpotent.exp_add_of_commute (hcomm a a) (hJ _ (hL _ ha)) (hJ _ (hR _ ha)),
    IsNilpotent.exp_add_of_commute (hcomm b b) (hJ _ (hL _ hb)) (hJ _ (hR _ hb)),
    IsNilpotent.exp_add_of_commute (hcomm _ _) (hJ _ (hL _ hc)) (hJ _ (hR _ hc)),
    ← IsNilpotent.map_exp (hI _ ha) L, ← IsNilpotent.map_exp (hI _ ha) R,
    ← IsNilpotent.map_exp (hI _ hb) L, ← IsNilpotent.map_exp (hI _ hb) R,
    ← IsNilpotent.map_exp (hI _ hc) L, ← IsNilpotent.map_exp (hI _ hc) R,
    exp_nilpotentBCH I hI ha hb, map_mul, map_mul]
  exact (hcomm (IsNilpotent.exp b) (IsNilpotent.exp a)).symm.mul_mul_mul_comm _ _

end Erdos3

end

section

namespace Erdos3

variable (A : Type*) [Ring A] [Algebra ℚ A]

structure NilpotentAlgebraFiltration (s : ℕ) where
  layer : ℕ → Submodule ℚ A
  antitone : Antitone layer
  zero_eq_top : layer 0 = ⊤
  mul_mem : ∀ {i j : ℕ} {a b : A}, a ∈ layer i → b ∈ layer j → a * b ∈ layer (i + j)
  terminal : layer (s + 1) = ⊥

namespace NilpotentAlgebraFiltration
variable {A} {s : ℕ} (F : NilpotentAlgebraFiltration A s)

def layerAlgebra (i : ℕ) : NonUnitalSubalgebra ℚ A where
  carrier := F.layer i
  zero_mem' := (F.layer i).zero_mem
  add_mem' := (F.layer i).add_mem
  smul_mem' c _ hx := (F.layer i).smul_mem c hx
  mul_mem' ha hb := F.antitone (Nat.le_add_right i i) (F.mul_mem ha hb)

@[simp] theorem mem_layerAlgebra (i : ℕ) (a : A) : a ∈ F.layerAlgebra i ↔ a ∈ F.layer i :=
  Iff.rfl

theorem pow_mem {i : ℕ} {a : A} (ha : a ∈ F.layer i) (n : ℕ) :
    a ^ n ∈ F.layer (n * i) := by
  induction n with
  | zero => simp [F.zero_eq_top]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact F.mul_mem ih ha

theorem pow_eq_zero {i : ℕ} (hi : 1 ≤ i) {a : A} (ha : a ∈ F.layer i) :
    a ^ (s + 1) = 0 := by
  have h := F.antitone (Nat.le_mul_of_pos_right (s + 1) hi) (F.pow_mem ha (s + 1))
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem isNilpotent_of_mem {i : ℕ} (hi : 1 ≤ i) {a : A} (ha : a ∈ F.layer i) :
    IsNilpotent a := ⟨s + 1, F.pow_eq_zero hi ha⟩

theorem positive_nilpotent : ∀ a ∈ F.layerAlgebra 1, IsNilpotent a :=
  fun _ ha => F.isNilpotent_of_mem le_rfl ha

abbrev Group := NilpotentBCHGroup (F.layerAlgebra 1) F.positive_nilpotent

theorem bchPolynomial_formula {a b : A} (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) :
    bchPolynomialEval a b (bchPolynomial (s + 1)) = nilpotentBCH a b :=
  bchPolynomialEval_eq (F.layerAlgebra 1) (fun _ hx => F.pow_eq_zero le_rfl hx) ha hb

theorem bch_mem {i : ℕ} (hi : 1 ≤ i) {a b : A}
    (ha : a ∈ F.layer i) (hb : b ∈ F.layer i) : nilpotentBCH a b ∈ F.layer i :=
  nilpotentBCH_mem (F.layerAlgebra i) ha hb
    (F.isNilpotent_of_mem hi ha) (F.isNilpotent_of_mem hi hb)

end NilpotentAlgebraFiltration
end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem seriesMap_commute (L R : A →ₐ[ℚ] B) (hcomm : ∀ a b, Commute (L a) (R b))
    (f g : PowerSeries A) : Commute (PowerSeries.mapAlgHom L f) (PowerSeries.mapAlgHom R g) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  conv_rhs => rw [← Finset.HasAntidiagonal.map_swap_antidiagonal]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk,
    PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map]
  apply Finset.sum_congr rfl
  intro ij _
  exact (hcomm _ _).eq

theorem truncatedSeriesMap_commute (s : ℕ) (L R : A →ₐ[ℚ] B)
    (hcomm : ∀ a b, Commute (L a) (R b)) (p q : TruncatedSeries A s) :
    Commute (truncatedSeriesMap s L p) (truncatedSeriesMap s R q) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  exact (seriesMap_commute L R hcomm f g).map (truncatedSeriesMk s)

variable {X : Type*}

def TruncatedPrimitive {s : ℕ} (p : TruncatedSeries (FreeAlgebra ℚ X) s) : Prop :=
  truncatedSeriesMap s freeCoproduct p =
    truncatedSeriesMap s Algebra.TensorProduct.includeLeft p +
      truncatedSeriesMap s Algebra.TensorProduct.includeRight p

theorem TruncatedPrimitive.coeff {s : ℕ} {p : TruncatedSeries (FreeAlgebra ℚ X) s}
    (hp : TruncatedPrimitive p) (n : ℕ) (hn : n ≤ s) :
    FreePrimitive (truncatedSeriesCoeff s n hn p) := by
  have h := congrArg (truncatedSeriesCoeff s n hn) hp
  simpa only [FreePrimitive, truncatedSeriesCoeff_map, map_add, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] using h

theorem truncatedPrimitive_iff_coeff {s : ℕ} (p : TruncatedSeries (FreeAlgebra ℚ X) s) :
    TruncatedPrimitive p ↔ ∀ n (hn : n ≤ s), FreePrimitive (truncatedSeriesCoeff s n hn p) := by
  refine ⟨fun hp n hn => hp.coeff n hn, fun h => ?_⟩
  apply truncatedSeries_ext
  intro n hn
  simpa only [FreePrimitive, truncatedSeriesCoeff_map, map_add, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] using h n hn

theorem TruncatedPrimitive.bch {s : ℕ} {p q : TruncatedSeries (FreeAlgebra ℚ X) s}
    (hp : TruncatedPrimitive p) (hq : TruncatedPrimitive q)
    (hp0 : p ∈ truncatedSeriesPositive s) (hq0 : q ∈ truncatedSeriesPositive s) :
    TruncatedPrimitive (nilpotentBCH p q) := by
  let I := truncatedSeriesPositive (A := FreeAlgebra ℚ X) s
  let J := truncatedSeriesPositive (A := FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s
  let D : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s freeCoproduct
  let L : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s Algebra.TensorProduct.includeLeft
  let R : TruncatedSeries (FreeAlgebra ℚ X) s →ₐ[ℚ]
      TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s :=
    truncatedSeriesMap s Algebra.TensorProduct.includeRight
  have hI : ∀ a ∈ I, IsNilpotent a := fun _ ha => truncatedSeriesPositive_nilpotent ha
  have hJ : ∀ a ∈ J, IsNilpotent a := fun _ ha => truncatedSeriesPositive_nilpotent ha
  change D (nilpotentBCH p q) = L (nilpotentBCH p q) + R (nilpotentBCH p q)
  calc
    D (nilpotentBCH p q) = nilpotentBCH (D p) (D q) :=
      map_nilpotentBCH (A := TruncatedSeries (FreeAlgebra ℚ X) s)
        (B := TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s)
        I hI D (a := p) (b := q) hp0 hq0
    _ = nilpotentBCH (L p + R p) (L q + R q) := congrArg₂ nilpotentBCH hp hq
    _ = L (nilpotentBCH p q) + R (nilpotentBCH p q) := ?_
  apply nilpotentBCH_commuting_maps (A := TruncatedSeries (FreeAlgebra ℚ X) s)
    (B := TruncatedSeries (FreeAlgebra ℚ X ⊗[ℚ] FreeAlgebra ℚ X) s) I hI J hJ L R
    (fun _ ha => truncatedSeriesMap_positive s _ ha)
    (fun _ ha => truncatedSeriesMap_positive s _ ha) _ hp0 hq0
  intro a b
  apply truncatedSeriesMap_commute
  intro u v
  change (u ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] v) = (1 ⊗ₜ[ℚ] v) * (u ⊗ₜ[ℚ] 1)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def scaledFreeGenerator (s : ℕ) (x : X) : TruncatedSeries (FreeAlgebra ℚ X) s :=
  truncatedSeriesMk s (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x))

theorem scaledFreeGenerator_positive (s : ℕ) (x : X) :
    scaledFreeGenerator s x ∈ truncatedSeriesPositive s := by
  rw [mem_truncatedSeriesPositive]
  change PowerSeries.constantCoeff (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x)) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_monomial]
  rfl

theorem scaledFreeGenerator_primitive (s : ℕ) (x : X) :
    TruncatedPrimitive (scaledFreeGenerator s x) := by
  apply (truncatedPrimitive_iff_coeff _).mpr
  intro n hn
  change FreePrimitive (PowerSeries.coeff n (PowerSeries.monomial 1 (FreeAlgebra.ι ℚ x)))
  rw [PowerSeries.coeff_monomial]
  split_ifs
  · exact freePrimitive_generator x
  · simp [FreePrimitive]

theorem scaled_bchPolynomial (s : ℕ) :
    truncatedSeriesMk s (freeScaleSeries (bchPolynomial (s + 1))) =
      nilpotentBCH (scaledFreeGenerator s (0 : Fin 2)) (scaledFreeGenerator s (1 : Fin 2)) := by
  have h := bchPolynomialEval_eq (A := TruncatedSeries (FreeAlgebra ℚ (Fin 2)) s)
    (truncatedSeriesPositive s) (k := s + 1)
    (fun _ ha => truncatedSeriesPositive_pow ha)
    (a := scaledFreeGenerator s (0 : Fin 2)) (b := scaledFreeGenerator s (1 : Fin 2))
    (scaledFreeGenerator_positive s (0 : Fin 2)) (scaledFreeGenerator_positive s (1 : Fin 2))
  rw [bchPolynomialEval_formula] at h
  simpa only [bchPolynomial, map_finiteLog, map_sub, map_mul, map_one, map_finiteExp,
    freeScaleSeries_generator, scaledFreeGenerator] using h

end Erdos3

end

section

namespace Erdos3
variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

theorem freeLieAssociativeExpansion_eval (f : X → A) (p : FreeLieAlgebra ℚ X) :
    FreeAlgebra.lift ℚ f (freeLieAssociativeExpansion p) = FreeLieAlgebra.lift ℚ f p := by
  have h : (FreeAlgebra.lift ℚ f).toLieHom.comp freeLieAssociativeExpansion = FreeLieAlgebra.lift ℚ f := by
    apply FreeLieAlgebra.hom_ext
    intro x
    simp [freeLieAssociativeExpansion]
  exact DFunLike.congr_fun h p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenPartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

noncomputable def partitionCell (cell : Ω → ι) (i : ι) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun x => cell x = i)

omit [Fintype ι] in
theorem mem_partitionCell (cell : Ω → ι) (i : ι) (x : Ω) :
    x ∈ partitionCell cell i ↔ cell x = i := by
  classical
  simp [partitionCell]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
attribute [local instance] LieRing.ofAssociativeRing

structure NilpotentLieBCHGroup (L : Type*) [LieRing L] [LieAlgebra ℚ L] (s : ℕ)
    (_hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) where
  coord : L

namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[ext] theorem ext {a b : NilpotentLieBCHGroup L s hnil} (h : a.coord = b.coord) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance instOne : One (NilpotentLieBCHGroup L s hnil) where
  one := ⟨0⟩

instance instInv : Inv (NilpotentLieBCHGroup L s hnil) where
  inv a := ⟨-a.coord⟩

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3
variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure NilpotentLieFiltration (s : ℕ) where
  layer : ℕ → Submodule ℚ L
  antitone : Antitone layer
  one_eq_top : layer 1 = ⊤
  lie_mem : ∀ {i j : ℕ} {a b : L}, a ∈ layer i → b ∈ layer j → ⁅a, b⁆ ∈ layer (i + j)
  terminal : layer (s + 1) = ⊥

namespace NilpotentLieFiltration
variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)
include F

def layerIdeal (i : ℕ) : LieIdeal ℚ L :=
  { F.layer i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 := by simp [F.one_eq_top]
      exact F.antitone (Nat.le_add_left i 1) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (i : ℕ) (a : L) : a ∈ F.layerIdeal i ↔ a ∈ F.layer i := Iff.rfl

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Function _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def embeddingDensity (e : X → Y) (c : ℝ) (f : X → ℝ) (y : Y) : ℝ :=
  c * Function.extend e f (fun _ => 0) y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def restrictedChartDensity (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℝ) : Y → ℝ :=
  embeddingDensity (fun x : S => q x.val) c (fun x => f x.val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCircleActions
namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [PseudoMetricSpace X]

def Commutes (A B : IsometricCircleAction X) : Prop :=
  ∀ t u x, A.act t (B.act u x) = B.act u (A.act t x)

theorem Commutes.symm {A B : IsometricCircleAction X} (h : A.Commutes B) : B.Commutes A :=
  fun t u x => (h u t x).symm

end Erdos3.CircleFourier.IsometricCircleAction

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure DegreeRankLieFiltration (s r : ℕ) where
  rank_le_degree : r ≤ s
  layer : ℕ → ℕ → Submodule ℚ L
  lex_antitone : ∀ {d e i j}, d < e ∨ d = e ∧ i ≤ j → layer e j ≤ layer d i
  one_eq_top : layer 1 0 = ⊤
  rank_zero_eq_one : ∀ d, layer d 0 = layer d 1
  overshoot : ∀ d i, d < i → layer d i = layer (d + 1) 0
  lie_mem : ∀ {d e i j} {x y : L}, x ∈ layer d i → y ∈ layer e j →
    ⁅x, y⁆ ∈ layer (d + e) (i + j)
  terminal : layer s (r + 1) = ⊥

namespace DegreeRankLieFiltration

variable {L} {s r : ℕ} (F : DegreeRankLieFiltration L s r)

theorem degree_antitone (i : ℕ) : Antitone (fun d => F.layer d i) := by
  intro d e hde
  rcases lt_or_eq_of_le hde with h | rfl
  · exact F.lex_antitone (Or.inl h)
  · exact le_rfl

theorem layer_eq_bot_of_past_top {d i : ℕ} (h : s < d ∨ s = d ∧ r < i) :
    F.layer d i = ⊥ := by
  apply bot_unique
  apply le_trans (b := F.layer s (r + 1))
  · apply F.lex_antitone
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩
  · exact F.terminal.le

end DegreeRankLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrthogonalBasisChart
namespace OAI

section

namespace Erdos3

open Module

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalBasisCoordinates (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃ₗ[ℝ] W × (Fin n → ℝ) where
  toFun x := (W.orthogonalProjectionOnto x, b.equivFun (Wᗮ.orthogonalProjectionOnto x))
  invFun p := p.1.val + (b.equivFun.symm p.2).val
  left_inv x := by
    change W.starProjection x + (b.equivFun.symm (b.equivFun (Wᗮ.orthogonalProjectionOnto x))).val = x
    rw [LinearEquiv.symm_apply_apply]
    exact W.starProjection_add_starProjection_orthogonal x
  right_inv p := by
    apply Prod.ext
    · change W.orthogonalProjectionOnto (p.1.val + (b.equivFun.symm p.2).val) = p.1
      rw [map_add, W.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (b.equivFun.symm p.2).property, add_zero]
      apply Subtype.ext
      exact W.starProjection_eq_self_iff.mpr p.1.property
    · change b.equivFun (Wᗮ.orthogonalProjectionOnto (p.1.val + (b.equivFun.symm p.2).val)) = p.2
      rw [map_add, W.orthogonalProjectionOnto_orthogonal_apply_eq_zero p.1.property, zero_add]
      have he : Wᗮ.orthogonalProjectionOnto (b.equivFun.symm p.2).val = b.equivFun.symm p.2 := by
        apply Subtype.ext
        exact Wᗮ.starProjection_eq_self_iff.mpr (b.equivFun.symm p.2).property
      rw [he, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' a x := by
    apply Prod.ext <;> simp

noncomputable def orthogonalBasisChart (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃L[ℝ] W × (Fin n → ℝ) := (orthogonalBasisCoordinates W b).toContinuousLinearEquiv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeBasisEquiv (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) : (I → ℤ) ≃ Λ :=
  (b.restrictScalars ℤ).equivFun.symm.toEquiv.trans
    (LinearEquiv.ofEq _ _ hb).toEquiv

end Erdos3

end

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def latticeSection (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Submodule ℤ W := ZLattice.comap ℝ Λ W.subtype

noncomputable def orthogonalLatticeImage (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Submodule ℤ W := Λ.map (W.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

noncomputable def standardEuclideanLattice : Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)

theorem mem_standardEuclideanLattice (x : EuclideanSpace ℝ ι) :
    x ∈ standardEuclideanLattice ι ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
  change x ∈ Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis) ↔ _
  rw [(EuclideanSpace.basisFun ι ℝ).toBasis.mem_span_iff_repr_mem ℤ x]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rfl

noncomputable def standardEuclideanPoint (z : ι → ℤ) : standardEuclideanLattice ι :=
  ⟨WithLp.toLp 2 (fun i => (z i : ℝ)), (mem_standardEuclideanLattice ι _).mpr (fun i => ⟨z i, rfl⟩)⟩

@[simp]
theorem standardEuclideanPoint_apply (z : ι → ℤ) (i : ι) :
    (standardEuclideanPoint ι z : EuclideanSpace ℝ ι) i = (z i : ℝ) := rfl

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def orthogonalLatticeProjection (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Λ →ₗ[ℤ] orthogonalLatticeImage Λ W :=
  ((W.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ).comp Λ.subtype).codRestrict
    (orthogonalLatticeImage Λ W) (fun x => ⟨x.val, x.property, rfl⟩)

theorem orthogonalLatticeProjection_surjective (Λ : Submodule ℤ E) (W : Submodule ℝ E) :
    Function.Surjective (orthogonalLatticeProjection Λ W) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end Erdos3

end

section

namespace Erdos3

variable (J : Type*) [Fintype J]

def standardLatticeSmallBox : Set (EuclideanSpace ℝ J) :=
  {x | ∀ i, |x i| < 1 / 2}

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def projectedLatticeLift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) : Λ :=
  (orthogonalLatticeProjection_surjective Λ Wᗮ z).choose

noncomputable def projectedLatticeShift (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) : W :=
  W.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def subspaceArrayIntegerLattice (I : Type*) {J : Type*} (U : Submodule ℝ (J → ℝ)) :
    AddSubgroup (I → U) where
  carrier := {x | ∀ i a, ∃ n : ℤ, (x i).val a = n}
  zero_mem' i a := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i a
    obtain ⟨n, hn⟩ := hx i a
    obtain ⟨m, hm⟩ := hy i a
    refine ⟨n + m, ?_⟩
    change (x i).val a + (y i).val a = ((n + m : ℤ) : ℝ)
    rw [hn, hm, Int.cast_add]
  neg_mem' := by
    intro x hx i a
    obtain ⟨n, hn⟩ := hx i a
    refine ⟨-n, ?_⟩
    change -(x i).val a = ((-n : ℤ) : ℝ)
    rw [hn, Int.cast_neg]

abbrev SubspaceArrayTorus (I : Type*) {J : Type*} (U : Submodule ℝ (J → ℝ)) :=
  (I → U) ⧸ subspaceArrayIntegerLattice I U

end Erdos3

end

section

namespace Erdos3

def unitSubspaceCoordinate {J : Type*} (U : Submodule ℝ (J → ℝ)) (a : J) :
    (Unit → U) →ₗ[ℝ] ℝ where
  toFun x := (x ()).val a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def subspaceAmbientTorus {J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus Unit U →+ (J → UnitAddCircle) :=
  AddMonoidHom.pi (fun a => quotientLinearPhase (subspaceArrayIntegerLattice Unit U)
    (unitSubspaceCoordinate U a) (fun _x hx => hx () a))

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

noncomputable def orthonormalChart (b : OrthonormalBasis I ℝ E) : (I → ℝ) ≃L[ℝ] E :=
  (EuclideanSpace.equiv I ℝ).symm.trans b.repr.toContinuousLinearEquiv.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {J : Type*} [Fintype J]

noncomputable def projectedIntegerLattice (W : Submodule ℝ (EuclideanSpace ℝ J)) :
    Submodule ℤ Wᗮ := orthogonalLatticeImage (standardEuclideanLattice J) Wᗮ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.OrthonormalMixedLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] [Fintype J]

noncomputable def orthonormalMixedChart (b : OrthonormalBasis I ℝ E) :
    ((I → ℝ) × (J → ℤ)) ≃ᵐ (E × (J → ℤ)) :=
  (orthonormalChart b).toHomeomorph.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

noncomputable def translatedQuotientChart (Λ : Submodule ℤ E) (v : T → E)
    (x : E × T) : E ⧸ Λ.toAddSubgroup := QuotientAddGroup.mk (x.1 - v x.2)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

noncomputable def normalizedLatticeQuotient (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W) :
    W × (Fin n → ℤ) → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  translatedQuotientChart (latticeSection (standardEuclideanLattice D) W)
    (fun z => projectedLatticeShift (standardEuclideanLattice D) W
      (latticeBasisEquiv (projectedIntegerLattice W) b hb z))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoverBasisResidues
namespace OAI

section

namespace Erdos3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (Γ : AddSubgroup E)

noncomputable def coverLatticePoint (d : ℕ) (hd : 0 < d) :
    Γ →+ (quotientIntegerCover Γ d).ker where
  toFun x := ⟨QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val), by
    change quotientIntegerCover Γ d (QuotientAddGroup.mk' Γ _) = 0
    rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr x.property⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp [smul_add]

theorem coverLatticePoint_val (d : ℕ) (hd : 0 < d) (x : Γ) :
    (coverLatticePoint Γ d hd x).val =
      QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val) := rfl

theorem coverLatticePoint_surjective (d : ℕ) (hd : 0 < d) :
    Function.Surjective (coverLatticePoint Γ d hd) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective Γ y.val
  have hxΓ : (d : ℝ) • x ∈ Γ := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change QuotientAddGroup.mk' Γ ((d : ℝ) • x) = 0
    rw [← quotientIntegerCover_mk, hx]
    exact y.property
  refine ⟨⟨(d : ℝ) • x, hxΓ⟩, ?_⟩
  apply Subtype.ext
  rw [coverLatticePoint_val, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
  exact hx

theorem coverLatticePoint_ker (d : ℕ) (hd : 0 < d) :
    (coverLatticePoint Γ d hd).ker = (nsmulAddMonoidHom (α := Γ) d).range := by
  ext x
  constructor
  · intro hx
    have he : QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • x.val) = 0 :=
      congrArg Subtype.val hx
    have hΓ := (QuotientAddGroup.eq_zero_iff _).mp he
    refine ⟨⟨(d : ℝ)⁻¹ • x.val, hΓ⟩, ?_⟩
    apply Subtype.ext
    change d • ((d : ℝ)⁻¹ • x.val) = x.val
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
  · rintro ⟨y, rfl⟩
    change coverLatticePoint Γ d hd (d • y) = 0
    apply Subtype.ext
    rw [coverLatticePoint_val]
    change QuotientAddGroup.mk' Γ ((d : ℝ)⁻¹ • (d • y.val)) = 0
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr y.property

abbrev CoverLatticeResidue (d : ℕ) := Γ ⧸ (nsmulAddMonoidHom (α := Γ) d).range

noncomputable def coverLatticeResidueEquiv (d : ℕ) (hd : 0 < d) :
    CoverLatticeResidue Γ d ≃+ (quotientIntegerCover Γ d).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (coverLatticePoint_ker Γ d hd)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (coverLatticePoint Γ d hd)
      (coverLatticePoint_surjective Γ d hd))

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Γ : AddSubgroup E) (b : Basis I ℤ Γ)

noncomputable def latticeBasisResidue (d : ℕ) : Γ →+ (I → ZMod d) :=
  (integerResidueMap I d).toAddMonoidHom.comp b.equivFun.toAddMonoidHom

omit [Module ℝ E] in
theorem latticeBasisResidue_surjective (d : ℕ) :
    Function.Surjective (latticeBasisResidue Γ b d) :=
  (integerResidueMap_surjective I d).comp b.equivFun.surjective

omit [Module ℝ E] in
theorem latticeBasisResidue_ker (d : ℕ) :
    (latticeBasisResidue Γ b d).ker = (nsmulAddMonoidHom (α := Γ) d).range := by
  ext x
  constructor
  · intro hx
    have hz : b.equivFun x ∈ integerScalarLattice I (d : ℤ) := by
      rw [← integerResidueMap_ker]
      exact hx
    obtain ⟨z, hz⟩ := (integerScalarLattice_mem _ _).mp hz
    refine ⟨b.equivFun.symm z, ?_⟩
    apply b.equivFun.injective
    change b.equivFun (d • b.equivFun.symm z) = b.equivFun x
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    simpa only [natCast_zsmul] using hz
  · rintro ⟨y, rfl⟩
    change integerResidueMap I d (b.equivFun (d • y)) = 0
    have hz : b.equivFun (d • y) ∈ integerScalarLattice I (d : ℤ) := by
      apply (integerScalarLattice_mem _ _).mpr
      exact ⟨b.equivFun y, by simp only [map_nsmul, natCast_zsmul]⟩
    rw [← integerResidueMap_ker] at hz
    exact hz

noncomputable def coverLatticeBasisEquiv (d : ℕ) :
    CoverLatticeResidue Γ d ≃+ (I → ZMod d) :=
  (QuotientAddGroup.quotientAddEquivOfEq (latticeBasisResidue_ker Γ b d)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (latticeBasisResidue Γ b d)
      (latticeBasisResidue_surjective Γ b d))

noncomputable def coverKernelBasisEquiv (d : ℕ) (hd : 0 < d) :
    (I → ZMod d) ≃+ (quotientIntegerCover Γ d).ker :=
  (coverLatticeBasisEquiv Γ b d).symm.trans (coverLatticeResidueEquiv Γ d hd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerKernelCoordinates
namespace OAI

section

namespace Erdos3

def nsmulKernelCongr {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) :
    (nsmulAddMonoidHom (α := G) d).ker ≃+
      (nsmulAddMonoidHom (α := H) d).ker where
  toFun x := ⟨e x.val, by
    change d • e x.val = 0
    rw [← map_nsmul, show d • x.val = 0 from x.property, map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    change d • e.symm y.val = 0
    rw [← map_nsmul, show d • y.val = 0 from y.property, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)

def nsmulKernelPiEquiv {I : Type*} (G : I → Type*) [∀ i, AddCommGroup (G i)]
    (d : ℕ) : (nsmulAddMonoidHom (α := ∀ i, G i) d).ker ≃+
      ∀ i, (nsmulAddMonoidHom (α := G i) d).ker where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun y := ⟨fun i => (y i).val, funext fun i => (y i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LayerTailDegree
namespace OAI

section

namespace Erdos3

def layerTailDegree (m : ℕ) : ℕ := m * (2^(m+1)+1)

theorem le_layerTailDegree (m : ℕ) : m ≤ layerTailDegree m := by
  unfold layerTailDegree
  nlinarith [Nat.zero_le (2^(m+1))]

theorem layerDegree_le_tailDegree {m : ℕ} (j : Fin m) : j.val+1 ≤ layerTailDegree m :=
  (Nat.succ_le_of_lt j.isLt).trans (le_layerTailDegree m)

end Erdos3

end

end OAI
end


