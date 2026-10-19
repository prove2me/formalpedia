-- Prove2me | Definitions.Def_OAIQWDF000
-- name    : OAIQWDF000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:48:07.203268+00:00
-- url     : https://prove2.me/theorems/f5302949-4850-4c5b-8909-fb6b8476b7f5
-- title:
--   OpenAI homogeneous depth-five IMM split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that homogeneous depth-five circuits for iterated matrix multiplication need $n^{\Theta(\sqrt n)}$ gates over characteristic-zero fields (`OAI.Problem335.main`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Algebra/DepthFive` (OpenAI, *Homogeneous depth-five lower bounds for iterated matrix multiplication*, OpenAI Math Release, September 25, 2026, result family 135, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are:
--   - the parameters of the lower bound (`LowerParameters.s`, `k`, `m`, `v`, `u`, `a`, `b`, `rankDimension`, `rankMomentScale`) and the balanced layer schedule (`balancedWord`, `balancedLayer`);
--   - the bidegree spaces with their factorial-normalized bases, and the mixed operators (`finiteMixedOperator`) with the normalized IMM matrix `immNormalizedMatrix`;
--   - the rank measure `rankData`;
--   - the block circuits of the upper bound (`immUpperCircuit` and the block data it is built from).
--
--   The bundle also contains the lemmas those definitions use in their bodies, since several of them carry proofs, such as the length of the balanced word.
--
--   The definitions of the published statement (`D5Leaf`, `Depth5Circuit`, `circuitValue`, `circuitSize`, `immLayer`, `imm`, `ceilSqrt`, `ceilDiv`, `upperGateBound` and the rest) are not repeated: the bundle imports them from the published bundle `Def_DepthFive`. It imports no other bundle. A small compatibility section declares, inside namespace `OAI`, lemmas that newer Lean versions provide under names this environment lacks (such as `ite_eq_left`, which is `if_pos`).
--
--   Modules: `ActualProductRank.lean`, `AnalyticParameters.lean`, `BalancedSchedule.lean`, `Bidegree.lean`, `BidegreeAverages.lean`, `BidegreeBasis.lean`, `BidegreeCompositionReindex.lean`, `BidegreeDimension.lean`, `BinomialRatios.lean`, `BlockCircuit.lean`, `BlockCircuitValue.lean`, `BlockMiddleSemantics.lean`, `BlockPartition.lean`, `CeilArithmetic.lean`, `CircuitProductBound.lean`, `CircuitWeightBound.lean`, `CoefficientDescent.lean`, `CoefficientMap.lean`, `CoefficientSupport.lean`, `CompositionAntidiag.lean`, `ConfiguredRankData.lean`, `DegreeDiscrepancy.lean`, `DegreeDistances.lean`, `DegreeWeight.lean`, `ExponentCardinality.lean`, `FactorialGeometricValue.lean`, `FactorialPositive.lean`, `FiniteOperator.lean`, `FirstOccupationMoment.lean`, `FockBidegreeBasis.lean`, `FockLayerProfile.lean`, `FockMonomials.lean`, `FockPaths.lean`, `FourPathLocal.lean`, `GateSums.lean`, `HomogeneousSpaceDimension.lean`, `ImmBlocks.lean`, `ImmDegree.lean`, `ImmFiniteMatrix.lean`, `ImmFirstTrace.lean`, `ImmFockMatrix.lean`, `ImmOperatorPaths.lean`, `ImmSecondTrace.lean`, `IndependentCoordinates.lean`, `IndexedCircuit.lean`, `IndexedCircuitValue.lean`, `IntermediateDimension.lean`, `IntermediateFactorization.lean`, `IsolatedFlip.lean`, `IsolatedWeight.lean`, `LayeredFourPath.lean`, `LocalFactorialExpansion.lean`, `LocalMomentPolynomials.lean`, `LocalMomentWeights.lean`, `LocalOccupationAverage.lean`, `LocalProductAverage.lean`, `LowerParameters.lean`, `LowerSchedule.lean`, `MatrixPathPairings.lean`, `MatrixPaths.lean`, `MatrixPathVertices.lean`, `MixedOperator.lean`, `MixedOperatorBidegree.lean`, `OccupationExpansion.lean`, `OccupationRatio.lean`, `OccupationSum.lean`, `OperatorHomogeneity.lean`, `OperatorRank.lean`, `PairingOccupationAverage.lean`, `PairingPartition.lean`, `Pairings.lean`, `PairingWeights.lean`, `ParameterBounds.lean`, `PathInjectivity.lean`, `PathOccupationGroups.lean`, `PathShifts.lean`, `PowerPerturbation.lean`, `RankMeasure.lean`, `RelaxedPaths.lean`, `RelaxedWeightBound.lean`, `RunBlocks.lean`, `ScheduleEnds.lean`, `ScheduleWeightBridge.lean`, `SecondMomentNormalization.lean`, `SecondMomentPairing.lean`, `SwitchRestoration.lean`, `TraceExpansion.lean`, `UpperBlockData.lean`, `UpperConstruction.lean`, `WordRuns.lean`, `WordSwitches.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the two solutions of this split. One proves the published intermediate statement `OAI.Problem335.complex_depth_five_lower_bound_of_eventual_second_trace`, and the other proves `OAI.Problem335.main` from it. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Homogeneous depth-five lower bounds for iterated matrix multiplication, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 135; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra/DepthFive at commit adc7f12

import Mathlib
import Definitions.Def_DepthFive

section
-- module Solutions.OAIQW_Problem335.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer parameters for the lower-bound rank measure. -/
namespace Problem335.LowerParameters

noncomputable section

def s (n : ℕ) : ℕ :=
  if Nat.sqrt n % 2 = n % 2 then Nat.sqrt n else Nat.sqrt n - 1

def k (n : ℕ) : ℕ := (n - s n) / 2

def m (n : ℕ) : ℕ := (n + s n) / 2

def rho (n : ℕ) : ℝ := (k n : ℝ) / (m n : ℝ)

def lambda (n : ℕ) : ℝ := (k n : ℝ) / (n : ℝ)

def v (n : ℕ) : ℕ := k n * n ^ 2

def u (n : ℕ) : ℕ := m n * n ^ 2

theorem s_le_nat_sqrt (n : ℕ) : s n ≤ Nat.sqrt n := by
  unfold s
  split <;> omega

theorem nat_sqrt_le_s_add_one (n : ℕ) : Nat.sqrt n ≤ s n + 1 := by
  unfold s
  split <;> omega

theorem s_le_n (n : ℕ) : s n ≤ n :=
  (s_le_nat_sqrt n).trans (Nat.sqrt_le_self n)

theorem s_mod_two (n : ℕ) : s n % 2 = n % 2 := by
  by_cases hn : n = 0
  · subst n
    norm_num [s]
  have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold s
  split <;> omega

theorem two_mul_k (n : ℕ) : 2 * k n = n - s n := by
  have hs := s_le_n n
  have hp := s_mod_two n
  unfold k
  omega

theorem two_mul_m (n : ℕ) : 2 * m n = n + s n := by
  have hp := s_mod_two n
  unfold m
  omega

theorem k_add_m (n : ℕ) : k n + m n = n := by
  have hs := s_le_n n
  have hk := two_mul_k n
  have hm := two_mul_m n
  omega

theorem m_eq_k_add_s (n : ℕ) : m n = k n + s n := by
  have hs := s_le_n n
  have hk := two_mul_k n
  have hm := two_mul_m n
  omega

theorem s_pos {n : ℕ} (hn : 4 ≤ n) : 0 < s n := by
  have h₁ : 2 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hn
  have h₂ := nat_sqrt_le_s_add_one n
  omega

theorem k_pos {n : ℕ} (hn : 4 ≤ n) : 0 < k n := by
  have h₁ : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
  have h₂ := s_le_nat_sqrt n
  have h₃ := two_mul_k n
  omega

theorem k_lt_m {n : ℕ} (hn : 4 ≤ n) : k n < m n := by
  have h₁ := m_eq_k_add_s n
  have h₂ := s_pos hn
  omega

theorem m_pos {n : ℕ} (hn : 4 ≤ n) : 0 < m n := by
  have := k_lt_m hn
  omega

theorem two_mul_k_add_s (n : ℕ) : 2 * k n + s n = n := by
  have h₁ := k_add_m n
  have h₂ := m_eq_k_add_s n
  omega

theorem rho_lt_one {n : ℕ} (hn : 4 ≤ n) : rho n < 1 := by
  have hm : (0 : ℝ) < m n := by exact_mod_cast m_pos hn
  rw [rho, div_lt_one hm]
  exact_mod_cast k_lt_m hn

theorem v_pos {n : ℕ} (hn : 4 ≤ n) : 0 < v n := by
  unfold v
  exact Nat.mul_pos (k_pos hn) (Nat.pow_pos (by omega))

end
end Problem335.LowerParameters

end OAI
end

section
-- module Solutions.OAIQW_Problem335.AnalyticParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded analytic parameters used by the lower-bound rank measure. -/
noncomputable section
namespace Problem335.LowerParameters

def a0 (n : ℕ) : ℝ := (v n : ℝ) / (Real.sqrt (n : ℝ) - 1)
def a (n : ℕ) : ℕ := ⌈a0 n⌉₊
def alpha (n : ℕ) : ℝ := (a n : ℝ) / ((a n : ℝ) + (v n : ℝ))
def b0 (n : ℕ) : ℝ := (u n : ℝ) * (alpha n) ^ (rho n) / (1 - (alpha n) ^ (rho n))
def b (n : ℕ) : ℕ := ⌈b0 n⌉₊
def beta (n : ℕ) : ℝ := (b n : ℝ) / ((b n : ℝ) + (u n : ℝ))
def q (n : ℕ) : ℝ := (alpha n) ^ ((1 + rho n) / 2)

theorem alpha_lt_one {n : ℕ} (hn : 4 ≤ n) : alpha n < 1 := by
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  unfold alpha
  apply (div_lt_one (by positivity)).mpr
  linarith

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.GateSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335

/-- The combined coefficient of all wires from a fixed predecessor.
Wire multiplicity is absorbed into this coefficient, not charged as gates. -/
def gateCoefficient {K ι : Type*} [AddCommMonoid K] [DecidableEq ι]
    (inputs : List (K × ι)) (i : ι) : K :=
  (inputs.map (fun entry => if entry.2 = i then entry.1 else 0)).sum

@[simp] theorem gateCoefficient_nil {K ι : Type*} [AddCommMonoid K] [DecidableEq ι]
    (i : ι) : gateCoefficient ([] : List (K × ι)) i = 0 := by
  simp [gateCoefficient]

@[simp] theorem gateCoefficient_cons {K ι : Type*} [AddCommMonoid K] [DecidableEq ι]
    (entry : K × ι) (inputs : List (K × ι)) (i : ι) :
    gateCoefficient (entry :: inputs) i =
      (if entry.2 = i then entry.1 else 0) + gateCoefficient inputs i := by
  simp [gateCoefficient]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace Problem335
universe u v

/-- The product estimate required when every positive formal degree is small. -/
def LowProductBound {K : Type u} [CommSemiring K] {σ : Type v}
    (R : MvPolynomial σ K → ℝ) (d : ℕ) (t B : ℝ) : Prop :=
  ∀ factors : List (MvPolynomial σ K × ℕ),
    (∀ q ∈ factors, 0 < q.2 ∧ q.1.IsHomogeneous q.2 ∧ (q.2 : ℝ) < t) →
    (factors.map Prod.snd).sum = d →
    R (factors.map Prod.fst).prod ≤ B

/-- The product estimate required after opening one large middle factor. -/
def HighProductBound {K : Type u} [CommSemiring K] {σ : Type v}
    (R : MvPolynomial σ K → ℝ) (d : ℕ) (t B : ℝ) : Prop :=
  ∀ (linears : List (MvPolynomial σ K)) (others : List (MvPolynomial σ K × ℕ)),
    (∀ p ∈ linears, p.IsHomogeneous 1) →
    (∀ q ∈ others, 0 < q.2 ∧ q.1.IsHomogeneous q.2) →
    t ≤ (linears.length : ℝ) →
    linears.length + (others.map Prod.snd).sum = d →
    R (linears.prod * (others.map Prod.fst).prod) ≤ B

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DegreeDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

/-- Distance to the nearest integer, with rounding used only to select a minimizer. -/
def nearestIntegerDistance (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- The degree-saving distance at slope `(n-s)/(2*n)`. -/
def degreeDistance (n s : ℝ) (e : ℕ) : ℝ :=
  nearestIntegerDistance ((1 / 2 - s / (2 * n)) * e)

open scoped BigOperators

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DegreeDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The one-factor bidegree weight used in the manuscript. -/
def degreeWeight (q lam : ℝ) (e : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (e + 1), q ^ |(i : ℝ) - lam * e|

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DegreeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The geometric majorant for weights at the integers around a chosen center. -/
def latticeMajorant (q d : ℝ) (z : ℤ) : ℝ :=
  if z = 0 then q ^ d else q ^ (1 - d) * q ^ (z.natAbs - 1)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitWeightBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

/-- The numerical parameter estimates needed by the circuit upper rank bound. -/
structure WeightParameters (n : ℕ) (s q : ℝ) : Prop where
  large : 64 ≤ n
  s_pos : 0 < s
  s_lower : Real.sqrt n / 2 ≤ s
  s_upper : s ≤ Real.sqrt n
  q_pos : 0 < q
  q_half : q ≤ 1 / 2
  q_sqrt : q ≤ 2 / Real.sqrt n
  q_pow : q ≤ (n : ℝ) ^ (-(2 / 5 : ℝ))
  q_small : 5 * q ^ ((3 : ℝ) / 16) ≤ 1

/-- The product-rank statement is kept explicit as the one algebraic input. -/
def HomogeneousProductRankBound {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (q lam D : ℝ) : Prop :=
  ∀ factors : List (MvPolynomial σ K × ℕ),
    (∀ f ∈ factors, 0 < f.2 ∧ f.1.IsHomogeneous f.2) →
    (factors.map Prod.snd).sum = n →
    R (factors.map Prod.fst).prod ≤
      2 * D * (factors.map (fun f => degreeWeight q lam f.2)).prod

/-- A common bound for a small product and for one expanded high product. -/
def circuitProductEnvelope (n : ℕ) (D : ℝ) : ℝ :=
  2 * D * Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) *
    (n : ℝ) ^ (-Real.sqrt n / 100)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.Bidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace Bidegree

open MvPolynomial Finsupp

variable {σ R : Type*} [CommSemiring R]

/-- The indicator weight of the derivative-variable side of a partition. -/
def weight (side : σ → Bool) (x : σ) : ℕ := if side x then 1 else 0

/-- Projection onto one degree in the selected variables. -/
def component (side : σ → Bool) (i : ℕ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent (weight side) i

@[simp] theorem coeff_component (side : σ → Bool) (i : ℕ)
    (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (component side i p).coeff d =
      if Finsupp.weight (weight side) d = i then p.coeff d else 0 :=
  coeff_weightedHomogeneousComponent i p d

@[simp] theorem component_same (side : σ → Bool) {p : MvPolynomial σ R} {i : ℕ}
    (hp : p.IsWeightedHomogeneous (weight side) i) : component side i p = p :=
  hp.weightedHomogeneousComponent_same

end Bidegree
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OperatorRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bigraded polynomial spaces used by the differentiation--multiplication rank measure.
The Boolean partition assigns derivative variables to `true` and multiplication
variables to `false`.
-/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*}

/-- Degree in derivative variables and in multiplication variables, respectively. -/
def bidegreeWeight (isV : σ → Bool) (i : σ) : ℕ × ℕ :=
  if isV i then (1, 0) else (0, 1)

@[simp] theorem bidegreeWeight_true (isV : σ → Bool) {i : σ} (hi : isV i = true) :
    bidegreeWeight isV i = (1, 0) := by simp [bidegreeWeight, hi]

@[simp] theorem bidegreeWeight_false (isV : σ → Bool) {i : σ} (hi : isV i = false) :
    bidegreeWeight isV i = (0, 1) := by simp [bidegreeWeight, hi]

/-- The sum of the two partial degrees is total degree. -/
theorem bidegreeWeight_total (isV : σ → Bool) (d : σ →₀ ℕ) :
    (Finsupp.weight (bidegreeWeight isV) d).1 +
      (Finsupp.weight (bidegreeWeight isV) d).2 = d.degree := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply,
    Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : isV i <;> simp [bidegreeWeight, h]

variable [CommSemiring K]

/-- The polynomial subspace of fixed bidegree. -/
def bidegreeSubmodule (isV : σ → Bool) (a b : ℕ) : Submodule K (MvPolynomial σ K) :=
  MvPolynomial.weightedHomogeneousSubmodule K (bidegreeWeight isV) (a, b)

/-- Linear projection to a fixed bidegree. -/
def bidegreeComponent (isV : σ → Bool) (a b : ℕ) :
    MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  MvPolynomial.weightedHomogeneousComponent (bidegreeWeight isV) (a, b)

@[simp] theorem mem_bidegreeSubmodule (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) :
    p ∈ bidegreeSubmodule isV a b ↔
      p.IsWeightedHomogeneous (bidegreeWeight isV) (a, b) := Iff.rfl

@[simp] theorem coeff_bidegreeComponent (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) (d : σ →₀ ℕ) :
    (bidegreeComponent isV a b p).coeff d =
      if Finsupp.weight (bidegreeWeight isV) d = (a, b)
      then p.coeff d else 0 :=
  MvPolynomial.coeff_weightedHomogeneousComponent _ _ _

 theorem bidegreeComponent_mem (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) :
    bidegreeComponent isV a b p ∈ bidegreeSubmodule isV a b :=
  MvPolynomial.weightedHomogeneousComponent_mem _ _ _

 theorem finite_bidegreeMonomials [Finite σ] (isV : σ → Bool) (a b : ℕ) :
    {d : σ →₀ ℕ | Finsupp.weight (bidegreeWeight isV) d = (a, b)}.Finite := by
  apply (Finsupp.finite_of_degree_le (σ := σ) (a + b)).subset
  intro d hd
  have h := bidegreeWeight_total isV d
  rw [hd] at h
  exact le_of_eq h.symm

instance bidegreeSubmodule_finite [Finite σ] (isV : σ → Bool) (a b : ℕ) :
    Module.Finite K (bidegreeSubmodule (K := K) isV a b) := by
  unfold bidegreeSubmodule
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_bidegreeMonomials isV a b).to_subtype
  exact Module.Finite.of_basis
    (MvPolynomial.basisRestrictSupport K
      {d | Finsupp.weight (bidegreeWeight isV) d = (a, b)})

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MixedOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full differentiation/multiplication substitution used by the rank measure.
The variables selected by `isV` act by partial differentiation; all others
act by multiplication. Since these two sets are disjoint, the operators
commute, and polynomial substitution is an algebra homomorphism. -/

noncomputable section

namespace Problem335

open MvPolynomial

universe u v
variable {K : Type u} [CommSemiring K] {σ : Type v}

/-- Formal partial derivatives commute, over an arbitrary commutative semiring. -/
theorem pderiv_pderiv_comm (i j : σ) (p : MvPolynomial σ K) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases h : i = j
  · subst j; rfl
  ext m
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    ite_eq_right h, ite_eq_right (Ne.symm h), add_zero]
  rw [add_right_comm m (Finsupp.single i 1) (Finsupp.single j 1)]
  ring

/-- The endomorphism assigned to an individual variable. -/
def variableOperator (isV : σ → Bool) (i : σ) :
    Module.End K (MvPolynomial σ K) :=
  if isV i then (pderiv i).toLinearMap else LinearMap.mulLeft K (X i)

@[simp] theorem variableOperator_of_true (isV : σ → Bool) (i : σ)
    (h : isV i = true) (p : MvPolynomial σ K) :
    variableOperator isV i p = pderiv i p := by
  simp [variableOperator, h]

@[simp] theorem variableOperator_of_false (isV : σ → Bool) (i : σ)
    (h : isV i = false) (p : MvPolynomial σ K) :
    variableOperator isV i p = X i * p := by
  simp [variableOperator, h]

/-- Operators assigned to any two variables commute. -/
theorem variableOperator_comm (isV : σ → Bool) (i j : σ) :
    Commute (variableOperator (K := K) isV i) (variableOperator isV j) := by
  classical
  change variableOperator isV i * variableOperator isV j =
    variableOperator isV j * variableOperator isV i
  apply LinearMap.ext
  intro p
  change variableOperator isV i (variableOperator isV j p) =
    variableOperator isV j (variableOperator isV i p)
  cases hi : isV i <;> cases hj : isV j
  · simp [variableOperator, hi, hj, mul_left_comm]
  · have hij : i ≠ j := by intro h; subst j; simp_all
    simp [variableOperator, hi, hj, pderiv_X_of_ne hij]
  · have hji : j ≠ i := by intro h; subst j; simp_all
    simp [variableOperator, hi, hj, pderiv_X_of_ne hji]
  · simpa [variableOperator, hi, hj] using pderiv_pderiv_comm i j p

open scoped IsMulCommutative in
/-- Substitution of derivatives on `V` and multiplication on its complement.
This is the full operator, before taking a bidegree component or restricting
to finite-dimensional homogeneous source and target spaces. -/
def mixedOperator (isV : σ → Bool) :
    MvPolynomial σ K →ₐ[K] Module.End K (MvPolynomial σ K) := by
  let A := Algebra.adjoin K (Set.range (variableOperator (K := K) isV))
  let : IsMulCommutative A := Algebra.isMulCommutative_adjoin K (by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact variableOperator_comm (K := K) isV i j)
  exact A.val.comp (MvPolynomial.aeval fun i =>
    (⟨variableOperator isV i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : A))

@[simp] theorem mixedOperator_X (isV : σ → Bool) (i : σ) :
    mixedOperator (K := K) isV (X i) = variableOperator isV i := by
  simp [mixedOperator]

@[simp] theorem mixedOperator_C (isV : σ → Bool) (a : K) :
    mixedOperator isV (C a) = a • (1 : Module.End K (MvPolynomial σ K)) := by
  simp [mixedOperator, Algebra.algebraMap_eq_smul_one]

@[simp] theorem mixedOperator_add (isV : σ → Bool) (p q : MvPolynomial σ K) :
    mixedOperator isV (p + q) = mixedOperator isV p + mixedOperator isV q :=
  map_add _ _ _

/-- The full operator respects products (unlike the projected finite rank map). -/
@[simp] theorem mixedOperator_mul (isV : σ → Bool) (p q : MvPolynomial σ K) :
    mixedOperator isV (p * q) = mixedOperator isV p * mixedOperator isV q :=
  map_mul _ _ _

theorem mixedOperator_mul_apply (isV : σ → Bool) (p q f : MvPolynomial σ K) :
    mixedOperator isV (p * q) f = mixedOperator isV p (mixedOperator isV q f) := by
  rw [mixedOperator_mul]
  rfl

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OperatorHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted-degree preservation for differential/multiplication substitution. -/

noncomputable section

namespace Problem335

open MvPolynomial

variable {K σ M : Type*} [CommSemiring K] [AddCommGroup M]

/-- A partial derivative subtracts the weight of its variable. The use of a
weight group avoids artificial truncation at degree zero. -/
theorem pderiv_isWeightedHomogeneous {w : σ → M} {p : MvPolynomial σ K}
    {a : M} (hp : p.IsWeightedHomogeneous w a) (i : σ) :
    (pderiv i p).IsWeightedHomogeneous w (a - w i) := by
  intro d hd
  have hc : p.coeff (d + Finsupp.single i 1) ≠ 0 := by
    intro h
    apply hd
    rw [coeff_pderiv, h, zero_mul]
  have hw := hp hc
  rw [map_add, Finsupp.weight_single, one_nsmul] at hw
  exact eq_sub_iff_add_eq.mpr hw

/-- The weighted-degree shift assigned to an operator variable: differentiation
has negative weight, while multiplication has positive weight. -/
def operatorWeight (isV : σ → Bool) (w : σ → M) (i : σ) : M :=
  if isV i then -w i else w i

theorem variableOperator_isWeightedHomogeneous (isV : σ → Bool) {w : σ → M}
    {p : MvPolynomial σ K} {a : M} (hp : p.IsWeightedHomogeneous w a) (i : σ) :
    (variableOperator isV i p).IsWeightedHomogeneous w (a + operatorWeight isV w i) := by
  cases hi : isV i
  · simpa [variableOperator, operatorWeight, hi, add_comm] using
      (isWeightedHomogeneous_X (R := K) w i).mul hp
  · simpa [variableOperator, operatorWeight, hi, sub_eq_add_neg] using
      pderiv_isWeightedHomogeneous hp i

/-- A power of a variable shifts degree by the corresponding multiple. -/
theorem mixedOperator_X_pow_isWeightedHomogeneous (isV : σ → Bool) (w : σ → M)
    (i : σ) (r : ℕ) {p : MvPolynomial σ K} {a : M}
    (hp : p.IsWeightedHomogeneous w a) :
    (mixedOperator isV (X i ^ r) p).IsWeightedHomogeneous w
      (a + r • operatorWeight isV w i) := by
  induction r with
  | zero => simpa using hp
  | succ r ih =>
    rw [pow_succ', mixedOperator_mul_apply, mixedOperator_X]
    simpa [succ_nsmul, add_assoc, add_comm, add_left_comm] using
      variableOperator_isWeightedHomogeneous isV ih i

/-- Monomial operators shift weighted degree by the sum of their variable shifts. -/
theorem mixedOperator_monomial_one_isWeightedHomogeneous (isV : σ → Bool) (w : σ → M)
    (d : σ →₀ ℕ) {p : MvPolynomial σ K} {a : M}
    (hp : p.IsWeightedHomogeneous w a) :
    (mixedOperator isV (monomial d 1) p).IsWeightedHomogeneous w
      (a + Finsupp.weight (operatorWeight isV w) d) := by
  induction d using Finsupp.induction_linear generalizing p a with
  | zero => simpa using hp
  | add d e hd he =>
    rw [show monomial (d + e) (1 : K) = monomial d 1 * monomial e 1 by
      rw [MvPolynomial.monomial_mul, one_mul]]
    rw [mixedOperator_mul_apply]
    simpa [map_add, add_assoc, add_comm, add_left_comm] using hd (he hp)
  | single i r =>
    rw [← X_pow_eq_monomial]
    simpa [Finsupp.weight_single] using
      mixedOperator_X_pow_isWeightedHomogeneous isV w i r hp

/-- The full mixed operator sends homogeneous inputs to the degree obtained by
adding the (signed) homogeneous degree of its defining polynomial. -/
theorem mixedOperator_isWeightedHomogeneous (isV : σ → Bool) (w : σ → M)
    {q p : MvPolynomial σ K} {d a : M}
    (hq : q.IsWeightedHomogeneous (operatorWeight isV w) d)
    (hp : p.IsWeightedHomogeneous w a) :
    (mixedOperator isV q p).IsWeightedHomogeneous w (a + d) := by
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]; exact isWeightedHomogeneous_zero _ _ _
  | add q r hq hr iq ir =>
    simpa only [map_add, LinearMap.add_apply] using iq.add ir
  | monomial e c he =>
    have hm := mixedOperator_monomial_one_isWeightedHomogeneous isV w e hp
    rw [he] at hm
    have heq : monomial e c = C c * monomial e (1 : K) := by rw [C_mul_monomial, mul_one]
    rw [heq, mixedOperator_mul_apply, mixedOperator_C]
    change (c • mixedOperator isV (monomial e 1) p).IsWeightedHomogeneous w (a + d)
    simpa only [C_mul'] using hm.C_mul c

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MixedOperatorBidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed operator restricts to the finite bidegree spaces used by the rank measure. -/

noncomputable section

namespace Problem335

open MvPolynomial

variable {K σ : Type*} [CommSemiring K]

theorem weight_map_hom {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) (w : σ → A) (e : σ →₀ ℕ) :
    Finsupp.weight (f ∘ w) e = f (Finsupp.weight w e) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]

theorem weighted_homogeneous_map {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) {w : σ → A} {p : MvPolynomial σ K} {d : A}
    (hp : p.IsWeightedHomogeneous w d) :
    p.IsWeightedHomogeneous (f ∘ w) (f d) := by
  intro e he
  rw [weight_map_hom, hp he]

def bidegreeCast : ℕ × ℕ →+ ℤ × ℤ :=
  (Nat.castAddMonoidHom ℤ).prodMap (Nat.castAddMonoidHom ℤ)

def bidegreeSign : ℕ × ℕ →+ ℤ × ℤ :=
  (-Nat.castAddMonoidHom ℤ).prodMap (Nat.castAddMonoidHom ℤ)

theorem bidegreeCast_injective : Function.Injective bidegreeCast := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simpa [bidegreeCast] using h

theorem operatorWeight_bidegree (isV : σ → Bool) :
    operatorWeight isV (bidegreeCast ∘ bidegreeWeight isV) =
      bidegreeSign ∘ bidegreeWeight isV := by
  funext i
  cases hi : isV i <;>
    simp [operatorWeight, bidegreeWeight, bidegreeCast, bidegreeSign, hi]

/-- Differentiation by a polynomial of bidegree `(k,m)` lowers derivative degree
by `k` and raises multiplication degree by `m`. -/
theorem mixedOperator_mem_bidegreeSubmodule (isV : σ → Bool)
    {q p : MvPolynomial σ K} {k m a b : ℕ} (hka : k ≤ a)
    (hq : q ∈ bidegreeSubmodule isV k m)
    (hp : p ∈ bidegreeSubmodule isV a b) :
    mixedOperator isV q p ∈ bidegreeSubmodule isV (a - k) (b + m) := by
  have hq' := weighted_homogeneous_map bidegreeSign hq
  have hp' := weighted_homogeneous_map bidegreeCast hp
  rw [← operatorWeight_bidegree isV] at hq'
  have h := mixedOperator_isWeightedHomogeneous isV
    (bidegreeCast ∘ bidegreeWeight isV) hq' hp'
  intro e he
  apply bidegreeCast_injective
  rw [← weight_map_hom, h he]
  simp [bidegreeCast, bidegreeSign, Nat.cast_sub hka, sub_eq_add_neg]

/-- More differentiation than the available derivative degree annihilates the input. -/
theorem mixedOperator_eq_zero_of_bidegree_lt (isV : σ → Bool)
    {q p : MvPolynomial σ K} {k m a b : ℕ} (hka : a < k)
    (hq : q ∈ bidegreeSubmodule isV k m)
    (hp : p ∈ bidegreeSubmodule isV a b) : mixedOperator isV q p = 0 := by
  have hq' := weighted_homogeneous_map bidegreeSign hq
  have hp' := weighted_homogeneous_map bidegreeCast hp
  rw [← operatorWeight_bidegree isV] at hq'
  have h := mixedOperator_isWeightedHomogeneous isV
    (bidegreeCast ∘ bidegreeWeight isV) hq' hp'
  apply MvPolynomial.eq_zero_iff.mpr
  intro e
  by_contra he
  have he' := h he
  rw [weight_map_hom] at he'
  have hfst := congrArg Prod.fst he'
  simp [bidegreeCast, bidegreeSign] at hfst
  omega

/-- The degree-shift membership also holds without a degree inequality: when
`k > a`, the output is zero and belongs to every homogeneous submodule. -/
theorem mixedOperator_mem_bidegreeSubmodule_all (isV : σ → Bool)
    {q p : MvPolynomial σ K} {k m a b : ℕ}
    (hq : q ∈ bidegreeSubmodule isV k m)
    (hp : p ∈ bidegreeSubmodule isV a b) :
    mixedOperator isV q p ∈ bidegreeSubmodule isV (a - k) (b + m) := by
  by_cases hka : k ≤ a
  · exact mixedOperator_mem_bidegreeSubmodule isV hka hq hp
  · rw [mixedOperator_eq_zero_of_bidegree_lt isV (Nat.lt_of_not_ge hka) hq hp]
    exact Submodule.zero_mem _

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RankMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-dimensional rank bookkeeping

The differentiation--multiplication measure is obtained by applying a linear
family of linear maps to a polynomial. Its rank can be studied independently
of the construction of that family and the choice of homogeneous spaces.
-/

noncomputable section

open scoped BigOperators

namespace Problem335
namespace RankMeasure

universe u v w x y

variable {K : Type u} [Field K]
variable {P : Type v} [AddCommGroup P] [Module K P]
variable {V : Type w} [AddCommGroup V] [Module K V]
variable {W : Type x} [AddCommGroup W] [Module K W]
variable {Z : Type y} [AddCommGroup Z] [Module K Z]

/-- The natural-number rank of a linear map. Its use below always has a
finite-dimensional source, or an explicit finite-dimensional factorization. -/
def mapRank (f : V →ₗ[K] W) : ℕ := Module.finrank K (LinearMap.range f)

@[simp] theorem mapRank_zero : mapRank (0 : V →ₗ[K] W) = 0 := by
  rw [mapRank, LinearMap.range_zero, finrank_bot]

/-- Restrict the source of a linear operator family to a chosen homogeneous
subspace, leaving the codomain ambient. This avoids unnecessary transports
between equivalent descriptions of the target homogeneous space. -/
def restrictFamily (F : P →ₗ[K] (V →ₗ[K] W)) (S : Submodule K V) :
    P →ₗ[K] (S →ₗ[K] W) where
  toFun p := (F p).comp S.subtype
  map_add' p q := by ext x; simp
  map_smul' a p := by ext x; simp

@[simp] theorem restrictFamily_apply (F : P →ₗ[K] (V →ₗ[K] W))
    (S : Submodule K V) (p : P) (x : S) :
    restrictFamily F S p x = F p x := rfl

/-- A rank measure associated with a linear family of linear maps. -/
def measure (F : P →ₗ[K] (V →ₗ[K] W)) (p : P) : ℕ := mapRank (F p)

@[simp] theorem measure_zero (F : P →ₗ[K] (V →ₗ[K] W)) :
    measure F 0 = 0 := by
  simp [measure]

end RankMeasure
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FiniteOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-source rank measure and its product decomposition. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*} [Field K]

/-- The full substitution operator restricted to a fixed bidegree source.
Keeping the ambient polynomial codomain avoids unnecessary degree transports. -/
def rawOperatorFamily (isV : σ → Bool) (a b : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K] MvPolynomial σ K) :=
  RankMeasure.restrictFamily (mixedOperator isV).toLinearMap
    (bidegreeSubmodule isV a b)

@[simp] theorem rawOperatorFamily_apply (isV : σ → Bool) (a b : ℕ)
    (q : MvPolynomial σ K) (p : bidegreeSubmodule (K := K) isV a b) :
    rawOperatorFamily isV a b q p = mixedOperator isV q p := rfl

/-- Project the defining polynomial to bidegree `(k,m)` before substitution. -/
def bidegreeOperatorFamily (isV : σ → Bool) (a b k m : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K] MvPolynomial σ K) :=
  (rawOperatorFamily isV a b).comp (bidegreeComponent isV k m)

@[simp] theorem bidegreeOperatorFamily_apply (isV : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) (p : bidegreeSubmodule (K := K) isV a b) :
    bidegreeOperatorFamily isV a b k m q p =
      mixedOperator isV (bidegreeComponent isV k m q) p := rfl

/-- The rank measure from the manuscript, with an ambient codomain. -/
def bidegreeRank (isV : σ → Bool) (a b k m : ℕ) (q : MvPolynomial σ K) : ℕ :=
  RankMeasure.measure (bidegreeOperatorFamily isV a b k m) q

@[simp] theorem bidegreeRank_zero (isV : σ → Bool) (a b k m : ℕ) :
    bidegreeRank (K := K) isV a b k m 0 = 0 :=
  RankMeasure.measure_zero _

/-- The finite-dimensional operator with its exact target bidegree.
The map is zero when `k > a`, so no degree-inequality argument is needed. -/
def finiteMixedOperator (isV : σ → Bool) (a b k m : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K]
        bidegreeSubmodule (K := K) isV (a - k) (b + m)) where
  toFun q := (bidegreeOperatorFamily isV a b k m q).codRestrict
    (bidegreeSubmodule isV (a - k) (b + m)) (fun p =>
      mixedOperator_mem_bidegreeSubmodule_all isV
        (bidegreeComponent_mem isV k m q) p.property)
  map_add' q r := by
    ext p : 2
    exact LinearMap.congr_fun (map_add (bidegreeOperatorFamily isV a b k m) q r) p
  map_smul' c q := by
    ext p : 2
    exact LinearMap.congr_fun (map_smul (bidegreeOperatorFamily isV a b k m) c q) p

@[simp] theorem finiteMixedOperator_apply_coe (isV : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) (p : bidegreeSubmodule (K := K) isV a b) :
    (finiteMixedOperator isV a b k m q p : MvPolynomial σ K) =
      mixedOperator isV (bidegreeComponent isV k m q) p := rfl

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IntermediateFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factorization of mixed operators through intermediate bidegree spaces.
The codomain is initially the full polynomial space.  Restricting it to a
bidegree submodule leaves the range dimension unchanged, as proved below. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*} [Field K]

/-- The full operator restricted to a finite-bidegree source, as a linear
family in the polynomial defining the operator. -/
def sourceMixedOperator (isV : σ → Bool) (a b : ℕ) :
    MvPolynomial σ K →ₗ[K]
      (bidegreeSubmodule (K := K) isV a b →ₗ[K] MvPolynomial σ K) where
  toFun p := (mixedOperator isV p).comp (bidegreeSubmodule isV a b).subtype
  map_add' p q := by
    ext f
    simp
  map_smul' c p := by
    ext f
    simp

@[simp] theorem sourceMixedOperator_apply (isV : σ → Bool) (a b : ℕ)
    (p : MvPolynomial σ K) (f : bidegreeSubmodule (K := K) isV a b) :
    sourceMixedOperator isV a b p f = mixedOperator isV p (f : MvPolynomial σ K) := rfl

/-- The operator for `p` maps the source into the proposed intermediate space. -/
def intermediateStart (isV : σ → Bool) (a b c d : ℕ)
    (p : MvPolynomial σ K)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV p (f : MvPolynomial σ K) ∈ bidegreeSubmodule isV c d) :
    bidegreeSubmodule (K := K) isV a b →ₗ[K] bidegreeSubmodule (K := K) isV c d :=
  LinearMap.codRestrict _ (sourceMixedOperator isV a b p) h

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.HomogeneousSpaceDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

universe u v w

/-- Degree-exact exponent vectors are multisets of the indicated cardinality. -/
def degreeExponentsEquivSym (σ : Type u) (d : ℕ) :
    { m : σ →₀ ℕ // m.degree = d } ≃ Sym σ d := by
  classical
  exact (Sym.equivNatSum σ d).symm

/-- Homogeneous polynomial spaces in finitely many variables are finite modules. -/
instance homogeneousSubmodule_finite (K : Type u) [CommSemiring K]
    (σ : Type v) [Finite σ] (d : ℕ) :
    Module.Finite K (MvPolynomial.homogeneousSubmodule σ K d) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg σ K d)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

universe u v

/-- Split a finite exponent vector into its derivative and multiplication coordinates. -/
def splitBidegreeExponents {σ : Type u} [Fintype σ] (side : σ → Bool) :
    (σ →₀ ℕ) ≃ ({i : σ // side i = true} →₀ ℕ) ×
      ({i : σ // side i = false} →₀ ℕ) := by
  classical
  refine {
    toFun := fun m => (m.subtypeDomain (fun i => side i = true),
      m.subtypeDomain (fun i => side i = false))
    invFun := fun p => Finsupp.equivFunOnFinite.symm (fun i =>
      if h : side i = true then p.1 ⟨i, h⟩ else p.2 ⟨i, by simpa using h⟩)
    left_inv := ?_
    right_inv := ?_ }
  · intro m
    ext i
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    split <;> rfl
  · intro p
    apply Prod.ext
    · ext i
      simp [i.property]
    · ext i
      simp [i.property]

/-- The bidegree is the pair of total degrees of the restricted exponent vectors. -/
theorem weight_splitBidegreeExponents {σ : Type u} [Fintype σ]
    (side : σ → Bool) (m : σ →₀ ℕ) :
    Finsupp.weight (bidegreeWeight side) m =
      ((splitBidegreeExponents side m).1.degree,
       (splitBidegreeExponents side m).2.degree) := by
  classical
  have hs (p : σ → Prop) [DecidablePred p] :
      (∑ i : Subtype p, m i) = ∑ i, if p i then m i else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  apply Prod.ext
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype, Finsupp.degree_eq_sum,
      splitBidegreeExponents, bidegreeWeight, Prod.fst_sum, hs]
    apply Finset.sum_congr rfl
    intro i _
    cases side i <;> simp
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype, Finsupp.degree_eq_sum,
      splitBidegreeExponents, bidegreeWeight, Prod.snd_sum, hs]
    apply Finset.sum_congr rfl
    intro i _
    cases side i <;> simp

/-- A fixed bidegree fiber is the product of two ordinary degree fibers. -/
def bidegreeFinsuppExponentsEquiv {σ : Type u} [Fintype σ] (side : σ → Bool) (a b : ℕ) :
    {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} ≃
      {m : {i : σ // side i = true} →₀ ℕ // m.degree = a} ×
      {m : {i : σ // side i = false} →₀ ℕ // m.degree = b} :=
  ((splitBidegreeExponents side).subtypeEquiv
    (p := fun m => Finsupp.weight (bidegreeWeight side) m = (a, b))
    (q := fun p : ({i : σ // side i = true} →₀ ℕ) ×
      ({i : σ // side i = false} →₀ ℕ) => p.1.degree = a ∧ p.2.degree = b)
    (by
      intro m
      constructor
      · intro h
        exact Prod.mk.inj ((weight_splitBidegreeExponents side m).symm.trans h)
      · rintro ⟨h1, h2⟩
        exact (weight_splitBidegreeExponents side m).trans (Prod.ext h1 h2))).trans
      (Equiv.subtypeProdEquivProd
        (p := fun m : {i : σ // side i = true} →₀ ℕ => m.degree = a)
        (q := fun m : {i : σ // side i = false} →₀ ℕ => m.degree = b))

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BinomialRatios
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binomial dimension estimates for the intermediate spaces in the
differentiation--multiplication rank argument. -/

namespace Problem335

/-- Dimension of homogeneous degree `t` polynomials in `r` variables,
for a positive number of variables. -/
def homogeneousDim (r t : ℕ) : ℕ := (r + t - 1).choose t

@[simp] theorem homogeneousDim_zero (r : ℕ) : homogeneousDim r 0 = 1 := by
  simp [homogeneousDim]

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IntermediateDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Factors applied first in the intermediate-space argument. -/
def positiveBidegreeSet {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) : Finset ι := by
  classical
  exact s.filter (fun j => 0 < (i j : ℝ) - lam * e j)

/-- Total differentiation degree of the first group of factors. -/
def positiveBidegreeV {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) : ℕ :=
  ∑ j ∈ positiveBidegreeSet s e i lam, i j

/-- Total multiplication degree of the first group of factors. -/
def positiveBidegreeU {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) : ℕ :=
  ∑ j ∈ positiveBidegreeSet s e i lam, (e j - i j)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualProductRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-rank estimates specialized to the actual rounded rank parameters. -/
noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

/-- Dimension of the source of the actual mixed operator. -/
def sourceDimension (n : ℕ) : ℝ :=
  (homogeneousDim (v n) (a n) : ℝ) * homogeneousDim (u n) (b n)

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BalancedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335
namespace BalancedSchedule

/-- Number of `U` layers following the `i`th `V` layer. -/
def chunkLength (k s i : ℕ) : ℕ :=
  1 + ((i + 1) * s / k - i * s / k)

lemma quotient_mono (k s : ℕ) {i j : ℕ} (hij : i ≤ j) :
    i * s / k ≤ j * s / k :=
  Nat.div_le_div_right (Nat.mul_le_mul_right s hij)

/-- The relative density used in the mixed rank measure. -/
def rho (k s : ℕ) : ℝ := (k : ℝ) / (k + s)

/-- `true` denotes a `V` layer and `false` denotes a `U` layer. -/
def chunk (k s i : ℕ) : List Bool :=
  true :: List.replicate (chunkLength k s i) false

/-- The first `r` complete chunks of the balanced schedule. -/
def wordPrefix (k s : ℕ) : ℕ → List Bool
  | 0 => []
  | r + 1 => wordPrefix k s r ++ chunk k s r

/-- The complete balanced layer schedule. -/
def word (k s : ℕ) : List Bool := wordPrefix k s k

/-- The number of `V` layers minus `ρ` times the number of `U` layers. -/
def discrepancy (k s : ℕ) (w : List Bool) : ℝ :=
  (w.count true : ℝ) - rho k s * (w.count false : ℝ)

@[simp] lemma count_true_chunk (k s i : ℕ) : (chunk k s i).count true = 1 := by
  simp [chunk, List.count_replicate]

@[simp] lemma count_false_chunk (k s i : ℕ) :
    (chunk k s i).count false = chunkLength k s i := by
  simp [chunk]

@[simp] lemma count_true_wordPrefix (k s r : ℕ) :
    (wordPrefix k s r).count true = r := by
  induction r with
  | zero => simp [wordPrefix]
  | succ r ih => simp [wordPrefix, List.count_append, ih]

@[simp] lemma count_false_wordPrefix (k s r : ℕ) :
    (wordPrefix k s r).count false = r + r * s / k := by
  induction r with
  | zero => simp [wordPrefix]
  | succ r ih =>
    simp only [wordPrefix, List.count_append, ih, count_false_chunk]
    have hm : r * s / k ≤ (r + 1) * s / k := quotient_mono k s (by omega)
    unfold chunkLength
    omega

@[simp] lemma discrepancy_nil (k s : ℕ) : discrepancy k s [] = 0 := by
  simp [discrepancy]

@[simp] lemma discrepancy_append (k s : ℕ) (w z : List Bool) :
    discrepancy k s (w ++ z) = discrepancy k s w + discrepancy k s z := by
  simp only [discrepancy, List.count_append, Nat.cast_add]
  ring

@[simp] lemma discrepancy_chunk (k s i : ℕ) :
    discrepancy k s (chunk k s i) = 1 - rho k s * chunkLength k s i := by
  simp [discrepancy]

@[simp] lemma word_count_true (k s : ℕ) : (word k s).count true = k := by
  simp [word]

@[simp] lemma word_count_false {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (word k s).count false = k + s := by
  simp [word, Nat.mul_div_cancel_left s hk]

lemma word_length {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (word k s).length = 2 * k + s := by
  rw [← List.count_true_add_count_false, word_count_true, word_count_false hk]
  omega

@[simp] lemma chunk_head (k s i : ℕ) : (chunk k s i).head? = some true := rfl

/-- Adjacent layer positions in either order. -/
def adjacent {n : ℕ} (i j : Fin n) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- Internal vertices adjacent to a layer. Vertex `j` is between layers `j` and `j+1`. -/
def internalEnds {n : ℕ} (i : Fin n) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun j => j.val = i.val ∨ j.val + 1 = i.val)

end BalancedSchedule
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ExponentCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinalities of homogeneous and bihomogeneous exponent sets -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*}

lemma bidegreeWeight_fst_sum [Fintype σ] (isV : σ → Bool) (d : σ →₀ ℕ) :
    (Finsupp.weight (bidegreeWeight isV) d).1 =
      ∑ x : {x // isV x = true}, d x := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Prod.fst_sum]
  calc
    _ = ∑ x, if isV x = true then d x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      cases h : isV x <;> simp [bidegreeWeight, h]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

lemma bidegreeWeight_snd_sum [Fintype σ] (isV : σ → Bool) (d : σ →₀ ℕ) :
    (Finsupp.weight (bidegreeWeight isV) d).2 =
      ∑ x : {x // ¬ isV x = true}, d x := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Prod.snd_sum]
  calc
    _ = ∑ x, if ¬ isV x = true then d x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      cases h : isV x <;> simp [bidegreeWeight, h]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

/-- Split a bihomogeneous monomial into its two independent exponent vectors. -/
def bidegreeExponentsEquiv [Fintype σ] (isV : σ → Bool) (a b : ℕ) :
    {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)} ≃
      {d : {x // isV x = true} → ℕ // ∑ x, d x = a} ×
      {d : {x // ¬ isV x = true} → ℕ // ∑ x, d x = b} := by
  classical
  let e : (σ →₀ ℕ) ≃
      ({x // isV x = true} → ℕ) × ({x // ¬ isV x = true} → ℕ) :=
    Finsupp.equivFunOnFinite.trans
      (Equiv.piEquivPiSubtypeProd (fun x => isV x = true) (fun _ => ℕ))
  refine (e.subtypeEquiv (q := fun z => (∑ x, z.1 x) = a ∧ (∑ x, z.2 x) = b)
    ?_).trans (Equiv.subtypeProdEquivProd
      (p := fun d : {x // isV x = true} → ℕ => (∑ x, d x) = a)
      (q := fun d : {x // ¬ isV x = true} → ℕ => (∑ x, d x) = b))
  intro d
  change Finsupp.weight (bidegreeWeight isV) d = (a, b) ↔
    (∑ x : {x // isV x = true}, d x) = a ∧
      (∑ x : {x // ¬ isV x = true}, d x) = b
  rw [Prod.ext_iff, bidegreeWeight_fst_sum, bidegreeWeight_snd_sum]

/-- The weak-composition function representation and the finite antidiagonal
representation used by power-series coefficient extraction are equivalent. -/
def homogeneousFunctionsEquivAntidiag [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {d : σ → ℕ // ∑ x, d x = a} ≃
      ↥(Finset.finsuppAntidiag (Finset.univ : Finset σ) a) := by
  classical
  refine Finsupp.equivFunOnFinite.symm.subtypeEquiv ?_
  intro d
  simp [Finset.mem_finsuppAntidiag]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BidegreeAverages

/-- A weak composition indexed by a finite variable set. -/
abbrev Composition (σ : Type*) [Fintype σ] (a : ℕ) :=
  {d : σ → ℕ // ∑ x, d x = a}

/-- The exponent index set for the source of the mixed operator. -/
abbrev Index {σ : Type*} (isV : σ → Bool) (a b : ℕ) :=
  {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)}

end Problem335.BidegreeAverages

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

universe u v

/-- Ordinary monomial basis of a fixed bidegree subspace. -/
def bidegreeMonomialBasis (K : Type u) [CommSemiring K]
    {σ : Type v} (side : σ → Bool) (a b : ℕ) :
    Module.Basis {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} K
      (bidegreeSubmodule (K := K) side a b) :=
  (MvPolynomial.basisRestrictSupport K
    {m : σ →₀ ℕ | Finsupp.weight (bidegreeWeight side) m = (a, b)}).map
      (LinearEquiv.ofEq _ _
        (MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported
          K (bidegreeWeight side) (a, b)).symm)

@[simp] theorem bidegreeMonomialBasis_repr (K : Type u) [CommSemiring K]
    {σ : Type v} (side : σ → Bool) (a b : ℕ)
    (p : bidegreeSubmodule (K := K) side a b)
    (d : {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)}) :
    (bidegreeMonomialBasis K side a b).repr p d = p.1.coeff d.1 := by
  rfl

@[simp] theorem bidegreeMonomialBasis_apply (K : Type u) [CommSemiring K]
    {σ : Type v} (side : σ → Bool) (a b : ℕ)
    (d : {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)}) :
    ((bidegreeMonomialBasis K side a b) d : MvPolynomial σ K) =
      MvPolynomial.monomial d.1 1 := by
  classical
  have hm : MvPolynomial.monomial d.1 (1 : K) ∈
      bidegreeSubmodule (K := K) side a b := by
    exact MvPolynomial.isWeightedHomogeneous_monomial (bidegreeWeight side) d.1 1 d.2
  have he : (bidegreeMonomialBasis K side a b) d =
      ⟨MvPolynomial.monomial d.1 1, hm⟩ := by
    apply (bidegreeMonomialBasis K side a b).repr.injective
    ext j
    rw [Module.Basis.repr_self, bidegreeMonomialBasis_repr]
    simp [MvPolynomial.coeff_monomial, Finsupp.single_apply, Subtype.ext_iff]
  exact congrArg Subtype.val he

/-- Finite monomial indexing for bidegree spaces over a finite variable set. -/
instance bidegreeMonomialFintype {σ : Type v} [Finite σ]
    (side : σ → Bool) (a b : ℕ) :
    Fintype {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} :=
  (finite_bidegreeMonomials side a b).fintype

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeCompositionReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Reindex a bidegree exponent by its two finite occupation antidiagonals. -/
def bidegreeAntidiagEquiv (side : σ → Bool) (a b : ℕ) :
    {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a,b)} ≃
      (Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a) ×
      (Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b) :=
  (bidegreeExponentsEquiv side a b).trans
    (Equiv.prodCongr (homogeneousFunctionsEquivAntidiag a)
      (homogeneousFunctionsEquivAntidiag b))

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IndexedCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

/-- A depth-five circuit whose gates are indexed by arbitrary finite types.
This representation is convenient for products, sums, and path-indexed gates;
`toDepth5Circuit` transports it to the qualified circuit representation. -/
structure IndexedDepth5Circuit (K : Type*) [CommSemiring K] (n : ℕ)
    (L B P M U : Type*) where
  leaves : L → D5Leaf K n
  bottomInputs : B → List (K × L)
  bottomDegree : B → ℕ
  bottomHomogeneous :
    ∀ i entry, entry ∈ bottomInputs i → d5LeafDegree (leaves entry.2) = bottomDegree i
  bottomEmpty :
    ∀ i, bottomInputs i = [] → bottomDegree i = 0
  lowerInputs : P → List B
  middleInputs : M → List (K × P)
  middleDegree : M → ℕ
  middleHomogeneous :
    ∀ i entry, entry ∈ middleInputs i →
      ((lowerInputs entry.2).map bottomDegree).sum = middleDegree i
  middleEmpty :
    ∀ i, middleInputs i = [] → middleDegree i = 0
  upperInputs : U → List M
  outputInputs : List (K × U)
  outputDegree : ℕ
  outputHomogeneous :
    ∀ entry, entry ∈ outputInputs →
      ((upperInputs entry.2).map middleDegree).sum = outputDegree
  outputEmpty : outputInputs = [] → outputDegree = 0

namespace IndexedDepth5Circuit

variable {K : Type*} [CommSemiring K] {n : ℕ}
variable {L B P M U : Type*}
variable [Fintype L] [Fintype B] [Fintype P] [Fintype M] [Fintype U]

/-- Relabel each finite gate type by `Fin` without changing any wire or degree. -/
def toDepth5Circuit (c : IndexedDepth5Circuit K n L B P M U) : Depth5Circuit K n where
  leafCount := Fintype.card L
  leaves i := c.leaves ((Fintype.equivFin L).symm i)
  bottomCount := Fintype.card B
  bottomInputs i := (c.bottomInputs ((Fintype.equivFin B).symm i)).map
    (fun e => (e.1, Fintype.equivFin L e.2))
  bottomDegree i := c.bottomDegree ((Fintype.equivFin B).symm i)
  bottomHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa using c.bottomHomogeneous ((Fintype.equivFin B).symm i) e he
  bottomEmpty := by
    intro i h
    exact c.bottomEmpty _ (List.map_eq_nil_iff.mp h)
  lowerCount := Fintype.card P
  lowerInputs i := (c.lowerInputs ((Fintype.equivFin P).symm i)).map (Fintype.equivFin B)
  middleCount := Fintype.card M
  middleInputs i := (c.middleInputs ((Fintype.equivFin M).symm i)).map
    (fun e => (e.1, Fintype.equivFin P e.2))
  middleDegree i := c.middleDegree ((Fintype.equivFin M).symm i)
  middleHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa [List.map_map, Function.comp_def] using
      c.middleHomogeneous ((Fintype.equivFin M).symm i) e he
  middleEmpty := by
    intro i h
    exact c.middleEmpty _ (List.map_eq_nil_iff.mp h)
  upperCount := Fintype.card U
  upperInputs i := (c.upperInputs ((Fintype.equivFin U).symm i)).map (Fintype.equivFin M)
  outputInputs := c.outputInputs.map (fun e => (e.1, Fintype.equivFin U e.2))
  outputDegree := c.outputDegree
  outputHomogeneous := by
    intro entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa [List.map_map, Function.comp_def] using c.outputHomogeneous e he
  outputEmpty := by
    intro h
    exact c.outputEmpty (List.map_eq_nil_iff.mp h)

@[simp] theorem circuitSize_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) :
    circuitSize c.toDepth5Circuit =
      Fintype.card L + Fintype.card B + Fintype.card P +
        Fintype.card M + Fintype.card U + 1 := rfl

@[simp] theorem outputDegree_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) :
    c.toDepth5Circuit.outputDegree = c.outputDegree := rfl

end IndexedDepth5Circuit
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι R : Type*}

/-- All labelled paths through a nonempty sequence of matrix layers.
The empty sequence uses the usual identity-matrix path convention. -/
def matrixEntryPaths [Fintype ι] [DecidableEq ι] :
    List σ → ι → ι → List (List (σ × ι × ι))
  | [], i, j => if i = j then [[]] else []
  | [t], i, j => [[(t, i, j)]]
  | t :: u :: ts, i, j =>
      (Finset.univ.toList).flatMap fun k =>
        (matrixEntryPaths (u :: ts) k j).map fun p => (t, i, k) :: p

/-- A path through `labels` chooses exactly one entry in each layer. -/
theorem matrixEntryPaths_labels [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) (p : List (σ × ι × ι))
    (hp : p ∈ matrixEntryPaths labels i j) : p.map Prod.fst = labels := by
  induction labels generalizing i p with
  | nil =>
      by_cases hij : i = j <;> simp_all [matrixEntryPaths]
  | cons t ts ih =>
      cases ts with
      | nil => simp_all [matrixEntryPaths]
      | cons u us =>
          simp only [matrixEntryPaths, List.mem_flatMap, List.mem_map] at hp
          obtain ⟨k, _, q, hq, rfl⟩ := hp
          simp [ih k q hq]

/-- Every enumerated path has one edge per layer. -/
theorem matrixEntryPaths_path_length [Fintype ι] [DecidableEq ι]
    (labels : List σ) (i j : ι) (p : List (σ × ι × ι))
    (hp : p ∈ matrixEntryPaths labels i j) : p.length = labels.length := by
  have h := congrArg List.length (matrixEntryPaths_labels labels i j p hp)
  simpa using h

/-- The number of internal-index paths through a nonempty list of layers. -/
theorem matrixEntryPaths_length [Fintype ι] [DecidableEq ι]
    (labels : List σ) (hne : labels ≠ []) (i j : ι) :
    (matrixEntryPaths labels i j).length = Fintype.card ι ^ (labels.length - 1) := by
  induction labels generalizing i with
  | nil => exact (hne rfl).elim
  | cons t ts ih =>
      cases ts with
      | nil => simp [matrixEntryPaths]
      | cons u us =>
          simp only [matrixEntryPaths, List.length_flatMap, List.length_map]
          simp_rw [ih (by simp)]
          simp [pow_succ, Nat.mul_comm]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.UpperBlockData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BlockData

variable {n : ℕ}

/-- Block-entry gates: block number and two matrix indices. -/
abbrev Middle (blocks : List (List (Fin n))) :=
  Fin blocks.length × Fin n × Fin n

def paths (blocks : List (List (Fin n))) (m : Middle blocks) :=
  matrixEntryPaths (blocks.get m.1) m.2.1 m.2.2

/-- Each lower gate is an enumerated path for one block entry. -/
abbrev Lower (blocks : List (List (Fin n))) :=
  Σ m : Middle blocks, Fin (paths blocks m).length

def lowerInputs (blocks : List (List (Fin n))) (p : Lower blocks) :
    List (Fin n × Fin n × Fin n) :=
  (paths blocks p.1).get p.2

def middleInputs (K : Type*) [One K] (blocks : List (List (Fin n)))
    (m : Middle blocks) : List (K × Lower blocks) :=
  List.ofFn fun p : Fin (paths blocks m).length => (1, ⟨m, p⟩)

def middleDegree (blocks : List (List (Fin n))) (m : Middle blocks) : ℕ :=
  (blocks.get m.1).length

def upperPaths (blocks : List (List (Fin n))) (z : Fin n) :
    List (List (Middle blocks)) :=
  matrixEntryPaths (List.finRange blocks.length) z z

abbrev Upper (blocks : List (List (Fin n))) (z : Fin n) :=
  Fin (upperPaths blocks z).length

def upperInputs (blocks : List (List (Fin n))) (z : Fin n)
    (p : Upper blocks z) : List (Middle blocks) :=
  (upperPaths blocks z).get p

def outputInputs (K : Type*) [One K] (blocks : List (List (Fin n)))
    (z : Fin n) : List (K × Upper blocks z) :=
  List.ofFn fun p : Upper blocks z => (1, p)

theorem lowerInputs_length (blocks : List (List (Fin n))) (p : Lower blocks) :
    (lowerInputs blocks p).length = middleDegree blocks p.1 := by
  exact matrixEntryPaths_path_length _ _ _ _ (List.get_mem _ _)

theorem middleInputs_homogeneous (K : Type*) [One K]
    (blocks : List (List (Fin n))) (m : Middle blocks)
    (entry : K × Lower blocks) (h : entry ∈ middleInputs K blocks m) :
    (lowerInputs blocks entry.2).length = middleDegree blocks m := by
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp h
  exact lowerInputs_length blocks ⟨m, p⟩

theorem upperInputs_labels (blocks : List (List (Fin n))) (z : Fin n)
    (p : Upper blocks z) :
    (upperInputs blocks z p).map Prod.fst = List.finRange blocks.length := by
  exact matrixEntryPaths_labels _ _ _ _ (List.get_mem _ _)

theorem upperInputs_degree (blocks : List (List (Fin n))) (z : Fin n)
    (p : Upper blocks z) :
    ((upperInputs blocks z p).map (middleDegree blocks)).sum =
      (blocks.map List.length).sum := by
  change ((upperInputs blocks z p).map (fun m => (blocks.get m.1).length)).sum = _
  have h := congrArg (fun l : List (Fin blocks.length) =>
    (l.map (fun b => (blocks.get b).length)).sum) (upperInputs_labels blocks z p)
  have hg := congrArg (List.map List.length) (List.map_get_finRange blocks)
  simp only [List.map_map, Function.comp_def] at hg
  simpa only [List.map_map, Function.comp_def, middleDegree, hg] using h

@[simp] theorem card_middle (blocks : List (List (Fin n))) :
    Fintype.card (Middle blocks) = blocks.length * n ^ 2 := by
  simp [Middle, pow_two]

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.BlockData

variable {n : ℕ}

theorem middleInputs_empty_degree (K : Type*) [One K]
    (blocks : List (List (Fin n))) (m : Middle blocks)
    (h : middleInputs K blocks m = []) : middleDegree blocks m = 0 := by
  by_cases hb : blocks.get m.1 = []
  · change (blocks.get m.1).length = 0
    rw [hb]
    rfl
  · have hc := congrArg List.length h
    simp only [middleInputs, List.length_ofFn, List.length_nil] at hc
    have hp := matrixEntryPaths_length (blocks.get m.1) hb m.2.1 m.2.2
    have hn : 0 < n := Nat.zero_lt_of_lt m.2.1.isLt
    have hpos : 0 < (paths blocks m).length := by
      rw [paths, hp, Fintype.card_fin]
      exact Nat.pow_pos hn
    omega

theorem outputInputs_empty_degree (K : Type*) [One K]
    (blocks : List (List (Fin n))) (z : Fin n)
    (h : outputInputs K blocks z = []) : (blocks.map List.length).sum = 0 := by
  by_cases hb : blocks = []
  · simp [hb]
  · have hc := congrArg List.length h
    simp only [outputInputs, List.length_ofFn, List.length_nil] at hc
    have hp := matrixEntryPaths_length (List.finRange blocks.length)
      (by simpa using hb) z z
    have hn : 0 < n := Nat.zero_lt_of_lt z.isLt
    have hpos : 0 < (upperPaths blocks z).length := by
      rw [upperPaths, hp, Fintype.card_fin]
      exact Nat.pow_pos hn
    omega

/-- The actual homogeneous five-layer block-expansion circuit, before finite reindexing. -/
def indexedCircuit (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    IndexedDepth5Circuit K n
      (Fin n × Fin n × Fin n) (Fin n × Fin n × Fin n)
      (Lower blocks) (Middle blocks) (Upper blocks z) where
  leaves := D5Leaf.variable
  bottomInputs v := [(1, v)]
  bottomDegree _ := 1
  bottomHomogeneous := by
    intro i entry h
    simp only [List.mem_singleton] at h
    subst entry
    rfl
  bottomEmpty := by simp
  lowerInputs := lowerInputs blocks
  middleInputs := middleInputs K blocks
  middleDegree := middleDegree blocks
  middleHomogeneous := by
    intro m entry h
    simpa using middleInputs_homogeneous K blocks m entry h
  middleEmpty := middleInputs_empty_degree K blocks
  upperInputs := upperInputs blocks z
  outputInputs := outputInputs K blocks z
  outputDegree := (blocks.map List.length).sum
  outputHomogeneous := by
    intro entry _
    exact upperInputs_degree blocks z entry.2
  outputEmpty := outputInputs_empty_degree K blocks z

/-- The qualified `Fin`-indexed circuit produced by block expansion. -/
def circuit (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) : Depth5Circuit K n :=
  (indexedCircuit K blocks z).toDepth5Circuit

@[simp] theorem circuit_outputDegree (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) :
    (circuit K blocks z).outputDegree = (blocks.map List.length).sum := rfl

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockMiddleSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.BlockData

variable {n : ℕ}

/-- The lower-gate monomial belonging to an enumerated block path. -/
def lowerMonomial (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (p : Lower blocks) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((lowerInputs blocks p).map MvPolynomial.X).prod

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Each block of layer labels represents the product of its matrices. -/
def immBlock (K : Type*) [CommSemiring K] (n : ℕ) (labels : List (Fin n)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) K) :=
  (labels.map (immLayer K n)).prod

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IndexedCircuitValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335
namespace IndexedDepth5Circuit

variable {K : Type*} [CommSemiring K] {n : ℕ}
variable {L B P M U : Type*}

/-- Value of a bottom gate before relabelling the gate types. -/
def bottomValue (c : IndexedDepth5Circuit K n L B P M U) (i : B) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.bottomInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * d5LeafValue (c.leaves entry.2))).sum

/-- Value of a lower product gate before relabelling the gate types. -/
def lowerValue (c : IndexedDepth5Circuit K n L B P M U) (i : P) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.lowerInputs i).map (fun j => bottomValue c j)).prod

/-- Value of a middle sum gate before relabelling the gate types. -/
def middleValue (c : IndexedDepth5Circuit K n L B P M U) (i : M) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.middleInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * lowerValue c entry.2)).sum

/-- Value of an upper product gate before relabelling the gate types. -/
def upperValue (c : IndexedDepth5Circuit K n L B P M U) (i : U) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  ((c.upperInputs i).map (fun j => middleValue c j)).prod

/-- Polynomial computed by a circuit indexed by arbitrary finite types. -/
def circuitValue (c : IndexedDepth5Circuit K n L B P M U) :
    MvPolynomial (Fin n × Fin n × Fin n) K :=
  (c.outputInputs.map (fun entry =>
    MvPolynomial.C entry.1 * upperValue c entry.2)).sum

variable [Fintype L] [Fintype B] [Fintype P] [Fintype M] [Fintype U]

@[simp] theorem bottomValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card B)) :
    Problem335.bottomValue c.toDepth5Circuit i =
      c.bottomValue ((Fintype.equivFin B).symm i) := by
  simp [Problem335.bottomValue, toDepth5Circuit, bottomValue,
    List.map_map, Function.comp_def]

@[simp] theorem lowerValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card P)) :
    Problem335.lowerValue c.toDepth5Circuit i =
      c.lowerValue ((Fintype.equivFin P).symm i) := by
  simp [Problem335.lowerValue, lowerValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.bottomValue, bottomValue]

@[simp] theorem middleValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card M)) :
    Problem335.middleValue c.toDepth5Circuit i =
      c.middleValue ((Fintype.equivFin M).symm i) := by
  simp [Problem335.middleValue, middleValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.lowerValue, lowerValue,
    Problem335.bottomValue, bottomValue]

@[simp] theorem upperValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) (i : Fin (Fintype.card U)) :
    Problem335.upperValue c.toDepth5Circuit i =
      c.upperValue ((Fintype.equivFin U).symm i) := by
  simp [Problem335.upperValue, upperValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.middleValue, middleValue,
    Problem335.lowerValue, lowerValue, Problem335.bottomValue, bottomValue]

@[simp] theorem circuitValue_toDepth5Circuit
    (c : IndexedDepth5Circuit K n L B P M U) :
    Problem335.circuitValue c.toDepth5Circuit = c.circuitValue := by
  simp [Problem335.circuitValue, circuitValue, toDepth5Circuit,
    List.map_map, Function.comp_def, Problem335.upperValue, upperValue,
    Problem335.middleValue, middleValue, Problem335.lowerValue, lowerValue,
    Problem335.bottomValue, bottomValue]

end IndexedDepth5Circuit
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockCircuitValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BlockData

variable {n : ℕ}

@[simp] theorem indexedCircuit_bottomValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (v : Fin n × Fin n × Fin n) :
    (indexedCircuit K blocks z).bottomValue v = MvPolynomial.X v := by
  simp [IndexedDepth5Circuit.bottomValue, indexedCircuit, d5LeafValue]

@[simp] theorem indexedCircuit_lowerValue (K : Type*) [CommSemiring K]
    (blocks : List (List (Fin n))) (z : Fin n) (p : Lower blocks) :
    (indexedCircuit K blocks z).lowerValue p = lowerMonomial K blocks p := by
  simp [IndexedDepth5Circuit.lowerValue, indexedCircuit, lowerMonomial,
    IndexedDepth5Circuit.bottomValue, d5LeafValue]

end Problem335.BlockData

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BlockPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335

/-- Full blocks followed by one possible shorter final block. -/
def blockLengths (n t : ℕ) : List ℕ :=
  List.replicate (n / t) t ++ if n % t = 0 then [] else [n % t]

/-- Consecutive blocks, with their lengths prescribed explicitly. -/
def consecutiveBlocks {α : Type*} (t : ℕ) (l : List α) : List (List α) :=
  (blockLengths l.length t).splitLengths l

/-- The consecutive blocks of the matrix-layer index list. -/
def layerBlocks (n t : ℕ) : List (List (Fin n)) :=
  consecutiveBlocks t (List.finRange n)

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CeilArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

@[simp] theorem ceilSqrt_one : ceilSqrt 1 = 1 := by
  simp [ceilSqrt]

@[simp] theorem ceilSqrt_two : ceilSqrt 2 = 2 := by
  norm_num [ceilSqrt, Nat.sqrt_two]

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CoefficientSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace Problem335

/-- The scalars actually occurring at a leaf. -/
def leafCoefficientSet {K : Type u} {n : ℕ} (x : D5Leaf K n) : Finset K := by
  classical
  exact match x with
  | .scalar a => {a}
  | .variable _ => ∅

/-- All coefficients occurring in a circuit, including weighted wires. -/
def circuitCoefficientSet {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) : Finset K := by
  classical
  exact (Finset.univ.biUnion fun i => leafCoefficientSet (c.leaves i)) ∪
    (Finset.univ.biUnion fun i => ((c.bottomInputs i).map Prod.fst).toFinset) ∪
    (Finset.univ.biUnion fun i => ((c.middleInputs i).map Prod.fst).toFinset) ∪
    (c.outputInputs.map Prod.fst).toFinset

lemma leaf_scalar_mem_coefficientSet {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.leafCount) (a : K)
    (h : c.leaves i = .scalar a) : a ∈ circuitCoefficientSet c := by
  classical
  simp only [circuitCoefficientSet, Finset.mem_union]
  left; left; left
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [h, leafCoefficientSet]⟩

lemma bottom_coeff_mem_coefficientSet {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) (entry : K × Fin c.leafCount)
    (h : entry ∈ c.bottomInputs i) : entry.1 ∈ circuitCoefficientSet c := by
  classical
  simp only [circuitCoefficientSet, Finset.mem_union]
  left; left; right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨entry, h, rfl⟩)⟩

lemma middle_coeff_mem_coefficientSet {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) (entry : K × Fin c.lowerCount)
    (h : entry ∈ c.middleInputs i) : entry.1 ∈ circuitCoefficientSet c := by
  classical
  simp only [circuitCoefficientSet, Finset.mem_union]
  left; right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨entry, h, rfl⟩)⟩

lemma output_coeff_mem_coefficientSet {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (entry : K × Fin c.upperCount)
    (h : entry ∈ c.outputInputs) : entry.1 ∈ circuitCoefficientSet c := by
  classical
  simp only [circuitCoefficientSet, Finset.mem_union]
  right
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, h, rfl⟩)

/-- The subfield generated by the finitely many coefficients of a circuit. -/
def circuitCoefficientField {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) : Subfield K :=
  Subfield.closure (↑(circuitCoefficientSet c) : Set K)

lemma leaf_scalar_mem {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.leafCount) (a : K)
    (h : c.leaves i = .scalar a) : a ∈ circuitCoefficientField c :=
  Subfield.subset_closure (leaf_scalar_mem_coefficientSet c i a h)

lemma bottom_coeff_mem {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) (entry : K × Fin c.leafCount)
    (h : entry ∈ c.bottomInputs i) : entry.1 ∈ circuitCoefficientField c :=
  Subfield.subset_closure (bottom_coeff_mem_coefficientSet c i entry h)

lemma middle_coeff_mem {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) (entry : K × Fin c.lowerCount)
    (h : entry ∈ c.middleInputs i) : entry.1 ∈ circuitCoefficientField c :=
  Subfield.subset_closure (middle_coeff_mem_coefficientSet c i entry h)

lemma output_coeff_mem {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) (entry : K × Fin c.upperCount)
    (h : entry ∈ c.outputInputs) : entry.1 ∈ circuitCoefficientField c :=
  Subfield.subset_closure (output_coeff_mem_coefficientSet c entry h)

instance circuitCoefficientField_countable {K : Type u} [Field K] {n : ℕ}
    (c : Depth5Circuit K n) : Countable (circuitCoefficientField c) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  exact (Subfield.cardinalMk_closure_le_max (↑(circuitCoefficientSet c) : Set K)).trans
    (max_le (Cardinal.mk_le_aleph0) le_rfl)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CoefficientDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v

namespace Problem335

variable {K : Type u} [Field K] {n : ℕ}

def restrictLeaf (c : Depth5Circuit K n) (i : Fin c.leafCount) :
    D5Leaf (circuitCoefficientField c) n :=
  match h : c.leaves i with
  | .scalar a => .scalar ⟨a, leaf_scalar_mem c i a h⟩
  | .variable x => .variable x

@[simp] theorem restrictLeaf_degree (c : Depth5Circuit K n) (i : Fin c.leafCount) :
    d5LeafDegree (restrictLeaf c i) = d5LeafDegree (c.leaves i) := by
  unfold restrictLeaf
  split <;> simp_all [d5LeafDegree]

def restrictWeightedInputs {ι : Type v} (S : Subfield K) (l : List (K × ι))
    (h : ∀ e ∈ l, e.1 ∈ S) : List (S × ι) :=
  l.attach.map fun e => (⟨e.val.1, h e.val e.property⟩, e.val.2)

@[simp] theorem restrictWeightedInputs_eq_nil_iff {ι : Type v} (S : Subfield K)
    (l : List (K × ι)) (h : ∀ e ∈ l, e.1 ∈ S) :
    restrictWeightedInputs S l h = [] ↔ l = [] := by
  simp [restrictWeightedInputs]

@[simp] theorem restrictWeightedInputs_map_coe {ι : Type v} (S : Subfield K)
    (l : List (K × ι)) (h : ∀ e ∈ l, e.1 ∈ S) :
    (restrictWeightedInputs S l h).map (fun e => ((e.1 : K), e.2)) = l := by
  simp [restrictWeightedInputs, List.map_map, Function.comp_def, List.attach_map_subtype_val]

/-- Restrict a circuit to the subfield generated by its occurring coefficients. -/
def restrictCircuit (c : Depth5Circuit K n) : Depth5Circuit (circuitCoefficientField c) n where
  leafCount := c.leafCount
  leaves := restrictLeaf c
  bottomCount := c.bottomCount
  bottomInputs i := restrictWeightedInputs _ (c.bottomInputs i) (bottom_coeff_mem c i)
  bottomDegree := c.bottomDegree
  bottomHomogeneous := by
    intro i e he
    rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
    simpa using c.bottomHomogeneous i a.val a.property
  bottomEmpty := by
    intro i h
    exact c.bottomEmpty i ((restrictWeightedInputs_eq_nil_iff _ _ _).mp h)
  lowerCount := c.lowerCount
  lowerInputs := c.lowerInputs
  middleCount := c.middleCount
  middleInputs i := restrictWeightedInputs _ (c.middleInputs i) (middle_coeff_mem c i)
  middleDegree := c.middleDegree
  middleHomogeneous := by
    intro i e he
    rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
    exact c.middleHomogeneous i a.val a.property
  middleEmpty := by
    intro i h
    exact c.middleEmpty i ((restrictWeightedInputs_eq_nil_iff _ _ _).mp h)
  upperCount := c.upperCount
  upperInputs := c.upperInputs
  outputInputs := restrictWeightedInputs _ c.outputInputs (output_coeff_mem c)
  outputDegree := c.outputDegree
  outputHomogeneous := by
    intro e he
    rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
    exact c.outputHomogeneous a.val a.property
  outputEmpty := by
    intro h
    exact c.outputEmpty ((restrictWeightedInputs_eq_nil_iff _ _ _).mp h)

@[simp] theorem circuitSize_restrictCircuit (c : Depth5Circuit K n) :
    circuitSize (restrictCircuit c) = circuitSize c := rfl


@[simp] theorem map_restrictLeaf_value (c : Depth5Circuit K n) (i : Fin c.leafCount) :
    MvPolynomial.map (circuitCoefficientField c).subtype (d5LeafValue (restrictLeaf c i)) =
      d5LeafValue (c.leaves i) := by
  unfold restrictLeaf
  split <;> simp_all [d5LeafValue]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CoefficientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u v w

namespace Problem335

namespace D5Leaf

def mapCoefficients {K : Type u} {L : Type v} {n : ℕ}
    (f : K → L) : D5Leaf K n → D5Leaf L n
  | .scalar a => .scalar (f a)
  | .variable x => .variable x

@[simp] theorem degree_mapCoefficients {K : Type u} {L : Type v} {n : ℕ}
    (f : K → L) (x : D5Leaf K n) :
    d5LeafDegree (mapCoefficients f x) = d5LeafDegree x := by
  cases x <;> rfl

@[simp] theorem mapCoefficients_id {K : Type u} {n : ℕ} (x : D5Leaf K n) :
    mapCoefficients id x = x := by cases x <;> rfl

@[simp] theorem mapCoefficients_comp {K : Type u} {L : Type v} {M : Type w}
    {n : ℕ} (f : K → L) (g : L → M) (x : D5Leaf K n) :
    mapCoefficients g (mapCoefficients f x) = mapCoefficients (g ∘ f) x := by
  cases x <;> rfl

end D5Leaf

/-- Pure coefficient relabeling; no algebraic properties are needed for syntactic homogeneity. -/
def Depth5Circuit.mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) : Depth5Circuit L n where
  leafCount := c.leafCount
  leaves := fun i => D5Leaf.mapCoefficients f (c.leaves i)
  bottomCount := c.bottomCount
  bottomInputs := fun i => (c.bottomInputs i).map (fun e => (f e.1, e.2))
  bottomDegree := c.bottomDegree
  bottomHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    simpa using c.bottomHomogeneous i e he
  bottomEmpty := by
    intro i h
    exact c.bottomEmpty i (List.map_eq_nil_iff.mp h)
  lowerCount := c.lowerCount
  lowerInputs := c.lowerInputs
  middleCount := c.middleCount
  middleInputs := fun i => (c.middleInputs i).map (fun e => (f e.1, e.2))
  middleDegree := c.middleDegree
  middleHomogeneous := by
    intro i entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact c.middleHomogeneous i e he
  middleEmpty := by
    intro i h
    exact c.middleEmpty i (List.map_eq_nil_iff.mp h)
  upperCount := c.upperCount
  upperInputs := c.upperInputs
  outputInputs := c.outputInputs.map (fun e => (f e.1, e.2))
  outputDegree := c.outputDegree
  outputHomogeneous := by
    intro entry h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    exact c.outputHomogeneous e he
  outputEmpty := by
    intro h
    exact c.outputEmpty (List.map_eq_nil_iff.mp h)

@[simp] theorem Depth5Circuit.lowerInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    (c.mapCoefficients f).lowerInputs i = c.lowerInputs i := rfl

@[simp] theorem Depth5Circuit.middleInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    (c.mapCoefficients f).middleInputs i =
      (c.middleInputs i).map (fun e => (f e.1, e.2)) := rfl

@[simp] theorem Depth5Circuit.upperInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    (c.mapCoefficients f).upperInputs i = c.upperInputs i := rfl

@[simp] theorem Depth5Circuit.outputInputs_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) :
    (c.mapCoefficients f).outputInputs =
      c.outputInputs.map (fun e => (f e.1, e.2)) := rfl

@[simp] theorem circuitSize_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K → L) (c : Depth5Circuit K n) :
    circuitSize (c.mapCoefficients f) = circuitSize c := rfl

@[simp] theorem d5LeafValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (x : D5Leaf K n) :
    d5LeafValue (x.mapCoefficients f) = MvPolynomial.map f (d5LeafValue x) := by
  cases x <;> simp [D5Leaf.mapCoefficients, d5LeafValue]

@[simp] theorem bottomValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    bottomValue (c.mapCoefficients f) i = MvPolynomial.map f (bottomValue c i) := by
  simp [bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum]

@[simp] theorem lowerValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    lowerValue (c.mapCoefficients f) i = MvPolynomial.map f (lowerValue c i) := by
  simp [lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]

@[simp] theorem middleValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    middleValue (c.mapCoefficients f) i = MvPolynomial.map f (middleValue c i) := by
  simp [middleValue, lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]

@[simp] theorem upperValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    upperValue (c.mapCoefficients f) i = MvPolynomial.map f (upperValue c i) := by
  simp [upperValue, middleValue, lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]

@[simp] theorem circuitValue_mapCoefficients {K : Type u} {L : Type v}
    [CommSemiring K] [CommSemiring L] {n : ℕ}
    (f : K →+* L) (c : Depth5Circuit K n) :
    circuitValue (c.mapCoefficients f) = MvPolynomial.map f (circuitValue c) := by
  simp [circuitValue, upperValue, middleValue, lowerValue, bottomValue, Depth5Circuit.mapCoefficients, List.map_map,
    Function.comp_def, map_list_sum, map_list_prod]
@[simp] theorem Depth5Circuit.mapCoefficients_id {K : Type u}
    [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n) :
    c.mapCoefficients id = c := by
  cases c
  simp [Depth5Circuit.mapCoefficients]

@[simp] theorem Depth5Circuit.mapCoefficients_comp {K : Type u} {L : Type v}
    {M : Type w} [CommSemiring K] [CommSemiring L] [CommSemiring M]
    {n : ℕ} (f : K → L) (g : L → M) (c : Depth5Circuit K n) :
    (c.mapCoefficients f).mapCoefficients g = c.mapCoefficients (g ∘ f) := by
  cases c
  simp [Depth5Circuit.mapCoefficients, List.map_map, Function.comp_def]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The finite product appearing when a composition factorial moment is normalized
by the independent geometric factorial moment. -/
def occupationRatio (t r : ℝ) (H : ℕ) : ℝ :=
  ∏ j ∈ Finset.range H, (1 - (j : ℝ) / t) / (1 + (j : ℝ) / r)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

def fallingFactorialSeries (d : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun j => (j.descFactorial d : ℝ)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FirstOccupationMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Uniform average over all weak compositions of `t` in the coordinates `ι`. -/
def occupationAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (f : (ι →₀ ℕ) → ℝ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t, f M) /
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CompositionAntidiag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BidegreeAverages

/-- The function representation of a weak composition and the finite
`finsuppAntidiag` representation used by occupation moments agree coordinatewise. -/
def compositionAntidiagEquiv (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    Composition σ a ≃ (Finset.finsuppAntidiag (Finset.univ : Finset σ) a) := by
  refine Finsupp.equivFunOnFinite.symm.subtypeEquiv ?_
  intro d
  simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rfl

@[simp] theorem compositionAntidiagEquiv_apply (σ : Type*)
    [Fintype σ] [DecidableEq σ] (a : ℕ) (d : Composition σ a) (i : σ) :
    (compositionAntidiagEquiv σ a d).val i = d.val i := rfl

end Problem335.BidegreeAverages

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ScheduleEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.BalancedSchedule

/-- The layer immediately left of an internal vertex. -/
def leftLayer {n : ℕ} (v : Fin (n - 1)) : Fin n := ⟨v.val, by omega⟩

/-- The layer immediately right of an internal vertex. -/
def rightLayer {n : ℕ} (v : Fin (n - 1)) : Fin n := ⟨v.val + 1, by omega⟩

/-- Internal ends at which both incident layers have type N (`false`). -/
def nnInternalEnds {n : ℕ} (τ : Fin n → Bool) (i : Fin n) : Finset (Fin (n - 1)) :=
  (internalEnds i).filter (fun v => τ (leftLayer v) = false ∧ τ (rightLayer v) = false)

end Problem335.BalancedSchedule

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.LowerParameters

/-- The actual balanced schedule for the rank-measure parameters of degree `n`. -/
def balancedWord (n : ℕ) : List Bool := BalancedSchedule.word (k n) (s n)

lemma balancedWord_length {n : ℕ} (hn : 4 ≤ n) : (balancedWord n).length = n := by
  rw [balancedWord, BalancedSchedule.word_length (k_pos hn), two_mul_k_add_s]

/-- `true` selects derivative layers and `false` selects multiplication layers. -/
def balancedLayer {n : ℕ} (hn : 4 ≤ n) : Fin n → Bool := fun i =>
  (balancedWord n).get ⟨i.val, by simp [balancedWord_length hn]⟩

/-- Layer-restricted IMM variables are a product of selected layers and matrix entries. -/
def layerVariableEquiv {n : ℕ} (p : Fin n → Bool) (b : Bool) :
    {x : Fin n × Fin n × Fin n // p x.1 = b} ≃
      {i : Fin n // p i = b} × Fin n × Fin n where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2.1, x.1.2.2)
  invFun x := ⟨(x.1.1, x.2.1, x.2.2), x.1.2⟩
  left_inv := by rintro ⟨⟨i, j, l⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨i, h⟩, j, l⟩; rfl

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ConfiguredRankData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common, concrete data for the two sides of the IMM rank comparison. -/

noncomputable section

namespace Problem335.LowerParameters

/-- The source dimension for the configured bidegree rank measure. -/
def rankDimension (n : ℕ) : ℝ :=
  (homogeneousDim (v n) (a n) : ℝ) * (homogeneousDim (u n) (b n) : ℝ)

/-- The common path-count and occupation-mean factor in the two trace moments. -/
def rankMomentScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (n - 1) * ((a n : ℝ) / (v n : ℝ)) ^ k n *
    (1 + (b n : ℝ) / (u n : ℝ)) ^ m n

/-- The actual rank measure, extended by zero outside the range where the
balanced schedule is used. The small values do not enter the eventual bounds. -/
def rankData (n : ℕ) (p : MvPolynomial (Fin n × Fin n × Fin n) ℂ) : ℝ :=
  if hn : 4 ≤ n then
    (bidegreeRank (fun x : Fin n × Fin n × Fin n => balancedLayer hn x.1)
      (a n) (b n) (k n) (m n) p : ℝ)
  else 0

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FactorialPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative falling-factorial expansions for the local trace weights. -/
namespace Problem335

open scoped BigOperators

universe u

/-- Evaluation of a falling-factorial monomial at a natural occupation vector. -/
def factorialMonomial {σ : Type u} [Fintype σ]
    (d M : σ → ℕ) : ℕ := ∏ i, (M i).descFactorial (d i)

/-- A finite expansion with natural (hence nonnegative) coefficients,
    bounded total order, supported on a specified coordinate set. -/
structure FactorialExpansion {σ : Type u} [Fintype σ]
    (f : (σ → ℕ) → ℕ) (S : Finset σ) (D : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  coeff : Index → ℕ
  degree : Index → σ → ℕ
  order_le : ∀ j, ∑ i, degree j i ≤ D
  supported : ∀ j i, i ∉ S → degree j i = 0
  eval_eq : ∀ M, f M = ∑ j, coeff j * factorialMonomial (degree j) M

attribute [instance] FactorialExpansion.indexFintype

namespace FactorialExpansion

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- A disjoint-coordinate product has the product of the local coefficients. -/
def mul {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (G : FactorialExpansion g T E)
    (hST : Disjoint S T) :
    FactorialExpansion (fun M => f M * g M) (S ∪ T) (D + E) where
  Index := F.Index × G.Index
  indexFintype := inferInstance
  coeff := fun j => F.coeff j.1 * G.coeff j.2
  degree := fun j i => F.degree j.1 i + G.degree j.2 i
  order_le := by
    intro j
    simpa [Finset.sum_add_distrib] using Nat.add_le_add (F.order_le j.1) (G.order_le j.2)
  supported := by
    intro j i hi
    simp only [Finset.mem_union, not_or] at hi
    simp [F.supported j.1 i hi.1, G.supported j.2 i hi.2]
  eval_eq := by
    intro M
    have hterm (a : F.Index) (b : G.Index) :
        factorialMonomial (fun i => F.degree a i + G.degree b i) M =
          factorialMonomial (F.degree a) M * factorialMonomial (G.degree b) M := by
      unfold factorialMonomial
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hS : i ∈ S
      · have hT : i ∉ T := fun ht => (Finset.disjoint_left.mp hST) hS ht
        simp [G.supported b i hT]
      · simp [F.supported a i hS]
    rw [F.eval_eq, G.eval_eq, Finset.sum_mul_sum]
    simp only [Fintype.sum_prod_type, hterm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring

theorem factorialMonomial_single (i : σ) (d : ℕ) (M : σ → ℕ) :
    factorialMonomial (fun j => if j = i then d else 0) M = (M i).descFactorial d := by
  simp [factorialMonomial, apply_ite]

/-- Lift an explicit univariate expansion to one selected coordinate. -/
def coordinate (i : σ) (J : Type) [Fintype J] (c e : J → ℕ)
    {f : ℕ → ℕ} {D : ℕ} (he : ∀ j, e j ≤ D)
    (hf : ∀ z, f z = ∑ j, c j * z.descFactorial (e j)) :
    FactorialExpansion (fun M => f (M i)) {i} D where
  Index := J
  indexFintype := inferInstance
  coeff := c
  degree := fun a j => if j = i then e a else 0
  order_le := by intro a; simpa using he a
  supported := by
    intro a j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  eval_eq := by intro M; simpa only [factorialMonomial_single] using hf (M i)

/-- The occupation itself has order one. -/
def occupation (i : σ) : FactorialExpansion (fun M => M i) {i} 1 :=
  coordinate (f := fun z => z) (D := 1) i Unit (fun _ => 1) (fun _ => 1) (by simp) (by simp)

/-- Creation operators contribute the successor occupation. -/
def successor (i : σ) : FactorialExpansion (fun M => M i + 1) {i} 1 :=
  coordinate (f := fun z => z + 1) (D := 1) i (Fin 2) (fun _ => 1) ![1, 0]
    (by intro j; fin_cases j <;> simp)
    (by intro z; simp [Fin.sum_univ_two])

theorem square_descFactorial (z : ℕ) : z ^ 2 = z.descFactorial 2 + z := by
  cases z with
  | zero => simp
  | succ z => simp [Nat.descFactorial_succ]; ring

/-- A repeated annihilation coordinate retains its extra first-order term. -/
def square (i : σ) : FactorialExpansion (fun M => (M i) ^ 2) {i} 2 :=
  coordinate (f := fun z => z ^ 2) (D := 2) i (Fin 2) (fun _ => 1) ![2, 1]
    (by intro j; fin_cases j <;> simp)
    (by intro z; simpa [Fin.sum_univ_two] using square_descFactorial z)

/-- The repeated creation-coordinate weight has coefficients `1,3,1`. -/
def successorSquare (i : σ) :
    FactorialExpansion (fun M => (M i + 1) ^ 2) {i} 2 :=
  coordinate (f := fun z => (z + 1) ^ 2) (D := 2) i (Fin 3) ![1, 3, 1] ![2, 1, 0]
    (by intro j; fin_cases j <;> simp)
    (by
      intro z
      simp only [Fin.sum_univ_three]
      simp
      have h := square_descFactorial z
      simp [Nat.descFactorial_succ] at h
      nlinarith)

/-- Copy the coefficient data while enlarging bounds or changing the displayed
function by pointwise equality. Unlike a type cast, this keeps all data projections transparent. -/
def reframe {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (hfg : ∀ M, f M = g M)
    (hST : S ⊆ T) (hDE : D ≤ E) : FactorialExpansion g T E where
  Index := F.Index
  indexFintype := F.indexFintype
  coeff := F.coeff
  degree := F.degree
  order_le := fun j => (F.order_le j).trans hDE
  supported := fun j i hi => F.supported j i (fun h => hi (hST h))
  eval_eq := fun M => (hfg M).symm.trans (F.eval_eq M)

/-- The normal pairing in a derivative layer, including equal coordinates. -/
def normalDerivative (i j : σ) :
    FactorialExpansion (fun M => M i * M j) {i, j} 2 := by
  by_cases h : i = j
  · exact (square i).reframe (by intro M; simp [h, pow_two]) (by simp) (by rfl)
  · exact ((occupation i).mul (occupation j) (by simpa using h)).reframe
      (by intro M; rfl) (by simp) (by rfl)

/-- The normal pairing in a multiplication layer, including equal coordinates. -/
def normalMultiplication (i j : σ) :
    FactorialExpansion (fun M => (M i + 1) * (M j + 1)) {i, j} 2 := by
  by_cases h : i = j
  · exact (successorSquare i).reframe (by intro M; simp [h, pow_two]) (by simp) (by rfl)
  · exact ((successor i).mul (successor j) (by simpa using h)).reframe
      (by intro M; rfl) (by simp) (by rfl)

/-- The distinct-coordinate pairing in a derivative layer. -/
def distinctDerivative (i j : σ) (h : i ≠ j) :
    FactorialExpansion (fun M => M i * (M j + 1)) {i, j} 2 :=
  ((occupation i).mul (successor j) (by simpa using h)).reframe
    (by intro M; rfl) (by simp) (by rfl)

/-- The distinct-coordinate pairing in a multiplication layer. -/
def distinctMultiplication (i j : σ) (h : i ≠ j) :
    FactorialExpansion (fun M => (M i + 1) * M j) {i, j} 2 :=
  ((successor i).mul (occupation j) (by simpa using h)).reframe
    (by intro M; rfl) (by simp) (by rfl)

/-- A constant has a single order-zero term. -/
def constant (c : ℕ) : FactorialExpansion (fun _ : σ → ℕ => c) ∅ 0 where
  Index := Unit
  indexFintype := inferInstance
  coeff := fun _ => c
  degree := fun _ _ => 0
  order_le := by simp
  supported := by simp
  eval_eq := by simp [factorialMonomial]

end FactorialExpansion
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalMomentPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

/-- Squared local Fock coefficient, with `true` denoting differentiation. -/
def mass (derivative : Bool) (z : ℕ) : ℝ :=
  if derivative then z else z + 1

def coefficient (derivative : Bool) (z : ℕ) : ℝ :=
  Real.sqrt (mass derivative z)

/-- One layer's four factors in the second trace. -/
def fourCoefficient (derivative : Bool) (a b c d : ℕ) : ℝ :=
  coefficient derivative a * coefficient derivative b *
    coefficient derivative c * coefficient derivative d

/-- The unavailable differentiation contribution vanishes identically. -/
@[simp] lemma derivative_invalid (b : ℕ) :
    (0 : ℝ) * ((b : ℝ) + 1) = 0 := zero_mul _

/-- If the multiplication shift would create a negative source occupation,
its table contribution is zero. -/
@[simp] lemma multiplication_invalid (a : ℕ) :
    ((a : ℝ) + 1) * (0 : ℝ) = 0 := mul_zero _

/-- Geometric first/second-moment input, before normalization, for normal pairings. -/
def normalGeometricMass (derivative : Bool) (G : ℝ) (collision : Bool) : ℝ :=
  if derivative then
    if collision then 2 * G^2 + G else G^2
  else
    if collision then 2 * G^2 + 3 * G + 1 else (G + 1)^2

def diagonalGeometricMass (G : ℝ) : ℝ := G * (G + 1)

end LocalMoments
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.Pairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-path pairing identities for the mixed-operator moment argument. -/

namespace Problem335
namespace Pairings

open scoped BigOperators

/-- Equality of differences of coordinate vectors has only the two pairing patterns. -/
theorem coordinate_difference_eq_iff {α : Type*} (p q r s : α) :
    (Finsupp.single p (1 : ℤ) - Finsupp.single q 1 =
      Finsupp.single r 1 - Finsupp.single s 1) ↔
    (p = q ∧ r = s) ∨ (p = r ∧ q = s) := by
  classical
  constructor
  · intro h
    by_cases hpq : p = q
    · left
      refine ⟨hpq, ?_⟩
      by_contra hrs
      have hr := congrArg (fun f : α →₀ ℤ => f r) h
      simp [hpq, hrs] at hr
    · right
      have hpr : p = r := by
        by_contra hpr
        have hp := congrArg (fun f : α →₀ ℤ => f p) h
        simp only [Finsupp.sub_apply, Finsupp.single_apply] at hp
        split_ifs at hp <;> simp_all
      refine ⟨hpr, ?_⟩
      by_contra hqs
      have hq := congrArg (fun f : α →₀ ℤ => f q) h
      simp only [Finsupp.sub_apply, Finsupp.single_apply] at hq
      split_ifs at hq <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The two cases become disjoint when the all-equal case is assigned to normal pairing. -/
theorem coordinate_difference_eq_iff_exclusive {α : Type*} (p q r s : α) :
    (Finsupp.single p (1 : ℤ) - Finsupp.single q 1 =
      Finsupp.single r 1 - Finsupp.single s 1) ↔
    (p = q ∧ r = s) ∨ (p = r ∧ q = s ∧ p ≠ q) := by
  rw [coordinate_difference_eq_iff]
  constructor
  · rintro (h | ⟨hpr, hqs⟩)
    · exact Or.inl h
    · by_cases hpq : p = q
      · exact Or.inl ⟨hpq, by simpa [← hpr, ← hqs] using hpq⟩
      · exact Or.inr ⟨hpr, hqs, hpq⟩
  · rintro (h | ⟨hpr, hqs, _⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hpr, hqs⟩

/-- Pairing patterns at a layer, with the inequality omitted in the diagonal case. -/
inductive Kind where
  | normal
  | diagonal
  deriving DecidableEq

protected abbrev Kind.enumList : List Kind := [.normal, .diagonal]

protected theorem Kind.enumList_getElem?_ctorIdx_eq (kind : Kind) :
    Kind.enumList[kind.ctorIdx]? = some kind := by
  cases kind <;> rfl

protected theorem Kind.enumList_nodup : Kind.enumList.Nodup := by decide

instance instFintypeKind : Fintype Kind where
  elems := ⟨Kind.enumList, Multiset.coe_nodup.mpr Kind.enumList_nodup⟩
  complete kind := List.mem_iff_getElem?.mpr
    ⟨kind.ctorIdx, Kind.enumList_getElem?_ctorIdx_eq kind⟩

/-- Boolean words use false for the normal pairing and true for the diagonal pairing. -/
def boolKindEquiv : Bool ≃ Kind where
  toFun b := if b then .diagonal else .normal
  invFun
    | .normal => false
    | .diagonal => true
  left_inv b := by cases b <;> rfl
  right_inv k := by cases k <;> rfl

@[simp] theorem boolKindEquiv_false : boolKindEquiv false = Kind.normal := rfl
@[simp] theorem boolKindEquiv_true : boolKindEquiv true = Kind.diagonal := rfl

/-- The four labels contributed by the four paths at a single vertex. -/
@[ext]
structure Labels (α : Type*) where
  p : α
  q : α
  r : α
  s : α
  deriving Fintype

def Respects {α : Type*} : Kind → Labels α → Prop
  | .normal, x => x.p = x.q ∧ x.r = x.s
  | .diagonal, x => x.p = x.r ∧ x.q = x.s

instance instDecidableRespectsOfDecidableEq {α : Type*} [DecidableEq α] (τ : Kind) (x : Labels α) :
    Decidable (Respects τ x) := by
  cases τ <;> unfold Respects <;> infer_instance

/-- The exact (disjoint) pairing classes before relaxing the diagonal inequality. -/
def ExactRespects {α : Type*} : Kind → Labels α → Prop
  | .normal, x => x.p = x.q ∧ x.r = x.s
  | .diagonal, x => x.p = x.r ∧ x.q = x.s ∧ x.p ≠ x.q

/-- No compatible coordinate quadruple belongs to both exact pairing classes. -/
theorem exactRespects_unique {α : Type*} {τ σ : Kind} {x : Labels α}
    (hτ : ExactRespects τ x) (hσ : ExactRespects σ x) : τ = σ := by
  cases τ <;> cases σ <;> simp_all [ExactRespects]

/-- Every compatible coordinate quadruple has a unique exact pairing type. -/
theorem coordinate_difference_eq_iff_existsUnique {α : Type*} (x : Labels α) :
    (Finsupp.single x.p (1 : ℤ) - Finsupp.single x.q 1 =
      Finsupp.single x.r 1 - Finsupp.single x.s 1) ↔
    ∃! τ : Kind, ExactRespects τ x := by
  rw [coordinate_difference_eq_iff_exclusive]
  constructor
  · rintro (h | h)
    · exact ⟨.normal, h, fun _ hk => exactRespects_unique hk h⟩
    · exact ⟨.diagonal, h, fun _ hk => exactRespects_unique hk h⟩
  · rintro ⟨τ, h, _⟩
    cases τ
    · exact Or.inl h
    · exact Or.inr h

/-- Labels allowed by both adjacent layers. -/
abbrev Vertex (α : Type*) (τ σ : Kind) :=
  {x : Labels α // Respects τ x ∧ Respects σ x}

def normalVertexEquiv (α : Type*) : Vertex α .normal .normal ≃ α × α where
  toFun x := (x.1.p, x.1.r)
  invFun x := ⟨⟨x.1, x.1, x.2, x.2⟩, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  left_inv x := by
    have hp := x.2
    apply Subtype.ext
    apply Labels.ext <;> simp_all [Respects]
  right_inv x := by cases x; rfl

def diagonalVertexEquiv (α : Type*) : Vertex α .diagonal .diagonal ≃ α × α where
  toFun x := (x.1.p, x.1.q)
  invFun x := ⟨⟨x.1, x.2, x.1, x.2⟩, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  left_inv x := by
    have hp := x.2
    apply Subtype.ext
    apply Labels.ext <;> simp_all [Respects]
  right_inv x := by cases x; rfl

def mixedVertexEquiv (α : Type*) : Vertex α .normal .diagonal ≃ α where
  toFun x := x.1.p
  invFun x := ⟨⟨x, x, x, x⟩, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩
  left_inv x := by
    have hp := x.2
    apply Subtype.ext
    apply Labels.ext <;> simp_all [Respects]
  right_inv x := rfl

def swapVertexEquiv (α : Type*) (τ σ : Kind) : Vertex α τ σ ≃ Vertex α σ τ where
  toFun x := ⟨x.1, x.2.symm⟩
  invFun x := ⟨x.1, x.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Number of interfaces at which a word changes its letter. -/
def adjacentSwitches {β : Type*} [DecidableEq β] {L : ℕ}
    (τ : Fin (L + 1) → β) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => τ i.castSucc ≠ τ i.succ)).card

/-- The relaxed four-path assignments factor as a product over internal vertices. -/
abbrev Assignments (α : Type*) {L : ℕ} (τ : Fin (L + 1) → Kind) :=
  (i : Fin L) → Vertex α (τ i.castSucc) (τ i.succ)

end Pairings
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FourPathLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

/-- A valid source-occupation shift arising from two paths at a single layer. -/
def ShiftRelation {σ : Type*} (derivative : Bool) (M M' : σ → ℕ) (p q : σ) : Prop :=
  ∀ x, (M' x : ℤ) = (M x : ℤ) + (if derivative then -1 else 1) *
    ((Finsupp.single p (1 : ℤ) - Finsupp.single q 1 : σ →₀ ℤ) x)

/-- The complete local second-trace polynomial. The all-equal case belongs to normal pairing. -/
def localPolynomial {σ : Type*} [DecidableEq σ] (derivative : Bool)
    (M : σ → ℕ) (p q r : σ) : ℝ :=
  if p = q then mass derivative (M p) * mass derivative (M r)
  else if derivative then (M p : ℝ) * ((M q : ℝ) + 1)
  else ((M p : ℝ) + 1) * (M q : ℝ)

end LocalMoments
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalFactorialExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local four-path table has bounded nonnegative factorial expansions. -/
namespace Problem335

open scoped BigOperators

namespace LocalMoments

variable {σ : Type*} [DecidableEq σ]

/-- Natural-valued version of the exact local table. -/
def localPolynomialNat (derivative : Bool) (M : σ → ℕ) (p q r : σ) : ℕ :=
  if p = q then
    if derivative then M p * M r else (M p + 1) * (M r + 1)
  else if derivative then M p * (M q + 1) else (M p + 1) * M q

@[simp] theorem localPolynomialNat_cast (derivative : Bool) (M : σ → ℕ) (p q r : σ) :
    (localPolynomialNat derivative M p q r : ℝ) = localPolynomial derivative M p q r := by
  cases derivative <;> by_cases h : p = q <;> simp [localPolynomialNat, localPolynomial, mass, h]

/-- All branches of the local four-path table have total factorial order at most two.
The normal branch includes coincident coordinates and their first-order corrections. -/
def localPolynomialExpansion [Fintype σ] (derivative : Bool) (p q r : σ) :
    FactorialExpansion (fun M => localPolynomialNat derivative M p q r) {p, q, r} 2 := by
  have hpr : ({p, r} : Finset σ) ⊆ {p, q, r} := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  have hpq : ({p, q} : Finset σ) ⊆ {p, q, r} := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  cases derivative
  · by_cases h : p = q
    · exact (FactorialExpansion.normalMultiplication p r).reframe
        (by intro M; simp [localPolynomialNat, h]) hpr (le_refl 2)
    · exact (FactorialExpansion.distinctMultiplication p q h).reframe
        (by intro M; simp [localPolynomialNat, h]) hpq (le_refl 2)
  · by_cases h : p = q
    · exact (FactorialExpansion.normalDerivative p r).reframe
        (by intro M; simp [localPolynomialNat, h]) hpr (le_refl 2)
    · exact (FactorialExpansion.distinctDerivative p q h).reframe
        (by intro M; simp [localPolynomialNat, h]) hpq (le_refl 2)

/-- The natural polynomial for a finite set of layers. -/
def localProductNat {ι : Type*} (layers : Finset ι) (derivative : ι → Bool)
    (p q r : ι → σ) (M : σ → ℕ) : ℕ :=
  ∏ t ∈ layers, localPolynomialNat (derivative t) M (p t) (q t) (r t)

@[simp] theorem localProductNat_cast {ι : Type*} (layers : Finset ι)
    (derivative : ι → Bool) (p q r : ι → σ) (M : σ → ℕ) :
    (localProductNat layers derivative p q r M : ℝ) =
      ∏ t ∈ layers, localPolynomial (derivative t) M (p t) (q t) (r t) := by
  simp [localProductNat]

end LocalMoments
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FactorialGeometricValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite geometric-moment evaluation of nonnegative factorial expansions. -/
namespace Problem335

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

/-- Independent geometric factorial moments, with a possibly different mean per coordinate. -/
def geometricFactorialMonomial (d : σ → ℕ) (G : σ → ℝ) : ℝ :=
  ∏ i, ((d i).factorial : ℝ) * G i ^ d i

namespace FactorialExpansion

/-- The finite value to which occupation comparison bounds an expansion. -/
def geometricValue {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}
    (F : FactorialExpansion f S D) (G : σ → ℝ) : ℝ :=
  ∑ j, (F.coeff j : ℝ) * geometricFactorialMonomial (F.degree j) G

@[simp] theorem geometricValue_reframe [DecidableEq σ]
    {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (hfg : ∀ M, f M = g M)
    (hST : S ⊆ T) (hDE : D ≤ E) (G : σ → ℝ) :
    (F.reframe hfg hST hDE).geometricValue G = F.geometricValue G := rfl

variable [DecidableEq σ]

@[simp] theorem geometricFactorialMonomial_single (i : σ) (d : ℕ) (G : σ → ℝ) :
    geometricFactorialMonomial (fun j => if j = i then d else 0) G =
      (d.factorial : ℝ) * G i ^ d := by
  unfold geometricFactorialMonomial
  calc
    _ = ∏ j, if j = i then (d.factorial : ℝ) * G j ^ d else 1 := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : j = i <;> simp [h]
    _ = _ := by simp

/-- Independence at disjoint coordinates is an exact algebraic identity of the
finite factorial-moment values; no probability-space construction is needed. -/
@[simp] theorem geometricValue_mul {f g : (σ → ℕ) → ℕ} {S T : Finset σ} {D E : ℕ}
    (F : FactorialExpansion f S D) (H : FactorialExpansion g T E)
    (hST : Disjoint S T) (G : σ → ℝ) :
    (F.mul H hST).geometricValue G = F.geometricValue G * H.geometricValue G := by
  have hterm (a : F.Index) (b : H.Index) :
      geometricFactorialMonomial (fun i => F.degree a i + H.degree b i) G =
        geometricFactorialMonomial (F.degree a) G * geometricFactorialMonomial (H.degree b) G := by
    unfold geometricFactorialMonomial
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hS : i ∈ S
    · have hT : i ∉ T := fun ht => (Finset.disjoint_left.mp hST) hS ht
      simp [H.supported b i hT]
    · simp [F.supported a i hS]
  change (∑ j : F.Index × H.Index, ((F.coeff j.1 * H.coeff j.2 : ℕ) : ℝ) *
      geometricFactorialMonomial (fun i => F.degree j.1 i + H.degree j.2 i) G) = _
  simp only [Fintype.sum_prod_type, Nat.cast_mul, hterm, geometricValue, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

@[simp] theorem geometricValue_coordinate (i : σ) (J : Type) [Fintype J] (c e : J → ℕ)
    {f : ℕ → ℕ} {D : ℕ} (he : ∀ j, e j ≤ D)
    (hf : ∀ z, f z = ∑ j, c j * z.descFactorial (e j)) (G : σ → ℝ) :
    (coordinate i J c e he hf).geometricValue G =
      ∑ j, (c j : ℝ) * ((e j).factorial : ℝ) * G i ^ e j := by
  change (∑ j : J, (c j : ℝ) *
    geometricFactorialMonomial (fun k => if k = i then e j else 0) G) = _
  simp only [geometricFactorialMonomial_single, mul_assoc]

@[simp] theorem geometricValue_occupation (i : σ) (G : σ → ℝ) :
    (occupation i).geometricValue G = G i := by simp [occupation]

@[simp] theorem geometricValue_successor (i : σ) (G : σ → ℝ) :
    (successor i).geometricValue G = G i + 1 := by
  simp [successor, Fin.sum_univ_two]

@[simp] theorem geometricValue_square (i : σ) (G : σ → ℝ) :
    (square i).geometricValue G = 2 * G i ^ 2 + G i := by
  simp [square, Fin.sum_univ_two]

@[simp] theorem geometricValue_successorSquare (i : σ) (G : σ → ℝ) :
    (successorSquare i).geometricValue G = 2 * G i ^ 2 + 3 * G i + 1 := by
  simp [successorSquare, Fin.sum_univ_three]

@[simp] theorem geometricValue_distinctDerivative (i j : σ) (h : i ≠ j) (G : σ → ℝ) :
    (distinctDerivative i j h).geometricValue G = G i * (G j + 1) := by
  change ((occupation i).mul (successor j) (by simpa using h)).geometricValue G = _
  rw [geometricValue_mul]
  simp

@[simp] theorem geometricValue_distinctMultiplication (i j : σ) (h : i ≠ j) (G : σ → ℝ) :
    (distinctMultiplication i j h).geometricValue G = (G i + 1) * G j := by
  change ((successor i).mul (occupation j) (by simpa using h)).geometricValue G = _
  rw [geometricValue_mul]
  simp

omit [DecidableEq σ] in
@[simp] theorem geometricValue_constant (c : ℕ) (G : σ → ℝ) :
    (constant c : FactorialExpansion (fun _ : σ → ℕ => c) ∅ 0).geometricValue G = c := by
  change (∑ _ : Unit, (c : ℝ) * geometricFactorialMonomial (fun _ : σ => 0) G) = _
  simp [geometricFactorialMonomial]

end FactorialExpansion

namespace LocalMoments

variable [DecidableEq σ]

/-- Exact independent geometric expectation of the local table at a common mean. -/
def localGeometricMass (derivative : Bool) (G : ℝ) (p q r : σ) : ℝ :=
  if p = q then normalGeometricMass derivative G (decide (p = r))
  else diagonalGeometricMass G

end LocalMoments
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockMonomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The product of coordinate factorials of an exponent vector. -/
def multiFactorial (d : σ →₀ ℕ) : ℕ := ∏ i, (d i).factorial

omit [DecidableEq σ] in
lemma multiFactorial_pos (d : σ →₀ ℕ) : 0 < multiFactorial d := by
  exact Finset.prod_pos (fun i _ => Nat.factorial_pos (d i))

lemma multiFactorial_add_single (d : σ →₀ ℕ) (i : σ) :
    multiFactorial (d + Finsupp.single i 1) = (d i + 1) * multiFactorial d := by
  unfold multiFactorial
  calc
    ∏ j, ((d + Finsupp.single i 1 : σ →₀ ℕ) j).factorial =
        ∏ j, (if i = j then d i + 1 else 1) * (d j).factorial := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : i = j
      · subst j
        simp [Nat.factorial_succ]
      · simp [h]
    _ = (d i + 1) * ∏ j, (d j).factorial := by
      rw [Finset.prod_mul_distrib]
      simp

/-- A factorial-normalized real monomial, the algebraic part of the
Bargmann--Fock basis used in the moment calculation. -/
def fockMonomial (d : σ →₀ ℕ) : MvPolynomial σ ℝ :=
  MvPolynomial.monomial d (Real.sqrt (multiFactorial d : ℝ))⁻¹

omit [DecidableEq σ] in
lemma sqrt_multiFactorial_pos (d : σ →₀ ℕ) :
    0 < Real.sqrt (multiFactorial d : ℝ) := by
  exact Real.sqrt_pos.2 (by exact_mod_cast multiFactorial_pos d)

lemma sqrt_multiFactorial_add_single (d : σ →₀ ℕ) (i : σ) :
    Real.sqrt (multiFactorial (d + Finsupp.single i 1) : ℝ) =
      Real.sqrt ((d i : ℝ) + 1) * Real.sqrt (multiFactorial d : ℝ) := by
  rw [multiFactorial_add_single, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity)]

lemma X_mul_fockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.X i * fockMonomial d =
      Real.sqrt ((d i : ℝ) + 1) • fockMonomial (d + Finsupp.single i 1) := by
  rw [fockMonomial, fockMonomial, MvPolynomial.X, MvPolynomial.monomial_mul,
    MvPolynomial.smul_monomial]
  rw [add_comm (Finsupp.single i 1) d]
  congr 1
  rw [one_mul, smul_eq_mul, sqrt_multiFactorial_add_single]
  have h : Real.sqrt ((d i : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

lemma pderiv_fockMonomial_add_single (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.pderiv i (fockMonomial (d + Finsupp.single i 1)) =
      Real.sqrt ((d i : ℝ) + 1) • fockMonomial d := by
  rw [fockMonomial, fockMonomial, MvPolynomial.pderiv_monomial,
    MvPolynomial.smul_monomial]
  simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.cast_add, Nat.cast_one, smul_eq_mul]
  congr 1
  rw [sqrt_multiFactorial_add_single]
  have h₁ := Real.sq_sqrt (show 0 ≤ (d i : ℝ) + 1 by positivity)
  have h₂ : Real.sqrt ((d i : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have h₃ := (sqrt_multiFactorial_pos d).ne'
  field_simp
  nlinarith

lemma pderiv_fockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.pderiv i (fockMonomial d) =
      Real.sqrt (d i : ℝ) • fockMonomial (d - Finsupp.single i 1) := by
  by_cases h : d i = 0
  · simp [fockMonomial, MvPolynomial.pderiv_monomial, h]
  · have hd := Finsupp.sub_add_single_one_cancel h
    have hc : ((d - Finsupp.single i 1 : σ →₀ ℕ) i : ℝ) + 1 = (d i : ℝ) := by
      have : (d - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = d i := by
        simpa using congrArg (fun a : σ →₀ ℕ => a i) hd
      exact_mod_cast this
    have heq := pderiv_fockMonomial_add_single (σ := σ) (d - Finsupp.single i 1) i
    rw [hd, hc] at heq
    exact heq

/-- Complex normalized monomials are obtained by coefficient extension. -/
def complexFockMonomial (d : σ →₀ ℕ) : MvPolynomial σ ℂ :=
  MvPolynomial.map (algebraMap ℝ ℂ) (fockMonomial d)

omit [DecidableEq σ] in
lemma complexFockMonomial_eq (d : σ →₀ ℕ) :
    complexFockMonomial d = MvPolynomial.monomial d
      ((Real.sqrt (multiFactorial d : ℝ))⁻¹ : ℂ) := by
  simp [complexFockMonomial, fockMonomial]

lemma X_mul_complexFockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.X i * complexFockMonomial d =
      (Real.sqrt ((d i : ℝ) + 1) : ℂ) • complexFockMonomial (d + Finsupp.single i 1) := by
  have h := congrArg (MvPolynomial.map (algebraMap ℝ ℂ)) (X_mul_fockMonomial d i)
  simpa [complexFockMonomial, fockMonomial, MvPolynomial.smul_monomial] using h

lemma pderiv_complexFockMonomial (d : σ →₀ ℕ) (i : σ) :
    MvPolynomial.pderiv i (complexFockMonomial d) =
      (Real.sqrt (d i : ℝ) : ℂ) • complexFockMonomial (d - Finsupp.single i 1) := by
  have h := congrArg (MvPolynomial.map (algebraMap ℝ ℂ)) (pderiv_fockMonomial d i)
  rw [complexFockMonomial, MvPolynomial.pderiv_map]
  simpa [complexFockMonomial, fockMonomial, MvPolynomial.smul_monomial] using h

/-- Complex version of the normalized monomial basis. -/
def complexFockBasis : Module.Basis (σ →₀ ℕ) ℂ (MvPolynomial σ ℂ) :=
  (MvPolynomial.basisMonomials σ ℂ).isUnitSMul
    (fun d => IsUnit.mk0 (((Real.sqrt (multiFactorial d : ℝ))⁻¹ : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (sqrt_multiFactorial_pos d).ne')))

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockBidegreeBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*}

/-- Exponent vectors at a fixed derivative/multiplication bidegree. -/
abbrev BidegreeIndex (isV : σ → Bool) (a b : ℕ) :=
  {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)}

section Normalized

variable [Fintype σ]

/-- The complex factorial-normalized monomial basis at fixed bidegree. -/
def bidegreeComplexFockBasis (isV : σ → Bool) (a b : ℕ) :
    Module.Basis (BidegreeIndex isV a b) ℂ (bidegreeSubmodule (K := ℂ) isV a b) :=
  (bidegreeMonomialBasis ℂ isV a b).isUnitSMul
    (fun d => IsUnit.mk0 (((Real.sqrt (multiFactorial d.1 : ℝ))⁻¹ : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero (sqrt_multiFactorial_pos d.1).ne')))

@[simp] theorem bidegreeComplexFockBasis_apply (isV : σ → Bool) (a b : ℕ)
    (d : BidegreeIndex isV a b) :
    ((bidegreeComplexFockBasis isV a b d : bidegreeSubmodule (K := ℂ) isV a b) :
      MvPolynomial σ ℂ) = complexFockMonomial d.1 := by
  simp [bidegreeComplexFockBasis, Module.Basis.isUnitSMul_apply,
    bidegreeMonomialBasis_apply, complexFockMonomial_eq, MvPolynomial.smul_monomial]

@[simp] theorem bidegreeComplexFockBasis_repr (isV : σ → Bool) (a b : ℕ)
    (p : bidegreeSubmodule (K := ℂ) isV a b) (d : BidegreeIndex isV a b) :
    (bidegreeComplexFockBasis isV a b).repr p d =
      (Real.sqrt (multiFactorial d.1 : ℝ) : ℂ) * p.1.coeff d.1 := by
  simp only [bidegreeComplexFockBasis, Module.Basis.repr_isUnitSMul, Units.smul_def,
    IsUnit.unit_spec, Units.val_inv_eq_inv_val, Complex.ofReal_inv, inv_inv,
    bidegreeMonomialBasis_repr, smul_eq_mul]

end Normalized

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Occupation update for one derivative or multiplication variable. Natural
subtraction is harmless when the derivative coefficient vanishes. -/
def stepOccupation (isV : σ → Bool) (i : σ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  if isV i then d - Finsupp.single i 1 else d + Finsupp.single i 1

/-- Occupation update for a variable path, in operator-composition order. -/
def pathOccupation (isV : σ → Bool) (l : List σ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  l.foldr (stepOccupation isV) d

/-- The nonnegative coefficient of one normalized creation/annihilation step. -/
def occupationAmplitude (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ) : ℝ :=
  Real.sqrt (if isV i then (d i : ℝ) else (d i : ℝ) + 1)

omit [Fintype σ] [DecidableEq σ] in
lemma stepOccupation_apply_of_ne (isV : σ → Bool) (d : σ →₀ ℕ)
    {i j : σ} (h : i ≠ j) : stepOccupation isV i d j = d j := by
  cases hi : isV i <;> simp [stepOccupation, hi, h]

omit [Fintype σ] [DecidableEq σ] in
lemma pathOccupation_apply_of_not_mem (isV : σ → Bool) (l : List σ)
    (d : σ →₀ ℕ) {i : σ} (h : i ∉ l) : pathOccupation isV l d i = d i := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : j ≠ i := by
      intro heq
      exact h (by simp [heq])
    have hil : i ∉ l := fun hi => h (List.mem_cons_of_mem _ hi)
    change stepOccupation isV j (pathOccupation isV l d) i = d i
    rw [stepOccupation_apply_of_ne isV _ hij, ih hil]

lemma variableOperator_complexFockMonomial (isV : σ → Bool)
    (d : σ →₀ ℕ) (i : σ) :
    variableOperator isV i (complexFockMonomial d) =
      (occupationAmplitude isV d i : ℂ) • complexFockMonomial (stepOccupation isV i d) := by
  cases h : isV i
  · simpa [occupationAmplitude, stepOccupation, h] using X_mul_complexFockMonomial d i
  · simpa [occupationAmplitude, stepOccupation, h] using pderiv_complexFockMonomial d i

/-- Exact factorial-normalized action of a product of distinct variables.
This is the sparse path-coefficient formula needed for IMM trace moments. -/
theorem mixedOperator_path_complexFockMonomial (isV : σ → Bool)
    (l : List σ) (hl : l.Nodup) (d : σ →₀ ℕ) :
    mixedOperator isV ((l.map (MvPolynomial.X : σ → MvPolynomial σ ℂ)).prod)
      (complexFockMonomial d) =
    (((l.map (occupationAmplitude isV d)).prod : ℝ) : ℂ) •
      complexFockMonomial (pathOccupation isV l d) := by
  induction l with
  | nil => simp [pathOccupation]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.prod_cons]
    rw [mixedOperator_mul_apply, ih hl, map_smul, mixedOperator_X,
      variableOperator_complexFockMonomial, smul_smul]
    have hc : occupationAmplitude isV (pathOccupation isV l d) i =
        occupationAmplitude isV d i := by
      unfold occupationAmplitude
      rw [pathOccupation_apply_of_not_mem isV l d hi]
    rw [hc]
    change _ • complexFockMonomial (pathOccupation isV (i :: l) d) = _
    congr 1
    push_cast
    ring

/-- An occupation vector viewed as a signed exponent vector. -/
def signedOccupation (d : σ →₀ ℕ) : σ →₀ ℤ :=
  d.mapRange (fun n : ℕ => (n : ℤ)) (by simp)

omit [Fintype σ] [DecidableEq σ] in
@[simp] lemma signedOccupation_apply (d : σ →₀ ℕ) (i : σ) :
    signedOccupation d i = (d i : ℤ) := rfl

/-- The signed shift of a product of variable operators. -/
def occupationShift (isV : σ → Bool) (l : List σ) : σ →₀ ℤ :=
  (l.map (fun i => Finsupp.single i (if isV i then (-1 : ℤ) else 1))).sum

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {K : Type*} [CommSemiring K]

/-- Evaluation assigning every matrix layer the identity matrix. -/
def immIdentityEvaluation (K : Type*) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n × Fin n) K →+* K :=
  MvPolynomial.eval (fun x => if x.2.1 = x.2.2 then 1 else 0)

@[simp] theorem immIdentityEvaluation_layer (n : ℕ) (t : Fin n) :
    (immIdentityEvaluation K n).mapMatrix (immLayer K n t) = 1 := by
  classical
  ext i j
  simp [immIdentityEvaluation, immLayer, Matrix.one_apply]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmOperatorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open MvPolynomial

/-- The canonical labelled paths contributing to the endpoint IMM entry. -/
def immPaths (n : ℕ) (hn : 0 < n) : List (List (Fin n × Fin n × Fin n)) :=
  matrixEntryPaths (List.finRange n) ⟨0, hn⟩ ⟨0, hn⟩

/-- Every IMM path uses exactly one coordinate in each layer, in layer order. -/
theorem immPaths_labels (n : ℕ) (hn : 0 < n)
    (p : List (Fin n × Fin n × Fin n)) (hp : p ∈ immPaths n hn) :
    p.map Prod.fst = List.finRange n :=
  matrixEntryPaths_labels _ _ _ _ hp

variable {K : Type*} [CommSemiring K]

/-- Each individual IMM path contains no repeated variable. -/
theorem immPaths_nodup (n : ℕ) (hn : 0 < n)
    (p : List (Fin n × Fin n × Fin n)) (hp : p ∈ immPaths n hn) : p.Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [immPaths_labels n hn p hp]
  exact List.nodup_finRange n

/-- Extend internal vertex choices by the two fixed endpoint vertices. -/
def immInternalPathVertices (d : ℕ) (p : Fin d → Fin (d + 1)) :
    Fin (d + 2) → Fin (d + 1) :=
  Fin.cons (α := fun _ => Fin (d + 1)) 0 (Fin.snoc p 0)

/-- The edge list associated to the tuple of internal vertices. -/
def immInternalPathEdges (d : ℕ) (p : Fin d → Fin (d + 1)) :
    List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) :=
  List.ofFn fun t : Fin (d + 1) =>
    (t, Fin.cons (α := fun _ => Fin (d + 1)) 0 p t,
      Fin.snoc (α := fun _ => Fin (d + 1)) p 0 t)

@[simp] theorem immInternalPathVertices_start (d : ℕ) (p : Fin d → Fin (d + 1)) :
    immInternalPathVertices d p 0 = 0 := by
  simp [immInternalPathVertices]

@[simp] theorem immInternalPathVertices_end (d : ℕ) (p : Fin d → Fin (d + 1)) :
    immInternalPathVertices d p (Fin.last (d + 1)) = 0 := by
  simp [immInternalPathVertices]

@[simp] theorem immInternalPathVertices_castSucc (d : ℕ)
    (p : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    immInternalPathVertices d p t.castSucc =
      Fin.cons (α := fun _ => Fin (d + 1)) 0 p t := by
  simp [immInternalPathVertices, Fin.cons_snoc_eq_snoc_cons]

@[simp] theorem immInternalPathVertices_succ (d : ℕ)
    (p : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    immInternalPathVertices d p t.succ =
      Fin.snoc (α := fun _ => Fin (d + 1)) p 0 t := by
  simp [immInternalPathVertices]

/-- The edge list has every layer as its first coordinate, exactly once. -/
theorem immInternalPathEdges_labels (d : ℕ) (p : Fin d → Fin (d + 1)) :
    (immInternalPathEdges d p).map Prod.fst = List.finRange (d + 1) := by
  rw [immInternalPathEdges, List.map_ofFn]
  exact List.ofFn_id _

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFockMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The normalized coefficient contributed by one endpoint path of IMM. -/
def immPathAmplitude (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) : ℝ :=
  (((immPaths n hn).get p).map (occupationAmplitude isV d)).prod

/-- The final occupation vector of one path operator. -/
def immPathOccupation (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) :
    (Fin n × Fin n × Fin n) →₀ ℕ :=
  pathOccupation isV ((immPaths n hn).get p) d

/-- A product of variables has the sum of their assigned weighted degrees. -/
theorem variable_list_product_isWeightedHomogeneous {K σ M : Type*}
    [CommSemiring K] [AddCommMonoid M] (w : σ → M) (l : List σ) :
    ((l.map (MvPolynomial.X : σ → MvPolynomial σ K)).prod).IsWeightedHomogeneous
      w (l.map w).sum := by
  induction l with
  | nil => simpa using MvPolynomial.isWeightedHomogeneous_one K w
  | cons x l ih =>
    simpa only [List.map_cons, List.prod_cons, List.sum_cons] using
      (MvPolynomial.isWeightedHomogeneous_X K w x).mul ih

/-- The path monomials all have the same layerwise bidegree as IMM. -/
theorem immPath_product_mem_bidegreeSubmodule (K : Type*) [CommSemiring K]
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (p : Fin (immPaths n hn).length) :
    ((((immPaths n hn).get p).map (MvPolynomial.X (R := K))).prod) ∈
      bidegreeSubmodule (fun x => side x.1)
        (Finset.univ.filter (fun t => side t = true)).card
        (Finset.univ.filter (fun t => side t = false)).card := by
  have h := variable_list_product_isWeightedHomogeneous (K := K)
    (fun x : Fin n × Fin n × Fin n => bidegreeWeight side x.1) ((immPaths n hn).get p)
  have hl := immPaths_labels n hn _ (List.get_mem _ p)
  have hs := congrArg (fun l : List (Fin n) => (l.map (bidegreeWeight side)).sum) hl
  simp only [List.map_map, Function.comp_def, ← List.ofFn_eq_map, List.sum_ofFn] at hs
  rw [hs] at h
  have he : (∑ t, bidegreeWeight side t) =
      ((Finset.univ.filter (fun t => side t = true)).card,
       (Finset.univ.filter (fun t => side t = false)).card) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases ht' : side t <;> simp [bidegreeWeight, ht']
    · simp only [Prod.snd_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases ht' : side t <;> simp [bidegreeWeight, ht']
  rw [he] at h
  exact h

/-- A nonzero scalar multiple of a normalized monomial determines its weighted degree. -/
theorem weight_eq_of_complexFockMonomial_smul_mem {σ M : Type*}
    [Fintype σ] [DecidableEq σ] [AddCommMonoid M]
    (w : σ → M) (d : σ →₀ ℕ) (a : M) (c : ℂ) (hc : c ≠ 0)
    (h : (c • complexFockMonomial d).IsWeightedHomogeneous w a) :
    Finsupp.weight w d = a := by
  apply h (d := d)
  rw [MvPolynomial.coeff_smul, complexFockMonomial_eq, MvPolynomial.coeff_monomial]
  simp only [smul_eq_mul]
  apply mul_ne_zero hc
  exact inv_ne_zero (by exact_mod_cast (sqrt_multiFactorial_pos d).ne')

/-- A nonzero path amplitude guarantees that its occupation lies in the genuine target bidegree. -/
theorem immPathOccupation_bidegree_of_amplitude_ne_zero (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ)
    (hd : Finsupp.weight (bidegreeWeight (fun x => side x.1)) d = (a, b))
    (p : Fin (immPaths n hn).length)
    (hp : immPathAmplitude n hn (fun x => side x.1) d p ≠ 0) :
    Finsupp.weight (bidegreeWeight (fun x => side x.1))
        (immPathOccupation n hn (fun x => side x.1) d p) =
      (a - (Finset.univ.filter (fun t => side t = true)).card,
       b + (Finset.univ.filter (fun t => side t = false)).card) := by
  have hinput : complexFockMonomial d ∈
      bidegreeSubmodule (fun x => side x.1) a b := by
    rw [complexFockMonomial_eq]
    exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ hd
  have hpoly := immPath_product_mem_bidegreeSubmodule ℂ n hn side p
  have hout := mixedOperator_mem_bidegreeSubmodule_all (K := ℂ)
    (σ := Fin n × Fin n × Fin n)
    (q := (((immPaths n hn).get p).map (MvPolynomial.X (R := ℂ))).prod)
    (p := complexFockMonomial d)
    (k := (Finset.univ.filter (fun t => side t = true)).card)
    (m := (Finset.univ.filter (fun t => side t = false)).card)
    (a := a) (b := b) (fun x => side x.1) hpoly hinput
  have hact := mixedOperator_path_complexFockMonomial (fun x => side x.1)
    ((immPaths n hn).get p) (immPaths_nodup n hn _ (List.get_mem _ p)) d
  rw [hact] at hout
  exact weight_eq_of_complexFockMonomial_smul_mem _ _ _ _
    (by exact_mod_cast hp) hout

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LayeredFourPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LayeredFourPath

/-- Signed occupations, retaining the layer coordinate explicitly. -/
def signedOccupation {T σ : Type*} (M : T → σ → ℕ) : T → σ → ℤ :=
  fun t x => M t x

/-- Every path chooses exactly one coordinate in every layer. -/
def signedShift {T σ : Type*} [DecidableEq σ]
    (side : T → Bool) (p : T → σ) : T → σ → ℤ :=
  fun t x => (if side t then -1 else 1) * (Finsupp.single (p t) (1 : ℤ)) x

/-- The Fock coefficient of a layered path. -/
def amplitude {T σ : Type*} [Fintype T]
    (side : T → Bool) (M : T → σ → ℕ) (p : T → σ) : ℝ :=
  ∏ t, LocalMoments.coefficient (side t) (M t (p t))

end LayeredFourPath
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathInjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι : Type*}

/-- Differentiated coordinates have sign -1, multiplied coordinates sign +1. -/
def edgeListShift (side : σ → Bool) : List (σ × ι × ι) → ((σ × ι × ι) →₀ ℤ)
  | [] => 0
  | e :: p => Finsupp.single e (if side e.1 then -1 else 1) + edgeListShift side p

@[simp] theorem edgeListShift_nil (side : σ → Bool) :
    edgeListShift (ι := ι) side [] = 0 := rfl

@[simp] theorem edgeListShift_cons (side : σ → Bool) (e : σ × ι × ι)
    (p : List (σ × ι × ι)) :
    edgeListShift side (e :: p) =
      Finsupp.single e (if side e.1 then -1 else 1) + edgeListShift side p := rfl

/-- A list containing all layer labels in order has the expected length. -/
theorem edgeList_length {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) : p.length = n := by
  simpa using congrArg List.length hp

/-- Convert an edge list ordered by layer into its finite coordinate profile. -/
def edgeProfile {n : ℕ} (p : List (Fin n × ι × ι))
    (hp : p.map Prod.fst = List.finRange n) (t : Fin n) : ι × ι :=
  (p[t.val]'(by rw [edgeList_length p hp]; exact t.isLt)).2

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockLayerProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335
namespace FockLayerProfile

variable {ι : Type*} {n : ℕ}

/-- Read a signed exponent by its layer and matrix-entry coordinates. -/
def currySigned : ((Fin n × ι × ι) →₀ ℤ) →+ (Fin n → ι × ι → ℤ) where
  toFun f t x := f (t, x)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma currySigned_signedOccupation (d : (Fin n × ι × ι) →₀ ℕ) :
    currySigned (Problem335.signedOccupation d) =
      LayeredFourPath.signedOccupation (fun t x => d (t, x)) := rfl

/-- Profile reconstruction simplifies on an explicitly layer-indexed edge list. -/
@[simp] theorem edgeProfile_ofFn (f : Fin n → ι × ι)
    (h : (List.ofFn (fun t => (t, f t))).map Prod.fst = List.finRange n) :
    edgeProfile (List.ofFn (fun t => (t, f t))) h = f := by
  funext t
  simp [edgeProfile]

/-- Reindexing an IMM path by its internal vertices also reindexes its layer profile. -/
@[simp] theorem edgeProfile_immInternalPathEdges (d : ℕ) (p : Fin d → Fin (d + 1))
    (h : (immInternalPathEdges d p).map Prod.fst = List.finRange (d + 1)) :
    edgeProfile (immInternalPathEdges d p) h =
      fun t => (Fin.cons (α := fun _ => Fin (d + 1)) 0 p t,
        Fin.snoc (α := fun _ => Fin (d + 1)) p 0 t) := by
  exact edgeProfile_ofFn _ h

/-- The canonical layer profile of a list-indexed IMM path. -/
def immProfile (n : ℕ) (hn : 0 < n) (p : Fin (immPaths n hn).length) :
    Fin n → Fin n × Fin n :=
  edgeProfile ((immPaths n hn).get p)
    (immPaths_labels n hn _ (List.get_mem _ p))

end FockLayerProfile
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathShifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The signed occupation shift of a layered path. -/
def pathShift {α : Type*} {n : ℕ} (sgn : Fin n → ℤ)
    (p : Fin (n + 1) → α) : (Fin n × α × α) →₀ ℤ :=
  ∑ t, Finsupp.single (t, p t.castSucc, p t.succ) (sgn t)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmPathCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

/-- The coordinate in one layer of a genuine endpoint-fixed internal path. -/
def immInternalCoordinate (d : ℕ) (p : Fin d → Fin (d + 1))
    (t : Fin (d + 1)) : Fin (d + 1) × Fin (d + 1) :=
  (immInternalPathVertices d p t.castSucc, immInternalPathVertices d p t.succ)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RelaxedPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335.Pairings

/-- The fixed labels at either external vertex. -/
def constantLabels {α : Type*} (a : α) : Labels α := ⟨a, a, a, a⟩

@[simp]
theorem respects_constantLabels {α : Type*} (τ : Kind) (a : α) :
    Respects τ (constantLabels a) := by
  cases τ <;> simp [Respects, constantLabels]

/-- Coordinates of the four paths in one layer are pairs of adjacent vertex labels. -/
def zipLabels {α β : Type*} (x : Labels α) (y : Labels β) : Labels (α × β) :=
  ⟨(x.p, y.p), (x.q, y.q), (x.r, y.r), (x.s, y.s)⟩

@[simp]
theorem respects_zipLabels {α β : Type*} (τ : Kind) (x : Labels α) (y : Labels β) :
    Respects τ (zipLabels x y) ↔ Respects τ x ∧ Respects τ y := by
  cases τ <;> simp only [Respects, zipLabels, Prod.mk.injEq] <;> tauto

/-- Add the two fixed external vertices to four paths specified by their internal labels. -/
def closePaths {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α) :
    Fin (L + 2) → Labels α :=
  Fin.cases (constantLabels a) (Fin.lastCases (constantLabels a) x)

@[simp]
theorem closePaths_zero {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α) :
    closePaths a x 0 = constantLabels a := rfl

@[simp]
theorem closePaths_last {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α) :
    closePaths a x (Fin.last (L + 1)) = constantLabels a := by
  simp [closePaths, ← Fin.succ_last]

@[simp]
theorem closePaths_internal {α : Type*} {L : ℕ} (a : α)
    (x : Fin L → Labels α) (i : Fin L) :
    closePaths a x i.castSucc.succ = x i := by
  simp [closePaths]

/-- Layer constraints are exactly the independent constraints at internal vertices. -/
theorem closePaths_compatible_iff {α : Type*} {L : ℕ}
    (a : α) (τ : Fin (L + 1) → Kind) (x : Fin L → Labels α) :
    (∀ t : Fin (L + 1), Respects (τ t)
      (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ))) ↔
    ∀ i : Fin L, Respects (τ i.castSucc) (x i) ∧ Respects (τ i.succ) (x i) := by
  simp only [respects_zipLabels]
  constructor
  · intro h i
    constructor
    · simpa using (h i.castSucc).2
    · simpa only [Fin.castSucc_succ, closePaths_internal] using (h i.succ).1
  · intro h t
    constructor
    · refine Fin.cases ?_ (fun i => ?_) t
      · simp
      · simpa only [Fin.castSucc_succ, closePaths_internal] using (h i).2
    · refine Fin.lastCases ?_ (fun i => ?_) t
      · simp
      · simpa using (h i).1

/-- Four endpoint-fixed paths respecting a prescribed relaxed pairing in every layer. -/
abbrev RelaxedPaths (α : Type*) {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind) :=
  {x : Fin L → Labels α // ∀ t : Fin (L + 1), Respects (τ t)
    (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ))}

/-- The explicit product decomposition used in the second trace count. -/
def relaxedPathsEquivAssignments (α : Type*) {L : ℕ}
    (a : α) (τ : Fin (L + 1) → Kind) :
    RelaxedPaths α a τ ≃ Assignments α τ where
  toFun x i := ⟨x.1 i, (closePaths_compatible_iff a τ x.1).mp x.2 i⟩
  invFun x := ⟨fun i => (x i).1,
    (closePaths_compatible_iff a τ _).mpr (fun i => (x i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Problem335.Pairings

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PairingPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335.Pairings

open scoped BigOperators

instance instDecidableExactRespectsOfDecidableEq {α : Type*} [DecidableEq α] (τ : Kind) (x : Labels α) :
    Decidable (ExactRespects τ x) := by
  cases τ <;> unfold ExactRespects <;> infer_instance

/-- Assign the all-equal case to normal pairing, as required for disjoint classes. -/
def classify {α : Type*} [DecidableEq α] (x : Labels α) : Kind :=
  if x.p = x.q then .normal else .diagonal

theorem exactRespects_classify_iff {α : Type*} [DecidableEq α] (x : Labels α) :
    ExactRespects (classify x) x ↔
      Finsupp.single x.p (1 : ℤ) - Finsupp.single x.q 1 =
        Finsupp.single x.r 1 - Finsupp.single x.s 1 := by
  rw [coordinate_difference_eq_iff_exclusive]
  by_cases h : x.p = x.q <;> simp [classify, ExactRespects, h]

theorem classify_eq_of_exact {α : Type*} [DecidableEq α] {τ : Kind} {x : Labels α}
    (h : ExactRespects τ x) : classify x = τ := by
  cases τ
  · simp [classify, h.1]
  · simp [classify, h.2.2]

/-- The four layer coordinates of endpoint-fixed paths. -/
def layerLabels {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α)
    (t : Fin (L + 1)) : Labels (α × α) :=
  zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ)

abbrev ExactPaths (α : Type*) {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind) :=
  {x : Fin L → Labels α // ∀ t, ExactRespects (τ t) (layerLabels a x t)}

abbrev CompatiblePaths (α : Type*) {L : ℕ} (a : α) :=
  {x : Fin L → Labels α // ∀ t : Fin (L + 1),
    Finsupp.single (layerLabels a x t).p (1 : ℤ) -
      Finsupp.single (layerLabels a x t).q 1 =
    Finsupp.single (layerLabels a x t).r 1 -
      Finsupp.single (layerLabels a x t).s 1}

/-- The compatible quadruples partition uniquely according to their exact pairing word. -/
def compatiblePathsEquivSigma (α : Type*) [DecidableEq α] {L : ℕ} (a : α) :
    CompatiblePaths α (L := L) a ≃
      Σ τ : Fin (L + 1) → Kind, ExactPaths α a τ where
  toFun x := ⟨fun t => classify (layerLabels a x.1 t),
    ⟨x.1, fun t => (exactRespects_classify_iff _).mpr (x.2 t)⟩⟩
  invFun x := ⟨x.2.1, fun t =>
    (coordinate_difference_eq_iff_existsUnique _).mpr
      ⟨x.1 t, x.2.2 t, fun _ hk => exactRespects_unique hk (x.2.2 t)⟩⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨τ, x⟩
    have hτ : (fun t => classify (layerLabels a x.1 t)) = τ :=
      funext (fun t => classify_eq_of_exact (x.2 t))
    apply Sigma.ext hτ
    have hp : ∀ y : Fin L → Labels α,
        (∀ t, ExactRespects (classify (layerLabels a x.1 t)) (layerLabels a y t)) ↔
          ∀ t, ExactRespects (τ t) (layerLabels a y t) := by
      intro y
      simp only [fun t => classify_eq_of_exact (x.2 t)]
    exact (Subtype.heq_iff_coe_eq hp).mpr rfl

end Problem335.Pairings

end OAI
end

section
-- module Solutions.OAIQW_Problem335.SecondMomentPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact four-path pairing classes are disjoint.  Dropping the diagonal
inequalities enlarges each class, and therefore increases every nonnegative
weighted second-moment sum. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

/-- The four edge coordinates in a layer of endpoint-fixed paths. -/
def layerLabels {γ : Type*} {L : ℕ} (endpoint : γ)
    (x : Fin L → Labels γ) (t : Fin (L + 1)) : Labels (γ × γ) :=
  zipLabels (closePaths endpoint x t.castSucc) (closePaths endpoint x t.succ)

/-- Compatibility of the four signed shifts, expressed independently in each layer. -/
def Compatible {γ : Type*} {L : ℕ} (endpoint : γ) (x : Fin L → Labels γ) : Prop :=
  ∀ t : Fin (L + 1),
    Finsupp.single (layerLabels endpoint x t).p (1 : ℤ) -
        Finsupp.single (layerLabels endpoint x t).q 1 =
      Finsupp.single (layerLabels endpoint x t).r 1 -
        Finsupp.single (layerLabels endpoint x t).s 1

instance compatibleDecidable {γ : Type*} [DecidableEq γ] {L : ℕ}
    (endpoint : γ) (x : Fin L → Labels γ) : Decidable (Compatible endpoint x) := by
  unfold Compatible
  infer_instance

/-- Assign the zero difference to the normal class; all other compatible
coordinate differences belong to the diagonal class. -/
def classifyLayer {γ : Type*} (x : Labels γ) : Kind := by
  classical
  exact if x.p = x.q then .normal else .diagonal

/-- The unique exact pairing word of a compatible quadruple. -/
def classifyWord {γ : Type*} {L : ℕ} (endpoint : γ)
    (x : Fin L → Labels γ) : Fin (L + 1) → Kind :=
  fun t => classifyLayer (layerLabels endpoint x t)

/-- Normal pairings retain their coordinate-coincidence factor.  Diagonal
pairings retain the assigned constant even after their inequality is dropped. -/
def layerWeight {γ : Type*} (c : ℝ) (τ : Kind) (x : Labels γ) : ℝ := by
  classical
  exact match τ with
    | .normal => 1 + c * (if x.p = x.r then 1 else 0)
    | .diagonal => c

/-- Product of the manuscript's normalized local geometric weights. -/
def pathWeight {γ : Type*} {L : ℕ} (isV : Fin (L + 1) → Bool)
    (α β : ℝ) (endpoint : γ) (τ : Fin (L + 1) → Kind)
    (x : Fin L → Labels γ) : ℝ :=
  ∏ t, layerWeight (if isV t then α⁻¹ else β) (τ t) (layerLabels endpoint x t)

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixPathVertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

variable {σ ι : Type*}

/-- Record the edges of a path from its internal vertices and fixed endpoints. -/
def internalPathEdges {d : ℕ} (labels : Fin (d + 1) → σ) (i j : ι)
    (p : Fin d → ι) : List (σ × ι × ι) :=
  List.ofFn fun t : Fin (d + 1) =>
    (labels t, Fin.cons (α := fun _ => ι) i p t, Fin.snoc (α := fun _ => ι) p j t)

theorem internalPathEdges_mem [Fintype ι] [DecidableEq ι]
    (d : ℕ) (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    internalPathEdges labels i j p ∈ matrixEntryPaths (List.ofFn labels) i j := by
  induction d generalizing i with
  | zero => simp [internalPathEdges, List.ofFn_succ, matrixEntryPaths, Fin.snoc_zero]
  | succ d ih =>
      rw [← Fin.cons_self_tail p]
      unfold internalPathEdges
      rw [List.ofFn_succ, List.ofFn_succ]
      conv_rhs => rw [List.ofFn_succ]
      rw [matrixEntryPaths]
      apply List.mem_flatMap.mpr
      refine ⟨p 0, by simp, ?_⟩
      apply List.mem_map.mpr
      refine ⟨internalPathEdges (Fin.tail labels) (p 0) j (Fin.tail p), ?_, ?_⟩
      · simpa only [List.ofFn_succ, Fin.tail] using
          ih (Fin.tail labels) (p 0) (Fin.tail p)
      · simp only [internalPathEdges, ← Fin.cons_snoc_eq_snoc_cons,
          Fin.cons_zero, Fin.cons_succ, Fin.tail]

theorem internalPathEdges_injective {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) :
    Function.Injective (internalPathEdges labels i j) := by
  intro p q h
  have hf := List.ofFn_injective h
  funext t
  have ht := congrArg (fun f => (f t.castSucc).2.2) hf
  simpa only [Fin.snoc_castSucc] using ht

/-- Locate the explicitly described path in the exact list enumeration. -/
def internalPathIndex [Fintype ι] [DecidableEq ι] {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    Fin (matrixEntryPaths (List.ofFn labels) i j).length :=
  Classical.choose (List.mem_iff_get.mp (internalPathEdges_mem d labels i j p))

@[simp] theorem get_internalPathIndex [Fintype ι] [DecidableEq ι] {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    (matrixEntryPaths (List.ofFn labels) i j).get (internalPathIndex labels i j p) =
      internalPathEdges labels i j p :=
  Classical.choose_spec (List.mem_iff_get.mp (internalPathEdges_mem d labels i j p))

theorem internalPathIndex_injective [Fintype ι] [DecidableEq ι] {d : ℕ}
    (labels : Fin (d + 1) → σ) (i j : ι) :
    Function.Injective (internalPathIndex labels i j) := by
  intro p q h
  apply internalPathEdges_injective labels i j
  rw [← get_internalPathIndex labels i j p, ← get_internalPathIndex labels i j q, h]

/-- The canonical matrix-path list and the tuple of internal vertices enumerate
exactly the same paths. The edge list is preserved, not merely its cardinality. -/
def internalPathEquiv [Fintype ι] [DecidableEq ι] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) :
    (Fin d → ι) ≃ Fin (matrixEntryPaths (List.ofFn labels) i j).length :=
  Equiv.ofBijective (internalPathIndex labels i j)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨internalPathIndex_injective labels i j, by
      simp only [Fintype.card_fun, Fintype.card_fin]
      rw [matrixEntryPaths_length _ (by simp) i j]
      simp⟩)

@[simp] theorem get_internalPathEquiv [Fintype ι] [DecidableEq ι] (d : ℕ)
    (labels : Fin (d + 1) → σ) (i j : ι) (p : Fin d → ι) :
    (matrixEntryPaths (List.ofFn labels) i j).get (internalPathEquiv d labels i j p) =
      internalPathEdges labels i j p := get_internalPathIndex labels i j p

open scoped BigOperators

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixPathPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings

variable {α β σ : Type*}

/-- Apply a representation equivalence independently to the four paths. -/
def matrixPathLabelsEquiv (e : α ≃ β) : Labels α ≃ Labels β where
  toFun x := ⟨e x.p, e x.q, e x.r, e x.s⟩
  invFun x := ⟨e.symm x.p, e.symm x.q, e.symm x.r, e.symm x.s⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp

/-- Transpose four vertex functions into four labels at each vertex. -/
def matrixPathFunctionEquiv (d : ℕ) : Labels (Fin d → α) ≃ (Fin d → Labels α) where
  toFun x t := ⟨x.p t, x.q t, x.r t, x.s t⟩
  invFun x := ⟨fun t => (x t).p, fun t => (x t).q, fun t => (x t).r, fun t => (x t).s⟩
  left_inv x := by cases x; rfl
  right_inv x := by funext t; apply Labels.ext <;> rfl

/-- Quadruples of exact enumerated matrix paths have the internal-label representation
used by `RelaxedPaths` and `CompatiblePaths`. -/
def quadruplePathIndexEquiv [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) :
    (Fin d → Labels α) ≃ Labels (Fin (matrixEntryPaths (List.ofFn labels) a a).length) :=
  (matrixPathFunctionEquiv d).symm.trans
    (matrixPathLabelsEquiv (internalPathEquiv d labels a a))

@[simp] theorem quadruplePathIndexEquiv_get_p [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).p =
      internalPathEdges labels a a (fun t => (x t).p) :=
  get_internalPathEquiv d labels a a _

@[simp] theorem quadruplePathIndexEquiv_get_q [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).q =
      internalPathEdges labels a a (fun t => (x t).q) :=
  get_internalPathEquiv d labels a a _

@[simp] theorem quadruplePathIndexEquiv_get_r [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).r =
      internalPathEdges labels a a (fun t => (x t).r) :=
  get_internalPathEquiv d labels a a _

@[simp] theorem quadruplePathIndexEquiv_get_s [Fintype α] [DecidableEq α] (d : ℕ)
    (labels : Fin (d + 1) → σ) (a : α) (x : Fin d → Labels α) :
    (matrixEntryPaths (List.ofFn labels) a a).get (quadruplePathIndexEquiv d labels a x).s =
      internalPathEdges labels a a (fun t => (x t).s) :=
  get_internalPathEquiv d labels a a _

/-- The four-field record is a nested Cartesian product. -/
def matrixPathLabelsProdEquiv : Labels α ≃ α × α × α × α where
  toFun x := (x.p, x.q, x.r, x.s)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨p,q,r,s⟩; rfl

end Problem335.Pairings

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmProfileCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335

/-- The list-based layer profile of an actual internal IMM path is its vertex coordinate. -/
@[simp] theorem edgeProfile_immInternalPathEdges (d : ℕ)
    (p : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    edgeProfile (immInternalPathEdges d p) (immInternalPathEdges_labels d p) t =
      immInternalCoordinate d p t := by
  simp only [edgeProfile, immInternalPathEdges, List.getElem_ofFn,
    immInternalCoordinate, immInternalPathVertices_castSucc, immInternalPathVertices_succ]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.TraceExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix expansions for the two trace moments in the IMM argument.
These identities contain no analytic or asymptotic assumptions. -/

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P R : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- A matrix whose column is a weighted sum of path shifts. -/
def pathShiftMatrix [AddCommMonoid R] (shift : I → P → J) (weight : I → P → R) :
    Matrix J I R := by
  classical
  exact fun j i => ∑ p, if shift i p = j then weight i p else 0

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFiniteMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The number of derivative layers in a layerwise partition. -/
def immLayerVCount {n : ℕ} (side : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun t => side t = true)).card

/-- The number of multiplication layers in a layerwise partition. -/
def immLayerUCount {n : ℕ} (side : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun t => side t = false)).card

/-- Source exponent vectors for the finite IMM operator. -/
abbrev ImmSourceIndex (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :=
  BidegreeIndex (fun x : Fin n × Fin n × Fin n => side x.1) a b

/-- Target exponent vectors for the finite IMM operator. -/
abbrev ImmTargetIndex (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :=
  BidegreeIndex (fun x : Fin n × Fin n × Fin n => side x.1)
    (a - immLayerVCount side) (b + immLayerUCount side)

/-- The actual finite IMM map written in factorial-normalized source and target bases. -/
def immNormalizedMatrix (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :
    Matrix (ImmTargetIndex n side a b) (ImmSourceIndex n side a b) ℂ :=
  LinearMap.toMatrix
    (bidegreeComplexFockBasis (σ := Fin n × Fin n × Fin n) (fun x => side x.1) a b)
    (bidegreeComplexFockBasis (σ := Fin n × Fin n × Fin n) (fun x => side x.1)
      (a - immLayerVCount side) (b + immLayerUCount side))
    (finiteMixedOperator (K := ℂ) (σ := Fin n × Fin n × Fin n) (fun x => side x.1) a b
      (immLayerVCount side) (immLayerUCount side) (imm ℂ n))

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmSecondTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second trace identity for the actual IMM operator in normalized
monomial coordinates.  Invalid path actions have zero amplitude, so their
chosen finite target index does not enter the trace. -/

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The signed exponent displacement of an actual IMM path. -/
def immPathSignedShift (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (p : Fin (immPaths n hn).length) : (Fin n × Fin n × Fin n) →₀ ℤ :=
  occupationShift isV ((immPaths n hn).get p)

/-- A finite submatrix of the genuine normalized IMM operator. -/
def immCoefficientMatrix {I J : Type*} (n : ℕ)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (source : I → (Fin n × Fin n × Fin n) →₀ ℕ)
    (target : J → (Fin n × Fin n × Fin n) →₀ ℕ) : Matrix J I ℂ :=
  fun j i => complexFockBasis.repr
    (mixedOperator isV (imm ℂ n) (complexFockMonomial (source i))) (target j)

/-- A finite target index for each path.  The fallback is used only for a
zero-amplitude path, and is therefore invisible in the operator matrix. -/
def immFinitePathShift (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ)
    (e0 : ImmTargetIndex n side a b) (d : ImmSourceIndex n side a b)
    (p : Fin (immPaths n hn).length) : ImmTargetIndex n side a b := by
  classical
  exact if h : immPathAmplitude n hn (fun x => side x.1) d.1 p ≠ 0 then
    ⟨immPathOccupation n hn (fun x => side x.1) d.1 p,
      immPathOccupation_bidegree_of_amplitude_ne_zero n hn side a b d.1 d.2 p h⟩
    else e0

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmCompatibleTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

def totalImmProfile (n : ℕ)
    (P : List (Fin n × Fin n × Fin n)) : Fin n → Fin n × Fin n :=
  if h : P.map Prod.fst = List.finRange n then edgeProfile P h else fun t => (t, t)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFirstTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

/-- The real, nonnegative matrix underlying the actual normalized IMM map. -/
def immRealNormalizedMatrix (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    Matrix (ImmTargetIndex n side a b) (ImmSourceIndex n side a b) ℝ := by
  classical
  exact fun e d => ∑ p : Fin (immPaths n hn).length,
    if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
    then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IndependentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace IndependentCoordinates

/-- The uniform average on a finite type, with value zero on an empty type. -/
def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α


/-- The indicator that two labels agree. -/
def pairEq {α : Type*} [DecidableEq α] (x : α × α) : ℝ :=
  if x.1 = x.2 then 1 else 0

/-- Dependent-coordinate version of restriction to an embedded coordinate set. -/
def restrictDependentAssignmentEquiv {σ τ : Type*} (β : σ → Type*)
    (j : τ → σ) (hj : Function.Injective j) :
    (∀ s, β s) ≃ (∀ t, β (j t)) × (∀ s : {s // s ∉ Set.range j}, β s) := by
  classical
  let e : τ ⊕ {s // s ∉ Set.range j} ≃ σ :=
    ((Equiv.ofInjective j hj).sumCongr (Equiv.refl _)).trans
      (Equiv.sumCompl (fun s => s ∈ Set.range j))
  exact (Equiv.piCongrLeft β e).symm.trans
    (Equiv.sumPiEquivProdPi (fun z => β (e z)))

@[simp] theorem restrictDependentAssignmentEquiv_fst {σ τ : Type*}
    (β : σ → Type*) (j : τ → σ) (hj : Function.Injective j)
    (x : ∀ s, β s) (t : τ) :
    (restrictDependentAssignmentEquiv β j hj x).1 t = x (j t) := rfl

end IndependentCoordinates
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IsolatedFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical removal of isolated positions in an independent set.

The value `true` denotes the D type from the manuscript.  The set `S`
contains the positions allowed to flip (interior V layers), and `R a b`
means that `b` is a neighbor of `a`.  Independence is the only property
of the path graph needed for the fiber calculation.
-/

noncomputable section

open scoped BigOperators

namespace Problem335.IsolatedFlip

variable {α : Type*} [Fintype α] [DecidableEq α]

def eligible (S : Finset α) (R : α → α → Prop) (w : α → Bool) : Finset α := by
  classical
  exact S.filter (fun a => ∀ b, R a b → w b = true)

def flip (S : Finset α) (R : α → α → Prop) (w : α → Bool) (a : α) : Bool := by
  classical
  exact if a ∈ eligible S R w then true else w a

def unset (w : α → Bool) (T : Finset α) (a : α) : Bool :=
  if a ∈ T then false else w a

def removed (S : Finset α) (R : α → α → Prop) (w : α → Bool) : Finset α := by
  classical
  exact (eligible S R w).filter (fun a => w a = false)

@[simp] theorem mem_eligible {α : Type u_1} [Fintype α] [DecidableEq α]
    {S : Finset α} {R : α → α → Prop}
    {w : α → Bool} {a : α} :
    a ∈ eligible S R w ↔ a ∈ S ∧ ∀ b, R a b → w b = true := by
  classical
  simp [eligible]

theorem eligible_subset (S : Finset α) (R : α → α → Prop) (w : α → Bool) :
    eligible S R w ⊆ S := by
  intro a ha
  exact (mem_eligible.mp ha).1

theorem flip_eq_of_not_mem {S : Finset α} {R : α → α → Prop}
    {w : α → Bool} {a : α} (ha : a ∉ S) : flip S R w a = w a := by
  classical
  have h : a ∉ eligible S R w := fun h => ha (eligible_subset S R w h)
  simp [flip, h]

theorem eligible_congr {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {w z : α → Bool} (h : ∀ a, a ∉ S → w a = z a) :
    eligible S R w = eligible S R z := by
  ext a
  simp only [mem_eligible]
  constructor
  · rintro ⟨ha, hw⟩
    refine ⟨ha, ?_⟩
    intro b hab
    rw [← h b (hS a ha b hab)]
    exact hw b hab
  · rintro ⟨ha, hz⟩
    refine ⟨ha, ?_⟩
    intro b hab
    rw [h b (hS a ha b hab)]
    exact hz b hab

theorem eligible_flip {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S) (w : α → Bool) :
    eligible S R (flip S R w) = eligible S R w := by
  apply eligible_congr hS
  intro a ha
  exact flip_eq_of_not_mem ha

theorem eligible_unset {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) {T : Finset α} (hT : T ⊆ S) :
    eligible S R (unset w T) = eligible S R w := by
  apply eligible_congr hS
  intro a ha
  have hn : a ∉ T := fun ht => ha (hT ht)
  simp [unset, hn]

theorem flip_unset {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {w : α → Bool} (hw : flip S R w = w)
    {T : Finset α} (hT : T ⊆ eligible S R w) :
    flip S R (unset w T) = w := by
  classical
  have he := eligible_unset hS w (hT.trans (eligible_subset S R w))
  funext a
  have hw' := congrFun hw a
  simp only [flip, he] at hw' ⊢
  by_cases ha : a ∈ eligible S R w
  · simpa [ha] using hw'
  · have hn : a ∉ T := fun ht => ha (hT ht)
    simp [ha, unset, hn]

theorem removed_subset {α : Type u_1} [Fintype α] [DecidableEq α]
    (S : Finset α) (R : α → α → Prop) (w : α → Bool) :
    removed S R w ⊆ eligible S R w := by
  classical
  exact Finset.filter_subset _ _

theorem unset_flip_removed (S : Finset α) (R : α → α → Prop)
    (w : α → Bool) : unset (flip S R w) (removed S R w) = w := by
  classical
  funext a
  by_cases ha : a ∈ eligible S R w
  · cases hw : w a <;> simp [unset, removed, flip, ha, hw]
  · simp [unset, removed, flip, ha]

theorem removed_unset {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    {w : α → Bool} (hw : flip S R w = w)
    {T : Finset α} (hT : T ⊆ eligible S R w) :
    removed S R (unset w T) = T := by
  classical
  have he := eligible_unset hS w (hT.trans (eligible_subset S R w))
  ext a
  simp only [removed, Finset.mem_filter, he]
  constructor
  · rintro ⟨ha, hz⟩
    by_contra hn
    have hw' := congrFun hw a
    simp [flip, ha] at hw'
    simp [unset, hn, hw'] at hz
  · intro ha
    exact ⟨hT ha, by simp [unset, ha]⟩

/-! Each fiber of the canonicalization is exactly a powerset. -/

def fiberEquiv {S : Finset α} {R : α → α → Prop}
    (hS : ∀ a ∈ S, ∀ b, R a b → b ∉ S)
    (w : α → Bool) (hw : flip S R w = w) :
    {z : α → Bool // flip S R z = w} ≃
      {T : Finset α // T ⊆ eligible S R w} where
  toFun z := ⟨removed S R z, by
    have he : eligible S R z = eligible S R w := by
      exact (eligible_flip hS z).symm.trans (congrArg (eligible S R) z.property)
    rw [← he]
    exact removed_subset S R z⟩
  invFun T := ⟨unset w T, flip_unset hS hw T.property⟩
  left_inv z := by
    apply Subtype.ext
    change unset w (removed S R z) = z
    exact (congrArg (fun q => unset q (removed S R z)) z.property.symm).trans
      (unset_flip_removed S R z)
  right_inv T := by
    apply Subtype.ext
    exact removed_unset hS hw T.property

end Problem335.IsolatedFlip

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.SwitchRestoration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335.SwitchRestoration

variable {ι : Type*} [DecidableEq ι]

/-- Switches in a Boolean labeling along a finite collection of oriented edges. -/
def switchCount (edges : Finset (ι × ι)) (w : ι → Bool) : ℕ :=
  ∑ e ∈ edges, if w e.1 ≠ w e.2 then 1 else 0

/-- The number of edge endpoints at a vertex, counting both ends of a loop. -/
def endpointDegree (edges : Finset (ι × ι)) (i : ι) : ℕ :=
  ∑ e ∈ edges, ((if e.1 = i then 1 else 0) + (if e.2 = i then 1 else 0))


/-- Edges of the path with `n+1` vertices. -/
def pathEdges (n : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.image fun i : Fin n => (i.castSucc, i.succ)

end Problem335.SwitchRestoration

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IsolatedWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.IsolatedWeight

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Internal neighboring positions of the same normal (false) type. -/
def falseNeighbors (R : ι → ι → Prop) (w : ι → Bool) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => R i j ∧ w j = false)

/-- The coincidence correction factors at the normal V positions. -/
def correction (V : Finset ι) (R : ι → ι → Prop) (A x : ℝ)
    (w : ι → Bool) : ℝ := by
  classical
  exact ∏ i ∈ V.filter (fun i => w i = false),
    (1 + A * x ^ (falseNeighbors R w i).card)

/-- The actual weighted word summand, with `A = alpha⁻¹`, `B = beta`,
and `x = n⁻¹`. The relation records internal adjacency. -/
def weight (edges : Finset (ι × ι)) (V : Finset ι) (R : ι → ι → Prop)
    (A B x : ℝ) (w : ι → Bool) : ℝ := by
  classical
  exact x ^ SwitchRestoration.switchCount edges w *
    A ^ (V.filter fun i => w i = true).card *
    B ^ ((Finset.univ \ V).filter fun i => w i = true).card *
    correction V R A x w

end Problem335.IsolatedWeight

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalMomentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the local geometric occupation moments in the four-path
trace expansion. Missing derivative occupations are handled by local-polynomial
identities, preserving the repeated-coordinate second moment rather than
treating it as a product of independent moments. -/

noncomputable section
open scoped BigOperators

namespace Problem335.LocalMomentWeights

/-- `isD` denotes the nonzero-difference pairing. `same` is relevant only in
its complementary pairing, where the two selected coordinates may coincide. -/
def moment (isV isD same : Bool) (A B : ℝ) : ℝ :=
  if isV then
    if isD then A * (A + 1) else if same then 2 * A ^ 2 + A else A ^ 2
  else
    if isD then B * (B + 1) else if same then 2 * B ^ 2 + 3 * B + 1
      else (B + 1) ^ 2

/-- The square of the first-moment factor at a layer. -/
def scale (isV : Bool) (A B : ℝ) : ℝ :=
  if isV then A ^ 2 else (B + 1) ^ 2

/-- The exact local weights after division by the first-moment square. -/
def weight (isV isD same : Bool) (alpha beta : ℝ) : ℝ :=
  if isV then
    if isD then alpha⁻¹ else 1 + if same then alpha⁻¹ else 0
  else
    if isD then beta else 1 + if same then beta else 0

end Problem335.LocalMomentWeights

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- A finite expansion in the multivariate falling-factorial basis. -/
def factorialExpansionValue {ι J : Type*} [Fintype ι]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (M : ι →₀ ℕ) : ℝ :=
  ∑ j ∈ s, c j * ∏ i, ((M i).descFactorial (d j i) : ℝ)

/-- Average over the finite uniform weak-composition space. -/
def compositionExpansionMean {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (t : ℕ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      factorialExpansionValue s c d M) /
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card

/-- Uniform averages in two independent weak-composition groups, with a shared term index. -/
def twoGroupCompositionExpansionMean {ι κ J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (s : Finset J) (c : J → ℝ)
    (d : J → ι → ℕ) (e : J → κ → ℕ) (a b : ℕ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a,
    compositionExpansionMean s
      (fun j => c j * ∏ i, ((M i).descFactorial (d j i) : ℝ)) e b) /
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card

/-- The product-geometric expression for a two-group factorial expansion. -/
def twoGroupGeometricExpansionValue {ι κ J : Type*} [Fintype ι] [Fintype κ]
    (s : Finset J) (c : J → ℝ) (d : J → ι → ℕ) (e : J → κ → ℕ)
    (A B : ℝ) : ℝ :=
  ∑ j ∈ s, (c j * (∏ i, (d j i).factorial : ℝ) * (∏ i, (e j i).factorial : ℝ)) *
    (A ^ (∑ i, d j i) * B ^ (∑ i, e j i))

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalOccupationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*} [Fintype σ]

/-- Reassemble two occupation vectors on the complementary variable classes. -/
def joinOccupation (side : σ → Bool)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ) : σ → ℕ :=
  fun i => if h : side i = true then M ⟨i, h⟩ else N ⟨i, h⟩

omit [Fintype σ] in
@[simp] theorem joinOccupation_true (side : σ → Bool)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ)
    (i : {i // side i = true}) : joinOccupation side M N i = M i := by
  simp [joinOccupation, i.property]

omit [Fintype σ] in
@[simp] theorem joinOccupation_false (side : σ → Bool)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ)
    (i : {i // ¬ side i = true}) : joinOccupation side M N i = N i := by
  simp [joinOccupation, i.property]

variable [DecidableEq σ]

/-- The actual finite uniform average, not an assumed moment functional. -/
def partitionCompositionMean (side : σ → Bool) (f : (σ → ℕ) → ℝ) (a b : ℕ) : ℝ := by
  classical
  exact (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a,
    (∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b,
      f (joinOccupation side M N)) /
      (Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b).card) /
    (Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a).card

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LocalProductAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ]

/-- Coordinate-form conversion to the local table used in the four-path identity. -/
@[simp] theorem localPolynomial_layered {κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (d : Bool) (M : ι × κ → ℕ) (t : ι) (p q r : κ) :
    localPolynomial d M (t, p) (t, q) (t, r) =
      localPolynomial d (fun x => M (t, x)) p q r := by
  simp [localPolynomial]

@[simp] theorem localGeometricMass_layered {κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (d : Bool) (G : ℝ) (t : ι) (p q r : κ) :
    localGeometricMass d G (t, p) (t, q) (t, r) = localGeometricMass d G p q r := by
  simp [localGeometricMass]

end LocalMoments
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.SecondMomentNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete normalization and reindexing of the geometric upper bound for
four-path occupation moments. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing

open Pairings

/-- The diagonal flag used by the local geometric moment table. -/
def isDiagonal : Kind → Bool
  | .normal => false
  | .diagonal => true

/-- Coordinate coincidence in the normal pairing. -/
def coincides {γ : Type*} (x : Labels γ) : Bool := by
  classical
  exact decide (x.p = x.r)

/-- The first-moment normalization for a fixed V/U layer partition. -/
def pathMean {L : ℕ} (isV : Fin (L + 1) → Bool) (A B : ℝ) : ℝ :=
  A ^ (Finset.univ.filter (fun t => isV t = true)).card *
    (B + 1) ^ (Finset.univ.filter (fun t => isV t = false)).card

/-- The product of independent geometric local moments for a fixed pairing. -/
def pathGeometricMoment {γ : Type*} {L : ℕ} (isV : Fin (L + 1) → Bool)
    (A B : ℝ) (endpoint : γ) (τ : Fin (L + 1) → Kind)
    (x : Fin L → Labels γ) : ℝ :=
  ∏ t, LocalMomentWeights.moment (isV t) (isDiagonal (τ t))
    (coincides (layerLabels endpoint x t)) A B

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PairingOccupationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite occupation averages feed the normalized pairing sum. -/

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing
open Pairings

def layerMeanV (γ : Type*) [Fintype γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) (a : ℕ) : ℝ :=
  (a : ℝ) / Fintype.card {v : Fin (L + 1) × (γ × γ) // side v.1 = true}

def layerMeanU (γ : Type*) [Fintype γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) (b : ℕ) : ℝ :=
  (b : ℝ) / Fintype.card {v : Fin (L + 1) × (γ × γ) // ¬ side v.1 = true}

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PairingWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings
open IndependentCoordinates

instance vertexNonempty (α : Type*) [Nonempty α] (τ σ : Kind) :
    Nonempty (Vertex α τ σ) := by
  obtain ⟨a⟩ := ‹Nonempty α›
  refine ⟨⟨⟨a,a,a,a⟩, ?_⟩⟩
  cases τ <;> cases σ <;> simp [Respects]

/-- Agreement between the two labels of a normal pairing at a vertex. -/
def vertexPairEq {α : Type*} [DecidableEq α] {τ σ : Kind}
    (x : Vertex α τ σ) : ℝ := if x.1.p = x.1.r then 1 else 0

/-- Number of endpoints at which both adjacent pairing types are normal. -/
def normalEndpointCount {L : ℕ} (τ : Fin (L + 1) → Kind)
    (s : Finset (Fin L)) : ℕ :=
  (s.filter (fun v => τ v.castSucc = .normal ∧ τ v.succ = .normal)).card

/-- Equality of both normal coordinates at all indicated internal endpoints. -/
def endpointCoincidence {α : Type*} [DecidableEq α] {L : ℕ}
    {τ : Fin (L + 1) → Kind} (s : Finset (Fin L)) (x : Assignments α τ) : ℝ :=
  ∏ v : s, vertexPairEq (x v)

/-- The internal vertices adjacent to a specified layer. -/
def internalEndpointSet {L : ℕ} (t : Fin (L + 1)) : Finset (Fin L) :=
  Finset.univ.filter (fun v => v.castSucc = t ∨ v.succ = t)

end Problem335.Pairings

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PowerPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small change in exponent from one to `rho` does not destroy the
inverse-square-root scale of the rounded operator parameters. -/

noncomputable section
open Filter Topology

namespace Problem335.PowerPerturbation

/-- An explicit error that tends to zero. -/
def error (n : ℝ) : ℝ := 2 * Real.log n / Real.sqrt n + 2 / n

end Problem335.PowerPerturbation

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the numerical inequalities for the actual rank parameters. -/
noncomputable section
namespace Problem335.LowerParameters

/-- The explicit inequalities from the parameter lemma that are consumed by
both circuit-rank and moment estimates.  All are asserted for the same `n`. -/
structure Admissible (n : ℕ) : Prop where
  n_ge_sixteen : 16 ≤ n
  s_lower : Real.sqrt (n : ℝ) / 2 ≤ (s n : ℝ)
  s_upper : (s n : ℝ) ≤ Real.sqrt (n : ℝ)
  lambda_lower : (3 : ℝ) / 8 ≤ lambda n
  rho_positive : 0 < rho n
  rho_lt_one : rho n < 1
  a_ge_k : k n ≤ a n
  a_ge_four_n : 4 * n ≤ a n
  b_ge_four_n : 4 * n ≤ b n
  alpha_positive : 0 < alpha n
  alpha_lt_one : alpha n < 1
  alpha_lower : (Real.sqrt (n : ℝ))⁻¹ ≤ alpha n
  alpha_inverse_upper : (alpha n)⁻¹ ≤ Real.sqrt (n : ℝ)
  beta_lower : (alpha n) ^ (rho n) ≤ beta n
  beta_upper : beta n ≤ 2 / Real.sqrt (n : ℝ)
  q_lower : (Real.sqrt (n : ℝ))⁻¹ ≤ q n
  q_upper : q n ≤ 2 / Real.sqrt (n : ℝ)
  sqrt_upper_power : 2 / Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ))
  sqrt_upper_half : 2 / Real.sqrt (n : ℝ) ≤ 1 / 2

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathOccupationGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [DecidableEq σ]

/-- Coordinates of one path belonging to a fixed Boolean variable group,
viewed in that group's own coordinate type. -/
def selectedPathCoordinates (side : σ → Bool) (p : List σ) (b : Bool) :
    Finset {x // side x = b} :=
  p.toFinset.subtype (fun x => side x = b)

@[simp] theorem mem_selectedPathCoordinates (side : σ → Bool) (p : List σ)
    (b : Bool) (x : {x // side x = b}) :
    x ∈ selectedPathCoordinates side p b ↔ x.val ∈ p := by
  simp [selectedPathCoordinates]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RelaxedWeightBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.MomentPairing

open scoped BigOperators
open Pairings

/-- Normal pairing layers belonging to the derivative-variable group. -/
def normalVLayers {L : ℕ} (isV : Fin (L + 1) → Bool)
    (τ : Fin (L + 1) → Kind) : Finset (Fin (L + 1)) :=
  Finset.univ.filter (fun t => isV t = true ∧ τ t = .normal)

def diagonalVCount {L : ℕ} (isV : Fin (L + 1) → Bool)
    (τ : Fin (L + 1) → Kind) : ℕ :=
  (Finset.univ.filter (fun t => isV t = true ∧ τ t = .diagonal)).card

def diagonalUCount {L : ℕ} (isV : Fin (L + 1) → Bool)
    (τ : Fin (L + 1) → Kind) : ℕ :=
  (Finset.univ.filter (fun t => isV t = false ∧ τ t = .diagonal)).card

def uLayerCount {L : ℕ} (isV : Fin (L + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun t => isV t = false)).card

/-- The V correction before averaging the path labels. -/
def normalVCorrection {γ : Type*} [DecidableEq γ] {L : ℕ} (isV : Fin (L + 1) → Bool)
    (α : ℝ) (endpoint : γ) (τ : Fin (L + 1) → Kind)
    (x : Fin L → Labels γ) : ℝ :=
  ∏ t : normalVLayers isV τ,
    (1 + α⁻¹ * if (layerLabels endpoint x t).p = (layerLabels endpoint x t).r then 1 else 0)

/-- The normalized pairing-word summand in the second-moment reduction. -/
def relaxedWordWeight {L : ℕ} (isV : Fin (L + 1) → Bool)
    (N α β : ℝ) (τ : Fin (L + 1) → Kind) : ℝ :=
  N⁻¹ ^ adjacentSwitches τ * α⁻¹ ^ diagonalVCount isV τ * β ^ diagonalUCount isV τ *
    ∏ t : normalVLayers isV τ,
      (1 + α⁻¹ * N⁻¹ ^ normalEndpointCount τ (internalEndpointSet t.1))

end Problem335.MomentPairing

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.WordSwitches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boolean words are uniquely specified by their initial bit and their switches.
This gives the exact binomial count used in the path-type sum. -/

open scoped BigOperators

namespace Problem335
namespace WordSwitches

/-- Internal positions where adjacent bits differ. A word has `n + 1` letters. -/
def switches {n : ℕ} (w : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i.castSucc ≠ w i.succ

@[simp] theorem mem_switches {n : ℕ} (w : Fin (n + 1) → Bool) (i : Fin n) :
    i ∈ switches w ↔ w i.castSucc ≠ w i.succ := by
  simp [switches]

/-- The initial letter and switch set encode a nonempty word. -/
def encode {n : ℕ} (w : Fin (n + 1) → Bool) : Bool × Finset (Fin n) :=
  (w 0, switches w)

theorem bool_eq_of_ne_iff (a b c : Bool)
    (h : a ≠ b ↔ a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem encode_injective (n : ℕ) :
    Function.Injective (@encode n) := by
  intro w v h
  have hzero : w 0 = v 0 := congrArg Prod.fst h
  have hs : switches w = switches v := congrArg Prod.snd h
  funext i
  induction i using Fin.induction with
  | zero => exact hzero
  | succ i ih =>
      have hi : w i.castSucc ≠ w i.succ ↔ v i.castSucc ≠ v i.succ := by
        rw [← mem_switches, ← mem_switches, hs]
      rw [ih] at hi
      exact bool_eq_of_ne_iff _ _ _ hi

/-- Every initial letter and set of switch positions specifies exactly one word. -/
theorem encode_bijective (n : ℕ) : Function.Bijective (@encode n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨encode_injective n, ?_⟩
  simp [pow_succ, Nat.mul_comm]

noncomputable def wordEquiv (n : ℕ) :
    (Fin (n + 1) → Bool) ≃ Bool × Finset (Fin n) :=
  Equiv.ofBijective encode (encode_bijective n)

@[simp] theorem wordEquiv_apply (n : ℕ) (w : Fin (n + 1) → Bool) :
    wordEquiv n w = (w 0, switches w) := rfl

end WordSwitches
end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.WordRuns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of true runs, and their relation to adjacent switches. -/

open scoped BigOperators

namespace Problem335.WordRuns

/-- Number of transitions from false to true. -/
def riseCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  ∑ i : Fin n, if w i.castSucc = false ∧ w i.succ = true then 1 else 0

/-- Number of transitions from true to false. -/
def fallCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  ∑ i : Fin n, if w i.castSucc = true ∧ w i.succ = false then 1 else 0

/-- True runs are counted by their first letters. -/
def runCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  riseCount w + (w 0).toNat

/-- In a mixed word, the number of true runs touching an endpoint. -/
def endpointRunCount {n : ℕ} (w : Fin (n + 1) → Bool) : ℕ :=
  (w 0).toNat + (w (Fin.last n)).toNat

@[simp] theorem riseCount_cons {n : ℕ} (b : Bool) (w : Fin (n + 1) → Bool) :
    riseCount (Fin.cons b w) =
      (if b = false ∧ w 0 = true then 1 else 0) + riseCount w := by
  unfold riseCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]

@[simp] theorem fallCount_cons {n : ℕ} (b : Bool) (w : Fin (n + 1) → Bool) :
    fallCount (Fin.cons b w) =
      (if b = true ∧ w 0 = false then 1 else 0) + fallCount w := by
  unfold fallCount
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]

end Problem335.WordRuns

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RunBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contiguous true blocks, with an exact block-count and product factorization. -/

open scoped BigOperators

namespace Problem335.WordRuns

variable {α : Type*}

/-- Split a list at false positions, retaining a possibly empty initial block. -/
def splitTrueAux (p : α → Bool) : List α → List α × List (List α)
  | [] => ([], [])
  | a :: l =>
    let q := splitTrueAux p l
    if p a then (a :: q.1, q.2) else ([], q.1 :: q.2)

/-- The nonempty maximal contiguous blocks of positions satisfying `p`. -/
def trueBlocks (p : α → Bool) (l : List α) : List (List α) :=
  let q := splitTrueAux p l
  (q.1 :: q.2).filter (fun b => !b.isEmpty)

@[simp] theorem splitTrueAux_fst_nil_cons (p : α → Bool) (a : α) (l : List α) :
    (splitTrueAux p (a :: l)).1 = [] ↔ p a = false := by
  cases hp : p a <;> simp [splitTrueAux, hp]

end Problem335.WordRuns

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ScheduleWeightBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335.BalancedSchedule

/-- The graph edges joining consecutive layers, indexed by internal vertices. -/
def internalEdges (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.image (fun v : Fin (n - 1) => (leftLayer v, rightLayer v))

end Problem335.BalancedSchedule

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.UpperConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

/-- The canonical block circuit at block width `ceilSqrt n`. -/
def immUpperCircuit (K : Type*) [CommSemiring K] (n : ℕ) (hn : 0 < n) :
    Depth5Circuit K n :=
  BlockData.circuit K (layerBlocks n (ceilSqrt n)) ⟨0, hn⟩

end Problem335

end

end OAI
end


