-- Prove2me | Definitions.Def_OAIE3v2B013
-- name    : OAIE3v2B013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:48.300577+00:00
-- url     : https://prove2.me/theorems/f99ebb64-53a9-4a9d-ab62-8300339e90a0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 14 of 311
-- statement:
--   Definitions bundle 14 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/DilationBudgets.lean`, `Dynamics/NativeHorizontalLiftBudget.lean`, `Dynamics/PrecenterNativeSelectionBudget.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/ControlledComparisonModel.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/CyclicRelativeChang.lean`, `Estimates/CyclicShortShiftSet.lean`, `Estimates/FiniteFiberTest.lean`, `Estimates/FiniteHypergraphAbstract.lean`, `Estimates/FixedPartnerPower.lean`, `Estimates/IndependentFiniteConditioning.lean`, `Estimates/LocalBoostedAlmostPeriods.lean`, `Estimates/LocalShiftFiber.lean`, `Estimates/LocalizedSiftingAlmostPeriods.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/PreparedFiniteScheduleUniversalMaskProductiveGood.lean`, `Estimates/ProgressionPartitionComposition.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RationalRowReduction.lean`, `Estimates/RealGeneratorCombinations.lean`, `Estimates/SymmetricSquarefreeMonotonicity.lean`, `Estimates/WeightedRudin.lean`, `FixedDensity/AdaptiveCoarseTargetRegularity.lean`, `FixedDensity/BooleanCutReduction.lean`, `FixedDensity/Energy.lean`, `FixedDensity/GeneratorCells.lean`, `FixedDensity/OrderedBoundaryPartition.lean`, `FixedDensity/OrderedPattern.lean`, `FixedDensity/OrderedPatternPartition.lean`, `FixedDensity/OrderedRemoval.lean`, `FixedDensity/SimplexTelescoping.lean`, `Fourier/FiniteFourierSmoothing.lean`, `Fourier/RelativeSpectrumDimension.lean`, `Fourier/TranslatedBohrDifference.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/LieStructureTransport.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Lattices/DenseResidueScalarScoreNet.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Lattices/ResidueStrideRebase.lean`, `Linear/BoundedAdaptedBasis.lean`, `Linear/EpochEventRank.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/RationalMatrixSeparation.lean`, `Linear/SpanningFlagSelection.lean`, `Linear/WeightedFlagBasis.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Polynomial/DegreeRankSunflower.lean`, `Probability/IndependentEmbeddedMixture.lean`, `Results/LinearFormsBasic.lean`, `Sampling/FiniteSamplingMoment.lean`.
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

theorem product_exponential_budget {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, f i ≤ Real.exp ((p + 2) ^ a))
    (hcard : (s.card : ℝ) ≤ (p + 2) ^ c) :
    (∏ i ∈ s, f i) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  calc
    _ ≤ ∏ _i ∈ s, Real.exp ((p + 2) ^ a) := Finset.prod_le_prod hf0 hf
    _ = Real.exp ((s.card : ℝ) * (p + 2) ^ a) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
    _ ≤ Real.exp ((p + 2) ^ (a + c)) := by
      apply Real.exp_le_exp.mpr
      rw [pow_add]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard
        (by positivity : 0 ≤ (p + 2) ^ a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def progressionBlockLabel {N : ℕ} (q H : ℕ) (hq : 0 < q) (n : Fin N) :
    Fin q × Fin (N / q / H + 1) :=
  (⟨n.val % q, Nat.mod_lt _ hq⟩,
    ⟨n.val / q / H, Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.div_le_div_right (Nat.le_of_lt n.isLt)))⟩)

def progressionBlockStart {N q H : ℕ} (i : Fin q × Fin (N / q / H + 1)) : ℕ :=
  i.1.val + q * (H * i.2.val)

theorem progressionBlock_reconstruct {N q H : ℕ} (hq : 0 < q) (n : Fin N) :
    progressionBlockStart (progressionBlockLabel q H hq n) + q * (n.val / q % H) =
      n.val := by
  dsimp [progressionBlockStart, progressionBlockLabel]
  calc
    _ = n.val % q + q * (n.val / q % H + H * (n.val / q / H)) := by ring
    _ = n.val := by rw [Nat.mod_add_div, Nat.mod_add_div]

theorem progressionBlockLabel_of_point {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (i : Fin q × Fin (N / q / H + 1)) {j : ℕ} (hj : j < H)
    (hpoint : progressionBlockStart i + q * j < N) :
    progressionBlockLabel q H hq ⟨progressionBlockStart i + q * j, hpoint⟩ = i := by
  apply Prod.ext <;> apply Fin.ext
  · simp [progressionBlockLabel, progressionBlockStart, Nat.add_mod,
      Nat.mod_eq_of_lt i.1.isLt]
  · change (i.1.val + q * (H * i.2.val) + q * j) / q / H = i.2.val
    rw [show i.1.val + q * (H * i.2.val) + q * j =
      i.1.val + q * (H * i.2.val + j) by ring]
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt i.1.isLt, zero_add]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hH, Nat.div_eq_of_lt hj, zero_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

theorem denseResidueMeshInterval (b len M : ℕ) (hM : 0 < M) (hlen : 2 * M < len) :
    let lo := b / M + 1
    let hi := (b + len) / M
    lo < hi ∧ b ≤ M * lo ∧ M * hi ≤ b + len ∧
      len - (M * hi - M * lo) ≤ 2 * M := by
  dsimp only
  have hb := Nat.mod_add_div b M
  have he := Nat.mod_add_div (b + len) M
  have hbm := Nat.mod_lt b hM
  have hem := Nat.mod_lt (b + len) hM
  have hstart : b < M * (b / M + 1) := by nlinarith
  have hstartUpper : M * (b / M + 1) ≤ b + M := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hend : M * ((b + len) / M) ≤ b + len := by omega
  have hendLower : b + len < M * ((b + len) / M) + M := by omega
  have hlt : b / M + 1 < (b + len) / M := by nlinarith
  refine ⟨hlt, hstart.le, hend, ?_⟩
  have hmul : M * (b / M + 1) ≤ M * ((b + len) / M) :=
    Nat.mul_le_mul_left M hlt.le
  omega

theorem denseResidueMeshInterval_code_bound (b len M K : ℕ)
    (hM : 0 < M) (hlen : 2 * M < len) (hbox : b + len ≤ K * M) :
    b / M + 1 ≤ K ∧ (b + len) / M ≤ K := by
  have h := denseResidueMeshInterval b len M hM hlen
  dsimp only at h
  have hhi : (b + len) / M ≤ K := by nlinarith [h.2.2.1]
  exact ⟨h.1.le.trans hhi, hhi⟩

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

variable {H : Type*} [AddCommGroup H] [Fintype H]

def multiplicativeDerivative (f : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (f (x + h))

noncomputable def gowersMoment : ℕ → (H → ℂ) → ℂ
  | 0, f => 𝔼 x, f x
  | j + 1, f => 𝔼 h, gowersMoment j (multiplicativeDerivative f h)

noncomputable def gowersNorm (j : ℕ) (f : H → ℂ) : ℝ :=
  (gowersMoment j f).re ^ (((2 ^ j : ℕ) : ℝ)⁻¹)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

def crossDerivative (f g : H → ℂ) (h : H) : H → ℂ :=
  fun x ↦ f x * star (g (x + h))

omit [Fintype H] in
@[simp] theorem crossDerivative_self (f : H → ℂ) (h : H) :
    crossDerivative f f h = multiplicativeDerivative f h := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def finiteMask (G : Finset Ω) : (Ω → ℂ) →ₗ[ℂ] (Ω → ℂ) where
  toFun v x := if x ∈ G then v x else 0
  map_add' v w := by ext x; by_cases hx : x ∈ G <;> simp [hx]
  map_smul' c v := by ext x; by_cases hx : x ∈ G <;> simp [hx]

omit [Fintype Ω] in
@[simp] theorem finiteMask_apply (G : Finset Ω) (v : Ω → ℂ) (x : Ω) :
    finiteMask G v x = if x ∈ G then v x else 0 := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rational_sum_cost_le_exp (m H : ℕ) {p : ℝ} (hp : 0 ≤ p) (a c : ℕ)
    (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a)) (hm : (m : ℝ) ≤ (p + 2) ^ c) :
    (((m + 1) * H ^ m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + 1)) := by
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg H) hH m
  rw [← Real.exp_nat_mul] at hpower
  have hone : 1 + (p + 2) ^ a ≤ (p + 2) ^ (a + 1) := by
    have ha : (1 : ℝ) ≤ (p + 2) ^ a := one_le_pow₀ (by linarith)
    calc
      _ ≤ 2 * (p + 2) ^ a := by linarith
      _ ≤ (p + 2) * (p + 2) ^ a :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  push_cast
  calc
    _ ≤ Real.exp m * Real.exp ((m : ℝ) * (p + 2) ^ a) :=
      mul_le_mul (Real.add_one_le_exp m) hpower (by positivity) (by positivity)
    _ = Real.exp ((m : ℝ) * (1 + (p + 2) ^ a)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ c * (p + 2) ^ (a + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul hm hone (by positivity) (by positivity))
    _ = _ := by rw [← pow_add]; congr 2; omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalMatrixSeparation
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem abs_matrix_mulVec_le (Q : Matrix ι κ ℝ) (H : ℝ≥0)
    (hQ : ∀ i j, |Q i j| ≤ H) (x : κ → ℝ) (i : ι) :
    |(Q *ᵥ x) i| ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * ‖x‖ := by
  classical
  calc
    _ ≤ ∑ j, |Q i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, (H : ℝ) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hQ i j) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
        (abs_nonneg _) H.coe_nonneg
    _ = (Fintype.card κ : ℝ) * H * ‖x‖ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by gcongr <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieStructureTransport
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def transportedLieConstants (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (i j k : κ) : ℚ :=
  ∑ abc : ι × (ι × ι), P k abc.1 * c abc.2.1 abc.2.2 abc.1 * S abc.2.1 i * S abc.2.2 j

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem basisMatrix_mulVec (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (x : κ → ℚ) :
    LinearMap.toMatrix b e φ *ᵥ x = e.equivFun (φ (b.equivFun.symm x)) := by
  have h := LinearMap.toMatrix_mulVec_repr b e φ (b.equivFun.symm x)
  simpa only [← b.equivFun_apply, LinearEquiv.apply_symm_apply, ← e.equivFun_apply] using h

omit [DecidableEq ι] in
theorem basisMatrix_injective (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (hφ : Function.Injective φ) : Function.Injective (LinearMap.toMatrix b e φ).mulVec := by
  intro x y hxy
  rw [basisMatrix_mulVec, basisMatrix_mulVec] at hxy
  exact b.equivFun.symm.injective (hφ (e.equivFun.injective hxy))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

def rationalLieStructureHeight (d H : ℕ) : ℕ :=
  (d ^ 3 + 1) * (H ^ 4) ^ (d ^ 3)

theorem rationalLieStructureHeight_le_exp (d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (a : ℕ) (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (rationalLieStructureHeight d H : ℝ) ≤ Real.exp ((p + 2) ^ (a + 6)) := by
  have hterm : ((H ^ 4 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
    rw [Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((p + 2) ^ a)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg H) hH 4
      _ = Real.exp (4 * (p + 2) ^ a) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [pow_add]
        have hsq : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (p + 2) ^ a)
  have hcard : ((d ^ 3 : ℕ) : ℝ) ≤ (p + 2) ^ 3 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg d) (hd.trans (by linarith)) _
  exact rational_sum_cost_le_exp (d ^ 3) (H ^ 4) hp (a + 2) 3 hterm hcard

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicShortShiftSet
namespace OAI

section

namespace Erdos3

def CyclicShortShiftSet {N : ℕ} (H : Finset (ZMod N)) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, 2 * |(x.val : ℤ) - y.val| < (N : ℤ)

theorem CyclicShortShiftSet.integer_relation {N : ℕ} [NeZero N]
    {H : Finset (ZMod N)} (hH : CyclicShortShiftSet H)
    {x₁ x₂ x₃ x₄ : ZMod N} (h₁ : x₁ ∈ H) (h₂ : x₂ ∈ H)
    (h₃ : x₃ ∈ H) (h₄ : x₄ ∈ H) (hrel : x₁ - x₂ = x₃ - x₄) :
    (x₁.val : ℤ) - x₂.val = (x₃.val : ℤ) - x₄.val := by
  let d₁ : ℤ := (x₁.val : ℤ) - x₂.val
  let d₂ : ℤ := (x₃.val : ℤ) - x₄.val
  have hd₁ : 2 * |d₁| < (N : ℤ) := hH x₁ h₁ x₂ h₂
  have hd₂ : 2 * |d₂| < (N : ℤ) := hH x₃ h₃ x₄ h₄
  have hcast : (d₁ : ZMod N) = (d₂ : ZMod N) := by
    simpa only [d₁, d₂, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] using hrel
  have hdvd : (N : ℤ) ∣ d₂ - d₁ :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d₁ d₂ N).mp hcast
  have habs : |d₂ - d₁| < (N : ℤ) :=
    (abs_sub d₂ d₁).trans_lt (by omega)
  have hsmall : (d₂ - d₁).natAbs < (N : ℤ).natAbs := by
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_natAbs, abs_of_nonneg (Int.natCast_nonneg N)] using habs
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hsmall
  change d₁ = d₂
  omega

theorem CyclicShortShiftSet.quadruple_relation {N : ℕ} [NeZero N]
    {H : Finset (ZMod N)} (hH : CyclicShortShiftSet H) (a h k : ZMod N)
    (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H) :
    -(h.val : ℤ) + (h - a).val + k.val - (k - a).val = 0 := by
  have heq := hH.integer_relation h₁ h₂ h₃ h₄ (by abel : h - (h - a) = k - (k - a))
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedPartnerPower
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def functionCorrelationLinearMap (w : Ω → ℂ) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 x, v x * w x
  map_add' v u := by simp [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply,
      Finset.mul_expect]

noncomputable def functionCorrelationSeminorm (w : Ω → ℂ) : Seminorm ℂ (Ω → ℂ) :=
  (normSeminorm ℂ ℂ).comp (functionCorrelationLinearMap w)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

noncomputable def shiftTestSeminormAt (B : G → ℂ) (T : ι → G → ℂ) (h : G) :
    Seminorm ℂ (G → ℂ) :=
  ⨆ i, functionCorrelationSeminorm (fun x => B (x + h) * T i x)

noncomputable def shiftTestingSeminorm (B : G → ℂ) (T : ι → G → ℂ) :
    Seminorm ℂ (G → ℂ) :=
  Seminorm.of (fun v => 𝔼 h, shiftTestSeminormAt B T h v)
    (fun u v => by
      rw [← Finset.expect_add_distrib]
      exact Finset.expect_le_expect (fun h _ => map_add_le_add _ _ _))
    (fun a v => by simp only [map_smul_eq_mul, Finset.mul_expect])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G]

def translatedTestFamily (T : ι → G → ℂ) (p : G × ι) (x : G) : ℂ := T p.2 (x + p.1)

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

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def ReflectsPairSums (φ : A →+ B) (Q : Set A) : Prop :=
  ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ∀ d ∈ Q,
    φ a + φ b = φ c + φ d → a + b = c + d

theorem ReflectsPairSums.injOn {φ : A →+ B} {Q : Set A}
    (hφ : ReflectsPairSums φ Q) : Set.InjOn φ Q := by
  intro a ha b hb he
  exact add_right_cancel (hφ a ha a ha b hb a ha (by rw [he]))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) : ℂ :=
  𝔼 x, f x * star (χ x)

theorem addChar_sub_star (χ : AddChar H ℂ) (x y : H) :
    χ (x - y) = χ x * star (χ y) := by
  rw [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
  rfl

theorem finiteFourier_inversion (f : H → ℂ) (x : H) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) = f x := by
  classical
  calc
    _ = 𝔼 y, f y * (∑ χ : AddChar H ℂ, χ (x - y)) := by
      simp only [finiteFourierCoeff, Finset.expect_mul]
      rw [← Finset.expect_sum_comm]
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [addChar_sub_star]
      ring
    _ = 𝔼 y, if x = y then (Fintype.card H : ℂ) * f x else 0 := by
      apply Finset.expect_congr rfl
      intro y _
      rw [AddChar.sum_apply_eq_ite]
      by_cases hxy : x = y
      · subst y
        simp [mul_comm]
      · simp [sub_eq_zero, hxy]
    _ = _ := by
      have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_eq_single x]
      · simp [hc]
      · intro y _ hy
        simp only [if_neg (Ne.symm hy)]
      · simp

end Erdos3

end

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def fourierL1 (f : G → ℂ) : ℝ :=
  ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖

theorem norm_sub_translate_le_fourier_sum (f : G → ℂ) (t x : G) :
    ‖f (x - t) - f x‖ ≤
      ∑ ψ : AddChar G ℂ,
        ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
  classical
  rw [← finiteFourier_inversion f (x - t),
    ← finiteFourier_inversion f x, ← Finset.sum_sub_distrib]
  calc
    ‖∑ ψ : AddChar G ℂ,
        (finiteFourierCoeff f ψ * ψ (x - t) -
          finiteFourierCoeff f ψ * ψ x)‖
        ≤ ∑ ψ : AddChar G ℂ,
            ‖finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x‖ :=
          norm_sum_le _ _
    _ = ∑ ψ : AddChar G ℂ,
          ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
      apply sum_congr rfl
      intro ψ _
      have hfactor :
          finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x =
            (finiteFourierCoeff f ψ * ψ x) * (ψ (-t) - 1) := by
        have hmap : ψ (x - t) = ψ x * ψ (-t) := by
          rw [sub_eq_add_neg, ψ.map_add_eq_mul]
        rw [hmap]
        ring
      rw [hfactor, norm_mul, norm_mul, AddChar.norm_apply, mul_one]

omit [Fintype G] in

lemma norm_character_neg_sub_one [Finite G] (psi : AddChar G ℂ) (t : G) :
    ‖psi (-t) - 1‖ = ‖1 - psi t‖ := by
  rw [psi.map_neg_eq_inv]
  have hne : psi t ≠ 0 := by
    intro h
    have := AddChar.norm_apply psi t
    simp [h] at this
  calc
    ‖(psi t)⁻¹ - 1‖ = ‖(psi t)⁻¹ * (1 - psi t)‖ := by
      congr 1
      field_simp
    _ = ‖1 - psi t‖ := by
      rw [norm_mul, norm_inv, AddChar.norm_apply, inv_one, one_mul]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  𝔼 a ∈ A, star (psi a)

theorem finiteFourierCoeff_translate (f : G → ℂ) (a : G) (psi : AddChar G ℂ) :
    finiteFourierCoeff (fun x => f (x - a)) psi = star (psi a) * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff
  calc
    (𝔼 x, f (x - a) * star (psi x)) = 𝔼 x, f x * star (psi (x + a)) := by
      apply Fintype.expect_equiv (Equiv.subRight a)
      intro x
      simp
    _ = star (psi a) * 𝔼 x, f x * star (psi x) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, star_mul]
      ring

theorem norm_setFourierMultiplier_le_one {A : Finset G} (hA : A.Nonempty)
    (psi : AddChar G ℂ) : ‖setFourierMultiplier A psi‖ ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  simp only [norm_star, AddChar.norm_apply, Finset.expect_const hA]
  exact le_rfl

end Erdos3

end

section

noncomputable section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

def IsWeightedDissociated (mu : G → ℝ) (K : ℝ)
    (Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ u : AddChar G ℂ → ℂ,
    (∀ psi ∈ Delta, ‖u psi‖ ≤ 1) →
      ∑ x : G, mu x *
        ∏ psi ∈ Delta, (1 + (u psi * psi x).re) ≤ exp K

def relativeLargeSpectrum (mu f : G → ℝ) (eta : ℝ) :
    Finset (AddChar G ℂ) :=
    Finset.univ.filter fun psi ↦
    eta * (∑ x : G, f x * mu x) ≤
      ‖∑ x : G, (f x * mu x : ℝ) * psi x‖

@[simp] theorem mem_relativeLargeSpectrum {mu f : G → ℝ} {eta : ℝ}
    {psi : AddChar G ℂ} :
    psi ∈ relativeLargeSpectrum mu f eta ↔
      eta * (∑ x : G, f x * mu x) ≤
        ‖∑ x : G, (f x * mu x : ℝ) * psi x‖ := by
  simp [relativeLargeSpectrum]

end Erdos3.RelativeChangSanders

end

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

def piRestrictionSet (G : ∀ j, Finset (Ω j)) : Finset (∀ j, Ω j) :=
  Finset.univ.filter (fun x => ∀ j, x j ∈ G j)

theorem mem_piRestrictionSet (G : ∀ j, Finset (Ω j)) (x : ∀ j, Ω j) :
    x ∈ piRestrictionSet G ↔ ∀ j, x j ∈ G j := by
  simp only [piRestrictionSet, Finset.mem_filter, Finset.mem_univ, true_and]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanningFlagSelection
namespace OAI

section

namespace Erdos3

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_nested_independent_spanning_sets (n : ℕ) :
    ∀ (P : Fin n → Submodule K V) (S : Set V), Antitone P →
      (∀ i, Submodule.span K (S ∩ (P i : Set V)) = P i) →
      ∃ B : Set V, B ⊆ S ∧ LinearIndepOn K id B ∧
        Submodule.span K B = Submodule.span K S ∧
        ∃ T : Fin n → Set V, Antitone T ∧ (∀ i, T i ⊆ B) ∧
          ∀ i, Submodule.span K (T i) = P i := by
  induction n with
  | zero =>
      intro P S _ _
      let h := linearIndepOn_empty K (id : V → V)
      let hsub : (∅ : Set V) ⊆ S := Set.empty_subset S
      refine ⟨h.extend hsub, h.extend_subset hsub, h.linearIndepOn_extend hsub,
        h.span_extend_eq_span hsub, Fin.elim0, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro P S hP hspan
      let S₀ := S ∩ (P 0 : Set V)
      let P' : Fin n → Submodule K V := fun i => P i.succ
      have hP' : Antitone P' := fun i j hij => hP (by simpa using hij)
      have hspan' (i : Fin n) : Submodule.span K (S₀ ∩ (P' i : Set V)) = P' i := by
        have heq : S₀ ∩ (P' i : Set V) = S ∩ (P i.succ : Set V) := by
          ext x
          constructor
          · exact fun hx => ⟨hx.1.1, hx.2⟩
          · exact fun hx => ⟨⟨hx.1, hP (Fin.zero_le i.succ) hx.2⟩, hx.2⟩
        rw [heq]
        exact hspan i.succ
      obtain ⟨B₀, hB₀, hiB₀, hspB₀, T₀, hT₀, hTB₀, hspT₀⟩ := ih P' S₀ hP' hspan'
      have hBS : B₀ ⊆ S := fun _ hx => (hB₀ hx).1
      let B := hiB₀.extend hBS
      have hB₀B : B₀ ⊆ B := hiB₀.subset_extend hBS
      let T : Fin (n + 1) → Set V := Fin.cases B₀ T₀
      refine ⟨B, hiB₀.extend_subset hBS, hiB₀.linearIndepOn_extend hBS,
        hiB₀.span_extend_eq_span hBS, T, ?_, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact Set.Subset.rfl
          · exact hTB₀ j
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i)) hij)
          · exact hT₀ (by simpa using hij)
      · intro i
        exact Fin.cases hB₀B (fun j => (hTB₀ j).trans hB₀B) i
      · intro i
        refine Fin.cases ?_ (fun j => hspT₀ j) i
        exact hspB₀.trans (hspan 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedFlagBasis
namespace OAI

section

namespace Erdos3

open Module

variable {κ : Type*} {n : ℕ}

noncomputable def nestedSupportWeight (S : Fin n → Set κ) (x : κ) : ℕ :=
  by classical exact (Finset.univ.filter fun i => x ∈ S i).card

theorem nestedSupportWeight_le (S : Fin n → Set κ) (x : κ) :
    nestedSupportWeight S x ≤ n := by
  classical
  simpa only [nestedSupportWeight, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => x ∈ S i)

theorem mem_nestedSupport_iff (S : Fin n → Set κ) (hS : Antitone S) (i : Fin n) (x : κ) :
    x ∈ S i ↔ i.val < nestedSupportWeight S x := by
  classical
  let A := Finset.univ.filter fun j => x ∈ S j
  constructor
  · intro hx
    have hle : Finset.Iic i ⊆ A := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS (Finset.mem_Iic.mp hj) hx⟩
    have hcard := Finset.card_le_card hle
    rw [Fin.card_Iic] at hcard
    exact hcard
  · intro hi
    by_contra hx
    have hle : A ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hij
      exact hx (hS (le_of_not_gt hij) (Finset.mem_filter.mp hj).2)
    have hcard := Finset.card_le_card hle
    rw [Fin.card_Iio] at hcard
    exact Nat.not_lt_of_ge hcard hi

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

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_inter_eq_of_spanning_family {η : Type*} (P : Submodule K V)
    (v : η → P) (hspan : Submodule.span K (Set.range v) = ⊤)
    (S : Set V) (hv : ∀ i, (v i : V) ∈ S) :
    Submodule.span K (S ∩ (P : Set V)) = P := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hx => hx.2)
  · have hmap := congrArg (Submodule.map P.subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
    conv_lhs => rw [← hmap]
    apply Submodule.span_mono
    rintro x ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨hv i, (v i).property⟩

theorem exists_sorted_flag_basis_from_spanning_set [FiniteDimensional K V] {n : ℕ}
    (P : Fin n → Submodule K V) (hP : Antitone P) (S : Set V)
    (hS : Submodule.span K S = ⊤)
    (hspan : ∀ i, Submodule.span K (S ∩ (P i : Set V)) = P i) :
    ∃ (e : Basis (Fin (finrank K V)) K V) (w : Fin (finrank K V) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ n) ∧ (∀ j, e j ∈ S) ∧
      ∀ i, P i = Submodule.span K (e '' {j | i.val < w j}) := by
  classical
  obtain ⟨B, hBS, hBli, hBspan, T, hT, hTB, hTspan⟩ :=
    exists_nested_independent_spanning_sets n P S hP hspan
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : B → V)) := by
    simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hBspan, hS, le_refl]
  let b : Basis B K V := Basis.mk hBli.linearIndependent_restrict hsp
  let : Finite B := Module.Finite.finite_basis b
  let : Fintype B := Fintype.ofFinite B
  let ρ : B ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let u : Fin (finrank K V) → ℕ := fun j => nestedSupportWeight T (ρ.symm j).val
  let σ := Tuple.sort u
  let e := b.reindex (ρ.trans σ.symm)
  let w : Fin (finrank K V) → ℕ := fun j => u (σ j)
  have he (j : Fin (finrank K V)) : e j = (ρ.symm (σ j)).val := by
    simp [e, b, Basis.reindex_apply]
  refine ⟨e, w, Tuple.monotone_sort u, fun j => nestedSupportWeight_le T _, ?_, ?_⟩
  · intro j
    rw [he]
    exact hBS (ρ.symm (σ j)).property
  · intro i
    rw [← hTspan i]
    congr 1
    ext x
    constructor
    · intro hx
      let k : B := ⟨x, hTB i hx⟩
      refine ⟨σ.symm (ρ k), ?_, ?_⟩
      · simpa only [Set.mem_ofPred_eq, w, u, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply] using (mem_nestedSupport_iff T hT i x).mp hx
      · simp only [he, Equiv.apply_symm_apply, Equiv.symm_apply_apply, k]
    · rintro ⟨j, hj, rfl⟩
      rw [he]
      exact (mem_nestedSupport_iff T hT i _).mpr hj

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d n : ℕ}

theorem finite_flag_weight_le (P : ℕ → Submodule ℚ L) (e : Basis (Fin d) ℚ L)
    (w : Fin d → ℕ) (hn : P n = ⊥)
    (hspan : P n = Submodule.span ℚ (e '' {j | n < w j})) (j : Fin d) : w j ≤ n := by
  by_contra h
  have hj : e j ∈ P n := by
    rw [hspan]
    exact Submodule.subset_span ⟨j, Nat.lt_of_not_ge h, rfl⟩
  rw [hn] at hj
  exact e.ne_zero j (by simpa only [Submodule.mem_bot] using hj)

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def weightCut {d : ℕ} (w : Fin d → ℕ) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => w j ≤ k)).card

theorem weightCut_le {d : ℕ} (w : Fin d → ℕ) (k : ℕ) : weightCut w k ≤ d := by
  classical
  simpa only [weightCut, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin d))) (p := fun j => w j ≤ k))

theorem weight_gt_iff_cut_le {d : ℕ} (w : Fin d → ℕ) (hw : Monotone w) (k : ℕ) (j : Fin d) :
    k < w j ↔ weightCut w k ≤ j.val := by
  classical
  let A := Finset.univ.filter (fun i => w i ≤ k)
  constructor
  · intro hj
    have hA : A ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      have hiw : w i ≤ k := (Finset.mem_filter.mp hi).2
      by_contra h
      have := hw (le_of_not_gt h)
      omega
    have hcard := Finset.card_le_card hA
    simpa only [A, Fin.card_Iio, weightCut] using hcard
  · intro hj
    by_contra h
    have hjw : w j ≤ k := le_of_not_gt h
    have hA : Finset.Iic j ⊆ A := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hw (Finset.mem_Iic.mp hi)).trans hjw⟩
    have hcard := Finset.card_le_card hA
    rw [Fin.card_Iic] at hcard
    change j.val + 1 ≤ weightCut w k at hcard
    omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rational_nat_smul_mem (M : Submodule ℤ L) {z : L} (hz : z ∈ M) (D : ℕ) :
    (D : ℚ) • z ∈ M := by
  rw [Nat.cast_smul_eq_nsmul ℚ]
  exact M.nsmul_mem hz D

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s r : ℕ}

theorem rankFlag_encode_lt (i j : ℕ) (hi : i ≤ s) (hj : j ≤ s) :
    i * (s + 1) + j < (s + 1) * (s + 1) := by
  have h := Nat.mul_le_mul_right (s + 1) hi
  nlinarith

theorem rankFlag_decode_lt {k : ℕ} (hk : k < (s + 1) * (s + 1)) :
    k / (s + 1) ≤ s ∧ k % (s + 1) ≤ s := by
  have hA : 0 < s + 1 := by omega
  have hdiv := (Nat.div_lt_iff_lt_mul hA).mpr hk
  have hmod : k % (s + 1) < s + 1 := Nat.mod_lt k hA
  omega

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

def separationBudget (p : ℝ) : ℝ := (p + 2) ^ 48 + (p + 2) ^ 24 + p + 1

theorem separationBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ separationBudget p := by
  unfold separationBudget
  positivity

theorem separationBudget_small {p D K r : ℝ}
    (hD : D ≤ Real.exp ((p + 2) ^ 48)) (hK : K ≤ Real.exp ((p + 2) ^ 24))
    (hK0 : 0 ≤ K) (hr0 : 0 ≤ r)
    (hr : r ≤ Real.exp p / Real.exp (separationBudget p)) :
    D * K * r < 1 := by
  calc
    D * K * r ≤ Real.exp ((p + 2) ^ 48) * Real.exp ((p + 2) ^ 24) *
        (Real.exp p / Real.exp (separationBudget p)) :=
      mul_le_mul (mul_le_mul hD hK hK0 (Real.exp_nonneg _)) hr hr0 (by positivity)
    _ = Real.exp (-1) := by
      rw [← Real.exp_sub, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold separationBudget
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

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

theorem real_column_span_mem_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (x : ι → ℝ) :
    x ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ↔
      x ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  have h := congrArg (fun U : Submodule ℝ (ι → ℝ) => x ∈ U)
    (Matrix.range_mulVecLin (Matrix.of (fun i j => (A i j : ℝ))))
  exact (iff_of_eq h).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

open scoped Matrix NNReal

namespace Erdos3

theorem norm_matrix_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι κ ℝ) (H : ℝ≥0) (hQ : ∀ i j, |Q i j| ≤ H) (x : κ → ℝ) :
    ‖Q *ᵥ x‖ ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using abs_matrix_mulVec_le Q H hQ x i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

noncomputable def realRationalCoordinateEquiv : (ℝ ⊗[ℚ] (ι → ℚ)) ≃ₗ[ℝ] (ι → ℝ) :=
  ((Pi.basisFun ℚ ι).baseChange ℝ).equivFun

theorem realRationalCoordinateEquiv_tmul (a : ℝ) (x : ι → ℚ) (i : ι) :
    realRationalCoordinateEquiv (a ⊗ₜ[ℚ] x) i = a * (x i : ℝ) := by
  change ((Pi.basisFun ℚ ι).baseChange ℝ).repr (a ⊗ₜ[ℚ] x) i = _
  rw [Basis.baseChange_repr_tmul]
  change (x i) • a = _
  simp only [Rat.smul_def, mul_comm]

noncomputable def realRationalCoordinateSpan (U : Submodule ℚ (ι → ℚ)) : Submodule ℝ (ι → ℝ) :=
  (U.baseChange ℝ).map realRationalCoordinateEquiv.toLinearMap

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι]

theorem realRationalCoordinateSpan_span (v : κ → ι → ℚ) :
    realRationalCoordinateSpan (Submodule.span ℚ (Set.range v)) =
      Submodule.span ℝ (Set.range (fun a i => (v a i : ℝ))) := by
  unfold realRationalCoordinateSpan
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    funext i
    change (v a i : ℝ) = realRationalCoordinateEquiv (1 ⊗ₜ[ℚ] v a) i
    simpa only [one_mul] using (realRationalCoordinateEquiv_tmul (1 : ℝ) (v a) i).symm
  · rintro ⟨a, rfl⟩
    refine ⟨v a, ⟨a, rfl⟩, ?_⟩
    funext i
    change realRationalCoordinateEquiv (1 ⊗ₜ[ℚ] v a) i = (v a i : ℝ)
    simpa only [one_mul] using realRationalCoordinateEquiv_tmul (1 : ℝ) (v a) i

theorem realRationalCoordinateSpan_eq_image [Fintype κ]
    (U : Submodule ℚ (ι → ℚ)) (v : κ → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = U) :
    realRationalCoordinateSpan U =
      LinearMap.range (Matrix.mulVecLin (fun i a => (v a i : ℝ))) := by
  rw [← hv, realRationalCoordinateSpan_span]
  ext x
  exact real_column_span_mem_iff (fun i a => v a i) x

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype μ] {V : Submodule ℚ L}

noncomputable def quotientCoordinateMatrix (b : Basis μ ℚ L) (f : Basis ι ℚ (L ⧸ V)) :
    Matrix ι μ ℚ := fun i j => f.repr (V.mkQ (b j)) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

noncomputable def translatedCyclicProduct (h : ι → ZMod N) (u : ι → ℤ → ℂ) (x : ZMod N) : ℂ :=
  ∏ i, u i ((h i + x).val : ℤ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

structure FiniteCoefficientSlice where
  length : ℕ
  offset : ℤ
  stride : ℤ
  modulus : ℕ
  residue : ZMod modulus

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def normalizedSliceTest {T : Type*} [Fintype T]
    (S : Finset T) (w : T → ℂ) (t : T) : ℂ :=
  ((Fintype.card T : ℂ) / S.card) * (if t ∈ S then w t else 0)

theorem normalizedSliceTest_norm_le {T : Type*} [Fintype T]
    (S : Finset T) (w : T → ℂ) {K : ℝ}
    (hsize : (Fintype.card T : ℝ) / S.card ≤ K) (hw : ∀ t, ‖w t‖ ≤ 1) (t : T) :
    ‖normalizedSliceTest S w t‖ ≤ K := by
  have hr : 0 ≤ (Fintype.card T : ℝ) / S.card := by positivity
  by_cases ht : t ∈ S
  · simp only [normalizedSliceTest, ht, ite_true, norm_mul, norm_div, Complex.norm_natCast]
    exact (mul_le_of_le_one_right hr (hw t)).trans hsize
  · simpa only [normalizedSliceTest, ht, ite_false, mul_zero, norm_zero] using hr.trans hsize

theorem normalizedSliceTest_mean {T : Type*} [Fintype T] [Nonempty T]
    (S : Finset T) (hS : S.Nonempty) (w f : T → ℂ) :
    (𝔼 t, f t * normalizedSliceTest S w t) = 𝔼 t ∈ S, f t * w t := by
  have hT : (Fintype.card T : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hS0 : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have he : (∑ t, f t * normalizedSliceTest S w t) =
      ((Fintype.card T : ℂ) / S.card) * ∑ t ∈ S, f t * w t := by
    rw [Finset.mul_sum]
    have hterm (t : T) : f t * normalizedSliceTest S w t =
        if t ∈ S then ((Fintype.card T : ℂ) / S.card) * (f t * w t) else 0 := by
      by_cases ht : t ∈ S <;> simp only [normalizedSliceTest, ht, ite_true, ite_false, mul_zero]
      ring
    simp_rw [hterm]
    simp
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, he]
  field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def sampledTestLinearMap {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 t, v (F t) * w t
  map_add' v u := by simp [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, Finset.mul_expect]

noncomputable def sampledSingleTestSeminorm {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) : Seminorm ℂ (X → ℂ) :=
  (normSeminorm ℂ ℂ).comp (sampledTestLinearMap F w)

theorem sampledSingleTestSeminorm_le {T X : Type*} [Fintype T]
    (F : T → X) (w : T → ℂ) {K : ℝ} (hw : ∀ t, ‖w t‖ ≤ K) (v : X → ℂ) :
    sampledSingleTestSeminorm F w v ≤ K * (𝔼 t, ‖v (F t)‖) := by
  change ‖𝔼 t, v (F t) * w t‖ ≤ _
  rw [Finset.mul_expect]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro t _
  rw [norm_mul, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hw t) (norm_nonneg _)

theorem sampledSingleTestSeminorm_bddAbove {Ω T X : Type*} [Fintype T]
    {J : Ω → Type*} (F : Ω → T → X) (w : ∀ z, J z → T → ℂ)
    {K : ℝ} (hw : ∀ z j t, ‖w z j t‖ ≤ K) (z : Ω) :
    BddAbove (Set.range (fun j => sampledSingleTestSeminorm (F z) (w z j))) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro v
  refine ⟨K * (𝔼 t, ‖v (F z t)‖), ?_⟩
  rintro _ ⟨j, rfl⟩
  exact sampledSingleTestSeminorm_le (F z) (w z j) (hw z j) v

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def centeredFiniteSliceResidualEnvelope
    {Ω T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : X → ℂ) (z : Ω) : ℝ :=
  (⨆ j, sampledSingleTestSeminorm (physical z)
    (normalizedSliceTest (slices z j) (tests z j))) signal

theorem centeredFiniteSliceResidualEnvelope_nonneg
    {Ω T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (signal : X → ℂ) (z : Ω) :
    0 ≤ centeredFiniteSliceResidualEnvelope physical slices tests signal z :=
  apply_nonneg _ _

theorem centeredFiniteSliceResidualEnvelope_dominates
    {Ω T X : Type*} [Fintype T] [Nonempty T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (signal : X → ℂ) (z : Ω) (j : J z) :
    ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ ≤
      centeredFiniteSliceResidualEnvelope physical slices tests signal z := by
  let W := fun z j => normalizedSliceTest (slices z j) (tests z j)
  have hW (z) (j) (t) : ‖W z j t‖ ≤ K :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (htests z j) t
  change _ ≤ (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal
  rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
  have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
      ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ := by
    change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
    rw [normalizedSliceTest_mean _ (hS z j)]
  rw [← he]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*}
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}

noncomputable def dilationPairGeometryBudget (s : ℕ) (p : ℝ) : ℝ :=
  ((p + 4) ^ 2 + (s + 2) * (p + 1) + 6) ^ 11

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.DilationBudgets
namespace OAI

section

namespace Erdos3.DilationBudget

open RationalFilteredNilmanifold
open scoped NNReal

noncomputable def reconstruction (t : ℕ) (q : ℤ) (p : ℝ) : ℝ :=
  3 * p + (p + 3) ^ 2 + (q ^ t).natAbs + 6

noncomputable def total (t : ℕ) (q : ℤ) (N : ℕ) (p : ℝ) : ℝ :=
  p + (reconstruction t q p + N) ^ N + 4

theorem reconstruction_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reconstruction t q p ∧ p + 1 ≤ reconstruction t q p := by
  have hn : 0 ≤ ((q ^ t).natAbs : ℝ) := Nat.cast_nonneg _
  unfold reconstruction
  constructor <;> nlinarith only [hp, hn, sq_nonneg (p + 3)]

theorem observable_bound (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) (K A : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp p) :
    (((q ^ t).natAbs : ℝ) + 1) * (K * (A * Real.exp ((p + 3) ^ 2))) ≤
      Real.exp (reconstruction t q p) := by
  have hn : ((q ^ t).natAbs : ℝ) + 1 ≤ Real.exp ((q ^ t).natAbs : ℝ) := Real.add_one_le_exp _
  have hP : 0 ≤ Real.exp ((p + 3) ^ 2) := (Real.exp_pos _).le
  have h := mul_le_mul hn
    (mul_le_mul hK (mul_le_mul_of_nonneg_right hA hP)
      (mul_nonneg A.coe_nonneg hP) (Real.exp_pos p).le)
    (mul_nonneg K.coe_nonneg (mul_nonneg A.coe_nonneg hP)) (Real.exp_pos _).le
  have he : Real.exp ((q ^ t).natAbs : ℝ) *
      (Real.exp p * (Real.exp p * Real.exp ((p + 3) ^ 2))) =
      Real.exp (2 * p + (p + 3) ^ 2 + (q ^ t).natAbs) := by
    rw [show 2 * p = p + p by ring]
    simp only [Real.exp_add]
    ring
  rw [he] at h
  exact h.trans (Real.exp_le_exp.mpr (by unfold reconstruction; linarith))

theorem total_bounds (t : ℕ) (q : ℤ) (N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ total t q N p ∧ (reconstruction t q p + N) ^ N + 4 ≤ total t q N p := by
  have hr := (reconstruction_bounds t q hp).1
  have hpow : 0 ≤ (reconstruction t q p + N) ^ N := by positivity
  unfold total
  exact ⟨by linarith, by linarith⟩

end Erdos3.DilationBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PrecenterNativeSelectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem precenter_exp_add_le_div (q a : ℝ) (ha : 0 < a)
    (hlog : Real.log a ≤ a) :
    Real.exp (-(q + a)) ≤ Real.exp (-q) / a := by
  calc
    _ ≤ Real.exp (-q - Real.log a) := Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := by rw [Real.exp_sub, Real.exp_log ha]

theorem precenter_native_selection_model_error_budget (inputLog rFreq : ℝ) :
    Real.exp inputLog * Real.exp (-(inputLog + rFreq + 2)) ≤ Real.exp (-rFreq) / 2 := by
  have htwo : Real.log (2 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  calc
    _ = Real.exp (-(rFreq + 2)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := precenter_exp_add_le_div rFreq 2 (by norm_num) htwo

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedRudin
namespace OAI

section

noncomputable section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in

theorem exp_weightedAverage_le_weightedAverage_exp
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw_sum : ∑ x : G, w x = 1)
    (f : G → ℝ) :
    exp (∑ x : G, w x * f x) ≤ ∑ x : G, w x * exp (f x) := by
  have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset G))
    (p := f) (fun x _ ↦ hw x) (by simpa using hw_sum)
    (fun x _ ↦ Set.mem_univ (f x))
  simpa using h

theorem weighted_rudin_exp_ineq
    (mu : G → ℝ) (K : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x)
    (hDelta : IsWeightedDissociated mu K Delta)
    (c : AddChar G ℂ → ℂ) :
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
      exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
  have hexp (z : ℂ) :
      exp z.re ≤ cosh ‖z‖ + (z / ‖z‖).re * sinh ‖z‖ := by
    calc
      _ = exp ((z / ‖z‖).re * ‖z‖) := by
        obtain rfl | hz := eq_or_ne z 0 <;> simp [*]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh
        (by simpa using z.abs_re_div_norm_le_one) _
  choose u hu huc using fun psi ↦ Complex.exists_norm_mul_eq_self (c psi)
  have hu0 (psi : AddChar G ℂ) : u psi ≠ 0 := fun h ↦ by
    simpa [h] using hu psi
  have hpoint (x : G) :
      exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
    calc
      exp ((∑ psi ∈ Delta, c psi * psi x).re) =
          ∏ psi ∈ Delta, exp ((c psi * psi x).re) := by
            simp_rw [← exp_sum, ← Complex.re_sum]
      _ ≤ ∏ psi ∈ Delta,
          (cosh ‖c psi * psi x‖ +
            ((c psi * psi x) / ‖c psi * psi x‖).re *
              sinh ‖c psi * psi x‖) := by
        gcongr with psi hpsi
        exact hexp _
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ +
            (u psi * (c psi * psi x) / (u psi * ↑‖c psi‖)).re *
              sinh ‖c psi‖) := by
        apply prod_congr rfl
        intro psi hpsi
        rw [norm_mul, AddChar.norm_apply, mul_one,
          mul_div_mul_left _ _ (hu0 psi)]
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
        apply prod_congr rfl
        intro psi hpsi
        obtain hc | hc := eq_or_ne (c psi) 0
        · simp [hc]
        simp only [huc, mul_left_comm (u psi), mul_div_cancel_left₀ _ hc,
          ← Complex.re_mul_ofReal, mul_right_comm]
  let q : AddChar G ℂ → ℝ := fun psi ↦ sinh ‖c psi‖ / cosh ‖c psi‖
  let v : AddChar G ℂ → ℂ := fun psi ↦ (q psi : ℂ) * u psi
  have hfactor (x : G) :
      (∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re)) =
        (∏ psi ∈ Delta, cosh ‖c psi‖) *
          (∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
    rw [← Finset.prod_mul_distrib]
    apply prod_congr rfl
    intro psi hpsi
    have hcosh : cosh ‖c psi‖ ≠ 0 := ne_of_gt (cosh_pos _)
    have hsinh_re :
        (u psi * (sinh ‖c psi‖ : ℂ) * psi x).re =
          sinh ‖c psi‖ * (u psi * psi x).re := by
      rw [show u psi * (sinh ‖c psi‖ : ℂ) * psi x =
          (sinh ‖c psi‖ : ℂ) * (u psi * psi x) by ring]
      exact Complex.re_ofReal_mul _ _
    have hv_re : (v psi * psi x).re = q psi * (u psi * psi x).re := by
      rw [show v psi * psi x = (q psi : ℂ) * (u psi * psi x) by
        simp [v]; ring]
      exact Complex.re_ofReal_mul _ _
    rw [hsinh_re, hv_re]
    dsimp [q]
    field_simp
  calc
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∑ x : G, mu x * ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x) (hmu x)
    _ = (∏ psi ∈ Delta, cosh ‖c psi‖) *
        (∑ x : G, mu x *
          ∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [hfactor]
      ring
    _ ≤ (∏ psi ∈ Delta, cosh ‖c psi‖) * exp K := by
      gcongr
      apply hDelta v
      intro psi hpsi
      have hq : |q psi| ≤ 1 := by
        simpa [q, Real.tanh_eq_sinh_div_cosh] using (Real.abs_tanh_lt_one ‖c psi‖).le
      simpa [v, norm_mul, hu psi, Complex.norm_real, Real.norm_eq_abs] using hq
    _ ≤ exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) * exp K := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      calc
        ∏ psi ∈ Delta, cosh ‖c psi‖ ≤
            ∏ psi ∈ Delta, exp (‖c psi‖ ^ 2 / 2) := by
          gcongr with psi hpsi
          exact cosh_le_exp_half_sq _
        _ = exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
          simp_rw [← exp_sum, ← sum_div]
    _ = exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
      rw [← exp_add]
      congr 1
      ring

end Erdos3.RelativeChangSanders

end

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RelativeSpectrumDimension
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable def realFinsetIndicator {G : Type*} (A : Finset G) (x : G) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

namespace RelativeSpectrumBridge

variable {G : Type*} [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in

theorem sum_realFinsetIndicator_mul_eq_const_mul_card
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) :
    ∑ x : G, realFinsetIndicator X x * w x = c * X.card := by
  classical
  calc
    ∑ x : G, realFinsetIndicator X x * w x = ∑ x ∈ X, c := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realFinsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [realFinsetIndicator, hxX]
    _ = c * X.card := by simp [mul_comm]

end RelativeSpectrumBridge
end Erdos3

end

section

noncomputable section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem card_weightedDissociated_relativeLargeSpectrum_le
    (mu f : G → ℝ) (K eta : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (heta : 0 < eta)
    (hDelta : IsWeightedDissociated mu K Delta)
    (hsub : Delta ⊆ relativeLargeSpectrum mu f eta)
    (hmass : 0 < ∑ x : G, f x * mu x) :
    (Delta.card : ℝ) ≤
      2 * (K + log ((∑ x : G, f x * mu x)⁻¹)) / eta ^ 2 := by
  let a : ℝ := ∑ x : G, f x * mu x
  have ha : 0 < a := by simpa [a] using hmass
  let spec : AddChar G ℂ → ℂ := fun psi ↦
    ∑ x : G, (f x * mu x : ℝ) * psi x
  choose u hu huspec using fun psi : AddChar G ℂ ↦
    Complex.exists_norm_eq_mul_self (spec psi)
  let c : AddChar G ℂ → ℂ := fun psi ↦ (eta : ℂ) * u psi
  let P : G → ℝ := fun x ↦ (∑ psi ∈ Delta, c psi * psi x).re
  have hc_norm (psi : AddChar G ℂ) : ‖c psi‖ ^ 2 = eta ^ 2 := by
    simp [c, hu, abs_of_pos heta]
  have hc_sq : ∑ psi ∈ Delta, ‖c psi‖ ^ 2 = eta ^ 2 * Delta.card := by
    simp_rw [hc_norm]
    simp
    ring
  have hcomplex :
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
        (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
    calc
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
          ∑ psi ∈ Delta,
            c psi * ∑ x : G, ((f x * mu x : ℝ) : ℂ) * psi x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro psi hpsi
        apply sum_congr rfl
        intro x hx
        ring
      _ = ∑ psi ∈ Delta, (eta : ℂ) * (‖spec psi‖ : ℂ) := by
        apply sum_congr rfl
        intro psi hpsi
        dsimp [c, spec]
        rw [mul_assoc, ← huspec]
      _ = (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
        rw [Finset.mul_sum]
  have hmeanP :
      ∑ x : G, f x * mu x * P x =
        eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
    have hre := congrArg Complex.re hcomplex
    calc
      ∑ x : G, f x * mu x * P x =
          (∑ x : G, ((f x * mu x : ℝ) : ℂ) *
            (∑ psi ∈ Delta, c psi * psi x)).re := by
        simp [P, Complex.re_sum, Complex.mul_re]
      _ = ((eta : ℂ) *
          ∑ psi ∈ Delta, (‖spec psi‖ : ℂ)).re := hre
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by simp
  have hmean_lower :
      eta ^ 2 * a * Delta.card ≤ ∑ x : G, f x * mu x * P x := by
    rw [hmeanP]
    calc
      eta ^ 2 * a * (Delta.card : ℝ) =
          ∑ psi ∈ Delta, eta * (eta * a) := by
        simp
        ring
      _ ≤ ∑ psi ∈ Delta, eta * ‖spec psi‖ := by
        gcongr with psi hpsi
        have hs := mem_relativeLargeSpectrum.mp (hsub hpsi)
        simpa [a, spec] using hs
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
        rw [Finset.mul_sum]
  let w : G → ℝ := fun x ↦ f x * mu x / a
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact div_nonneg (mul_nonneg (hf0 x) (hmu x)) ha.le
  have hw_sum : ∑ x : G, w x = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    dsimp [a]
    exact div_self ha.ne'
  have hmean_w : eta ^ 2 * Delta.card ≤ ∑ x : G, w x * P x := by
    calc
      eta ^ 2 * (Delta.card : ℝ) ≤
          (∑ x : G, f x * mu x * P x) / a := by
        rw [le_div_iff₀ ha]
        calc
          eta ^ 2 * (Delta.card : ℝ) * a =
              eta ^ 2 * a * (Delta.card : ℝ) := by ring
          _ ≤ _ := hmean_lower
      _ = ∑ x : G, w x * P x := by
        dsimp [w]
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro x hx
        ring
  have hJensen :
      exp (eta ^ 2 * Delta.card) ≤
        ∑ x : G, w x * exp (P x) := by
    calc
      exp (eta ^ 2 * Delta.card) ≤ exp (∑ x : G, w x * P x) := by
        exact Real.exp_le_exp.mpr hmean_w
      _ ≤ _ := exp_weightedAverage_le_weightedAverage_exp w hw0 hw_sum P
  have hweighted_le :
      ∑ x : G, w x * exp (P x) ≤
        a⁻¹ * ∑ x : G, mu x * exp (P x) := by
    dsimp [w]
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x hx
    rw [div_eq_inv_mul]
    calc
      a⁻¹ * (f x * mu x) * exp (P x) ≤
          a⁻¹ * (1 * mu x) * exp (P x) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
        exact mul_le_mul_of_nonneg_right (hf1 x) (hmu x)
      _ = a⁻¹ * (mu x * exp (P x)) := by ring
  have hRudin :
      ∑ x : G, mu x * exp (P x) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    have hr := weighted_rudin_exp_ineq mu K Delta hmu hDelta c
    simpa [P, hc_sq] using hr
  have hchain :
      exp (eta ^ 2 * Delta.card) ≤
        a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2) :=
    hJensen.trans (hweighted_le.trans
      (mul_le_mul_of_nonneg_left hRudin (inv_nonneg.mpr ha.le)))
  have hmul :
      a * exp (eta ^ 2 * Delta.card) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    calc
      a * exp (eta ^ 2 * Delta.card) ≤
          a * (a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2)) := by
        gcongr
      _ = exp (K + eta ^ 2 * Delta.card / 2) := by
        field_simp
  have hlinear :
      log a + eta ^ 2 * Delta.card ≤
        K + eta ^ 2 * Delta.card / 2 := by
    rw [← exp_log ha, ← exp_add] at hmul
    exact Real.exp_le_exp.mp hmul
  have heta_sq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [le_div_iff₀ heta_sq]
  rw [log_inv]
  nlinarith

end Erdos3.RelativeChangSanders

end

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def massCoeff (w : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, (w x : ℂ) * ψ x

omit [DecidableEq G] in

theorem norm_massCoeff_le_sum {w : G → ℝ} (hw : ∀ x, 0 ≤ w x)
    (ψ : AddChar G ℂ) :
    ‖massCoeff w ψ‖ ≤ ∑ x : G, w x := by
  unfold massCoeff
  calc
    ‖∑ x : G, (w x : ℂ) * ψ x‖ ≤
        ∑ x : G, ‖(w x : ℂ) * ψ x‖ := norm_sum_le _ _
    _ = ∑ x : G, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hw x]

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicRelativeChang
namespace OAI

section

noncomputable section

open _root_.Finset Real
open scoped BigOperators ComplexConjugate

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

def AddDissociatedMod (S Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ t u : Finset (AddChar G ℂ), t ⊆ Delta → u ⊆ Delta →
    Disjoint t u → (t ∪ u).Nonempty →
      (∑ psi ∈ t, psi) - ∑ psi ∈ u, psi ∉ S

omit [Fintype G] in
theorem addDissociatedMod_empty (S : Finset (AddChar G ℂ)) :
    AddDissociatedMod S ∅ := by
  intro t u ht hu htu hne
  simp only [Finset.subset_empty] at ht hu
  subst t
  subst u
  simp at hne

omit [Fintype G] in
theorem AddDissociatedMod.mono {S : Finset (AddChar G ℂ)}
    {Delta Gamma : Finset (AddChar G ℂ)}
    (h : AddDissociatedMod S Delta) (hsub : Gamma ⊆ Delta) :
    AddDissociatedMod S Gamma := by
  intro t u ht hu
  exact h t u (ht.trans hsub) (hu.trans hsub)

omit [Fintype G] in

theorem exists_maximal_addDissociatedMod [Finite G]
    (S T : Finset (AddChar G ℂ))
    (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  let := Fintype.ofFinite G
  classical
  let candidates := T.powerset.filter (AddDissociatedMod S)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, addDissociatedMod_empty]
  obtain ⟨Delta, hDelta_mem, hDelta_max⟩ := candidates.exists_maximal hcandidates
  have hDelta := Finset.mem_filter.mp hDelta_mem
  refine ⟨Delta, Finset.mem_powerset.mp hDelta.1, hDelta.2, ?_⟩
  intro psi hpsiT
  by_cases hpsiDelta : psi ∈ Delta
  · exact ⟨psi, Finset.subset_addSpan hpsiDelta, 0, hzero, by simp⟩
  · have hinsert_subset : insert psi Delta ⊆ T :=
      Finset.insert_subset hpsiT (Finset.mem_powerset.mp hDelta.1)
    have hnot : ¬ AddDissociatedMod S (insert psi Delta) := by
      intro hins
      have hinsert_mem : insert psi Delta ∈ candidates := by
        simp [candidates, hinsert_subset, hins]
      have hsub := hDelta_max hinsert_mem (Finset.subset_insert psi Delta)
      exact hpsiDelta (hsub (Finset.mem_insert_self psi Delta))
    rw [AddDissociatedMod] at hnot
    push Not at hnot
    obtain ⟨t, u, ht, hu, htu, hne, hsumS⟩ := hnot
    have hpsi_tu : psi ∈ t ∪ u := by
      by_contra hpsi
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_left u ha))
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_right t ha))
      exact hDelta.2 t u htDelta huDelta htu hne hsumS
    rw [Finset.mem_union] at hpsi_tu
    rcases hpsi_tu with hpsi_t | hpsi_u
    · have hpsi_not_u : psi ∉ u := fun h ↦ Finset.disjoint_left.mp htu hpsi_t h
      have htErase : t.erase psi ⊆ Delta := by
        intro a ha
        have ha' := ht (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_u (h ▸ ha))
      let z := (∑ a ∈ u, a) - ∑ a ∈ t.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan huDelta htErase
      refine ⟨z, hz, (∑ a ∈ t, a) - ∑ a ∈ u, a, hsumS, ?_⟩
      dsimp [z]
      rw [← Finset.sum_erase_add _ _ hpsi_t]
      abel
    · have hpsi_not_t : psi ∉ t := fun h ↦ Finset.disjoint_left.mp htu h hpsi_u
      have huErase : u.erase psi ⊆ Delta := by
        intro a ha
        have ha' := hu (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_t (h ▸ ha))
      let z := (∑ a ∈ t, a) - ∑ a ∈ u.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan htDelta huErase
      let s := -((∑ a ∈ t, a) - ∑ a ∈ u, a)
      have hs : s ∈ S := hS _ hsumS
      refine ⟨z, hz, s, hs, ?_⟩
      dsimp [z, s]
      rw [← Finset.sum_erase_add _ _ hpsi_u]
      abel

omit [Fintype G] in

theorem exists_maximal_addDissociatedMod_card_le [Finite G]
    (S T : Finset (AddChar G ℂ)) (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) (D : ℝ) (k : ℕ)
    (hDk : D < k)
    (hdim : ∀ Gamma : Finset (AddChar G ℂ), Gamma ⊆ T →
      AddDissociatedMod S Gamma → Gamma.card ≤ k →
        (Gamma.card : ℝ) ≤ D) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        (Delta.card : ℝ) ≤ D ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  let := Fintype.ofFinite G
  obtain ⟨Delta, hDeltaT, hDelta, hcover⟩ :=
    exists_maximal_addDissociatedMod S T hzero hS
  have hcard : Delta.card ≤ k := by
    by_contra hnot
    have hkDelta : k ≤ Delta.card := Nat.le_of_lt (Nat.lt_of_not_ge hnot)
    obtain ⟨Gamma, hGammaDelta, hGammaCard⟩ :=
      Finset.exists_subset_card_eq hkDelta
    have hGammaReal : (Gamma.card : ℝ) ≤ D :=
      hdim Gamma (hGammaDelta.trans hDeltaT) (hDelta.mono hGammaDelta)
        (by omega)
    have hkD : (k : ℝ) ≤ D := by simpa [hGammaCard] using hGammaReal
    exact (not_le_of_gt hDk) hkD
  exact ⟨Delta, hDeltaT, hDelta, hdim Delta hDeltaT hDelta hcard, hcover⟩

def signedFrequency (t u : Finset (AddChar G ℂ)) : AddChar G ℂ :=
  (∑ psi ∈ u, psi) - ∑ psi ∈ t \ u, psi

def signedCoefficient (v : AddChar G ℂ → ℂ)
    (t u : Finset (AddChar G ℂ)) : ℂ :=
  ((∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)) /
    (2 : ℂ) ^ t.card

omit [Fintype G] in
lemma rieszProduct_eq_signedExpansion [Finite G]
    (Delta : Finset (AddChar G ℂ)) (v : AddChar G ℂ → ℂ) (x : G) :
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
  let := Fintype.ofFinite G
  calc
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
        ∏ psi ∈ Delta,
          (((v psi * psi x) + conj (v psi * psi x)) / 2 + 1) := by
      apply Finset.prod_congr rfl
      intro psi hpsi
      rw [add_comm, ← Complex.re_eq_add_conj]
      push_cast
      rfl
    _ = ∑ t ∈ Delta.powerset,
        ∏ psi ∈ t, ((v psi * psi x) + conj (v psi * psi x)) / 2 := by
      rw [Finset.prod_add]
      simp
    _ = ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_div_distrib]
      rw [Finset.prod_add]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      rw [signedCoefficient, signedFrequency]
      simp only [AddChar.sum_apply, AddChar.sub_apply,
        AddChar.map_neg_eq_conj]
      simp only [Finset.prod_const]
      simp_rw [map_mul, Finset.prod_mul_distrib]
      rw [map_prod]
      ring

lemma weightedRiesz_eq_signedExpansion
    (w : G → ℝ) (Delta : Finset (AddChar G ℂ))
    (v : AddChar G ℂ → ℂ) :
    ((∑ x : G, w x *
        ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u *
          Erdos3.massCoeff w (signedFrequency t u) := by
  simp_rw [Complex.ofReal_prod]
  simp_rw [rieszProduct_eq_signedExpansion]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Erdos3.massCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

omit [Fintype G] in
lemma signedFrequency_not_mem
    {S Delta t u : Finset (AddChar G ℂ)}
    (hDelta : AddDissociatedMod S Delta)
    (ht : t ⊆ Delta) (ht0 : t.Nonempty) (hu : u ⊆ t) :
    signedFrequency t u ∉ S := by
  apply hDelta u (t \ u)
  · exact hu.trans ht
  · exact Finset.sdiff_subset.trans ht
  · rw [Finset.disjoint_left]
    intro psi hpsiu hpsitu
    exact (Finset.mem_sdiff.mp hpsitu).2 hpsiu
  · simpa [Finset.union_sdiff_of_subset hu] using ht0

omit [Fintype G] in
lemma norm_signedCoefficient_le
    {v : AddChar G ℂ → ℂ} {t u : Finset (AddChar G ℂ)}
    (hu : u ⊆ t) (hv : ∀ psi ∈ t, ‖v psi‖ ≤ 1) :
    ‖signedCoefficient v t u‖ ≤ ((2 : ℝ) ^ t.card)⁻¹ := by
  have hvu : ‖∏ psi ∈ u, v psi‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ hv psi (hu hpsi))
  have hvtu : ‖∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ by
        rw [RCLike.norm_conj]
        exact hv psi (Finset.sdiff_subset hpsi))
  have hnum :
      ‖(∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul hvu hvtu (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  rw [signedCoefficient, norm_div]
  calc
    _ ≤ 1 / ‖(2 : ℂ) ^ t.card‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = ((2 : ℝ) ^ t.card)⁻¹ := by
      rw [norm_pow]
      norm_num

theorem AddDissociatedMod.weighted_riesz_randomisation_le
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ}
    (hDelta : AddDissociatedMod S Delta)
    (_hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (v : AddChar G ℂ → ℂ) (hv : ∀ psi ∈ Delta, ‖v psi‖ ≤ 1) :
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
      1 + q * (2 : ℝ) ^ Delta.card := by
  classical
  let F : Finset (AddChar G ℂ) → ℂ := fun t ↦
    ∑ u ∈ t.powerset, signedCoefficient v t u *
      Erdos3.massCoeff w (signedFrequency t u)
  let E : ℂ := ∑ t ∈ Delta.powerset.erase ∅, F t
  have hempty : (∅ : Finset (AddChar G ℂ)) ∈ Delta.powerset := by simp
  have hw1c : ∑ x : G, (w x : ℂ) = 1 := by exact_mod_cast hw1
  have hFempty : F ∅ = 1 := by
    simp [F, signedCoefficient, signedFrequency, Erdos3.massCoeff, hw1c]
  have hexp :
      ((∑ x : G, w x *
          ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) = 1 + E := by
    rw [weightedRiesz_eq_signedExpansion]
    rw [← Finset.sum_erase_add _ _ hempty]
    simp only [hFempty, E, F]
    ring
  have hinner (t : Finset (AddChar G ℂ))
      (ht : t ∈ Delta.powerset.erase ∅) : ‖F t‖ ≤ q := by
    have htDelta : t ⊆ Delta := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have ht0 : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    calc
      ‖F t‖ ≤ ∑ u ∈ t.powerset,
          ‖signedCoefficient v t u *
            Erdos3.massCoeff w (signedFrequency t u)‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ _u ∈ t.powerset, ((2 : ℝ) ^ t.card)⁻¹ * q := by
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul]
        apply mul_le_mul
        · exact norm_signedCoefficient_le (Finset.mem_powerset.mp hu)
            (fun psi hpsi ↦ hv psi (htDelta hpsi))
        · exact hq _ (signedFrequency_not_mem hDelta htDelta ht0
            (Finset.mem_powerset.mp hu))
        · exact norm_nonneg _
        · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
      _ = q := by
        rw [Finset.sum_const, Finset.card_powerset]
        simp [nsmul_eq_mul]
  have hEnorm : ‖E‖ ≤ q * (2 : ℝ) ^ Delta.card := by
    calc
      ‖E‖ ≤ ∑ t ∈ Delta.powerset.erase ∅, ‖F t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ Delta.powerset.erase ∅, q := by
        exact Finset.sum_le_sum fun t ht ↦ hinner t ht
      _ ≤ ∑ _t ∈ Delta.powerset, q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ ↦ hq0)
      _ = q * (2 : ℝ) ^ Delta.card := by
        simp [Finset.card_powerset]
        ring
  let R : ℝ :=
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re)
  have hexpR : (R : ℂ) = 1 + E := by
    calc
      (R : ℂ) = ∑ x : G, (w x : ℂ) *
          (↑(∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) := by
        dsimp [R]
        push_cast
        rfl
      _ = 1 + E := hexp
  have hre : R = 1 + E.re := by
    have := congrArg Complex.re hexpR
    simpa using this
  change R ≤ 1 + q * (2 : ℝ) ^ Delta.card
  calc
    R = 1 + E.re := hre
    _ ≤ 1 + ‖E‖ := add_le_add (le_refl 1) (Complex.re_le_norm E)
    _ ≤ 1 + q * (2 : ℝ) ^ Delta.card := add_le_add (le_refl 1) hEnorm

theorem AddDissociatedMod.isWeightedDissociated
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hqk : q * (2 : ℝ) ^ k ≤ 1) :
    IsWeightedDissociated w 1 Delta := by
  intro v hv
  have hpowNat : 2 ^ Delta.card ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by norm_num) hcard
  have hpow : (2 : ℝ) ^ Delta.card ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hpowNat
  have htail : q * (2 : ℝ) ^ Delta.card ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow hq0).trans hqk
  calc
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
        1 + q * (2 : ℝ) ^ Delta.card :=
      hDelta.weighted_riesz_randomisation_le hw0 hw1 hq0 hq v hv
    _ ≤ 2 := by linarith
    _ ≤ exp 1 := Real.exp_one_gt_two.le

theorem AddDissociatedMod.isWeightedDissociated_of_le_quarter_pow
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hq_quarter : q ≤ (1 / 4 : ℝ) ^ k) :
    IsWeightedDissociated w 1 Delta := by
  apply hDelta.isWeightedDissociated hw0 hw1 hq0 hq hcard
  calc
    q * (2 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hq_quarter (pow_nonneg (by norm_num) _)
    _ = (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; congr 1; norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

end Erdos3.RelativeChangSanders

end

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
namespace OAI

section

namespace Erdos3

variable {X : Type*}

def FiniteTupleDependsOn (s : ℕ → Bool) (n : ℕ) (f : (Fin n → X) → ℝ) : Prop :=
  ∀ v u, (∀ i : Fin n, s i = true → v i = u i) → f v = f u

theorem FiniteTupleDependsOn.snoc {s : ℕ → Bool} {n : ℕ}
    {f : (Fin (n + 1) → X) → ℝ} (hf : FiniteTupleDependsOn s (n + 1) f)
    {v u : Fin n → X} {a b : X}
    (hvu : ∀ i : Fin n, s i = true → v i = u i) (hab : s n = true → a = b) :
    f (Fin.snoc v a) = f (Fin.snoc u b) := by
  apply hf
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro hs
    simpa only [Fin.snoc_last] using hab hs
  · intro hs
    simpa only [Fin.snoc_castSucc] using hvu j hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteSamplingMoment
namespace OAI

section

namespace Erdos3.CyclicMZ

open _root_.Finset Fintype Nat

variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

lemma step_one (hA : A.Nonempty) (f : ι → ℝ) (a : Fin n → ι)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #A ^ n := by
  let B := A ^^ n
  calc
    |∑ i, f (a i)| ^ (m + 1) =
        |∑ i, (f (a i) - (∑ b ∈ B, f (b i)) / #B)| ^ (m + 1) := by
      simp only [B, hf, sub_zero, zero_div]
    _ = |(∑ b ∈ B, ∑ i, (f (a i) - f (b i))) / #B| ^ (m + 1) := by
      simp only [sum_sub_distrib]
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      positivity
    _ = |∑ b ∈ B, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / #B ^ (m + 1) := by
      rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ (m + 1) := by
      gcongr
      exact IsAbsoluteValue.abv_sum _ _ _
    _ = (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ m / #B := by
      rw [div_div, ← _root_.pow_succ]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #B := by
      gcongr
      exact pow_sum_div_card_le_sum_pow (fun _ _ ↦ abs_nonneg _) _
    _ = _ := by simp [B]

lemma step_one' (hA : A.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) (m : ℕ) (a : Fin n → ι) :
    |∑ i, f (a i)| ^ m ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ m) / #A ^ n := by
  cases m
  · simp only [_root_.pow_zero, sum_const, prod_const, Nat.smul_one_eq_cast,
      Finset.card_fin, card_piFinset, ← Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  exact step_one hA f a hf

lemma step_two_aux (A : Finset ι) (f : ι → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ) ^^ n) (g : (Fin n → ℝ) → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (f ∘ a - f ∘ b) := by
  rw [← sum_product', ← sum_product']
  let swapper : (Fin n → ι) × (Fin n → ι) → (Fin n → ι) × (Fin n → ι) := by
    intro xy
    exact (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i,
      fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper a ∈ (A ^^ n) ×ˢ (A ^^ n) := by
    simp only [mem_product, mem_piFinset, ← forall_and, swapper]
    intro a h i
    split_ifs
    · exact h i
    · exact (h i).symm
  have h₂ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only [swapper] <;> split_ifs <;> rfl
  refine sum_nbij' swapper swapper h₁ h₁ h₂ h₂ ?_
  rintro ⟨a, b⟩ _
  congr with i : 1
  simp only [mem_piFinset, mem_insert, mem_singleton] at hε
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, swapper]
  split_ifs with h
  · simp [h]
  rw [(hε i).resolve_right h]
  ring

lemma step_two (f : ι → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ n * ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
        ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  let B := A ^^ n
  have h : ∀ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
      ∑ a ∈ B, ∑ b ∈ B, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
        ∑ a ∈ B, ∑ b ∈ B, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ step_two_aux A f _ hε fun z : Fin n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl h, sum_const, card_piFinset_const, card_pair, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

lemma step_three (f : ι → ℝ) :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
        (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ (2 * m),
        (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
          ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A ^^ n), sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun a _ ↦ ?_
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ), ← mul_sum, ← sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, mul_right_comm]

lemma step_four {k : Fin n → ℕ} :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t =
      2 ^ n * ite (∀ i, Even (k i)) 1 0 := by
  calc
    _ = ∏ i, ∑ j ∈ ({-1, 1} : Finset ℝ), j ^ k i := by rw [← sum_prod_piFinset]
    _ = ∏ i, if Even (k i) then 2 else 0 := by
      congr with i
      split_ifs <;> simp_all [sum_pair (show (-1 : ℝ) ≠ 1 by norm_num), one_add_one_eq_two]
    _ = _ := by simp [Fintype.prod_ite_zero]

namespace Real

attribute [-instance] decidableForallFin

end Real

end Erdos3.CyclicMZ

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalShiftFiber
namespace OAI

section

namespace Erdos3

open _root_.Finset Fintype
open scoped BigOperators Pointwise

namespace CyclicCrootSisask

variable {N k m : ℕ} [NeZero N]

lemma markov_card_good
    {ι : Type*} {S : Finset ι} {g : ι → ℝ} {c ε : ℝ}
    (hc : 0 < c) (hg : ∀ a ∈ S, 0 ≤ g a)
    (h : ∑ a ∈ S, g a ≤ ε * c * S.card) :
    (1 - ε) * S.card ≤ (S.filter fun a ↦ g a ≤ c).card := by
  classical
  have hbad := h.trans'
    (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun a ↦ ¬g a ≤ c) S) fun i hi _ ↦ hg i hi)
  have hcount :=
    (Finset.card_nsmul_le_sum (S.filter fun a ↦ ¬g a ≤ c) g c
      (by simp +contextual [le_of_lt])).trans hbad
  rw [nsmul_eq_mul, mul_right_comm] at hcount
  have hcount' := le_of_mul_le_mul_right hcount hc
  rw [Finset.filter_not, Finset.cast_card_sdiff (Finset.filter_subset _ _)] at hcount'
  linarith

end CyclicCrootSisask
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalBoostedAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

theorem half_card_le_filter_of_sum_le {ι : Type*} (S : Finset ι) (g : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ a ∈ S, 0 ≤ g a)
    (htotal : ∑ a ∈ S, g a ≤ (1 / 2 : ℝ) * C * S.card) :
    (S.card : ℝ) / 2 ≤ (S.filter (fun a => g a ≤ C)).card := by
  classical
  by_cases hpos : 0 < C
  · have h := markov_card_good hpos hg htotal
    norm_num at h
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using h
  · have hzero : C = 0 := le_antisymm (not_lt.mp hpos) hC
    have hsum : ∑ a ∈ S, g a = 0 := by
      apply le_antisymm
      · simpa only [hzero, mul_zero, zero_mul] using htotal
      · exact Finset.sum_nonneg hg
    have hpoint := (Finset.sum_eq_zero_iff_of_nonneg hg).mp hsum
    have hfilter : S.filter (fun a => g a ≤ C) = S := by
      apply Finset.filter_eq_self.mpr
      intro a ha
      rw [hpoint a ha, hzero]
    rw [hfilter]
    have : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    linarith

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem old_frequency_scale_le_regularity {epsilon p d : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p) (hd : 0 < d) :
    epsilon * Real.exp (-p) / (6400 * d) ≤ 1 / (200 * d) := by
  have he : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hprod : epsilon * Real.exp (-p) ≤ 1 :=
    (mul_le_mul_of_nonneg_left he hepsilon).trans (by simpa using hepsilon1)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

def residueStepMatrix {I : Type*} [DecidableEq I] (J : I → ℕ) : I → I → ℤ :=
  fun i j => if i = j then (J i : ℤ) else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_fiber_set (F : ∀ j, X j → R j) (r : ∀ j, R j) :
    (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) =
      piRestrictionSet (fun j => Finset.univ.filter (fun x => F j x = r j)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_piRestrictionSet, funext_iff]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealGeneratorCombinations
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix

variable {ι κ V : Type*} [Fintype κ] [AddCommGroup V] [Module ℚ V]

noncomputable def realGeneratorCombination (v : κ → V) (a : κ → ℝ) : ℝ ⊗[ℚ] V :=
  ∑ j, a j ⊗ₜ[ℚ] v j

theorem realGeneratorCombination_mem (U : Submodule ℚ V) (v : κ → V)
    (hv : ∀ j, v j ∈ U) (a : κ → ℝ) : realGeneratorCombination v a ∈ U.baseChange ℝ := by
  classical
  exact Submodule.sum_mem _ (fun j _ => Submodule.tmul_mem_baseChange_of_mem (a j) (hv j))

theorem realGeneratorCombination_coordinates [Fintype ι] (b : Basis ι ℚ V)
    (v : κ → V) (a : κ → ℝ) :
    (b.baseChange ℝ).equivFun (realGeneratorCombination v a) =
      (fun i j => (b.repr (v j) i : ℝ)) *ᵥ a := by
  classical
  funext i
  simp only [realGeneratorCombination, map_sum, Basis.equivFun_apply, Finset.sum_apply,
    Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, Rat.smul_def]

theorem realGeneratorCombination_map_coordinates [Fintype ι]
    (φ : V →ₗ[ℚ] (ι → ℚ)) (v : κ → V) (a : κ → ℝ) :
    realRationalCoordinateEquiv (φ.baseChange ℝ (realGeneratorCombination v a)) =
      (fun i j => (φ (v j) i : ℝ)) *ᵥ a := by
  classical
  funext i
  simp only [realGeneratorCombination, map_sum, Finset.sum_apply, LinearMap.baseChange_tmul,
    realRationalCoordinateEquiv_tmul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

noncomputable def correlationExponent (h n : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 h + Finsupp.single 1 n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def finsetIndicator {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α) : ℝ :=
  if x ∈ A then 1 else 0

@[simp]
theorem finsetIndicator_of_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by
  simp [finsetIndicator, hx]

@[simp]
theorem finsetIndicator_of_not_mem {α : Type*} [DecidableEq α]
    {A : Finset α} {x : α} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by
  simp [finsetIndicator, hx]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) : ℝ :=
  Finset.expect (P.part x) f

theorem conditionalMean_eq_of_part_eq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hxy : P.part x = P.part y) :
    conditionalMean P f x = conditionalMean P f y := by
  rw [conditionalMean, conditionalMean, hxy]

theorem conditionalMean_eq_of_mem_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hy : y ∈ P.part x) :
    conditionalMean P f y = conditionalMean P f x := by
  apply conditionalMean_eq_of_part_eq
  apply P.part_eq_of_mem
  · simp
  · exact hy

theorem conditionalMean_sub {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => f y - g y) x =
      conditionalMean P f x - conditionalMean P g x := by
  exact Finset.expect_sub_distrib (P.part x) f g

@[simp]
theorem conditionalMean_const {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (x : Ω) :
    conditionalMean P (fun _ => c) x = c := by
  rw [conditionalMean]
  exact Finset.expect_const (by simp) c

@[simp]
theorem conditionalMean_idem {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean P f) x =
      conditionalMean P f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean P f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean P f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part P f hy
    _ = conditionalMean P f x :=
      Finset.expect_const (by simp) _

theorem sum_conditionalMean_on_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ P.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ s, Finset.expect s f := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [conditionalMean, P.part_eq_of_mem hs hx]
    _ = (s.card : ℝ) * Finset.expect s f := by
      simp
    _ = ∑ x ∈ s, f x := Finset.card_mul_expect s f

theorem sum_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    ∑ x, conditionalMean P f x = ∑ x, f x := by
  classical
  have hparts :
      P.parts.biUnion id = (Finset.univ : Finset Ω) :=
    P.biUnion_parts
  calc
    ∑ x, conditionalMean P f x =
        ∑ x ∈ P.parts.biUnion id, conditionalMean P f x := by
      exact Finset.sum_congr hparts.symm fun _ _ => rfl
    _ =
        ∑ s ∈ P.parts, ∑ x ∈ s, conditionalMean P f x := by
      exact Finset.sum_biUnion P.disjoint
    _ = ∑ s ∈ P.parts, ∑ x ∈ s, f x := by
      apply Finset.sum_congr rfl
      intro s hs
      exact sum_conditionalMean_on_part P f hs
    _ = ∑ x ∈ P.parts.biUnion id, f x :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ x, f x := by
      exact Finset.sum_congr hparts fun _ _ => rfl

theorem conditionalMean_sq_le {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P f x ^ 2 ≤
      conditionalMean P (fun y => f y ^ 2) x := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      (P.part x) f (fun _ : Ω => (1 : ℝ))
  simpa [conditionalMean,
    Finset.expect_const (s := P.part x) (by simp) (1 : ℝ)] using h

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

abbrev FacePartition (Ω : Type*) [Fintype Ω] [DecidableEq Ω] :=
  Finpartition (Finset.univ : Finset Ω)

namespace FacePartition

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem part_subset_of_le {P Q : FacePartition Ω}
    (h : P ≤ Q) (x : Ω) :
    P.part x ⊆ Q.part x := by
  obtain ⟨s, hs, hsub⟩ :=
    h (P.part_mem.2 (Finset.mem_univ x))
  have hxs : x ∈ s :=
    hsub (P.mem_part (Finset.mem_univ x))
  rw [Q.part_eq_of_mem hs hxs]
  exact hsub

def indiscrete : FacePartition Ω :=
  ⊤

@[simp]
theorem part_indiscrete (x : Ω) :
    (indiscrete : FacePartition Ω).part x = Finset.univ := by
  change (⊤ : FacePartition Ω).part x = Finset.univ
  have hmem :
      (⊤ : FacePartition Ω).part x ∈
        (⊤ : FacePartition Ω).parts :=
    (⊤ : FacePartition Ω).part_mem.2 (Finset.mem_univ x)
  exact Finset.mem_singleton.mp
    (Finpartition.parts_top_subset
      (Finset.univ : Finset Ω) hmem)

def complexity (P : FacePartition Ω) : ℕ :=
  P.parts.card

@[simp]
theorem complexity_indiscrete [Nonempty Ω] :
    complexity (indiscrete : FacePartition Ω) = 1 := by
  let x : Ω := Classical.choice inferInstance
  have huniv :
      (Finset.univ : Finset Ω) ∈
        (⊤ : FacePartition Ω).parts := by
    have hx :=
      (⊤ : FacePartition Ω).part_mem.2
        (Finset.mem_univ x)
    change
      (indiscrete : FacePartition Ω).part x ∈
        (indiscrete : FacePartition Ω).parts at hx
    rw [part_indiscrete] at hx
    exact hx
  have hparts :
      (⊤ : FacePartition Ω).parts =
        {(Finset.univ : Finset Ω)} := by
    apply Finset.Subset.antisymm
    · exact Finpartition.parts_top_subset _
    · intro s hs
      rw [Finset.mem_singleton] at hs
      simpa [hs] using huniv
  simp [complexity, indiscrete, hparts]

def join (P Q : FacePartition Ω) : FacePartition Ω :=
  P ⊓ Q

theorem join_le_right (P Q : FacePartition Ω) :
    join P Q ≤ Q :=
  inf_le_right

@[simp]
theorem part_join (P Q : FacePartition Ω) (x : Ω) :
    (join P Q).part x = P.part x ∩ Q.part x := by
  apply Finpartition.part_eq_of_mem
  · rw [join, Finpartition.parts_inf]
    apply Finset.mem_erase.mpr
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, by simp⟩
    · apply Finset.mem_image.mpr
      refine ⟨(P.part x, Q.part x), ?_, rfl⟩
      simp
  · simp

def joinFinset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → FacePartition Ω) :
    FacePartition Ω :=
  s.inf P

@[simp]
theorem joinFinset_empty {ι : Type*} [DecidableEq ι]
    (P : ι → FacePartition Ω) :
    joinFinset ∅ P = indiscrete :=
  rfl

@[simp]
theorem joinFinset_insert {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (P : ι → FacePartition Ω) :
    joinFinset (insert a s) P =
      join (P a) (joinFinset s P) := by
  simp [joinFinset, join]

def generatedBy (F : Finset (Finset Ω)) : FacePartition Ω :=
  Finpartition.atomise Finset.univ F

@[simp]
theorem mem_part_generatedBy_iff (F : Finset (Finset Ω))
    (x y : Ω) :
    y ∈ (generatedBy F).part x ↔
      ∀ s ∈ F, (x ∈ s ↔ y ∈ s) := by
  classical
  let P : FacePartition Ω := generatedBy F
  have hp : P.part x ∈ P.parts :=
    P.part_mem.2 (Finset.mem_univ x)
  have hpAtom :
      P.part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts := by
    change
      (Finpartition.atomise
        (Finset.univ : Finset Ω) F).part x ∈
        (Finpartition.atomise
          (Finset.univ : Finset Ω) F).parts at hp
    exact hp
  obtain ⟨_, Q, hQ, hpart⟩ :=
    Finpartition.mem_atomise.mp hpAtom
  have hmem := Finset.ext_iff.mp hpart
  have hx : x ∈ P.part x :=
    P.mem_part (Finset.mem_univ x)
  have hxAtom := (hmem x).2 hx
  simp only [Finset.mem_filter] at hxAtom
  constructor
  · intro hy s hs
    have hyAtom := (hmem y).2 hy
    simp only [Finset.mem_filter] at hyAtom
    exact (hxAtom.2 s hs).symm.trans (hyAtom.2 s hs)
  · intro hsignature
    apply (hmem y).1
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ y, ?_⟩
    intro s hs
    exact (hxAtom.2 s hs).trans (hsignature s hs)

theorem complexity_generatedBy_le (F : Finset (Finset Ω)) :
    complexity (generatedBy F) ≤ 2 ^ F.card := by
  exact Finpartition.card_atomise_le

def pullbackSetoid {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : Setoid Ω where
  r x y := Q.part (f x) = Q.part (f y)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

instance instDecidableRelPullbackSetoid {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) :
    DecidableRel (pullbackSetoid f Q) := by
  intro x y
  change Decidable (Q.part (f x) = Q.part (f y))
  infer_instance

def pullback {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) : FacePartition Ω :=
  Finpartition.ofSetoid (pullbackSetoid f Q)

@[simp]
theorem mem_part_pullback_iff {Λ : Type*}
    [Fintype Λ] [DecidableEq Λ]
    (f : Ω → Λ) (Q : FacePartition Λ) (x y : Ω) :
    y ∈ (pullback f Q).part x ↔
      Q.part (f x) = Q.part (f y) := by
  change
    y ∈
        (Finpartition.ofSetoid
          (pullbackSetoid f Q)).part x ↔
      Q.part (f x) = Q.part (f y)
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

end FacePartition

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem sum_conditionalMean_on_coarser_part
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ Q.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  let fineParts : Finset (Finset Ω) :=
    P.parts.filter (fun t => t ⊆ s)
  have hUnion : fineParts.biUnion id = s := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp ht).2 hxt
    · intro hxs
      obtain ⟨t, ht, hxt⟩ :=
        P.exists_mem (Finset.mem_univ x)
      obtain ⟨u, hu, htu⟩ := hPQ ht
      have hus : u = s :=
        Q.eq_of_mem_parts hu hs (htu hxt) hxs
      have hts : t ⊆ s := by
        simpa [hus] using htu
      exact Finset.mem_biUnion.mpr
        ⟨t, Finset.mem_filter.mpr ⟨ht, hts⟩, hxt⟩
  have hdisjoint :
      (↑fineParts : Set (Finset Ω)).PairwiseDisjoint id := by
    apply Set.Pairwise.mono ?_ P.disjoint
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ fineParts.biUnion id,
          conditionalMean P f x := by
      exact Finset.sum_congr hUnion.symm fun _ _ => rfl
    _ =
        ∑ t ∈ fineParts,
          ∑ x ∈ t, conditionalMean P f x :=
      Finset.sum_biUnion hdisjoint
    _ = ∑ t ∈ fineParts, ∑ x ∈ t, f x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact sum_conditionalMean_on_part P f
        (Finset.mem_filter.mp ht).1
    _ = ∑ x ∈ fineParts.biUnion id, f x :=
      (Finset.sum_biUnion hdisjoint).symm
    _ = ∑ x ∈ s, f x := by
      exact Finset.sum_congr hUnion fun _ _ => rfl

@[simp]
theorem conditionalMean_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean Q (conditionalMean P f) x =
      conditionalMean Q f x := by
  change
    Finset.expect (Q.part x) (conditionalMean P f) =
      Finset.expect (Q.part x) f
  rw [Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card,
    sum_conditionalMean_on_coarser_part P Q hPQ f
      (Q.part_mem.2 (Finset.mem_univ x))]

@[simp]
theorem conditionalMean_reverse_tower_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean Q f) x =
      conditionalMean Q f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean Q f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean Q f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part Q f
        (FacePartition.part_subset_of_le hPQ x hy)
    _ = conditionalMean Q f x :=
      Finset.expect_const (by simp) _

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleUniversalMaskProductiveGood
namespace OAI

section

namespace Erdos3

structure FinitePrecenterInputFamily (X : Type*) (p countLog : ℝ) where
  Branch : Type
  [branchFintype : Fintype Branch]
  input : Branch → X → ℂ
  norm : ∀ branch x, ‖input branch x‖ ≤ Real.exp p
  card : (Fintype.card Branch : ℝ) ≤ Real.exp countLog

attribute [instance] FinitePrecenterInputFamily.branchFintype

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.LinearFormsBasic
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure AffineForm (ι R : Type*) [Zero R] where
  constant : R
  coefficient : ι → R

namespace AffineForm

def eval {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) (x : ι → R) : R :=
  ψ.constant + ∑ i, ψ.coefficient i * x i

@[simp]
theorem eval_zero {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) :
    ψ.eval (fun _ => 0) = ψ.constant := by
  simp [eval]

end AffineForm

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SimplexTelescoping
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev DeletedVector {k : ℕ} (V : Fin k → Type*) (j : Fin k) :=
  (i : {i : Fin k // i ≠ j}) → V i.1

def deleteCoordinate {k : ℕ} {V : Fin k → Type*}
    (x : (i : Fin k) → V i) (j : Fin k) :
    DeletedVector V j :=
  fun i => x i.1

structure WeightedSimplexSystem {k : ℕ} (V : Fin k → Type*) where
  edgeWeight : (j : Fin k) → DeletedVector V j → ℝ

def apSimplexForm (k N : ℕ) (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i

def simplexCoordinateSum (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, x i

def simplexCoordinateMoment (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, (i : ZMod N) * x i

theorem apSimplexForm_deleteCoordinate (k N : ℕ) (j : Fin k)
    (x : Fin k → ZMod N) :
    apSimplexForm k N j (deleteCoordinate x j) =
      simplexCoordinateMoment k N x -
        (j : ZMod N) * simplexCoordinateSum k N x := by
  classical
  let f : Fin k → ZMod N :=
    fun i => (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i ≠ j) f
  have hcomplement :
      (∑ i : {i : Fin k // ¬i ≠ j}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i
    simp only [Finset.mem_univ, forall_const]
    have hij : i.1 = j := not_ne_iff.mp i.2
    rw [hij]
    simp [f]
  have hsum : (∑ i : {i : Fin k // i ≠ j}, f i.1) = ∑ i : Fin k, f i := by
    rw [hcomplement, add_zero] at hsplit
    exact hsplit
  rw [apSimplexForm]
  change (∑ i : {i : Fin k // i ≠ j}, f i.1) =
    simplexCoordinateMoment k N x -
      (j : ZMod N) * simplexCoordinateSum k N x
  rw [hsum]
  simp only [simplexCoordinateMoment, simplexCoordinateSum, f]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def simplexTailSum (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, y i

def simplexTailMoment (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, (i.succ.succ : ZMod N) * y i

def simplexCoordinatesOfAP (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) : Fin (r + 2) → ZMod N :=
  Fin.cases
    (simplexTailMoment r N y - a - d - simplexTailSum r N y)
    (Fin.cases (a - simplexTailMoment r N y) y)

@[simp]
theorem simplexCoordinatesOfAP_zero (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 0 =
      simplexTailMoment r N y - a - d - simplexTailSum r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_one (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 1 =
      a - simplexTailMoment r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_succ_succ (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) (i : Fin r) :
    simplexCoordinatesOfAP r N a d y i.succ.succ = y i :=
  rfl

theorem simplexCoordinateSum_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateSum (r + 2) N x =
      x 0 + x 1 +
        simplexTailSum r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateSum, simplexTailSum, Fin.sum_univ_succ,
    add_assoc]

theorem simplexCoordinateMoment_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateMoment (r + 2) N x =
      x 1 + simplexTailMoment r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateMoment, simplexTailMoment,
    Fin.sum_univ_succ]

@[simp]
theorem simplexCoordinateSum_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateSum (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = -d := by
  rw [simplexCoordinateSum_decompose]
  simp
  ring

@[simp]
theorem simplexCoordinateMoment_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateMoment (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = a := by
  rw [simplexCoordinateMoment_decompose]
  simp

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure SimplexHypergraph {k : ℕ} (V : Fin k → Type*) where
  edge : (j : Fin k) → DeletedVector V j → Prop

namespace SimplexHypergraph

noncomputable def edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k) :
    Finset (DeletedVector V j) := by
  classical
  exact Finset.univ.filter (H.edge j)

@[simp]
theorem mem_edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k)
    (x : DeletedVector V j) :
    x ∈ H.edgeFinset j ↔ H.edge j x := by
  classical
  simp [edgeFinset]

noncomputable def simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    Finset ((i : Fin k) → V i) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, H.edge j (deleteCoordinate x j)

@[simp]
theorem mem_simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    x ∈ H.simplexFinset ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  classical
  simp [simplexFinset]

noncomputable def toWeighted {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) : WeightedSimplexSystem V := by
  classical
  exact
    { edgeWeight := fun j x => if H.edge j x then 1 else 0 }

@[simp]
theorem toWeighted_edgeWeight_of_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : H.edge j x) :
    H.toWeighted.edgeWeight j x = 1 := by
  classical
  simp [toWeighted, hx]

@[simp]
theorem toWeighted_edgeWeight_of_not_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : ¬H.edge j x) :
    H.toWeighted.edgeWeight j x = 0 := by
  classical
  simp [toWeighted, hx]

def IsSimplexCover {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) : Prop :=
  ∀ x ∈ H.simplexFinset,
    ∃ j, deleteCoordinate x j ∈ deleted j

end SimplexHypergraph

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def eraseCoordinate {G : Type*} {r : ℕ}
    (i : Fin r) (x : Fin r → G) : Fin (r - 1) → G := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => exact fun j => x (i.succAbove j)

@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl

@[simp]
theorem eraseCoordinate_insertNth {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (a : G) (x : Fin n → G) :
    eraseCoordinate i (Fin.insertNth i a x) = x := by
  funext j
  simp only [eraseCoordinate_apply, Fin.insertNth_apply_succAbove]

abbrev CutTestFamily (G : Type*) (r : ℕ) :=
  (i : Fin r) → (Fin (r - 1) → G) → ℝ

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def finSuccAboveEquiv {n : ℕ} (j : Fin (n + 1)) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ j} :=
  Equiv.ofBijective
    (fun t : Fin n => ⟨j.succAbove t, Fin.succAbove_ne j t⟩)
    ⟨by
      intro a b hab
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val hab,
    by
      intro i
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq i.2
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl

noncomputable def finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G) :
    DeletedVector (fun _ : Fin (n + 1) => G) j :=
  fun i => y ((finSuccAboveEquiv j).symm i)

@[simp]
theorem finTupleToDeletedVector_succAbove
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G)
    (t : Fin n) :
    finTupleToDeletedVector j y
        (finSuccAboveEquiv j t) =
      y t := by
  simp [finTupleToDeletedVector]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

abbrev CutTestCoordinate (G : Type*) (r : ℕ) :=
  Fin r × (Fin (r - 1) → G)

abbrev BooleanCutAssignment (G : Type*) (r : ℕ) :=
  CutTestCoordinate G r → Bool

def usedCutTestCoordinateEmbedding
    {G : Type*} {r : ℕ} (x : Fin r → G) :
    Fin r ↪ CutTestCoordinate G r where
  toFun i := ⟨i, eraseCoordinate i x⟩
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

@[simp]
theorem usedCutTestCoordinateEmbedding_apply
    {G : Type*} {r : ℕ} (x : Fin r → G) (i : Fin r) :
    usedCutTestCoordinateEmbedding x i =
      (i, eraseCoordinate i x) :=
  rfl

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

structure FaceRegularityState (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  partition : FacePartition Ω

namespace FaceRegularityState

noncomputable def structured (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  conditionalMean S.partition f

noncomputable def residual (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : Ω → ℝ :=
  fun x => f x - S.structured f x

end FaceRegularityState

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPattern
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedFace (k r : ℕ) :=
  Fin r ↪o Fin k

instance orderedFaceDecidableEq
    (k r : ℕ) : DecidableEq (OrderedFace k r) :=
  Function.Injective.decidableEq
    (f := fun e : OrderedFace k r => (e : Fin r → Fin k))
    DFunLike.coe_injective

def orderedFaceTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    Fin r → G :=
  fun i => x (e i)

abbrev OrderedFaceComplement
    {k r : ℕ} (e : OrderedFace k r) :=
  {v : Fin k // v ∉ Set.range e}

noncomputable def orderedFaceSumEquiv
    {k r : ℕ} (e : OrderedFace k r) :
    Fin r ⊕ OrderedFaceComplement e ≃ Fin k :=
  (Equiv.sumCongr e.toEmbedding.toEquivRange
      (Equiv.refl (OrderedFaceComplement e))).trans
    (Equiv.sumCompl
      (fun v : Fin k => v ∈ Set.range e))

noncomputable def splitOrderedFaceEquiv
    {G : Type*} {k r : ℕ} (e : OrderedFace k r) :
    (Fin k → G) ≃
      ((Fin r → G) × (OrderedFaceComplement e → G)) :=
  (Equiv.piCongrLeft (fun _ : Fin k => G)
      (orderedFaceSumEquiv e)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : Fin r ⊕ OrderedFaceComplement e => G))

@[simp]
theorem splitOrderedFaceEquiv_fst
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).1 =
      orderedFaceTuple e x := by
  funext i
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceTuple]
  rfl

def orderedFaceComplementTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    OrderedFaceComplement e → G :=
  fun v => x v.1

@[simp]
theorem splitOrderedFaceEquiv_snd
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).2 =
      orderedFaceComplementTuple e x := by
  funext v
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceComplementTuple]

@[simp]
theorem orderedFaceTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = y := by
  rw [← splitOrderedFaceEquiv_fst]
  simp

@[simp]
theorem orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceComplementTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = z := by
  rw [← splitOrderedFaceEquiv_snd]
  simp

structure WeightedOrderedPattern
    (G : Type*) (k r : ℕ) where
  edgeWeight : OrderedFace k r → (Fin r → G) → ℝ

structure OrderedPattern
    (G : Type*) (k r : ℕ) where
  edge : OrderedFace k r → (Fin r → G) → Prop

namespace OrderedPattern

def IsOccurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) : Prop :=
  ∀ e, H.edge e (orderedFaceTuple e x)

noncomputable def occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter H.IsOccurrence

@[simp]
theorem mem_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) :
    x ∈ H.occurrenceFinset ↔ H.IsOccurrence x := by
  simp [occurrenceFinset]

end OrderedPattern

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace SimplexHypergraph

abbrev DeletionFamily {k : ℕ} (V : Fin k → Type*) :=
  (j : Fin k) → Finset (DeletedVector V j)

@[simp]
theorem card_deletedVector_fin (k n : ℕ) (j : Fin k) :
    Fintype.card
        (DeletedVector (fun _ : Fin k => Fin n) j) =
      n ^ (k - 1) := by
  simp [DeletedVector, Fintype.card_pi]

noncomputable def colorDeletionDensity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) : ℝ :=
  ((deleted j).card : ℝ) /
    Fintype.card (DeletedVector V j)

@[simp]
theorem colorDeletionDensity_fin {k n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin k => Fin n))
    (j : Fin k) :
    colorDeletionDensity deleted j =
      ((deleted j).card : ℝ) / (n ^ (k - 1) : ℕ) := by
  simp [colorDeletionDensity]

end SimplexHypergraph

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def apSetHypergraph (k N : ℕ) (A : Finset (ZMod N)) :
    SimplexHypergraph (fun _ : Fin k => ZMod N) where
  edge j x := apSimplexForm k N j x ∈ A

@[simp]
theorem apSetHypergraph_edge
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).edge j x ↔
      apSimplexForm k N j x ∈ A :=
  Iff.rfl

@[simp]
theorem apSetHypergraph_toWeighted_edgeWeight
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).toWeighted.edgeWeight j x =
      finsetIndicator A (apSimplexForm k N j x) := by
  classical
  by_cases hx : apSimplexForm k N j x ∈ A
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_edge]
    · exact (finsetIndicator_of_mem hx).symm
    · exact hx
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_not_edge]
    · exact (finsetIndicator_of_not_mem hx).symm
    · exact hx

noncomputable def deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def orderedFacet {n : ℕ} (j : Fin (n + 1)) :
    OrderedFace (n + 1) n :=
  Fin.succAboveOrderEmb j

noncomputable def orderedFacetEquiv (n : ℕ) :
    Fin (n + 1) ≃ OrderedFace (n + 1) n :=
  (Set.powersetCard.ofSingleton :
      Fin (n + 1) ≃ Set.powersetCard (Fin (n + 1)) 1) |>.trans
    ((Set.powersetCard.compl (m := n) (n := 1) (by simp) :
        Set.powersetCard (Fin (n + 1)) 1 ≃
          Set.powersetCard (Fin (n + 1)) n) |>.trans
      (Set.powersetCard.ofFinEmbEquiv :
        OrderedFace (n + 1) n ≃
          Set.powersetCard (Fin (n + 1)) n).symm)

@[simp]
theorem orderedFacetEquiv_apply
    {n : ℕ} (j : Fin (n + 1)) :
    orderedFacetEquiv n j = orderedFacet j := by
  apply OrderEmbedding.range_inj.mp
  change
    Set.range ((orderedFacetEquiv n) j) =
      Set.range (Fin.succAboveOrderEmb j)
  rw [Fin.range_succAboveOrderEmb]
  ext i
  simp only [orderedFacetEquiv, Equiv.trans_apply]
  rw [
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  rw [Set.powersetCard.mem_compl]
  change
    i ∉ ({j} : Finset (Fin (n + 1))) ↔
      i ∈ ({j} : Set (Fin (n + 1)))ᶜ
  simp

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedBoundaryPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def eraseBoundaryCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    Fin j → G :=
  fun q => x (i.succAbove q)

def eraseBoundaryFace
    {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    OrderedFace k j :=
  (Fin.succAboveOrderEmb i).trans e

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPatternPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev OrderedRegularityTolerance (r : ℕ) := Fin r → ℝ

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.AdaptiveCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

inductive AdaptiveCoarseTargetSchedule (k : ℕ) : ℕ → Type
  | nil : AdaptiveCoarseTargetSchedule k 0
  | node {r : ℕ}
      (tolerance : ℕ → ℝ)
      (budget : ℕ → ℕ)
      (length : ℕ)
      (next : Fin length → AdaptiveCoarseTargetSchedule k r) :
      AdaptiveCoarseTargetSchedule k (r + 1)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EpochEventRank
namespace OAI

section

namespace Erdos3

inductive EpochStackEvent (d : ℕ) : List ℕ → List ℕ → Prop
  | head {r r' : ℕ} {xs ys : List ℕ} (drop : r' < r) (length : ys.length = xs.length)
      (bounded : ∀ q ∈ ys, q ≤ d) : EpochStackEvent d (r :: xs) (r' :: ys)
  | tail {r : ℕ} {xs ys : List ℕ} (event : EpochStackEvent d xs ys) :
      EpochStackEvent d (r :: xs) (r :: ys)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueScalarScoreNet
namespace OAI

section

namespace Erdos3

abbrev DenseResidueSliceNetCode (X : Type*) (Q K : ℕ) :=
  Fin (Q + 1) × (X → Fin (Q + 1)) × (X → Fin (K + 1)) × (X → Fin (K + 1))

namespace DenseResidueSliceNetCode

variable {X : Type*} {Q K : ℕ}

def stride (c : DenseResidueSliceNetCode X Q K) : ℕ := c.1.val

def start (M : ℕ) (c : DenseResidueSliceNetCode X Q K) (i : X) : ℕ :=
  (c.2.1 i).val + c.stride * (M * (c.2.2.1 i).val)

def length (M : ℕ) (c : DenseResidueSliceNetCode X Q K) (i : X) : ℕ :=
  M * (c.2.2.2 i).val - M * (c.2.2.1 i).val

def Valid (N : X → ℕ) (H : ℝ) (M : ℕ) (c : DenseResidueSliceNetCode X Q K) : Prop :=
  0 < c.stride ∧
    (∀ i j, j < c.length M i → c.start M i + c.stride * j < N i) ∧
    ∀ i, H / 2 ≤ (c.length M i : ℝ)

theorem card [Fintype X] [DecidableEq X] (Q K : ℕ) :
    Fintype.card (DenseResidueSliceNetCode X Q K) =
      (Q + 1) * ((Q + 1) * (K + 1) ^ 2) ^ Fintype.card X := by
  simp only [DenseResidueSliceNetCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [mul_pow, ← pow_mul, Nat.mul_comm 2 _, pow_mul]
  ring

end DenseResidueSliceNetCode
end Erdos3

end

end OAI
end


