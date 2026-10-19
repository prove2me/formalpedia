-- Prove2me | Definitions.Def_OAIE3v2B023
-- name    : OAIE3v2B023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:52.334653+00:00
-- url     : https://prove2.me/theorems/52852dc6-3ce2-4524-88c3-6b0448b80b21
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 24 of 311
-- statement:
--   Definitions bundle 24 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/ComparisonEquivalenceBudget.lean`, `Dynamics/SquarefreeModelBudget.lean`, `Estimates/CommonRefilteredFactorization.lean`, `Estimates/ControlledComparisonModel.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/FiniteTripleAssembly.lean`, `Estimates/InvariantUnitFamily.lean`, `Estimates/MomentEvaluationBounds.lean`, `Estimates/NativeDilationObservable.lean`, `Estimates/NativeMultilinearityCorrelation.lean`, `Estimates/NativeSelectedCorrelators.lean`, `Estimates/NormalizedVectorLipschitz.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/RationalSubspaces.lean`, `Estimates/ShiftTestingGowers.lean`, `Estimates/SquarefreeRealAction.lean`, `Estimates/SymmetricEvaluationLowerBound.lean`, `Estimates/SymmetricSquarefreeMonotonicity.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Geometry/FiniteSumCoordinate.lean`, `Geometry/FiniteUnitCoordinate.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Geometry/SymmetricEvaluationMetric.lean`, `Lattices/NativeIntegerHalving.lean`, `Linear/ComparisonBasisBudget.lean`, `Linear/FiniteNormalizedFrame.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Polynomial/FiniteMomentPolynomial.lean`, `Sampling/IntegralGridBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalSubspaces
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

section Intersection

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

def jointMatrix (A : ∀ i, Matrix (ρ i) κ ℚ) : Matrix (Σ i, ρ i) κ ℚ :=
  fun ij k => A ij.1 ij.2 k

omit [Fintype η] [∀ i, Fintype (ρ i)] [DecidableEq κ] in
theorem jointMatrix_ker (A : ∀ i, Matrix (ρ i) κ ℚ) :
    LinearMap.ker (jointMatrix A).mulVecLin = ⨅ i, LinearMap.ker (A i).mulVecLin := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    funext_iff, Pi.zero_apply]
  exact ⟨fun h i j => h ⟨i, j⟩, fun h ij => h ij.1 ij.2⟩

end Intersection

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

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem shift_phase_average (v B : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, a h * (𝔼 x, v x * (B (x + h) * L h x)) =
      (‖𝔼 x, v x * (B (x + h) * L h x)‖ : ℂ)) :
    (𝔼 y, B y * (𝔼 h, a h * v (y - h) * L h (y - h))) =
      ((𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) : ℝ) := by
  have hmove (h : G) :
      a h * (𝔼 x, v x * (B (x + h) * L h x)) =
        𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  calc
    _ = 𝔼 h, 𝔼 y, B y * (a h * v (y - h) * L h (y - h)) := by
      simp_rw [Finset.mul_expect]
      rw [Finset.expect_comm]
    _ = 𝔼 h, a h * (𝔼 x, v x * (B (x + h) * L h x)) := by simp_rw [← hmove]
    _ = _ := by simp_rw [ha]; simp [Fintype.expect_eq_sum_div_card]

theorem shift_phase_cross_norm (v : G → ℂ) (L : G → G → ℂ) (a : G → ℂ)
    (ha : ∀ h, ‖a h‖ = 1) (h k : G) :
    ‖𝔼 y, (a h * v (y - h) * L h (y - h)) *
      star (a k * v (y - k) * L k (y - k))‖ =
    ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖ := by
  have hid : (a h * star (a k)) *
      (𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))) =
      𝔼 y, (a h * v (y - h) * L h (y - h)) *
        star (a k * v (y - k) * L k (y - k)) := by
    rw [Finset.mul_expect]
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right, star_mul]
    ring
  rw [← hid, norm_mul, norm_mul, norm_star, ha, ha, one_mul, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

def quarterUpper (N : ℕ) (i : Fin 4) : ℕ := (i.val + 1) * N / 4

end Erdos3

end

section

namespace Erdos3

def cyclicTranslationOffset {N : ℕ} (h : ZMod N) (a : ℕ) : ℤ :=
  (h.val : ℤ) - if N - h.val ≤ a then (N : ℤ) else 0

theorem cyclic_representative_add {N : ℕ} [NeZero N] (h x : ZMod N) :
    ((h + x).val : ℤ) = (x.val : ℤ) + h.val -
      if N - h.val ≤ x.val then (N : ℤ) else 0 := by
  have hh := h.val_lt
  by_cases hw : N - h.val ≤ x.val
  · have he := ZMod.val_add_val_of_le (a := h) (b := x) (by omega)
    rw [if_pos hw]
    omega
  · have he := ZMod.val_add_of_lt (a := h) (b := x) (by omega)
    rw [if_neg hw]
    omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

theorem enlarged_power_dominates_twice_add_sixteen {p : ℝ} (hp : 0 ≤ p)
    (C : ℕ) (hC : 2 ≤ C) :
    2 * (p + C) ^ C + 16 ≤ (p + (C + 5 : ℕ)) ^ (C + 5) := by
  let t : ℝ := p + (C + 5 : ℕ)
  have ht : 7 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hq : (p + C) ^ C ≤ t ^ C := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  calc
    _ ≤ 18 * t ^ C := by linarith
    _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = t ^ (C + 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ t ^ (C + 5) := pow_le_pow_right₀ (by linarith) (by omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem lieSubalgebra_mem_iInf {η R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (U : η → LieSubalgebra R L) (x : L) : x ∈ (⨅ j, U j) ↔ ∀ j, x ∈ U j := by
  change x ∈ ((sInf (Set.range U) : LieSubalgebra R L) : Set L) ↔ _
  rw [LieSubalgebra.coe_sInf]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedVectorLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem norm_normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {rho : ℝ} (hrho : 0 < rho) (x y : V) (hx : rho ≤ ‖x‖) (hy : rho ≤ ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ (2 / rho) * ‖x - y‖ := by
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hrho.trans_le hy)
  have hid : ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y := by
    simp only [smul_sub, sub_smul, NormedSpace.norm_smul_normalize]
    abel
  have hscale : ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤ 2 * ‖x - y‖ := by
    calc
      _ = ‖‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
      _ = ‖(x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := congrArg norm hid
      _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := norm_add_le _ _
      _ = ‖x - y‖ + |‖y‖ - ‖x‖| := by
        rw [norm_smul, NormedSpace.norm_normalize hy0, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * ‖x - y‖ := by
        have h := abs_norm_sub_norm_le x y
        rw [abs_sub_comm] at h
        linarith
  have hsmall := (mul_le_mul_of_nonneg_right hx
    (norm_nonneg (NormedSpace.normalize x - NormedSpace.normalize y))).trans hscale
  calc
    _ ≤ (2 * ‖x - y‖) / rho := (le_div_iff₀ hrho).mpr (by nlinarith [hsmall])
    _ = _ := by ring

theorem lipschitzWith_normalize {X V : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (u : X → V) {rho K : ℝ≥0}
    (hrho : 0 < rho) (hLip : LipschitzWith K u) (hlower : ∀ x, (rho : ℝ) ≤ ‖u x‖) :
    LipschitzWith (2 / rho * K) (fun x => NormedSpace.normalize (u x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  calc
    _ ≤ (2 / (rho : ℝ)) * ‖u x - u y‖ := norm_normalize_sub_le hrho _ _ (hlower x) (hlower y)
    _ ≤ (2 / (rho : ℝ)) * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y) (by positivity)
    _ = ((2 / rho * K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteNormalizedFrame
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem euclidean_norm_le_card_add_one_mul {I : Type*} [Fintype I]
    (v : EuclideanSpace ℂ I) {M : ℝ} (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) :
    ‖v‖ ≤ (Fintype.card I + 1 : ℝ) * M := by
  have hsq : ‖v‖ ^ 2 ≤ (Fintype.card I : ℝ) * M ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcard : (Fintype.card I : ℝ) ≤ (Fintype.card I + 1 : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card I)]
  have hbound := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)
  nlinarith [norm_nonneg v, mul_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card I + 1) hM]

theorem lipschitzWith_complex_vector {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (u : I → X → ℂ) {K : ℝ≥0} (hu : ∀ i, LipschitzWith K (u i)) :
    LipschitzWith ((Fintype.card I + 1 : ℝ≥0) * K)
      (fun x => (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℂ I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have h := euclidean_norm_le_card_add_one_mul
    ((WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℂ I) - WithLp.toLp 2 (fun i => u i y))
    (M := (K : ℝ) * dist x y) (by positivity) (fun i => by
      simpa only [PiLp.sub_apply, PiLp.toLp_apply, dist_eq_norm] using (hu i).dist_le_mul x y)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, mul_assoc] using h

theorem normalize_complex_unit_smul {I : Type*} [Fintype I]
    (c : ℂ) (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ I) :
    NormedSpace.normalize (c • v) = c • NormedSpace.normalize v := by
  unfold NormedSpace.normalize
  rw [norm_smul, hc, one_mul]
  exact smul_comm _ _ _

theorem exists_normalized_complex_family {I X : Type*} [Fintype I] [PseudoMetricSpace X]
    (u : I → X → ℂ) {rho K : ℝ≥0} (hrho : 0 < rho)
    (hLip : ∀ i, LipschitzWith K (u i)) (hlower : ∀ x, ∃ i, (rho : ℝ) ≤ ‖u i x‖) :
    ∃ v : I → X → ℂ,
      (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
      (∀ i x, ‖v i x‖ ≤ 1) ∧
      (∀ i, LipschitzWith (2 / rho * ((Fintype.card I + 1 : ℝ≥0) * K)) (v i)) ∧
      ∀ x y c, ‖c‖ = 1 → (∀ i, u i x = c * u i y) → ∀ i, v i x = c * v i y := by
  let U (x : X) : EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => u i x)
  have hnorm (x : X) : (rho : ℝ) ≤ ‖U x‖ := by
    obtain ⟨i, hi⟩ := hlower x
    exact hi.trans (PiLp.norm_apply_le (U x) i)
  have hne (x : X) : U x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hrho (hnorm x))
  have hone (x : X) : ‖NormedSpace.normalize (U x)‖ = 1 := NormedSpace.norm_normalize (hne x)
  let v (i : I) (x : X) := NormedSpace.normalize (U x) i
  have hvLip := lipschitzWith_normalize U hrho (lipschitzWith_complex_vector u hLip) hnorm
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [← EuclideanSpace.norm_sq_eq, hone, one_pow]
  · intro i x
    exact (PiLp.norm_apply_le (NormedSpace.normalize (U x)) i).trans_eq (hone x)
  · intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (PiLp.dist_apply_le (NormedSpace.normalize (U x)) (NormedSpace.normalize (U y)) i).trans
      (hvLip.dist_le_mul x y)
  · intro x y c hc hu i
    have heq : U x = c • U y := by
      ext j
      exact hu j
    change NormedSpace.normalize (U x) i = c * NormedSpace.normalize (U y) i
    rw [heq, normalize_complex_unit_smul c hc]
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralGridBudget
namespace OAI

section

namespace Erdos3

open Module

theorem integral_grid_allowance_le_exp (K d H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((K * H ^ (d ^ 3) * l : ℕ) : ℝ) ≤ Real.exp ((p + (K + 5 : ℕ)) ^ (K + 5)) := by
  let C := K + 5
  let t : ℝ := p + C
  have ht : 5 ≤ t := by dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hpt : p ≤ t := by dsimp [t]; exact le_add_of_nonneg_right (Nat.cast_nonneg C)
  have hKt : (K : ℝ) ≤ t := by dsimp [t, C]; push_cast; linarith
  have htt : t ≤ t ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ t by linarith) (by decide : 1 ≤ 4)
  have hp4 : ((d ^ 3 : ℕ) : ℝ) * p ≤ t ^ 4 := by
    rw [Nat.cast_pow]
    calc
      _ ≤ p ^ 3 * p := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg d) hd 3) hp
      _ = p ^ 4 := by ring
      _ ≤ t ^ 4 := pow_le_pow_left₀ hp hpt 4
  have hlog : (K : ℝ) + (d ^ 3 : ℕ) * p + p ≤ t ^ C := by
    calc
      _ ≤ t ^ 4 + t ^ 4 + t ^ 4 := add_le_add (add_le_add (hKt.trans htt) hp4) (hpt.trans htt)
      _ = 3 * t ^ 4 := by ring
      _ ≤ t * t ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = t ^ 5 := by ring
      _ ≤ t ^ C := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hK : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have hpow : ((H ^ (d ^ 3) : ℕ) : ℝ) ≤ Real.exp ((d ^ 3 : ℕ) * p) := by
    rw [Nat.cast_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg H) hH _
  calc
    _ ≤ Real.exp K * Real.exp ((d ^ 3 : ℕ) * p) * Real.exp p := by
      rw [Nat.cast_mul, Nat.cast_mul]
      exact mul_le_mul (mul_le_mul hK hpow (by positivity) (by positivity)) hl
        (by positivity) (by positivity)
    _ = Real.exp ((K : ℝ) + (d ^ 3 : ℕ) * p + p) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SquarefreeModelBudget
namespace OAI

section

namespace Erdos3

noncomputable def squarefreeInputBudget (t : ℕ) (p : ℝ) : ℝ := (2 : ℝ) ^ t * p + (p + 3) ^ 8

theorem squarefreeInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ squarefreeInputBudget t p := by
  unfold squarefreeInputBudget
  positivity

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

def intervalCutUpper (S : Finset ℕ) (N a : ℕ) : ℕ :=
  (insert N (S.filter (a < ·))).min' (Finset.insert_nonempty _ _)

theorem intervalCutUpper_le_end (S : Finset ℕ) (N a : ℕ) :
    intervalCutUpper S N a ≤ N :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem intervalCutUpper_le_cut (S : Finset ℕ) (N : ℕ) {a b : ℕ}
    (hb : b ∈ S) (hab : a < b) : intervalCutUpper S N a ≤ b :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hb, hab⟩))

theorem le_intervalCutUpper (S : Finset ℕ) (N : ℕ) {a : ℕ} (ha : a ≤ N) :
    a ≤ intervalCutUpper S N a := by
  apply Finset.le_min'
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ha
  · exact (Finset.mem_filter.mp hb).2.le

theorem exists_intervalCut (S : Finset ℕ) (N : ℕ) (hzero : 0 ∈ S)
    {x : ℕ} (hx : x < N) :
    ∃ a ∈ S, a ≤ x ∧ x < intervalCutUpper S N a := by
  let A := S.filter (· ≤ x)
  have hA : A.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hzero, Nat.zero_le _⟩⟩
  let a := A.max' hA
  have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
  refine ⟨a, ha.1, ha.2, ?_⟩
  apply (Finset.lt_min'_iff _ _).mpr
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact hx
  · obtain ⟨hbS, hab⟩ := Finset.mem_filter.mp hb
    by_contra hxb
    have hbA : b ∈ A := Finset.mem_filter.mpr ⟨hbS, by omega⟩
    have hba : b ≤ a := Finset.le_max' A b hbA
    omega

theorem intervalCut_unique (S : Finset ℕ) (N : ℕ) {a b x : ℕ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hax : a ≤ x) (hxa : x < intervalCutUpper S N a)
    (hbx : b ≤ x) (hxb : x < intervalCutUpper S N b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · have hh := intervalCutUpper_le_cut S N hb hab
    omega
  · exact hab
  · have hh := intervalCutUpper_le_cut S N ha hba
    omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ComparisonBasisBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def comparisonBasisBudget (t : ℕ) (p : ℝ) : ℝ := p + 1 + (t : ℝ) ^ 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem map_mem_submodule_of_basis {κ V W : Type*} [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (b : Basis κ ℚ V) (f : V →ₗ[ℚ] W) (P : Submodule ℚ W)
    (h : ∀ i, f (b i) ∈ P) (x : V) : f x ∈ P := by
  rw [← b.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact P.smul_mem _ (h i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FiniteMomentPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open Polynomial

noncomputable def finiteMomentPolynomial {m : ℕ} (v : Fin m → ℂ) : Polynomial ℂ :=
  ∑ j, Polynomial.C (v j) * Polynomial.X ^ j.val

theorem finiteMomentPolynomial_coeff {m : ℕ} (v : Fin m → ℂ) (j : Fin m) :
    (finiteMomentPolynomial v).coeff j.val = v j := by
  classical
  simp only [finiteMomentPolynomial, finsetSum_coeff, coeff_C_mul_X_pow, ← Fin.ext_iff]
  simp

theorem finiteMomentPolynomial_ne_zero {m : ℕ} {v : Fin m → ℂ} (hv : v ≠ 0) :
    finiteMomentPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hj := finiteMomentPolynomial_coeff v j
  rw [h, coeff_zero] at hj
  exact hj.symm

theorem finiteMomentPolynomial_natDegree_le {m : ℕ} (v : Fin m → ℂ) :
    (finiteMomentPolynomial v).natDegree ≤ m := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt j.isLt)

theorem finiteMomentPolynomial_eval {m : ℕ} (v : Fin m → ℂ) (z : ℂ) :
    (finiteMomentPolynomial v).eval z = ∑ j, v j * z ^ j.val := by
  simp [finiteMomentPolynomial, eval_finsetSum]

noncomputable def momentProduct {m : ℕ} (v : Fin m → Fin m → ℂ)
    (z : Fin (m * m + 1)) : ℂ :=
  ∏ i, ∑ j, v i j * (z.val : ℂ) ^ j.val

theorem momentProduct_ne_zero_some {m : ℕ} (v : Fin m → Fin m → ℂ)
    (hv : ∀ i, v i ≠ 0) : ∃ z, momentProduct v z ≠ 0 := by
  classical
  let P : Polynomial ℂ := ∏ i, finiteMomentPolynomial (v i)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => finiteMomentPolynomial_ne_zero (hv i))
  have hdeg : P.natDegree ≤ m * m := by
    calc
      _ ≤ ∑ i : Fin m, (finiteMomentPolynomial (v i)).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin m, m := Finset.sum_le_sum (fun i _ => finiteMomentPolynomial_natDegree_le (v i))
      _ = _ := by simp
  by_contra h
  push Not at h
  apply hP
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun z : Fin (m * m + 1) => (z.val : ℂ))
  · intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  · intro z
    simpa only [P, eval_prod, finiteMomentPolynomial_eval, momentProduct] using h z
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hdeg

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MomentEvaluationBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def momentWeightBound (m : ℕ) : ℕ := (m + 1) * (m * m + 1) ^ m

theorem momentWeightBound_pos (m : ℕ) : 0 < momentWeightBound m := by
  unfold momentWeightBound
  positivity

theorem norm_momentWeight_le {m : ℕ} (z : Fin (m * m + 1)) (j : Fin m) :
    ‖(z.val : ℂ) ^ j.val‖ ≤ ((m * m + 1) ^ m : ℕ) := by
  rw [norm_pow, Complex.norm_natCast]
  have hz : (z.val : ℝ) ≤ (m * m + 1 : ℕ) := by exact_mod_cast (Nat.le_of_lt z.isLt)
  calc
    _ ≤ ((m * m + 1 : ℕ) : ℝ) ^ j.val := pow_le_pow_left₀ (Nat.cast_nonneg _) hz _
    _ ≤ ((m * m + 1 : ℕ) : ℝ) ^ m :=
      pow_le_pow_right₀ (by exact_mod_cast (Nat.le_add_left 1 (m * m))) (Nat.le_of_lt j.isLt)
    _ = _ := by norm_cast

noncomputable def momentLinear {m : ℕ} (v : Fin m → ℂ) (z : Fin (m * m + 1)) : ℂ :=
  ∑ j, v j * (z.val : ℂ) ^ j.val

theorem norm_momentLinear_le {m : ℕ} (v : Fin m → ℂ) (z : Fin (m * m + 1))
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ j, ‖v j‖ ≤ M) :
    ‖momentLinear v z‖ ≤ (momentWeightBound m : ℝ) * M := by
  calc
    _ ≤ ∑ j, ‖v j‖ * ‖(z.val : ℂ) ^ j.val‖ := by
      simpa only [momentLinear, norm_mul] using norm_sum_le (s := Finset.univ)
        (f := fun j => v j * (z.val : ℂ) ^ j.val)
    _ ≤ ∑ _j : Fin m, M * (((m * m + 1) ^ m : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul (hv j) (norm_momentWeight_le z j) (norm_nonneg _) hM)
    _ ≤ (momentWeightBound m : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, momentWeightBound]
      push_cast
      nlinarith [mul_nonneg hM (pow_nonneg (by positivity : (0 : ℝ) ≤ m * m + 1) m)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteUnitCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_unit_coordinate {I : Type*} [Fintype I] (v : I → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    ∃ i, 1 / (Fintype.card I + 1 : ℝ) ≤ ‖v i‖ := by
  classical
  have hpos : (0 : ℝ) < Fintype.card I + 1 := by positivity
  by_contra h
  push Not at h
  have hn : ‖v‖ < 1 / (Fintype.card I + 1 : ℝ) :=
    (pi_norm_lt_iff (by positivity)).mpr h
  let V : EuclideanSpace ℂ I := WithLp.toLp 2 v
  have hV : ‖V‖ = 1 := by
    have hs : ‖V‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact hv
    nlinarith [norm_nonneg V]
  have hbound := euclidean_norm_le_card_add_one_mul V (norm_nonneg v)
    (fun i => norm_le_pi_norm v i)
  rw [hV] at hbound
  have hsmall := (lt_div_iff₀ hpos).mp hn
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricEvaluationLowerBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem continuous_momentProduct (m : ℕ) :
    Continuous (fun v : Fin m → Fin m → ℂ => momentProduct v) := by
  unfold momentProduct
  fun_prop

theorem exists_momentProduct_unit_lower (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin m → Fin m → ℂ,
      (∀ i, ‖v i‖ = 1) → c ≤ ‖momentProduct v‖ := by
  have hcompact : IsCompact {v : Fin m → Fin m → ℂ | ∀ i, ‖v i‖ = 1} := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      isCompact_pi_infinite (fun _i : Fin m => isCompact_sphere (0 : Fin m → ℂ) 1)
  apply hcompact.exists_forall_le' ((continuous_momentProduct m).norm.continuousOn)
  intro v hv
  apply norm_pos_iff.mpr
  obtain ⟨z, hz⟩ := momentProduct_ne_zero_some v (fun i hi => by
    have h := hv i
    simp only [hi, norm_zero, zero_ne_one] at h)
  intro h
  exact hz (congrFun h z)

theorem momentProduct_smul {m : ℕ} (v : Fin m → Fin m → ℂ) (c : Fin m → ℂ) :
    momentProduct (fun i => c i • v i) = (∏ i, c i) • momentProduct v := by
  funext z
  simp only [momentProduct, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum, Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_momentProduct_lower (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin m → Fin m → ℂ,
      (∀ i, v i ≠ 0) → ∃ z, c * ∏ i, ‖v i‖ ≤ ‖momentProduct v z‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_momentProduct_unit_lower m
  refine ⟨c, hc, ?_⟩
  intro v hv
  let w : Fin m → Fin m → ℂ := fun i => (‖v i‖ : ℂ)⁻¹ • v i
  have hn (i) : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (hv i)
  have hnc (i) : (‖v i‖ : ℂ) ≠ 0 := by exact_mod_cast hn i
  have hw (i) : ‖w i‖ = 1 := by
    simp only [w, norm_smul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (hn i)
  have hreconstruct : (fun i => (‖v i‖ : ℂ) • w i) = v := by
    funext i
    simp only [w, smul_smul, mul_inv_cancel₀ (hnc i), one_smul]
  have hex : ∃ z, c ≤ ‖momentProduct w z‖ := by
    by_contra h
    push Not at h
    exact not_lt_of_ge (hbound w hw) ((pi_norm_lt_iff hc).mpr h)
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ?_⟩
  have heq : ‖momentProduct v z‖ = (∏ i, ‖v i‖) * ‖momentProduct w z‖ := by
    have h := congrFun (momentProduct_smul w (fun i => (‖v i‖ : ℂ))) z
    rw [hreconstruct] at h
    rw [h, Pi.smul_apply, norm_smul, norm_prod]
    simp only [Complex.norm_real, norm_norm]
  rw [heq, mul_comm c]
  exact mul_le_mul_of_nonneg_left hz (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))

noncomputable def momentLowerConstant (m : ℕ) : ℝ :=
  Classical.choose (exists_momentProduct_lower m)

theorem momentLowerConstant_pos (m : ℕ) : 0 < momentLowerConstant m :=
  (Classical.choose_spec (exists_momentProduct_lower m)).1

theorem momentLowerConstant_bound {m : ℕ} (v : Fin m → Fin m → ℂ)
    (hv : ∀ i, v i ≠ 0) :
    ∃ z, momentLowerConstant m * ∏ i, ‖v i‖ ≤ ‖momentProduct v z‖ :=
  (Classical.choose_spec (exists_momentProduct_lower m)).2 v hv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev SymmetricEvaluationIndex (m : ℕ) (I : Type*) := (Fin m → I) × Fin (m * m + 1)

noncomputable def symmetricEvaluation {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (k : SymmetricEvaluationIndex m I) : ℂ :=
  momentProduct (fun i j => v i (k.1 j)) k.2

theorem symmetricEvaluation_permute {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (e : Equiv.Perm (Fin m)) :
    symmetricEvaluation (fun i => v (e i)) = symmetricEvaluation v := by
  funext k
  exact Equiv.prod_comp e (fun i => ∑ j, v i (k.1 j) * (k.2.val : ℂ) ^ j.val)

theorem symmetricEvaluation_smul {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (c : Fin m → ℂ) :
    symmetricEvaluation (fun i => c i • v i) = (∏ i, c i) • symmetricEvaluation v := by
  funext k
  exact congrFun (momentProduct_smul (fun i j => v i (k.1 j)) c) k.2

theorem symmetricEvaluation_const_mul {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (c : ℂ) (k : SymmetricEvaluationIndex m I) :
    symmetricEvaluation (fun i j => c * v i j) k = c ^ m * symmetricEvaluation v k := by
  have h := congrFun (symmetricEvaluation_smul v (fun _ => c)) k
  change symmetricEvaluation (fun i => c • v i) k = _
  simpa only [Pi.smul_apply, smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem symmetricEvaluationIndex_card (m : ℕ) (I : Type*) [Fintype I] :
    Fintype.card (SymmetricEvaluationIndex m I) = Fintype.card I ^ m * (m * m + 1) := by
  simp only [SymmetricEvaluationIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem symmetricEvaluation_lower {m : ℕ} {I : Type*} [Fintype I]
    (v : Fin m → I → ℂ) (hv : ∀ i, ∑ j, ‖v i j‖ ^ 2 = 1) :
    ∃ k, momentLowerConstant m / (Fintype.card I + 1 : ℝ) ^ m ≤
      ‖symmetricEvaluation v k‖ := by
  classical
  choose a ha using fun i => exists_large_unit_coordinate (v i) (hv i)
  let w : Fin m → Fin m → ℂ := fun i j => v i (a j)
  let δ : ℝ := 1 / (Fintype.card I + 1 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hw (i) : δ ≤ ‖w i‖ := (ha i).trans (norm_le_pi_norm (w i) i)
  have hw0 (i) : w i ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hw i))
  obtain ⟨z, hz⟩ := momentLowerConstant_bound w hw0
  refine ⟨(a, z), ?_⟩
  have hprod : δ ^ m ≤ ∏ i, ‖w i‖ := by
    have h := Finset.prod_le_prod (s := Finset.univ)
      (fun _ _ => hδ.le) (fun i _ => hw i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  calc
    _ = momentLowerConstant m * δ ^ m := by simp [δ, div_eq_mul_inv, inv_pow]
    _ ≤ momentLowerConstant m * ∏ i, ‖w i‖ :=
      mul_le_mul_of_nonneg_left hprod (momentLowerConstant_pos m).le
    _ ≤ ‖symmetricEvaluation v (a, z)‖ := hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymmetricEvaluationMetric
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def symmetricEvaluationLip (m : ℕ) (K : ℝ≥0) : ℝ≥0 :=
  m * ((momentWeightBound m : ℝ≥0) * K) * (momentWeightBound m : ℝ≥0) ^ m

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InvariantUnitFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def symmetricEvaluationRadius (m n : ℕ) : ℝ≥0 :=
  ⟨momentLowerConstant m / (n + 1 : ℝ) ^ m, by
    have := momentLowerConstant_pos m
    positivity⟩

theorem symmetricEvaluationRadius_pos (m n : ℕ) : 0 < symmetricEvaluationRadius m n := by
  change 0 < momentLowerConstant m / (n + 1 : ℝ) ^ m
  have := momentLowerConstant_pos m
  positivity

noncomputable def symmetricUnitFamilyLip (m n : ℕ) (K : ℝ≥0) : ℝ≥0 :=
  2 / symmetricEvaluationRadius m n *
    ((n ^ m * (m * m + 1) + 1 : ℝ≥0) * symmetricEvaluationLip m K)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSelectedCorrelators
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem derivative_quadruple_exp_threshold (p : ℝ) :
    (Real.exp (-p) * Real.exp (-(2 * p))) ^ 4 / 2 = Real.exp (-(12 * p)) / 2 := by
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3

def replicatedFrequencyHeight (d H : ℕ) : ℕ := (d + 1) * (H * H) ^ d

theorem replicatedFrequencyHeight_pos (d : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < replicatedFrequencyHeight d H := by
  have hHpos : 0 < H := by omega
  unfold replicatedFrequencyHeight
  positivity

end Erdos3

end

section

namespace Erdos3

noncomputable def replicatedFrequencyDenominatorBudget (t : ℕ) (p : ℝ) : ℝ :=
  (2 : ℝ) ^ t * (p + 3) ^ 5

end Erdos3

end

section

namespace Erdos3

noncomputable def squarefreeFrequencyInputBudget (t : ℕ) (p : ℝ) : ℝ :=
  squarefreeInputBudget t p + replicatedFrequencyDenominatorBudget t p

theorem squarefreeInputBudget_le_frequency (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeInputBudget t p ≤ squarefreeFrequencyInputBudget t p := by
  apply le_add_of_nonneg_right
  unfold replicatedFrequencyDenominatorBudget
  positivity

theorem squarefreeFrequencyInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ squarefreeFrequencyInputBudget t p :=
  (squarefreeInputBudget_nonneg t hp).trans (squarefreeInputBudget_le_frequency t hp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ : Type}
  {L : Type*}
  [Fintype σ]
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}
  {bound : σ → ℕ}

noncomputable def comparisonGeometryBudget (t : ℕ) (p q : ℝ) : ℝ :=
  ((p + q + 4) ^ 2 + comparisonBasisBudget t p + 6) ^ 11

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem coordinate_spanning_range {ι κ V : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (v : κ → V) (U : Submodule ℚ V)
    (hv : Submodule.span ℚ (Set.range v) = U) :
    LinearMap.range (Matrix.mulVecLin (fun i k => b.equivFun (v k) i)) =
      U.map b.equivFun.toLinearMap := by
  rw [← hv, Submodule.map_span, ← Set.range_comp]
  exact (Matrix.range_mulVecLin _)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*}
  [Fintype σ]
  [DecidableEq σ]
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}
  {bound : σ → ℕ}

theorem le_triple_basis_budget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ ((p + 4) ^ 2 + 2) ^ 63 := by
  have hb : 1 ≤ (p + 4) ^ 2 + 2 := by nlinarith [sq_nonneg (p + 4)]
  have hpow : (p + 4) ^ 2 + 2 ≤ ((p + 4) ^ 2 + 2) ^ 63 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by decide : 1 ≤ 63)
  exact (show p ≤ (p + 4) ^ 2 + 2 by nlinarith [sq_nonneg p]).trans hpow

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def comparisonProductLip (c : ℕ) (K L A : ℝ≥0) (p : ℝ) : ℝ≥0 :=
  c * K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩) +
    L * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩

noncomputable def comparisonProductCost (p : ℝ) : ℝ := (p + 3) ^ 2 + 3 * p + 5

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteTripleAssembly
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem assemble_triple_fibers {G : Type*} (A : Finset G) (P : A → Finset (G × G)) :
    ∃ Q : Finset (G × G × G), Q.card = ∑ a : A, (P a).card ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t.1 ∧ t.2 ∈ P a := by
  classical
  let e : (Σ _ : A, G × G) ↪ G × G × G := {
    toFun := fun t => (t.1.val, t.2)
    inj' := by
      rintro ⟨a, u⟩ ⟨b, v⟩ h
      have hab : a = b := Subtype.ext (congrArg Prod.fst h)
      have huv : u = v := congrArg Prod.snd h
      cases hab
      cases huv
      rfl }
  refine ⟨(Finset.univ.sigma P).map e, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_sigma]
  · intro t
    constructor
    · intro ht
      obtain ⟨⟨a, u⟩, hau, heq⟩ := Finset.mem_map.mp ht
      have ha := (Finset.mem_sigma.mp hau).2
      exact ⟨a, congrArg Prod.fst heq, (congrArg Prod.snd heq) ▸ ha⟩
    · rintro ⟨a, ha, ht⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨a, t.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
      exact Prod.ext ha rfl

theorem dense_triple_fibers {G : Type*} [Fintype G]
    (A : Finset G) (P : A → Finset (G × G)) {α β : ℝ}
    (hβ : 0 ≤ β) (hA : α * (Fintype.card G : ℝ) ≤ A.card)
    (hP : ∀ a : A, β * (Fintype.card G : ℝ) ^ 2 ≤ (P a).card) :
    ∃ Q : Finset (G × G × G),
      α * β * (Fintype.card G : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t.1 ∧ t.2 ∈ P a := by
  obtain ⟨Q, hcard, hmem⟩ := assemble_triple_fibers A P
  refine ⟨Q, ?_, hmem⟩
  calc
    _ = (α * Fintype.card G) * (β * (Fintype.card G : ℝ) ^ 2) := by ring
    _ ≤ (A.card : ℝ) * (β * (Fintype.card G : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg hβ (sq_nonneg _))
    _ = ∑ _a : A, β * (Fintype.card G : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑ a : A, ((P a).card : ℝ) := Finset.sum_le_sum (fun a _ => hP a)
    _ = (Q.card : ℝ) := by rw [hcard, Nat.cast_sum]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def signedTensorProduct (m : ℤ) (v : Fin m.natAbs → ℂ) : ℂ :=
  if m < 0 then star (∏ i, v i) else ∏ i, v i

theorem signedTensorProduct_norm (m : ℤ) (v : Fin m.natAbs → ℂ) :
    ‖signedTensorProduct m v‖ = ∏ i, ‖v i‖ := by
  unfold signedTensorProduct
  split_ifs <;> simp only [norm_star, norm_prod]

theorem signedTensorProduct_norm_le (m : ℤ) (v : Fin m.natAbs → ℂ)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖signedTensorProduct m v‖ ≤ 1 := by
  rw [signedTensorProduct_norm]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hv i)

end Erdos3

end

section

namespace Erdos3

variable {σ I : Type*}

noncomputable def integerDilationVector (f : I → (σ → ℤ) → ℂ)
    (q : ℤ) (a : I) (x : σ → ℤ) : ℂ := f a (fun i => q * x i)

noncomputable def signedTensorVector (f : I → (σ → ℤ) → ℂ)
    (m : ℤ) (a : Fin m.natAbs → I) (x : σ → ℤ) : ℂ :=
  signedTensorProduct m (fun j => f (a j) x)

noncomputable def dilationTensorCrossProduct (f : I → (σ → ℤ) → ℂ)
    (q : ℤ) (t : ℕ) (a : I × (Fin (q ^ t).natAbs → I)) (x : σ → ℤ) : ℂ :=
  integerDilationVector f q a.1 x * star (signedTensorVector f (q ^ t) a.2 x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteSumCoordinate
namespace OAI

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ]

def coordinateAdditionInputs (i : σ) (x : Option σ → ℤ) : Fin 3 → σ → ℤ :=
  ![Function.update (fun j => x (some j)) i (x (some i) + x none),
    fun j => x (some j), Function.update (fun j => x (some j)) i (x none)]

@[simp] theorem coordinateAdditionInputs_sum (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 0 =
      Function.update (fun j => x (some j)) i (x (some i) + x none) := rfl

@[simp] theorem coordinateAdditionInputs_left (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 1 = (fun j => x (some j)) := rfl

@[simp] theorem coordinateAdditionInputs_right (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i x 2 = Function.update (fun j => x (some j)) i (x none) := rfl

noncomputable def coordinateAdditionProduct {I : Type*} (f : I → (σ → ℤ) → ℂ)
    (a : Fin 3 → I) (i : σ) (x : Option σ → ℤ) : ℂ :=
  f (a 0) (coordinateAdditionInputs i x 0) * star (f (a 1) (coordinateAdditionInputs i x 1)) *
    star (f (a 2) (coordinateAdditionInputs i x 2))

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ]

def coordinateConstantInput (i : σ) (h n : ℤ) : σ → ℤ :=
  Function.update (fun _ => n) i h

def coordinatePairInput (i : σ) (a b n : ℤ) : Option σ → ℤ
  | none => b
  | some j => coordinateConstantInput i a n j

theorem coordinatePairInput_sum (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 0 =
      coordinateConstantInput i (a + b) n := by
  simp [coordinateAdditionInputs, coordinatePairInput, coordinateConstantInput]

theorem coordinatePairInput_left (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 1 = coordinateConstantInput i a n := rfl

theorem coordinatePairInput_right (i : σ) (a b n : ℤ) :
    coordinateAdditionInputs i (coordinatePairInput i a b n) 2 = coordinateConstantInput i b n := by
  simp [coordinateAdditionInputs, coordinatePairInput, coordinateConstantInput]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearityCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ]

noncomputable def coordinateSumVector (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I) (x : Option σ → ℤ) : ℂ :=
  f a (coordinateAdditionInputs i x 0)

noncomputable def coordinateTensorVector (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I × I) (x : Option σ → ℤ) : ℂ :=
  f a.1 (coordinateAdditionInputs i x 1) * f a.2 (coordinateAdditionInputs i x 2)

theorem coordinateAdditionProduct_eq (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I) (b : I × I) (x : Option σ → ℤ) :
    coordinateAdditionProduct f ![a, b.1, b.2] i x =
      coordinateSumVector f i a x * star (coordinateTensorVector f i b x) := by
  simp [coordinateAdditionProduct, coordinateSumVector, coordinateTensorVector, mul_assoc]

theorem coordinateTensorVector_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ x, ∑ a, ‖f a x‖ ^ 2 = 1) (i : σ) (x : Option σ → ℤ) :
    ∑ a, ‖coordinateTensorVector f i a x‖ ^ 2 = 1 := by
  simp only [coordinateTensorVector, norm_mul, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, hf, mul_one]

end Erdos3

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

def coordinateTranslatedInput (l : List σ) (x : Option σ → ℤ) (i : σ) : ℤ :=
  x (some i) + if i ∈ l then x none else 0

def coordinateTranslationHom (l : List σ) (j : Option σ) : ((Option σ → ℤ) →+ ℤ) where
  toFun x := match j with
    | none => x none
    | some i => coordinateTranslatedInput l x i
  map_zero' := by cases j <;> simp [coordinateTranslatedInput]
  map_add' x y := by
    cases j with
    | none => rfl
    | some i =>
      simp only [coordinateTranslatedInput, Pi.add_apply]
      split_ifs <;> ring

theorem coordinateTranslation_sum (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 0 =
      coordinateTranslatedInput (i :: l) x := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput, hj]

theorem coordinateTranslation_left (l : List σ) (i : σ) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 1 =
      coordinateTranslatedInput l x := rfl

end Erdos3

end

end OAI
end


