-- Prove2me | Definitions.Def_OAIE3v2B031
-- name    : OAIE3v2B031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:35.450159+00:00
-- url     : https://prove2.me/theorems/1bdab768-8e4b-4cc2-92ba-29503bd92b32
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 32 of 311
-- statement:
--   Definitions bundle 32 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Dynamics/CandidateFrontSourceLossBudget.lean`, `Dynamics/CandidatePhysicalOrdinaryBudget.lean`, `Dynamics/NormalizedTwistNativeApproximationBudget.lean`, `Dynamics/PrecenterNativeSelectionBudget.lean`, `Dynamics/PreparedModularCanonicalDetectorResourceBudget.lean`, `Estimates/AllocatedCoverLogBounds.lean`, `Estimates/AllocatedExternalCandidateTaggedPairUniformFactors.lean`, `Estimates/AllocatedPrimitiveFrontInitialLong.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/ConvexEmpiricalApproximation.lean`, `Estimates/InitializedEarlyCanonicalSliceScales.lean`, `Estimates/MarginalTailModeling.lean`, `Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean`, `Estimates/SmoothHalfspaceCutoff.lean`, `Estimates/WeightedSummandCorrelation.lean`, `Geometry/AllocatedInactiveSupportBudget.lean`, `Geometry/AllocatedProductChartRadius.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Lattices/CertifiedAffineNormalizedBudget.lean`, `Linear/BalancedDualBounds.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Probability/PreparedReadyNormalizationMassBudget.lean`, `Sampling/AveragedNormalizedTwistForecastJointModel.lean`.
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

namespace Erdos3.VectorPolynomial

theorem candidateFrontSourceLossBounds (cap p q u pModel native bin : ℝ)
    (hcap : 3 ≤ cap)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hu : 0 ≤ u) (hmodel : 0 ≤ pModel)
    (hnative : 0 ≤ native) (hbin : 0 ≤ bin)
    (hpCap : p ≤ cap) (hqCap : q ≤ cap) (huCap : u ≤ cap)
    (hmodelCap : pModel ≤ cap) (hnativeCap : native ≤ cap) (hbinU : bin ≤ u) :
    let Q := max (max native 3) (2 * u + 4 * pModel + 20)
    let r := q + bin + Q + 6
    let M := 2 * p + q + p * (bin + (2 * Q + 2 * u + 4 * pModel + 34)) + 2
    0 ≤ Q ∧ Q ≤ 6 * cap + 20 ∧
      0 ≤ r ∧ r ≤ (cap + 3) ^ 4 ∧
      0 ≤ M ∧ M ≤ (cap + 3) ^ 4 := by
  let Q := max (max native 3) (2 * u + 4 * pModel + 20)
  have hc0 : 0 ≤ cap := le_trans (by norm_num) hcap
  have hQ0 : 0 ≤ Q := (hnative.trans (le_max_left _ _)).trans (le_max_left _ _)
  have hQcap : Q ≤ 6 * cap + 20 := by
    apply max_le
    · exact max_le (by linarith only [hnativeCap, hc0]) (by linarith only [hcap])
    · linarith only [huCap, hmodelCap]
  have hbinCap : bin ≤ cap := hbinU.trans huCap
  have hterm0 : 0 ≤ bin + (2 * Q + 2 * u + 4 * pModel + 34) := by positivity
  have hterm : bin + (2 * Q + 2 * u + 4 * pModel + 34) ≤ 19 * cap + 74 := by
    linarith only [hbinCap, hQcap, huCap, hmodelCap]
  have hproduct := mul_le_mul hpCap hterm hterm0 hc0
  have hmass : 2 * p + q + p * (bin + (2 * Q + 2 * u + 4 * pModel + 34)) + 2 ≤
      19 * cap ^ 2 + 77 * cap + 2 := by
    nlinarith only [hpCap, hqCap, hproduct]
  have hresidual : q + bin + Q + 6 ≤ 8 * cap + 26 := by
    linarith only [hqCap, hbinCap, hQcap]
  have hquartic : (cap + 3) ^ 4 = cap ^ 4 + 12 * cap ^ 3 + 54 * cap ^ 2 +
      108 * cap + 81 := by ring
  have hc2 : 0 ≤ cap ^ 2 := pow_nonneg hc0 _
  have hc3 : 0 ≤ cap ^ 3 := pow_nonneg hc0 _
  have hc4 : 0 ≤ cap ^ 4 := pow_nonneg hc0 _
  have hresidualQuartic : 8 * cap + 26 ≤ (cap + 3) ^ 4 := by
    rw [hquartic]
    linarith only [hc0, hc2, hc3, hc4]
  have hmassQuartic : 19 * cap ^ 2 + 77 * cap + 2 ≤ (cap + 3) ^ 4 := by
    rw [hquartic]
    linarith only [hc0, hc2, hc3, hc4]
  exact ⟨hQ0, hQcap, by positivity, hresidual.trans hresidualQuartic,
    by positivity, hmass.trans hmassQuartic⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteSiteExtension {T X : Type*} [Nonempty T]
    (e : T → X) (f : T → ℂ) : X → ℂ := fun x => f (Function.invFun e x)

theorem finiteSiteExtension_apply {T X : Type*} [Nonempty T]
    (e : T → X) (he : Function.Injective e) (f : T → ℂ) (t : T) :
    finiteSiteExtension e f (e t) = f t := by
  rw [finiteSiteExtension, Function.leftInverse_invFun he t]

theorem finiteSiteExtension_norm_le {T X : Type*} [Nonempty T]
    (e : T → X) (f : T → ℂ) {B : ℝ} (hf : ∀ t, ‖f t‖ ≤ B) (x : X) :
    ‖finiteSiteExtension e f x‖ ≤ B := hf _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BalancedDualBounds
namespace OAI

section

namespace Erdos3

theorem seminorm_dual_bound_of_ball {E : Type*} [AddCommGroup E] [Module ℂ E]
    (X : Seminorm ℂ E) (f : E →ₗ[ℂ] ℂ) {tau : ℝ} (htau : 0 < tau)
    (hball : ∀ v, X v ≤ tau → ‖f v‖ < 1) : ∀ v, tau * ‖f v‖ ≤ X v := by
  intro v
  by_contra h
  have hv : X v < tau * ‖f v‖ := lt_of_not_ge h
  have hnorm : 0 < ‖f v‖ := by nlinarith [apply_nonneg X v, norm_nonneg (f v)]
  let a : ℂ := (‖f v‖⁻¹ : ℝ)
  have ha : ‖a‖ = ‖f v‖⁻¹ := by
    simp [a]
  have hX : X (a • v) ≤ tau := by
    rw [map_smul_eq_mul, ha, inv_mul_eq_div]
    exact ((div_lt_iff₀ hnorm).mpr (by simpa only [mul_comm] using hv)).le
  have hbad := hball (a • v) hX
  have hbad' : (1 : ℝ) < 1 := by
    simpa only [map_smul, norm_smul, ha, inv_mul_cancel₀ hnorm.ne'] using hbad
  exact (lt_irrefl 1) hbad'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothHalfspaceCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_smoothTransition_lipschitz :
    ∃ A : ℝ≥0, 1 ≤ A ∧ LipschitzWith A Real.smoothTransition := by
  have hs : ContDiffOn ℝ 1 Real.smoothTransition (Set.Icc (0 : ℝ) 1) :=
    Real.smoothTransition.contDiff.contDiffOn
  obtain ⟨K, hK⟩ := hs.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hglobal : LipschitzWith K Real.smoothTransition := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hx := (Set.projIcc (0 : ℝ) 1 zero_le_one x).property
    have hy := (Set.projIcc (0 : ℝ) 1 zero_le_one y).property
    have h := hK.dist_le_mul _ hx _ hy
    simp only [Real.smoothTransition.projIcc] at h
    have hp := (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at hp
    exact h.trans (mul_le_mul_of_nonneg_left hp K.coe_nonneg)
  exact ⟨K + 1, by simp, hglobal.weaken (by simp)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def shearKernelLogBudget (s d : ℕ) (M u : ℝ) : ℝ :=
  u + M + d + s + ((s * d : ℕ) * M + 1) * (s * (d + 1) : ℕ)

def shearActionLogBudget (s d : ℕ) (M : ℝ) : ℝ :=
  s + s * ((d * ((s + 1) * (d + 1) ^ s) * s : ℕ) : ℝ) +
    s * ((s * d : ℕ) * M)

theorem shearKernelLogBudget_nonneg (s d : ℕ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 ≤ u) :
    0 ≤ shearKernelLogBudget s d M u := by unfold shearKernelLogBudget; positivity

theorem shearActionLogBudget_nonneg (s d : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ shearActionLogBudget s d M := by unfold shearActionLogBudget; positivity

theorem shearRadius_le_exp (s d : ℕ) (M : ℝ≥0) :
    (((1 + M) ^ (s * d) : ℝ≥0) : ℝ) ≤ Real.exp ((s * d : ℕ) * (M : ℝ)) := by
  simp only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one]
  calc
    _ ≤ (Real.exp (M : ℝ)) ^ (s * d) := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [Real.add_one_le_exp (M : ℝ)]
    _ = _ := (Real.exp_nat_mul _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConvexEmpiricalApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_le_linear_of_mem_convexHull
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) (f : E →ₗ[ℝ] ℝ) :
    ∃ q ∈ S, f q ≤ f z := by
  by_contra h
  push Not at h
  have hz' := (convexHull_min h (convex_halfSpace_gt f.isLinear (f z))) hz
  exact (lt_irrefl (f z)) hz'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem empirical_step_sq_le (u z q : E) {R : ℝ}
    (hchoice : inner ℝ (u - z) q ≤ inner ℝ (u - z) z) (hq : ‖q‖ ≤ R) :
    ‖u + (q - z)‖ ^ 2 ≤ ‖u‖ ^ 2 + R ^ 2 := by
  have hqsq := pow_le_pow_left₀ (norm_nonneg q) hq 2
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at hchoice
  rw [← real_inner_comm z q] at hchoice
  rw [norm_add_sq_real, norm_sub_sq_real, inner_sub_right]
  nlinarith only [hchoice, hqsq, sq_nonneg ‖z‖]

theorem exists_convex_empirical_sum {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {R : ℝ} (hS : ∀ q ∈ S, ‖q‖ ≤ R) (n : ℕ) :
    ∃ q : Fin n → E, (∀ i, q i ∈ S) ∧
      ‖(∑ i, q i) - (n : ℝ) • z‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, hsum⟩ := ih
    let u := (∑ i, q i) - (n : ℝ) • z
    obtain ⟨x, hx, hchoice⟩ := exists_le_linear_of_mem_convexHull hz
      (innerSL ℝ (u - z)).toLinearMap
    refine ⟨Fin.cons x q, ?_, ?_⟩
    · exact Fin.forall_fin_succ.mpr ⟨hx, hq⟩
    · have hid : (∑ i : Fin (n + 1), Fin.cons x q i) - ((n + 1 : ℕ) : ℝ) • z =
          u + (x - z) := by
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_add,
          Nat.cast_one, add_smul, one_smul]
        dsimp only [u]
        abel
      rw [hid]
      have hstep := empirical_step_sq_le u z x hchoice (hS x hx)
      change ‖u‖ ^ 2 ≤ (n : ℝ) * R ^ 2 at hsum
      push_cast
      nlinarith only [hsum, hstep]

theorem exists_convex_empirical_average {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {R : ℝ} (hS : ∀ q ∈ S, ‖q‖ ≤ R)
    (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → E, (∀ i, q i ∈ S) ∧
      ‖(n : ℝ)⁻¹ • (∑ i, q i) - z‖ ^ 2 ≤ R ^ 2 / n := by
  obtain ⟨q, hq, hsum⟩ := exists_convex_empirical_sum hz hS n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨q, hq, ?_⟩
  have hid : (n : ℝ)⁻¹ • ((∑ i, q i) - (n : ℝ) • z) =
      (n : ℝ)⁻¹ • (∑ i, q i) - z := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hnR.ne', one_smul]
  rw [← hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnR.le), mul_pow]
  apply (mul_le_mul_of_nonneg_left hsum (sq_nonneg ((n : ℝ)⁻¹))).trans_eq
  field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def allocatedScaleLog (P : ℝ) : ℝ := (1+P^2)*(5*P+49)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarginalTailModeling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_empirical_length {R K tau : ℝ} (htau : 0 < tau) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 1 + R ^ 2 * K ^ 2 / tau ^ 2 ∧
      Real.sqrt (R ^ 2 * K ^ 2 / n) < tau := by
  let t := R ^ 2 * K ^ 2 / tau ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  let n := ⌊t⌋₊ + 1
  have hn : 0 < n := by dsimp only [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlen : (n : ℝ) ≤ 1 + t := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le ht]
  have hlt : t < (n : ℝ) := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hprod : R ^ 2 * K ^ 2 < tau ^ 2 * n := by
    have h := (div_lt_iff₀ (pow_pos htau 2)).mp hlt
    simpa only [mul_comm] using h
  have hsmall : R ^ 2 * K ^ 2 / n < tau ^ 2 := (div_lt_iff₀ hnR).mpr hprod
  have hsquare := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  refine ⟨n, hn, hlen, ?_⟩
  nlinarith [Real.sqrt_nonneg (R ^ 2 * K ^ 2 / n)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistNativeApproximationBudget
namespace OAI

section

namespace Erdos3

theorem allocatedModel_size_bounds {u p Q K C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) :
    2 / Real.exp (-Q) ≤ Real.exp (Q + 2) ∧
      1 + 4 * (K * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤
        Real.exp (2 * Q + 2 * u + 4 * p + 30) := by
  constructor
  · rw [Real.exp_neg, div_eq_mul_inv, inv_inv, Real.exp_add]
    nlinarith [Real.add_one_le_exp (2 : ℝ), Real.exp_pos Q]
  · let L := 2 * Q + 2 * u + 4 * p + 6
    have hL : 0 ≤ L := by dsimp only [L]; positivity
    have hlarge : 1 ≤ Real.exp L := Real.one_le_exp hL
    have hratio : 4 * (K * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤ 16 * Real.exp L := by
      calc
        _ ≤ 4 * (Real.exp p * (2 * Real.exp p)) ^ 2 /
            (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) := by gcongr
        _ = 16 * Real.exp L := by
          dsimp only [L]
          rw [Real.exp_neg, Real.exp_neg,
            show 2 * Q + 2 * u + 4 * p + 6 = Q + Q + ((u + 3) + (u + 3)) + ((p + p) + (p + p)) by ring]
          simp only [Real.exp_add]
          field_simp
          ring
    calc
      _ ≤ 17 * Real.exp L := by linarith
      _ ≤ Real.exp L * Real.exp 24 := by
        nlinarith [Real.add_one_le_exp (24 : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [L]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

abbrev n (q : ℕ) (_ : Fin q) : ℕ := 0

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

def allocatedSiteCoefficientLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 5 * D + 8

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedIdealCoverInputLog {A : Type*} [Semiring A] (m : ℕ) (D c : A) : A :=
  allocatedSiteCoefficientLog D + (m + 1 : ℕ) * D + c + 4

theorem allocatedIdealCoverInputLog_bounds (m : ℕ) {D c : ℝ}
    (hD : 0 ≤ D) (hc : 0 ≤ c) :
    let L := allocatedIdealCoverInputLog m D c
    0 ≤ L ∧ D ^ 2 + 2 * D ≤ L ∧ (m + 1 : ℕ) * D + 2 ≤ L ∧
      allocatedSiteCoefficientLog D + 1 ≤ L ∧ D ≤ L ∧ c ≤ L := by
  have hm : 0 ≤ (m + 1 : ℕ) * D := mul_nonneg (Nat.cast_nonneg _) hD
  dsimp only [allocatedIdealCoverInputLog, allocatedSiteCoefficientLog]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg D]
  constructor
  · linarith
  constructor <;> nlinarith [sq_nonneg D]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedModularCanonicalDetectorResourceConstants where
  m : ℕ
  Cperiod : ℕ
  Cgrid : ℕ
  Acover : ℕ
  Asample : ℕ
  Cpref : ℕ
  Apert : ℕ
  AmassWindow : ℕ
  Aproj : ℕ
  Aside : ℕ
  Cnative : ℕ
  Anorm : ℕ
  Amarginal : ℕ

structure PreparedModularCanonicalDetectorResources (α : Type*) where
  Q : α
  v : α
  w : α
  Dg : α
  Pproj : α
  coverLog : α
  Pmass : α
  Vlog : α
  Nlog : α
  Pbox : α
  Banalytic : α
  baseAmbient : α
  tq : α
  pq : α
  gridlog : α
  Fpref : α
  sumlog : α
  idealQ : α
  ambient : α
  Psample : α
  Pside : α
  Pnative : α
  nativeBudget : α
  E : α
  full : α
  required : α

namespace PreparedModularCanonicalDetectorResources

structure Bounds (r : PreparedModularCanonicalDetectorResources ℝ) (budget : ℝ) : Prop where
  Q : r.Q ∈ Set.Icc 0 budget
  v : r.v ∈ Set.Icc 0 budget
  w : r.w ∈ Set.Icc 0 budget
  Dg : r.Dg ∈ Set.Icc 0 budget
  Pproj : r.Pproj ∈ Set.Icc 0 budget
  coverLog : r.coverLog ∈ Set.Icc 0 budget
  Pmass : r.Pmass ∈ Set.Icc 0 budget
  Vlog : r.Vlog ∈ Set.Icc 0 budget
  Nlog : r.Nlog ∈ Set.Icc 0 budget
  Pbox : r.Pbox ∈ Set.Icc 0 budget
  Banalytic : r.Banalytic ∈ Set.Icc 0 budget
  baseAmbient : r.baseAmbient ∈ Set.Icc 0 budget
  tq : r.tq ∈ Set.Icc 0 budget
  pq : r.pq ∈ Set.Icc 0 budget
  gridlog : r.gridlog ∈ Set.Icc 0 budget
  Fpref : r.Fpref ∈ Set.Icc 0 budget
  sumlog : r.sumlog ∈ Set.Icc 0 budget
  idealQ : r.idealQ ∈ Set.Icc 0 budget
  ambient : r.ambient ∈ Set.Icc 0 budget
  Psample : r.Psample ∈ Set.Icc 0 budget
  Pside : r.Pside ∈ Set.Icc 0 budget
  Pnative : r.Pnative ∈ Set.Icc 0 budget
  nativeBudget : r.nativeBudget ∈ Set.Icc 0 budget
  E : r.E ∈ Set.Icc 0 budget
  full : r.full ∈ Set.Icc 0 budget
  required : r.required ∈ Set.Icc 0 budget

end PreparedModularCanonicalDetectorResources

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

theorem forecastAugmented_model_size {u p Q K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hF : 0 ≤ Fcap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    2 / Real.exp (-Q) ≤ Real.exp (Q + 2) ∧
      1 + 4 * (2 * K * C + Fcap) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤
        Real.exp (2 * Q + 2 * u + 4 * p + 34) := by
  have hKP : K + Fcap ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos p]
  have hCp' : C ≤ Real.exp (p + 1) := hCp.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨hcoeff, hterms⟩ := allocatedModel_size_bounds hu (show 0 ≤ p + 1 by linarith)
    hQ (add_nonneg hK hF) (by linarith : 0 ≤ C) hKP hCp'
  refine ⟨hcoeff, ?_⟩
  have hL : 2 * K * C + Fcap ≤ (K + Fcap) * (2 * C) := by nlinarith
  have hL0 : 0 ≤ 2 * K * C + Fcap := by positivity
  calc
    _ ≤ 1 + 4 * ((K + Fcap) * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) := by gcongr
    _ ≤ Real.exp (2 * Q + 2 * u + 4 * (p + 1) + 30) := hterms
    _ = _ := by congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_model_parameters {u p q sourceGain : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsource : 0 ≤ sourceGain) :
    let Q := max sourceGain (2 * u + 4 * p + q + 20)
    let Ptail := u + 2 * p + Q + 32
    0 ≤ Q ∧ 0 ≤ Ptail ∧ sourceGain ≤ Q ∧
      2 * u + 4 * p + q + 20 ≤ Q ∧
      Real.exp (-Q) ≤ Real.exp (-sourceGain) ∧
      u + 2 * p + Q + 32 ≤ Ptail := by
  dsimp only
  have hQ : 0 ≤ max sourceGain (2 * u + 4 * p + q + 20) :=
    hsource.trans (le_max_left _ _)
  exact ⟨hQ, by positivity, le_max_left _ _, le_max_right _ _,
    Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _)), le_rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProductChartRadius
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

def allocatedProductChartLog {A : Type*} [Semiring A] (m : ℕ) (D c : A) : A :=
  4 * ((8 * allocatedIdealCoverInputLog m D c + 14) + 2 * D + 2) + 6

theorem allocatedProductChartLog_mono (m : ℕ) {D c D' c' : ℝ}
    (hD : 0 ≤ D) (hDD : D ≤ D') (hcc : c ≤ c') :
    allocatedProductChartLog m D c ≤ allocatedProductChartLog m D' c' := by
  unfold allocatedProductChartLog allocatedIdealCoverInputLog allocatedSiteCoefficientLog
  gcongr

noncomputable def allocatedProductChartRadius (m : ℕ) (D c : ℝ) : ℝ :=
  Real.exp (-allocatedProductChartLog m D c)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InitializedEarlyCanonicalSliceScales
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

noncomputable def canonicalTransitionLip : ℝ≥0 :=
  Classical.choose exists_smoothTransition_lipschitz

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem stageSlice_addition_bounds (s : ℕ) {v P R : ℝ}
    (hv : 2 ≤ v) (hP : 0 ≤ P) (hRP : R ≤ P) :
    0 ≤ P + 2 * (v + 2) ^ 9 + v + s + 4 ∧
    R ≤ P + 2 * (v + 2) ^ 9 + v + s + 4 ∧
    v + s + 1 ≤ P + 2 * (v + 2) ^ 9 + v + s + 4 ∧
    2 * (v + 2) ^ 9 < P + 2 * (v + 2) ^ 9 + v + s + 4 := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hvpow : 0 ≤ 2 * (v + 2) ^ 9 := by positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  exact ⟨by linarith only [hP, hvpow, hv, hs0],
    by linarith only [hRP, hvpow, hv, hs0],
    by linarith only [hP, hvpow],
    by linarith only [hP, hv, hs0]⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedReadyNormalizationMassBudget
namespace OAI

section

namespace Erdos3

theorem relativeReturnedNormalization_denominator_pos (D s : ℕ) :
    (0 : ℝ) < ((D + 1) * (s + 1) ^ D : ℕ) := by
  positivity

theorem relativeReturnedNormalization_denominator_le_exp (D s : ℕ)
    {cost : ℝ} (hD : (D : ℝ) ≤ cost) :
    (((D + 1) * (s + 1) ^ D : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * cost) := by
  have hD1 : ((D + 1 : ℕ) : ℝ) ≤ Real.exp cost := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hD, Real.add_one_le_exp cost]
  have hs1 : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (s : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (s : ℝ)
  have hpower : (((s + 1) ^ D : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * cost) := by
    calc
      _ = ((s + 1 : ℕ) : ℝ) ^ D := Nat.cast_pow _ _
      _ ≤ (Real.exp (s : ℝ)) ^ D := pow_le_pow_left₀ (Nat.cast_nonneg _) hs1 D
      _ = Real.exp ((D : ℝ) * s) := (Real.exp_nat_mul (s : ℝ) D).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg s))
  calc
    _ = ((D + 1 : ℕ) : ℝ) * (((s + 1) ^ D : ℕ) : ℝ) := Nat.cast_mul _ _
    _ ≤ Real.exp cost * Real.exp ((s : ℝ) * cost) :=
      mul_le_mul hD1 hpower (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * cost) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem relativeReturnedNormalization_mass_expression_lower (D s : ℕ)
    {cost massLog normBudget originalMass : ℝ}
    (hD : (D : ℝ) ≤ cost) (hmass : Real.exp (-massLog) ≤ originalMass) :
    Real.exp (-(massLog + ((s : ℝ) + 1) * cost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) := by
  have hden := relativeReturnedNormalization_denominator_pos D s
  have hbound := relativeReturnedNormalization_denominator_le_exp D s hD
  have hdiv : Real.exp (-massLog) / Real.exp (((s : ℝ) + 1) * cost) ≤
      originalMass / ((D + 1) * (s + 1) ^ D : ℕ) :=
    (div_le_div_of_nonneg_left (Real.exp_nonneg _) hden hbound).trans
      (div_le_div_of_nonneg_right hmass hden.le)
  calc
    _ = (Real.exp (-massLog) / Real.exp (((s : ℝ) + 1) * cost)) *
        Real.exp (-normBudget) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (Real.exp_nonneg _)

end Erdos3

end

section

namespace Erdos3

theorem preparedReady_mass_lower {p gain originalMass : ℝ}
    (hgain : Real.exp (-p) ≤ gain) (hmass : gain / 16 < originalMass) :
    Real.exp (-(p + 16)) ≤ originalMass := by
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by
    linarith only [Real.add_one_le_exp (16 : ℝ)]
  have hexp : Real.exp (-(p + 16)) = Real.exp (-p) / Real.exp 16 := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp]
  exact ((div_le_div_of_nonneg_left (Real.exp_nonneg (-p)) (by norm_num) h16).trans
    (div_le_div_of_nonneg_right hgain (by norm_num))).trans hmass.le

theorem preparedReady_normalized_mass_lower (D s : ℕ)
    {p gain originalMass childCost normBudget : ℝ}
    (hD : (D : ℝ) ≤ childCost) (hgain : Real.exp (-p) ≤ gain)
    (hmass : gain / 16 < originalMass) :
    Real.exp (-(p + 16 + ((s : ℝ) + 1) * childCost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) :=
  relativeReturnedNormalization_mass_expression_lower D s hD
    (preparedReady_mass_lower hgain hmass)

theorem preparedReady_capped_normalized_mass_lower (rankBound s : ℕ)
    {p gain originalMass childCost normBudget : ℝ} (hcost : 0 ≤ childCost)
    (hgain : Real.exp (-p) ≤ gain) (hmass : gain / 16 < originalMass) :
    let D := min rankBound ⌊childCost⌋₊
    Real.exp (-(p + 16 + ((s : ℝ) + 1) * childCost + normBudget)) ≤
      (originalMass / ((D + 1) * (s + 1) ^ D : ℕ)) * Real.exp (-normBudget) := by
  apply preparedReady_normalized_mass_lower _ _ _ hgain hmass
  exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hcost)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical TensorProduct

theorem affineCenterBudget_arithmetic {p a b : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2*p+a+b+1 ∧ p ≤ 2*p+a+b+1 ∧ a ≤ 2*p+a+b+1 ∧
      2*p+b+1 ≤ 2*p+a+b+1 := by
  constructor
  · linarith only [hp, ha, hb]
  constructor
  · linarith only [hp, ha, hb]
  constructor <;> linarith only [hp, ha, hb]

theorem affineCenterBudget_exp {p b : ℝ} :
    Real.exp (p+b+1) * Real.exp p = Real.exp (2*p+b+1) := by
  rw [← Real.exp_add]
  congr 1
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineNormalizedBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical TensorProduct

noncomputable def certifiedAffineLongSideBound (p : ℝ) : ℝ :=
  Real.exp ((p + 2) ^ 9) ^ 2 * Real.exp p

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem terminal_affine_budget_arithmetic {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2 * c + a + b + 1 ∧ b ≤ 2 * c + a + b + 1 := by
  constructor <;> linarith only [hc, ha, hb]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def candidatePhysicalOrdinaryBudget (pFull : ℝ) : ℝ :=
  (pFull + 4) ^ 10

theorem candidatePhysicalOrdinaryBudget_bounds {pFull : ℝ} (hp : 0 ≤ pFull) :
    0 ≤ candidatePhysicalOrdinaryBudget pFull ∧
      pFull ≤ candidatePhysicalOrdinaryBudget pFull ∧
      (2 * pFull + 3) ^ 3 + pFull ≤ candidatePhysicalOrdinaryBudget pFull ∧
      pFull + 2 + 2 * (pFull + 4) ^ 2 ≤ candidatePhysicalOrdinaryBudget pFull ∧
      3 * pFull ≤ candidatePhysicalOrdinaryBudget pFull := by
  have hfour : (pFull + 4) ^ 4 ≤ candidatePhysicalOrdinaryBudget pFull :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ pFull + 4) (by norm_num : 4 ≤ 10)
  have hpow3 : 0 ≤ pFull ^ 3 := pow_nonneg hp _
  have hpow4 : 0 ≤ pFull ^ 4 := pow_nonneg hp _
  have hmass : (2 * pFull + 3) ^ 3 + pFull ≤ (pFull + 4) ^ 4 := by
    nlinarith [sq_nonneg pFull]
  have hlip : pFull + 2 + 2 * (pFull + 4) ^ 2 ≤ (pFull + 4) ^ 4 := by
    nlinarith [sq_nonneg pFull]
  have hlinear : 3 * pFull ≤ (pFull + 4) ^ 4 := by
    nlinarith [sq_nonneg pFull]
  exact ⟨by unfold candidatePhysicalOrdinaryBudget; positivity,
    (show pFull ≤ (pFull + 4) ^ 4 by linarith only [hp, hlinear]).trans hfour,
    hmass.trans hfour, hlip.trans hfour, hlinear.trans hfour⟩

theorem certifiedAffine_budget_lower_arithmetic {p q : ℝ}
    (hp : 0 ≤ p) (hq : p ≤ q) :
    p ≤ 2 * p + (q + 2) ^ 10 + (q + 2) ^ 8 + 1 ∧
      (p + 2) ^ 9 ≤ 2 * p + (q + 2) ^ 10 + (q + 2) ^ 8 + 1 := by
  have hq0 : 0 ≤ q := hp.trans hq
  have hbase : p + 2 ≤ q + 2 := by linarith only [hq]
  have hpowers : (p + 2) ^ 9 ≤ (q + 2) ^ 10 :=
    (pow_le_pow_left₀ (by positivity) hbase 9).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ q + 2) (by norm_num : 9 ≤ 10))
  have hten : 0 ≤ (q + 2) ^ 10 := pow_nonneg (by positivity) _
  have height : 0 ≤ (q + 2) ^ 8 := pow_nonneg (by positivity) _
  constructor <;> linarith only [hp, hten, height, hpowers]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PrecenterNativeSelectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem precenter_native_selection_mass_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] (rank : ℕ)
    {b t d mass : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hrank : (rank : ℝ) ≤ d)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b) (hmass : 0 ≤ mass) :
    Real.exp (-(d * (b + t))) * mass ≤
      mass / ((Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank) := by
  have hcardpos : (0 : ℝ) < Fintype.card Bin := by
    exact_mod_cast Fintype.card_pos
  have hden : 0 < (Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank := by positivity
  have hbound : (Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank ≤
      Real.exp (d * (b + t)) := by
    calc
      _ ≤ (Real.exp b) ^ rank * (Real.exp t) ^ rank :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hcardpos.le hcard rank) (by positivity)
      _ = Real.exp ((rank : ℝ) * (b + t)) := by
        rw [← mul_pow, ← Real.exp_add, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrank (add_nonneg hb ht))
  calc
    _ = mass / Real.exp (d * (b + t)) := by rw [Real.exp_neg]; ring
    _ ≤ _ := div_le_div_of_nonneg_left hmass hden hbound

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct Classical

def allocatedFrozenTaggedFamilyInputBudget (b t : ℝ) : ℝ :=
  b + t + (b + 3) ^ 4 + 1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleLocalPhysical
    (m nX count : ℕ) (Qstride Pk : ℝ) : ℝ :=
  ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + Pk

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPrimitiveFrontInitialLong
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped BigOperators Classical TensorProduct NNReal

theorem allocatedCandidate_initialLong_excluded_bound
    {K : Type*} (side : K → ℝ) (oldKeep : K → Prop)
    {cost initialShortLog : ℝ}
    (hshort : ∀ i, ¬oldKeep i → side i ≤ Real.exp cost) :
    ∀ i, ¬(oldKeep i ∧ Real.exp initialShortLog ≤ side i) →
      side i ≤ Real.exp (max cost initialShortLog) := by
  intro i hi
  by_cases hold : oldKeep i
  · have hside : ¬Real.exp initialShortLog ≤ side i := fun hs => hi ⟨hold, hs⟩
    exact (lt_of_not_ge hside).le.trans
      (Real.exp_le_exp.mpr (le_max_right cost initialShortLog))
  · exact (hshort i hold).trans
      (Real.exp_le_exp.mpr (le_max_left cost initialShortLog))

end Erdos3.VectorPolynomial

end

end OAI
end


