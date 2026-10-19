-- Prove2me | Definitions.Def_OAIE3v2B054
-- name    : OAIE3v2B054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:34.31598+00:00
-- url     : https://prove2.me/theorems/02dcf431-4072-4717-a04b-bcb39a7279e6
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 55 of 311
-- statement:
--   Definitions bundle 55 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B007`, `OAIE3v2B010`, `OAIE3v2B012`, `OAIE3v2B013`, `OAIE3v2B014`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B018`, `OAIE3v2B022`, `OAIE3v2B023` of this split.
--
--   Modules: `Dynamics/ReducedRelativeBudget.lean`, `Dynamics/StepOneSplittingBudget.lean`, `Dynamics/SymmetricUnitBudget.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/CyclicShortShiftSet.lean`, `Estimates/DenseCorrelationPairs.lean`, `Estimates/NativeDilationObservable.lean`, `Estimates/NativeSelectedCorrelators.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/ShiftTestingGowers.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/SquarefreeSplitCount.lean`, `Estimates/UnitExpansionCorrelation.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Geometry/DilationPairCoordinates.lean`, `Geometry/NativeDilationObservableMetric.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Geometry/NativeTripleObservableMetric.lean`, `Linear/ComparisonBasisBudget.lean`, `Linear/NativeRankRelationExistence.lean`, `Linear/RankQuotientHeightBudget.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/FinitePhaseCancellation.lean`, `Polynomial/TriplePhaseCancellation.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B014
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B018
import Definitions.Def_OAIE3v2B022
import Definitions.Def_OAIE3v2B023

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReducedRelativeBudget
namespace OAI

section

namespace Erdos3

theorem exists_reducedRelative_budget (s a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      4 * (p + (s + 2)) ^ (s + 2) + 2 + (reducedRelativeParameter s p + a) ^ a ≤
        (p + C) ^ C ∧
      (reducedRelativeParameter s p + b) ^ b ≤ (p + C) ^ C := by
  let D : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2)
  let Q : Polynomial ℕ := 2 * Polynomial.X + 2 * D + 4
  let P : Polynomial ℕ := 4 * D + 2 + (Q + Polynomial.C a) ^ a + (Q + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hd : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hq := (reducedRelativeParameter_controls s hp).1
  have ha : 0 ≤ (reducedRelativeParameter s p + a) ^ a := by positivity
  have hb : 0 ≤ (reducedRelativeParameter s p + b) ^ b := by positivity
  have hsum : 4 * (p + (s + 2)) ^ (s + 2) + 2 + (reducedRelativeParameter s p + a) ^ a +
      (reducedRelativeParameter s p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, D, reducedRelativeParameter, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DilationPairCoordinates
namespace OAI

section

namespace Erdos3

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem scaledPairAssemble_decompose (q : ℚ) (x : L × L) :
    scaledPairAssemble q (scaledPairDifference q x) x.2 = x := by
  apply Prod.ext <;> simp [scaledPairAssemble]

def scaledPairLayerEquiv (P Q : Submodule ℚ L) (hQP : Q ≤ P) (q : ℚ) :
    (Q × P) ≃ₗ[ℚ] scaledPairLayer P Q q where
  toFun x := ⟨scaledPairAssemble q x.1 x.2,
    ⟨P.add_mem (hQP x.1.property) (P.smul_mem q x.2.property), x.2.property,
      by
        rw [scaledPairDifference_assemble]
        exact x.1.property⟩⟩
  invFun x := (⟨scaledPairDifference q x.val, x.property.2.2⟩, ⟨x.val.2, x.property.2.1⟩)
  left_inv x := by
    apply Prod.ext
    · exact Subtype.ext (scaledPairDifference_assemble q (x.1 : L) (x.2 : L))
    · rfl
  right_inv x := Subtype.ext (scaledPairAssemble_decompose q x.val)
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · simp only [scaledPairAssemble, Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
      abel
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · change a • (x.1 : L) + q • (a • (x.2 : L)) = a • ((x.1 : L) + q • (x.2 : L))
      rw [smul_add, smul_comm q a]
    · rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_weighted_pair {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d z : ∀ i, J i → ℂ)
    {delta C D : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hsum : delta ≤ ‖∑ i, ∑ j, (c i * d i j) * z i j‖) :
    ∃ i j, delta / (C * D) ≤ ‖z i j‖ := by
  obtain ⟨p, hp⟩ := exists_large_weighted_term
    (fun p : Sigma J => c p.1 * d p.1 p.2) (fun p => z p.1 p.2)
    hdelta (mul_pos hC hD) (sum_pair_coefficient_norms_le c d hD.le hc hd)
    (by simpa only [Fintype.sum_sigma] using hsum)
  exact ⟨p.1, p.2, hp⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unit_expansion_correlation {X K : Type*} {A : K → Type*}
    [Fintype K] [∀ k, Fintype (A k)] (s : Finset X)
    (f Q : X → ℂ) (P : K → X → ℂ) (c : ∀ k, A k → ℂ) (psi : ∀ k, A k → X → ℂ)
    (hunit : ∀ x ∈ s, ∑ k, ‖P k x‖ ^ 2 = 1)
    (hexp : ∀ k x, x ∈ s → Q x * star (P k x) = ∑ a, c k a * psi k a x)
    {rho D M : ℝ} (hrho : 0 < rho) (hD : 0 < D) (hM : 0 < M)
    (hcard : (Fintype.card K : ℝ) ≤ D) (hc : ∀ k, (∑ a, ‖c k a‖) ≤ M)
    (hcorr : rho ≤ ‖𝔼 x ∈ s, f x * Q x‖) :
    ∃ k a, rho / (D * M) ≤ ‖𝔼 x ∈ s, f x * P k x * psi k a x‖ := by
  have hpoint (x : X) (hx : x ∈ s) :
      f x * Q x = ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) := by
    rw [complex_unit_vector_resolution (fun k => P k x) (hunit x hx) (Q x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hexp k x hx, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hmean : (𝔼 x ∈ s, f x * Q x) =
      ∑ k, ∑ a, c k a * (𝔼 x ∈ s, f x * P k x * psi k a x) := by
    calc
      _ = 𝔼 x ∈ s, ∑ k, ∑ a, c k a * (f x * P k x * psi k a x) :=
        Finset.expect_congr rfl hpoint
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  apply exists_large_weighted_pair (fun _ : K => (1 : ℂ)) c
    (fun k a => 𝔼 x ∈ s, f x * P k x * psi k a x) hrho hD hM
  · simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcard
  · exact hc
  · simpa only [one_mul, ← hmean] using hcorr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicShortShiftSet
namespace OAI

section

namespace Erdos3

theorem exists_cyclicShortShiftSet {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (hH : H.Nonempty) :
    ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
      (H.card : ℝ) / 2 ≤ (S.card : ℝ) ∧ CyclicShortShiftSet S := by
  classical
  let label (x : ZMod N) : Bool := decide (2 * x.val < N)
  have hcount : (Finset.univ : Finset Bool).card • ((H.card : ℝ) / 2) ≤ (H.card : ℝ) := by
    norm_num
    linarith
  obtain ⟨b, _, hb⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := H) (t := (Finset.univ : Finset Bool)) (f := label)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hcount
  let S := H.filter (fun x => label x = b)
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (half_pos hpos).trans_le hb
  refine ⟨S, Finset.filter_subset _ _, hS, hb, ?_⟩
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hxN := x.val_lt
  have hyN := y.val_lt
  cases b <;> simp only [label, decide_eq_false_iff_not, decide_eq_true_eq] at hx' hy'
  · by_cases hxy : (y.val : ℤ) ≤ x.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega
  · by_cases hxy : (y.val : ℤ) ≤ x.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega

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

theorem shifted_test_cauchy_schwarz (v B : G → ℂ) (L : G → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) :
    (𝔼 h, ‖𝔼 x, v x * (B (x + h) * L h x)‖) ^ 2 ≤
      M ^ 2 * (𝔼 h, 𝔼 k,
        ‖𝔼 x, v x * star (v (x + h - k)) * L h x * star (L k (x + h - k))‖) := by
  have hex (h : G) := exists_complex_unit_phase (𝔼 x, v x * (B (x + h) * L h x))
  choose a ha hphase using hex
  have hcs := finite_family_cauchy_schwarz B
    (fun h y => a h * v (y - h) * L h (y - h)) hB
  rw [shift_phase_average v B L a hphase, Complex.norm_real,
    Real.norm_of_nonneg (Finset.expect_nonneg (fun h _ => norm_nonneg _))] at hcs
  simpa only [shift_phase_cross_norm v L a ha] using hcs

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

theorem exists_dense_first_fibers {I G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (T : Finset I) (a h : I → G) (hinj : Set.InjOn (fun i => (a i, h i)) (T : Set I))
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : ρ * (Fintype.card G : ℝ) ^ 2 ≤ T.card) :
    ∃ A : Finset G, A.Nonempty ∧ ρ / 2 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      ∀ x ∈ A, ρ / 2 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  let F (x : G) := T.filter (fun i => a i = x)
  have hcard (x : G) : (F x).card ≤ Fintype.card G := by
    have hmap : Function.Injective (fun t : F x => h t.val) := by
      intro u v huv
      apply Subtype.ext
      apply hinj (Finset.mem_filter.mp u.property).1 (Finset.mem_filter.mp v.property).1
      exact Prod.ext ((Finset.mem_filter.mp u.property).2.trans (Finset.mem_filter.mp v.property).2.symm) huv
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hmap
  have hsum : ∑ x : G, (F x).card = T.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (f := a) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  let density (x : G) := ((F x).card : ℝ) / Fintype.card G
  have hmean : ρ ≤ 𝔼 x, density x := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [density, ← Finset.sum_div, ← Nat.cast_sum, hsum]
    apply (le_div_iff₀ hN).mpr
    apply (le_div_iff₀ hN).mpr
    nlinarith only [hsize]
  have hunit (x : G) : density x ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (hcard x) : ((F x).card : ℝ) ≤ Fintype.card G)
  obtain ⟨A, hAsize, hA⟩ := exists_dense_level_set density hρ.le hunit hmean
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le (by positivity) hAsize
  refine ⟨A, Finset.card_pos.mp (by exact_mod_cast hApos), hAsize, ?_⟩
  intro x hx
  exact (le_div_iff₀ hN).mp (hA x hx)

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

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem additiveQuadrupleCorrelation_le_one (g : G → G → ℂ)
    (hg : ∀ h x, ‖g h x‖ ≤ 1) (a h k : G) : additiveQuadrupleCorrelation g a h k ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hg _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hg _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (hg _ _)).trans (hg _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

namespace Erdos3

variable {N : ℕ} [NeZero N]

theorem mem_cyclicInterval_representatives (a b : ℕ) (hab : a ≤ b) (hbN : b ≤ N) (x : ZMod N) :
    x ∈ cyclicInterval (a : ZMod N) (b - a) ↔ a ≤ x.val ∧ x.val < b := by
  constructor
  · intro hx
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hx
    have hk' := Finset.mem_range.mp hk
    have hak : a + k < b := by omega
    have he' : ((a + k : ℕ) : ZMod N) = x := by simpa only [Nat.cast_add] using he
    rw [← he', ZMod.val_natCast_of_lt (hak.trans_le hbN)]
    omega
  · intro hx
    refine Finset.mem_image.mpr ⟨x.val - a, Finset.mem_range.mpr (by omega), ?_⟩
    have he : a + (x.val - a) = x.val := Nat.add_sub_of_le hx.1
    calc
      (a : ZMod N) + (x.val - a : ℕ) = ((a + (x.val - a) : ℕ) : ZMod N) := by push_cast; rfl
      _ = x := by rw [he, ZMod.natCast_zmod_val]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

def cyclicQuarter (N : ℕ) (i : Fin 4) : Finset (ZMod N) :=
  cyclicInterval (quarterLower N i : ZMod N) (quarterUpper N i - quarterLower N i)

theorem quarter_short (N : ℕ) (hN : 0 < N) (i : Fin 4) :
    2 * ((quarterUpper N i : ℤ) - quarterLower N i - 1) < N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

theorem quarter_diameter_lt_third (N : ℕ) (hN : 0 < N) (i : Fin 4) :
    3 * ((quarterUpper N i : ℤ) - quarterLower N i - 1) < N := by
  fin_cases i <;> simp only [quarterLower, quarterUpper] <;> omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

theorem multidegreeFactorial_pos (a : σ → ℕ) : 0 < multidegreeFactorial a :=
  Finset.prod_pos fun i _ => Nat.factorial_pos (a i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} (bound : σ → ℕ)

noncomputable instance replicatedPermutationFintype [Fintype σ] :
    Fintype (ReplicatedPermutation bound) := Fintype.ofFinite _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

theorem ceil_exp_power_le_exp {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ((⌈Real.exp p⌉₊ ^ n : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * (p + 1)) := by
  rw [Nat.cast_pow, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ceil_exp_le_exp_add_one hp) n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.StepOneSplittingBudget
namespace OAI

section

namespace Erdos3

theorem stepOne_denominator_budget {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 4) :=
  (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr
    ((show p + 1 ≤ 3 * p + 1 by linarith).trans (stepOne_linear_budget hp)))

theorem stepOne_slow_budget {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) / (2 * (Real.exp (-p) / Real.exp p)) ≤ Real.exp ((p + 2) ^ 4) := by
  have hδ : 0 < Real.exp (-p) / Real.exp p := div_pos (Real.exp_pos _) (Real.exp_pos _)
  calc
    _ ≤ (⌈Real.exp p⌉₊ : ℝ) / (Real.exp (-p) / Real.exp p) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (by linarith)
    _ ≤ Real.exp (p + 1) / (Real.exp (-p) / Real.exp p) :=
      div_le_div_of_nonneg_right (ceil_exp_le_exp_add_one hp) hδ.le
    _ = Real.exp (3 * p + 1) := by
      rw [← Real.exp_sub, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (stepOne_linear_budget hp)

theorem stepOne_kernel_height_budget {p : ℝ} (hp : 0 ≤ p) :
    ((2 * ⌈Real.exp p⌉₊ ^ 2 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    _ ≤ Real.exp 1 * (Real.exp (p + 1)) ^ 2 := by
      apply mul_le_mul
      · have h := Real.add_one_le_exp (1 : ℝ)
        linarith only [h]
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ceil_exp_le_exp_add_one hp) 2
      · positivity
      · positivity
    _ = Real.exp (2 * p + 3) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h : 2 * p + 3 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
      exact h.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 2 ≤ 4))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SymmetricUnitBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def symmetricUnitConstant (m : ℕ) : ℕ :=
  ⌈2 / momentLowerConstant m⌉₊ + m * m + 2 + (m + 1) * momentWeightBound m

noncomputable def symmetricUnitBudget (m : ℕ) (p : ℝ) : ℝ :=
  (2 * m + 2 : ℝ) * (p + 1) + symmetricUnitConstant m

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

universe u v

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v}
  [Fintype ι]
  {L₀ : Type u}
  {L : ι → Type u}
  [LieRing L₀]
  [∀ i, LieRing (L i)]
  [LieAlgebra ℚ L₀]
  [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ}
  {d : ι → ℕ}

variable {H : Type u} [LieRing H] [LieAlgebra ℚ H]

def optionMaps (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) :
    ∀ i : Option ι, H →ₗ⁅ℚ⁆ optionLieSpace L₀ L i
  | none => φ₀
  | some i => φ i

end RationalFilteredNilmanifold
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

def cyclicCutCell (S : Finset ℕ) (N a : ℕ) : Finset (ZMod N) :=
  cyclicInterval (a : ZMod N) (intervalCutUpper S N a - a)

theorem mem_cyclicCutCell {N : ℕ} [NeZero N] (S : Finset ℕ) {a : ℕ} (ha : a ≤ N)
    (x : ZMod N) : x ∈ cyclicCutCell S N a ↔ a ≤ x.val ∧ x.val < intervalCutUpper S N a :=
  mem_cyclicInterval_representatives a _ (le_intervalCutUpper S N ha)
    (intervalCutUpper_le_end S N a) x

theorem sum_cyclicCutCell_indicator {N : ℕ} [NeZero N] (S : Finset ℕ)
    (hzero : 0 ∈ S) (hbound : ∀ a ∈ S, a ≤ N) (x : ZMod N) :
    (∑ a : S, finiteIndicator (cyclicCutCell S N a) x) = 1 := by
  obtain ⟨a, ha, hax, hxa⟩ := exists_intervalCut S N hzero x.val_lt
  have hmem : x ∈ cyclicCutCell S N a := (mem_cyclicCutCell S (hbound a ha) x).mpr ⟨hax, hxa⟩
  rw [Finset.sum_eq_single (⟨a, ha⟩ : S)]
  · simp only [finiteIndicator, hmem, ite_true]
  · intro b _ hba
    have hnot : x ∉ cyclicCutCell S N b := by
      intro hx
      have hb := (mem_cyclicCutCell S (hbound b b.property) x).mp hx
      have he := intervalCut_unique S N b.property ha hb.1 hb.2 hax hxa
      exact hba (Subtype.ext he)
    simp only [finiteIndicator, hnot, ite_false]
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module

def rankQuotientLayerHeight (n m H : ℕ) : ℕ :=
  (n + 1) * (H * rationalKernelHeight m H) ^ n

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

theorem multidegreeFactorial_mono {a b : σ → ℕ} (h : a ≤ b) :
    multidegreeFactorial a ≤ multidegreeFactorial b :=
  Finset.prod_le_prod' (fun i _ => Nat.factorial_le (h i))

theorem multidegreeFactorial_le_total (a : σ → ℕ) :
    multidegreeFactorial a ≤ (∑ i, a i).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ a)

noncomputable def comparisonBasisHeight (bound : σ → ℕ) (p : ℝ) : ℕ :=
  ⌈Real.exp p⌉₊ * multidegreeFactorial bound

theorem comparisonBasisHeight_ge_ceil (bound : σ → ℕ) (p : ℝ) :
    ⌈Real.exp p⌉₊ ≤ comparisonBasisHeight bound p :=
  Nat.le_mul_of_pos_right _ (multidegreeFactorial_pos bound)

theorem comparisonBasisHeight_ge_factorial (bound : σ → ℕ) (p : ℝ) :
    multidegreeFactorial bound ≤ comparisonBasisHeight bound p :=
  Nat.le_mul_of_pos_left _ (one_le_ceil_exp p)

theorem comparisonBasisHeight_pos (bound : σ → ℕ) (p : ℝ) :
    0 < comparisonBasisHeight bound p :=
  (multidegreeFactorial_pos bound).trans_le (comparisonBasisHeight_ge_factorial bound p)

theorem comparisonBasisHeight_le_exp (bound : σ → ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (comparisonBasisHeight bound p : ℝ) ≤ Real.exp (comparisonBasisBudget (∑ i, bound i) p) := by
  have hf : (multidegreeFactorial bound : ℝ) ≤ Real.exp (((∑ i, bound i : ℕ) : ℝ) ^ 2) := by
    exact (Nat.cast_le.mpr (multidegreeFactorial_le_total bound)).trans (factorial_le_exp_sq _)
  rw [comparisonBasisHeight, Nat.cast_mul]
  calc
    _ ≤ Real.exp (p + 1) * Real.exp (((∑ i, bound i : ℕ) : ℝ) ^ 2) :=
      mul_le_mul (ceil_exp_le_exp_add_one hp) hf (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3

theorem replicatedFrequencyHeight_le_exp (d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (replicatedFrequencyHeight d H : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hprod : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp p := by rw [Nat.cast_mul]; gcongr
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact rational_sum_cost_le_exp d (H * H) hp 2 1 hprod
    (by simpa only [pow_one] using hd.trans (by linarith))

theorem replicatedFrequencyHeight_ceil_exp (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 4) := by
  have h := replicatedFrequencyHeight_le_exp d ⌈Real.exp p⌉₊
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  have heq : p + 1 + 2 = p + 3 := by ring
  simpa only [heq] using h

theorem replicatedFrequencyDenominator_le_exp (t N d l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : N ≤ 2 ^ t * d)
    (hl : l ≤ replicatedFrequencyHeight d ⌈Real.exp p⌉₊ ^ N) :
    (l : ℝ) ≤ Real.exp (replicatedFrequencyDenominatorBudget t p) := by
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ t * (p + 3) := by
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ _ := mul_le_mul_of_nonneg_left (hd.trans (by linarith)) (by positivity)
  calc
    (l : ℝ) ≤ (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ^ N := by exact_mod_cast hl
    _ ≤ (Real.exp ((p + 3) ^ 4)) ^ N :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (replicatedFrequencyHeight_ceil_exp d hp hd) N
    _ = Real.exp ((N : ℝ) * (p + 3) ^ 4) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (((2 : ℝ) ^ t * (p + 3)) * (p + 3) ^ 4) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hNr (by positivity))
    _ = _ := by congr 1; unfold replicatedFrequencyDenominatorBudget; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FinitePhaseCancellation
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

theorem circle_character_mul_star (θ : CircleFourier.Circle) :
    character θ * star (character θ) = 1 := by
  rw [← character_neg, ← character_add, add_neg_cancel, character_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal

theorem signedTensorProduct_lipschitz {X : Type*} [PseudoMetricSpace X]
    (m : ℤ) (f : Fin m.natAbs → X → ℂ) {K : ℝ≥0}
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, ‖f i x‖ ≤ 1) :
    LipschitzWith (m.natAbs * K) (fun x => signedTensorProduct m (fun i => f i x)) := by
  have h := bounded_lipschitz_fintype_prod f (B := 1) le_rfl hf hn
  have hp : LipschitzWith (m.natAbs * K) (fun x => ∏ i, f i x) := by
    simpa only [Fintype.card_fin, one_pow, mul_one] using h.2
  unfold signedTensorProduct
  split_ifs
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← star_sub, norm_star] using hp.dist_le_mul x y
  · exact hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal TensorProduct

noncomputable def invariantVerticalBudget (m : ℕ) (p : ℝ) : ℝ :=
  symmetricUnitBudget m (2 * p) + p + m + 1

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

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem additiveQuadrupleCorrelation_support (g : G → G → ℂ) (H : Finset G)
    (hg : ∀ h, h ∉ H → ∀ x, g h x = 0) {a h k : G}
    (hpos : 0 < additiveQuadrupleCorrelation g a h k) :
    h ∈ H ∧ h - a ∈ H ∧ k ∈ H ∧ k - a ∈ H := by
  have hmem : h ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg h hn] at hpos
  have hsub : h - a ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg (h - a) hn] at hpos
  have hkmem : k ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg k hn] at hpos
  have hksub : k - a ∈ H := by
    by_contra hn
    simp [additiveQuadrupleCorrelation, hg (k - a) hn] at hpos
  exact ⟨hmem, hsub, hkmem, hksub⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem additiveQuadrupleCorrelation_real_scale {G : Type*} [AddCommGroup G] [Fintype G]
    (g : G → G → ℂ) (c : ℝ) (hc : 0 ≤ c) (a h k : G) :
    additiveQuadrupleCorrelation (fun h x => (c : ℂ) * g h x) a h k =
      c ^ 4 * additiveQuadrupleCorrelation g a h k := by
  unfold additiveQuadrupleCorrelation
  have hmean : (𝔼 x, star ((c : ℂ) * g h x) * ((c : ℂ) * g (h - a) (x + a)) *
      ((c : ℂ) * g k x) * star ((c : ℂ) * g (k - a) (x + a))) =
      (c : ℂ) ^ 4 * (𝔼 x, star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hmean, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeDilationObservableMetric
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_signed_tensor_cross_product {X : Type*} [PseudoMetricSpace X]
    (m : ℤ) (f₀ : X → ℂ) (f : Fin m.natAbs → X → ℂ) {K : ℝ≥0}
    (hf₀ : LipschitzWith K f₀) (hf : ∀ j, LipschitzWith K (f j))
    (h₀ : ∀ x, ‖f₀ x‖ ≤ 1) (hbound : ∀ j x, ‖f j x‖ ≤ 1) :
    LipschitzWith ((m.natAbs + 1 : ℝ≥0) * K)
      (fun x => f₀ x * star (signedTensorProduct m (fun j => f j x))) := by
  have h := lipschitz_mul_star_of_bounds f₀ (fun x => signedTensorProduct m (fun j => f j x))
    (Bf := 1) (Bg := 1) hf₀ (signedTensorProduct_lipschitz m f hf hbound)
    h₀ (fun x => signedTensorProduct_norm_le m _ (fun j => hbound j x))
  convert h using 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3

noncomputable def positivePolynomialInputBudget (t : ℕ) (p : ℝ) : ℝ :=
  p + 1 + squarefreeInputBudget t p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TriplePhaseCancellation
namespace OAI

section

namespace Erdos3

theorem circle_character_triple_cancel (a b : CircleFourier.Circle) :
    CircleFourier.character (a + b) * star (CircleFourier.character a) *
      star (CircleFourier.character b) = 1 := by
  rw [← CircleFourier.character_neg, ← CircleFourier.character_neg,
    ← CircleFourier.character_add, ← CircleFourier.character_add]
  convert CircleFourier.character_zero using 1
  congr 1
  abel

theorem triple_phase_cancellation (v : Fin 3 → ℂ) (θ : Fin 3 → CircleFourier.Circle)
    (hθ : θ 0 = θ 1 + θ 2) :
    (CircleFourier.character (θ 0) * v 0) * star (CircleFourier.character (θ 1) * v 1) *
      star (CircleFourier.character (θ 2) * v 2) = v 0 * star (v 1) * star (v 2) := by
  rw [star_mul, star_mul]
  calc
    _ = (CircleFourier.character (θ 0) * star (CircleFourier.character (θ 1)) *
        star (CircleFourier.character (θ 2))) * (v 0 * star (v 1) * star (v 2)) := by ring
    _ = _ := by rw [hθ, circle_character_triple_cancel, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTripleObservableMetric
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitz_three_conjugates_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f : Fin 3 → X → ℂ) {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (hbound : ∀ j x, ‖f j x‖ ≤ 1) :
    LipschitzWith (3 * K) (fun x => f 0 x * star (f 1 x) * star (f 2 x)) := by
  have h01 := lipschitz_mul_star_of_bounds (f 0) (f 1)
    (Bf := 1) (Bg := 1) (hf 0) (hf 1) (hbound 0) (hbound 1)
  have hb01 (x : X) : ‖f 0 x * star (f 1 x)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mul_one] using
      mul_le_mul (hbound 0 x) (hbound 1 x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h := lipschitz_mul_star_of_bounds (fun x => f 0 x * star (f 1 x)) (f 2)
    (Bf := 1) (Bg := 1) h01 (hf 2) hb01 (hbound 2)
  convert h using 1
  ring

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

theorem coordinateTranslation_right (l : List σ) (i : σ) (hi : i ∉ l) (x : Option σ → ℤ) :
    coordinateAdditionInputs i (fun j => coordinateTranslationHom l j x) 2 =
      coordinateTranslatedInput l (coordinateReplaceInput i x) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hi]
  · simp [coordinateAdditionInputs, coordinateTranslationHom, coordinateTranslatedInput,
      coordinateReplaceInput, coordinateReplaceIndex, hj]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

theorem rank_pair_density_loss (p : ℝ) :
    Real.exp (-(11 * p + 7)) ≤ Real.exp (-p) / 4 *
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) := by
  have he : Real.exp (-(8 * p + 1)) * Real.exp (-p) ^ 3 = Real.exp (-(11 * p + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hright : Real.exp (-p) / 4 *
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) = Real.exp (-(11 * p + 1)) / 64 := by
    calc
      _ = (Real.exp (-(8 * p + 1)) * Real.exp (-p) ^ 3) / 64 := by ring
      _ = _ := by rw [he]
  rw [hright]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
  have h64 := two_pow_le_exp_of_le 6 le_rfl
  norm_num at h64
  calc
    _ ≤ Real.exp (-(11 * p + 7)) * Real.exp 6 :=
      mul_le_mul_of_nonneg_left h64 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end


