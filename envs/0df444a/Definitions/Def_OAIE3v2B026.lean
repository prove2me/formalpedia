-- Prove2me | Definitions.Def_OAIE3v2B026
-- name    : OAIE3v2B026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:28.219835+00:00
-- url     : https://prove2.me/theorems/19759f91-a8cc-41bc-aaf0-a9951d8cd7fa
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 27 of 311
-- statement:
--   Definitions bundle 27 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/FinitePrimitiveCorrectionBudget.lean`, `Dynamics/PrimitiveCorrectionRadiusBudget.lean`, `Estimates/FiniteBoundedListEnumeration.lean`, `Estimates/FiniteClassifiedRepresentatives.lean`, `Estimates/FiniteEnumerationFilter.lean`, `Estimates/FiniteGradedBranchPrefixLog.lean`, `Estimates/NativeRoundedGraphEnergy.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/RealSubquotientEquiv.lean`, `Estimates/RoundingRecoveryScale.lean`, `Estimates/SharedFreeRoundingThreshold.lean`, `Fourier/DivisibleCharacterExtension.lean`, `Fourier/NormalizedTwistLocalizedFourierSelection.lean`, `Fourier/QuadraticLocalFrequency.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Geometry/DenseRealBoxCell.lean`, `Geometry/RealCoordinateFunctionals.lean`, `Lattices/LatticeCoordinateLifts.lean`, `Lattices/NaturalScaleIntegerWindow.lean`, `Lattices/ProperAffineBoxRestriction.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/FiniteRankTriangularFinset.lean`, `Linear/ProperCyclicKernelBasis.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Linear/SpatialMatrixBlockWideProbability.lean`, `Linear/TaggedSubmoduleBasis.lean`, `Polynomial/FiniteSupportedPolynomialSubstitution.lean`, `Probability/RoundedModelDensityBudget.lean`, `Sampling/BoundedKernelGridEnumerationBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PrimitiveCorrectionRadiusBudget
namespace OAI

section

namespace Erdos3

def primitiveCorrectionRadius (s u b i : ℕ) (L M : ℝ) : ℝ :=
  (((u + b : ℕ) : ℝ) + 1) ^ s * M * (max 1 ((i : ℝ) * L)) ^ s

theorem primitiveCorrectionRadius_nonneg (s u b i : ℕ) (L : ℝ) {M : ℝ}
    (hM : 0 ≤ M) : 0 ≤ primitiveCorrectionRadius s u b i L M := by
  unfold primitiveCorrectionRadius
  positivity

theorem primitiveCorrectionRadius_le_exp (s u b i : ℕ) {p t L M : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hu : (u : ℝ) ≤ p) (hb : (b : ℝ) ≤ p) (hi : (i : ℝ) ≤ p)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp t) (hLcap : L ≤ Real.exp t) :
    primitiveCorrectionRadius s u b i L M ≤
      Real.exp ((s : ℝ) * (3 * p + 1) + (s + 1) * t) := by
  have hbase : ((u + b : ℕ) : ℝ) + 1 ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_add]
    linarith [Real.add_one_le_exp (2 * p + 1)]
  have hie : (i : ℝ) ≤ Real.exp p :=
    hi.trans (by linarith [Real.add_one_le_exp p])
  have hmax : max 1 ((i : ℝ) * L) ≤ Real.exp (p + t) := by
    apply max_le
    · exact Real.one_le_exp (add_nonneg hp ht)
    · calc
        _ ≤ (i : ℝ) * Real.exp t := mul_le_mul_of_nonneg_left hLcap (Nat.cast_nonneg _)
        _ ≤ Real.exp p * Real.exp t :=
          mul_le_mul_of_nonneg_right hie (Real.exp_nonneg _)
        _ = Real.exp (p + t) := (Real.exp_add _ _).symm
  calc
    primitiveCorrectionRadius s u b i L M ≤
        (Real.exp (2 * p + 1)) ^ s * Real.exp t * (Real.exp (p + t)) ^ s := by
      unfold primitiveCorrectionRadius
      apply mul_le_mul
      · exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase s) hMcap hM
          (by positivity)
      · exact pow_le_pow_left₀ (by positivity) hmax s
      · positivity
      · positivity
    _ = Real.exp ((s : ℝ) * (3 * p + 1) + (s + 1) * t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem one_tmul_mem_real_baseChange_iff {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S : Submodule ℚ V) (v : V) : (1 : ℝ) ⊗ₜ[ℚ] v ∈ S.baseChange ℝ ↔ v ∈ S := by
  constructor
  · intro hv
    let : Module.Free ℚ (V ⧸ S) := Module.Free.of_divisionRing ℚ (V ⧸ S)
    have hker : S.baseChange ℝ ≤ LinearMap.ker (S.mkQ.baseChange ℝ) := by
      rw [Submodule.baseChange_eq_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      change S.mkQ.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) = 0
      rw [LinearMap.baseChange_tmul]
      have hxq : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [hxq, TensorProduct.tmul_zero]
    have hz : (1 : ℝ) ⊗ₜ[ℚ] S.mkQ v = 0 := hker hv
    have hinj := Module.Flat.tensorProduct_mk_injective (R := ℚ) (S := ℝ) (M := V ⧸ S)
    have hvq : S.mkQ v = 0 := hinj (by simpa only [TensorProduct.mk_apply, map_zero] using hz)
    exact (Submodule.Quotient.mk_eq_zero S).mp hvq
  · exact Submodule.tmul_mem_baseChange_of_mem 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget
namespace OAI

section

namespace Erdos3

theorem real_grid_window_count_le_exp (d m : ℕ) {B p : ℝ}
    (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    (((2 * ⌈(m : ℝ) * B⌉₊ + 3) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
  have hprod : (m : ℝ) * B ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using
      mul_le_mul hm hB hB0 (Real.exp_nonneg p)
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hB0)).le
  have hone : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by linarith)
  have hseven : (7 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hbase : ((2 * ⌈(m : ℝ) * B⌉₊ + 3 : ℕ) : ℝ) ≤ Real.exp (2 * p + 6) := by
    rw [Real.exp_add]
    push_cast
    have h := mul_le_mul_of_nonneg_left hseven (Real.exp_nonneg (2 * p))
    nlinarith
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (2 * p + 6)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp ((d : ℝ) * (2 * p + 6)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (2 * p + 6)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hp (sq_nonneg p)]

end Erdos3

end

section

namespace Erdos3

theorem real_grid_integer_box_count_bound (d m : ℕ) {B p : ℝ}
    (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    (((2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hprod : (m : ℝ) * B ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using
      mul_le_mul hm hB hB0 (Real.exp_nonneg p)
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hB0)).le
  have hone : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by linarith)
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbase : ((2 * ⌈(m : ℝ) * B⌉₊ + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 4) := by
    rw [Real.exp_add]
    push_cast
    have h := mul_le_mul_of_nonneg_left hfive (Real.exp_nonneg (2 * p))
    nlinarith
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (2 * p + 4)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp ((d : ℝ) * (2 * p + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (2 * p + 4)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hp (sq_nonneg p)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FinitePrimitiveCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem primitive_correction_denominator_bound (q d s : ℕ) {t : ℝ}
    (hq : (q : ℝ) ≤ Real.exp t) (hd : (d : ℝ) ≤ Real.exp t) :
    ((q * d ^ s : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * t) := by
  have hp : ((d ^ s : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * t) := by
    rw [Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg d) hd s).trans_eq (Real.exp_nat_mul t s).symm
  calc
    _ = (q : ℝ) * ((d ^ s : ℕ) : ℝ) := by rw [Nat.cast_mul]
    _ ≤ Real.exp t * Real.exp ((s : ℝ) * t) :=
      mul_le_mul hq hp (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * t) := by rw [← Real.exp_add]; congr 1; ring

theorem primitive_correction_dimension_bound (u i r s : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hu : (u : ℝ) ≤ p) (hi : (i : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) :
    ((((u + i + 1) ^ s) * r : ℕ) : ℝ) ≤ p * (2 * p + 1) ^ s := by
  have hbase : ((u + i + 1 : ℕ) : ℝ) ≤ 2 * p + 1 := by push_cast; linarith
  have hpw := pow_le_pow_left₀ (Nat.cast_nonneg (u + i + 1)) hbase s
  push_cast at hpw
  push_cast
  calc
    _ ≤ (2 * p + 1) ^ s * p :=
      mul_le_mul hpw hr (Nat.cast_nonneg _) (pow_nonneg (by positivity) s)
    _ = _ := mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteBoundedListEnumeration
namespace OAI

section

namespace Erdos3

theorem exists_boundedList_option_padding {α : Type*} {M : ℕ}
    (c : Fin M → α) (P : α → Prop)
    (hcover : ∀ x, P x → ∃ i, c i = x) :
    ∀ (N : ℕ) (l : List α), l.length ≤ N → (∀ x ∈ l, P x) →
      ∃ v : Fin N → Option (Fin M),
        (List.ofFn v).filterMap (Option.map c) = l := by
  intro N
  induction N with
  | zero =>
      intro l hlen hP
      have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      subst l
      exact ⟨fun i => Fin.elim0 i, by simp⟩
  | succ N ih =>
      intro l hlen hP
      cases l with
      | nil =>
          exact ⟨fun _ => none, by simp [List.ofFn_const]⟩
      | cons x l =>
          obtain ⟨i, hi⟩ := hcover x (hP x (by simp))
          have hlen' : l.length ≤ N := Nat.le_of_succ_le_succ hlen
          obtain ⟨v, hv⟩ := ih l hlen' (fun y hy => hP y (by simp [hy]))
          refine ⟨Fin.cons (some i) v, ?_⟩
          simpa [List.ofFn_succ, hi] using congrArg (List.cons x) hv

end Erdos3

end

section

namespace Erdos3

theorem exists_finite_bounded_list_enumeration {α : Type*} {M : ℕ}
    (c : Fin M → α) (P : α → Prop)
    (hvalid : ∀ i, P (c i)) (hcover : ∀ x, P x → ∃ i, c i = x) (N : ℕ) :
    ∃ n : ℕ, n ≤ (M + 1) ^ N ∧ ∃ candidates : Fin n → List α,
      (∀ j, (candidates j).length ≤ N) ∧
      (∀ j x, x ∈ candidates j → P x) ∧
      ∀ l : List α, l.length ≤ N → (∀ x, x ∈ l → P x) →
        ∃ j, candidates j = l := by
  classical
  let V := Fin N → Option (Fin M)
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let decode : V → List α := fun v => (List.ofFn v).filterMap (Option.map c)
  refine ⟨Fintype.card V, ?_, (fun j => decode (e.symm j)), ?_, ?_, ?_⟩
  · simp [V]
  · intro j
    exact (List.length_filterMap_le _ _).trans (by simp)
  · intro j x hx
    obtain ⟨o, _, ho⟩ := List.mem_filterMap.mp hx
    obtain ⟨i, _, hi⟩ := Option.map_eq_some_iff.mp ho
    exact hi ▸ hvalid i
  · intro l hlen hl
    obtain ⟨v, hv⟩ := exists_boundedList_option_padding c P hcover N l hlen hl
    refine ⟨e v, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteClassifiedRepresentatives
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_indexed_representative_enumeration
    {Γ α : Type*} [Fintype Γ] (valid : Γ → α → Prop) (rel : Γ → α → α → Prop)
    {B : ℝ}
    (hbranch : ∀ i, ∃ n : ℕ, (n : ℝ) ≤ B ∧ ∃ candidate : Fin n → α,
      (∀ j, valid i (candidate j)) ∧
      ∀ x, valid i x → ∃ j, rel i (candidate j) x) :
    ∃ n : ℕ, (n : ℝ) ≤ Fintype.card Γ * B ∧
      ∃ candidate : Fin n → Γ × α,
        (∀ j, valid (candidate j).1 (candidate j).2) ∧
        ∀ i x, valid i x → ∃ j,
          (candidate j).1 = i ∧ rel i (candidate j).2 x := by
  classical
  choose n hn candidate hvalid hcover using hbranch
  let J := Σ i : Γ, Fin (n i)
  let e := Fintype.equivFin J
  let combined : Fin (Fintype.card J) → Γ × α :=
    fun j => ((e.symm j).1, candidate (e.symm j).1 (e.symm j).2)
  refine ⟨Fintype.card J, ?_, combined, ?_, ?_⟩
  · change ((Fintype.card (Σ i : Γ, Fin (n i)) : ℕ) : ℝ) ≤ _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Nat.cast_sum]
    calc
      (∑ i, (n i : ℝ)) ≤ ∑ _i : Γ, B := Finset.sum_le_sum (fun i _ => hn i)
      _ = Fintype.card Γ * B := by simp
  · intro j
    exact hvalid (e.symm j).1 (e.symm j).2
  · intro i x hx
    obtain ⟨j, hj⟩ := hcover i x hx
    have hpair : combined (e ⟨i, j⟩) = (i, candidate i j) :=
      congrArg (fun k : J => (k.1, candidate k.1 k.2)) (e.symm_apply_apply ⟨i, j⟩)
    refine ⟨e ⟨i, j⟩, congrArg Prod.fst hpair, ?_⟩
    rw [hpair]
    exact hj

end Erdos3

end

section

namespace Erdos3

theorem exists_finite_classified_representatives {Λ α : Type*} {n : ℕ}
    (labels : Fin n → Λ) (valid : Λ → α → Prop) (rel : Λ → α → α → Prop)
    (hlabels : ∀ l x, valid l x → ∃ i, labels i = l) {B : ℝ}
    (hbranch : ∀ i, ∃ c : ℕ, (c : ℝ) ≤ B ∧ ∃ candidate : Fin c → α,
      (∀ j, valid (labels i) (candidate j)) ∧
      ∀ x, valid (labels i) x → ∃ j, rel (labels i) (candidate j) x) :
    ∃ c : ℕ, (c : ℝ) ≤ (n : ℝ) * B ∧ ∃ candidate : Fin c → Λ × α,
      (∀ j, valid (candidate j).1 (candidate j).2) ∧
      ∀ l x, valid l x → ∃ j, (candidate j).1 = l ∧ rel l (candidate j).2 x := by
  obtain ⟨c, hc, family, hvalid, hcover⟩ :=
    exists_finite_indexed_representative_enumeration
      (fun i => valid (labels i)) (fun i => rel (labels i)) hbranch
  let candidate := fun j : Fin c => (labels (family j).1, (family j).2)
  refine ⟨c, by simpa only [Fintype.card_fin] using hc, candidate, hvalid, ?_⟩
  intro l x hx
  obtain ⟨i, hi⟩ := hlabels l x hx
  obtain ⟨j, hj, hr⟩ := hcover i x (hi ▸ hx)
  refine ⟨j, ?_, ?_⟩
  · change labels (family j).1 = l
    rw [hj, hi]
  · exact hi ▸ hr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEnumerationFilter
namespace OAI

section

namespace Erdos3

theorem exists_filtered_finite_enumeration {α : Type*} {n : ℕ}
    (c : Fin n → α) (P : α → Prop) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : Fin m → α,
      (∀ j, P (d j)) ∧
      (∀ j, ∃ i, c i = d j) ∧
      ∀ x, P x → (∃ i, c i = x) → ∃ j, d j = x := by
  classical
  let I := {i : Fin n // P (c i)}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, ?_, (fun j => c (e.symm j).val), ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin n => P (c i))
  · intro j
    exact (e.symm j).property
  · intro j
    exact ⟨(e.symm j).val, rfl⟩
  · rintro x hx ⟨i, hi⟩
    have hpi : P (c i) := hi ▸ hx
    refine ⟨e ⟨i, hpi⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGradedBranchPrefixLog
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def finiteGradedBranchLevel {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) :
    ∀ n, Finset (State n)
  | 0 => {initial}
  | n + 1 => (finiteGradedBranchLevel initial children n).biUnion (children n)

@[simp] theorem finiteGradedBranchLevel_mem_zero {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1))) (x : State 0) :
    x ∈ finiteGradedBranchLevel initial children 0 ↔ x = initial := by
  exact Finset.mem_singleton

theorem finiteGradedBranchLevel_mem_succ {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (n : ℕ) (x : State (n + 1)) :
    x ∈ finiteGradedBranchLevel initial children (n + 1) ↔
      ∃ y ∈ finiteGradedBranchLevel initial children n, x ∈ children n y :=
  Finset.mem_biUnion

theorem finiteGradedBranchLevel_child_mem {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    {n : ℕ} {y : State n} {x : State (n + 1)}
    (hy : y ∈ finiteGradedBranchLevel initial children n) (hx : x ∈ children n y) :
    x ∈ finiteGradedBranchLevel initial children (n + 1) :=
  (finiteGradedBranchLevel_mem_succ initial children n x).mpr ⟨y, hy, hx⟩

theorem finiteGradedBranchLevel_all_valid {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (valid : ∀ n, State n → Prop) (hinit : valid 0 initial)
    (hstep : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      valid n x → ∀ y ∈ children n x, valid (n + 1) y) :
    ∀ n, n ≤ depth → ∀ x ∈ finiteGradedBranchLevel initial children n, valid n x := by
  intro n
  induction n with
  | zero =>
    intro _ x hx
    have he := (finiteGradedBranchLevel_mem_zero initial children x).mp hx
    simpa only [he] using hinit
  | succ n ih =>
    intro hn x hx
    obtain ⟨y, hy, hxy⟩ := (finiteGradedBranchLevel_mem_succ initial children n x).mp hx
    exact hstep n (Nat.lt_of_succ_le hn) y hy (ih (Nat.le_of_succ_le hn) y hy) x hxy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem finiteGradedBranchLevel_card_le_exp_sum {State : ℕ → Type*}
    (initial : State 0) (children : ∀ n, State n → Finset (State (n + 1)))
    (depth : ℕ) (logCap : ℕ → ℝ)
    (hcard : ∀ n, n < depth → ∀ x ∈ finiteGradedBranchLevel initial children n,
      ((children n x).card : ℝ) ≤ Real.exp (logCap n)) :
    ∀ n, n ≤ depth → ((finiteGradedBranchLevel initial children n).card : ℝ) ≤
      Real.exp (∑ j ∈ Finset.range n, logCap j) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [finiteGradedBranchLevel]
  | succ n ih =>
    intro hn
    have hnd : n < depth := Nat.lt_of_succ_le hn
    change (((finiteGradedBranchLevel initial children n).biUnion (children n)).card : ℝ) ≤ _
    calc
      _ ≤ ((∑ x ∈ finiteGradedBranchLevel initial children n, (children n x).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ x ∈ finiteGradedBranchLevel initial children n, ((children n x).card : ℝ) := by
        simp only [Nat.cast_sum]
      _ ≤ ∑ _x ∈ finiteGradedBranchLevel initial children n, Real.exp (logCap n) :=
        Finset.sum_le_sum (fun x hx => hcard n hnd x hx)
      _ = ((finiteGradedBranchLevel initial children n).card : ℝ) * Real.exp (logCap n) := by
        simp [nsmul_eq_mul]
      _ ≤ Real.exp (∑ j ∈ Finset.range n, logCap j) * Real.exp (logCap n) :=
        mul_le_mul_of_nonneg_right (ih (Nat.le_of_lt hnd)) (Real.exp_nonneg _)
      _ = Real.exp (∑ j ∈ Finset.range (n + 1), logCap j) := by
        rw [Finset.sum_range_succ, Real.exp_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RoundingRecoveryScale
namespace OAI

section

namespace Erdos3

theorem exists_rounding_modulus (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ) ∧
      (M : ℝ) * l * ε ≤ 1 := by
  let u : ℝ := (l : ℝ) * ε
  have hu : 0 < u := mul_pos (by exact_mod_cast hl) hε
  have hu2 : 2 * u ≤ 1 := by simpa only [u, mul_assoc] using hsmall
  have hx : 2 ≤ 1 / u := (le_div_iff₀ hu).mpr hu2
  let M := ⌊1 / u⌋₊
  have hM : 0 < M := Nat.floor_pos.mpr (by linarith)
  have hfloor : (M : ℝ) ≤ 1 / u := Nat.floor_le (by positivity)
  have hlt : 1 / u < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨M, hM, ?_, ?_⟩
  · have heq : 1 / (2 * (l : ℝ) * ε) = (1 / u) / 2 := by
      dsimp only [u]
      ring
    rw [heq]
    linarith
  · have h := (le_div_iff₀ hu).mp hfloor
    simpa only [u, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

theorem rounding_recovery_error_le (M l : ℕ) [NeZero M] (hl : 0 < l)
    {ε : ℝ} (hε : 0 < ε) (hM : 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ)) :
    1 / ((M : ℝ) * l) ≤ 2 * ε := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hMR : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hmul := (div_le_iff₀ (by positivity : 0 < 2 * (l : ℝ) * ε)).mp hM
  apply (div_le_iff₀ (mul_pos hMR hlR)).mpr
  nlinarith

theorem exists_rounding_modulus_with_recovery (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ (M : ℝ) * l * ε ≤ 1 ∧ 1 / ((M : ℝ) * l) ≤ 2 * ε := by
  obtain ⟨M, hM, hlower, hupper⟩ := exists_rounding_modulus l hl hε hsmall
  let _ : NeZero M := ⟨hM.ne'⟩
  exact ⟨M, hM, hupper, rounding_recovery_error_le M l hl hε hlower⟩

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

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem real_four_single (k : Fin 4) (x : ℝ ⊗[ℚ] V) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V))
        ((LinearMap.single ℚ (fun _ : Fin 4 => V) k).baseChange ℝ x) =
      LinearMap.single ℝ (fun _ : Fin 4 => ℝ ⊗[ℚ] V) k x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    ext j
    change a ⊗ₜ[ℚ] ((Pi.single k x : Fin 4 → V) j) =
      (Pi.single k (a ⊗ₜ[ℚ] x) : Fin 4 → ℝ ⊗[ℚ] V) j
    rw [TensorProduct.tmul_single]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def coordinateFunctionalMatrix (b : Basis I ℚ V)
    (ℓ : V →ₗ[ℚ] (J → ℚ)) : Matrix J I ℚ := fun j i => ℓ (b i) j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DenseRealBoxCell
namespace OAI

section

namespace Erdos3

noncomputable def realBoxCellCount (C : ℝ) (q : ℕ) : ℕ := ⌊2 * q * C⌋₊ + 1

theorem realBoxCellCount_pos (C : ℝ) (q : ℕ) : 0 < realBoxCellCount C q := by
  unfold realBoxCellCount
  omega

theorem realBoxCellCount_le {C : ℝ} (hC : 0 ≤ C) (q : ℕ) :
    (realBoxCellCount C q : ℝ) ≤ 2 * q * C + 1 := by
  unfold realBoxCellCount
  push_cast
  exact add_le_add (Nat.floor_le (by positivity)) (le_refl 1)

theorem realBoxCell_floor_lt {C : ℝ} (q : ℕ) (y : ℝ) (hy : |y| ≤ C) :
    ⌊(q : ℝ) * (y + C)⌋₊ < realBoxCellCount C q := by
  have hupper : (q : ℝ) * (y + C) ≤ 2 * q * C := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 (Nat.cast_nonneg (α := ℝ) q)
    nlinarith
  exact Nat.lt_succ_of_le (Nat.floor_mono hupper)

noncomputable def realBoxCellCenter (C : ℝ) (q n : ℕ) : ℝ :=
  ((n : ℝ) + 1 / 2) / q - C

theorem realBoxCell_offset {C : ℝ} (q : ℕ) (hq : 0 < q) (y : ℝ) (hy : |y| ≤ C) :
    |y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊| ≤ (1 / 2 : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnonneg : 0 ≤ (q : ℝ) * (y + C) := by
    exact mul_nonneg hqR.le (by linarith [(abs_le.mp hy).1])
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((q : ℝ) * (y + C))
  have he : (q : ℝ) * (y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊) =
      (q : ℝ) * (y + C) - (⌊(q : ℝ) * (y + C)⌋₊ + (1 / 2 : ℝ)) := by
    unfold realBoxCellCenter
    field_simp
    ring
  apply (le_div_iff₀ hqR).mpr
  calc
    _ = |(q : ℝ) * (y - realBoxCellCenter C q ⌊(q : ℝ) * (y + C)⌋₊)| := by
      rw [abs_mul, abs_of_pos hqR]
      ring
    _ ≤ _ := by rw [he]; apply abs_le.mpr; constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.DivisibleCharacterExtension
namespace OAI

section

namespace Erdos3

theorem exists_divisible_character_extension
    {A G Q : Type} [AddCommGroup A] [AddCommGroup G] [AddCommGroup Q]
    [DivisibleBy Q ℤ] (η : A →+ G) (φ : A →+ Q)
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ θ : G →+ Q, ∀ x, θ (η x) = φ x := by
  let : Module.Injective ℤ Q := (Module.Baer.of_divisible Q).injective
  let f := (QuotientAddGroup.kerLift η).toIntLinearMap
  let g := (QuotientAddGroup.lift η.ker φ (fun x hx => hker x hx)).toIntLinearMap
  obtain ⟨θ, hθ⟩ := Module.Injective.out f (QuotientAddGroup.kerLift_injective η) g
  exact ⟨θ.toAddMonoidHom, fun x => hθ (QuotientAddGroup.mk x)⟩

theorem exists_cyclic_real_character_lift
    {A : Type} [AddCommGroup A] {N : ℕ} [NeZero N]
    (η : A →+ ZMod N) (φ : A →+ AddCircle (1 : ℝ))
    (hker : ∀ x, η x = 0 → φ x = 0) :
    ∃ t ∈ Set.Ico (0 : ℝ) 1,
      (∃ k : ℤ, (N : ℝ) * t = (k : ℝ)) ∧
      ∀ (x : A) (n : ℤ), η x = (n : ZMod N) →
        φ x = (((n : ℝ) * t : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨χ, hχ⟩ := exists_divisible_character_extension η φ hker
  obtain ⟨t, ht, he⟩ := AddCircle.eq_coe_Ico (χ 1)
  have hN : N • χ 1 = 0 := by rw [← map_nsmul]; simp [nsmul_eq_mul]
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← he, ← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hN
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by simpa [nsmul_eq_mul] using hk.symm⟩
  · intro x n hn
    rw [← hχ x, hn]
    have hcast : (n : ZMod N) = n • (1 : ZMod N) := by simp [zsmul_eq_mul]
    rw [hcast, map_zsmul, ← he, ← AddCircle.coe_zsmul]
    congr 1
    simp [zsmul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module

variable {ι : Type*}

def integerVectorRealMap : (ι → ℤ) →ₗ[ℤ] (ι → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem integerVectorRealMap_injective :
    Function.Injective (integerVectorRealMap (ι := ι)) := by
  intro x y h
  ext i
  exact Int.cast_injective (congrFun h i)

variable [Fintype ι] {N : ℕ}

def cyclicIntegerKernel (η : (ι → ℤ) →+ ZMod N) : Submodule ℤ (ι → ℝ) :=
  (LinearMap.ker η.toIntLinearMap).map integerVectorRealMap

omit [Fintype ι] in
theorem integerVectorRealMap_mem_cyclicIntegerKernel
    (η : (ι → ℤ) →+ ZMod N) (x : ι → ℤ) :
    integerVectorRealMap x ∈ cyclicIntegerKernel η ↔ η x = 0 := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact integerVectorRealMap_injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Fintype ι] in
theorem nsmul_integerVectorRealMap_mem_cyclicIntegerKernel
    (η : (ι → ℤ) →+ ZMod N) (x : ι → ℤ) :
    N • integerVectorRealMap x ∈ cyclicIntegerKernel η := by
  rw [← map_nsmul, integerVectorRealMap_mem_cyclicIntegerKernel, map_nsmul]
  simp [nsmul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]

omit [Fintype ι] [DecidableEq ι] in
theorem card_mul_le_of_kernel_translates (φ : (ι → ℤ) →+ G)
    (S X : Finset (ι → ℤ)) (k : ℕ) (v : ι → ℤ) (hv : v ≠ 0)
    (hker : φ v = 0) (hinj : Set.InjOn φ (S : Set _))
    (hsub : ∀ x ∈ S, ∀ j < k, x + j • v ∈ X) : S.card * k ≤ X.card := by
  classical
  rw [← Finset.card_range k, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun z : (ι → ℤ) × ℕ => z.1 + z.2 • v)
  · intro z hz
    exact hsub z.1 (Finset.mem_product.mp hz).1 z.2
      (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  · intro x hx y hy hxy
    change x.1 + x.2 • v = y.1 + y.2 • v at hxy
    have hφ : φ x.1 = φ y.1 := by
      have h := congrArg φ hxy
      simpa only [map_add, map_nsmul, hker, nsmul_zero, add_zero] using h
    have hbase : x.1 = y.1 := hinj (Finset.mem_product.mp hx).1
      (Finset.mem_product.mp hy).1 hφ
    apply Prod.ext hbase
    have hmul : x.2 • v = y.2 • v := by
      rw [hbase] at hxy
      exact add_left_cancel hxy
    have hnonzero : ¬ ∀ i, v i = 0 := fun h => hv (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnonzero
    have hiEq := congrFun hmul i
    simp only [Pi.smul_apply, nsmul_eq_mul] at hiEq
    exact_mod_cast mul_right_cancel₀ hi hiEq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProperCyclicKernelBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

theorem cyclicIntegerKernel_eq_zero_of_lt_radii
    {ι : Type} [Fintype ι] {N : ℕ} (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (y : ι → ℝ) (hy : y ∈ cyclicIntegerKernel η)
    (hsmall : ∀ i, |y i| < (R i : ℝ) + 1) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  change ∀ i, |(x i : ℝ)| < (R i : ℝ) + 1 at hsmall
  have hbound : ∀ i, |x i| ≤ (R i : ℤ) := by
    intro i
    have h : |x i| < (R i : ℤ) + 1 := by exact_mod_cast hsmall i
    omega
  have he : x = 0 := hinj hbound (by simp) (by simpa using hx)
  rw [he, map_zero]

theorem cyclicIntegerKernel_nonzero_large_coordinate
    {ι : Type} [Fintype ι] {N : ℕ} (η : (ι → ℤ) →+ ZMod N) (R : ι → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (y : ι → ℝ) (hy : y ∈ cyclicIntegerKernel η) (hne : y ≠ 0) :
    ∃ i, (R i : ℝ) + 1 ≤ |y i| := by
  by_contra! h
  exact hne (cyclicIntegerKernel_eq_zero_of_lt_radii η R hinj y hy h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

theorem local_cyclic_torus_total_loss_le {r : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p) :
    p + (r : ℝ) * ((p + 4) ^ 5 + 17) ≤ (p + 4) ^ 7 := by
  let U := p + 4
  have hU : 4 ≤ U := by dsimp [U]; linarith
  have h1 : 1 ≤ U := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hpow : (4 : ℝ) ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ (by norm_num) hU 3
  have hlinear : 18 * U ≤ U ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hpow hU0
    nlinarith
  calc
    _ ≤ U + U * (U ^ 5 + 17) := by dsimp [U]; gcongr <;> linarith
    _ = U ^ 6 + 18 * U := by ring
    _ ≤ U ^ 6 + U ^ 4 := add_le_add (le_refl _) hlinear
    _ ≤ U ^ 6 + U ^ 6 := add_le_add (le_refl _) (pow_le_pow_right₀ h1 (by omega))
    _ ≤ U ^ 7 := by
      have h := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ U by linarith) (pow_nonneg hU0 6)
      nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TaggedSubmoduleBasis
namespace OAI

section

namespace Erdos3

open Module

variable {R T : Type*} [Semiring R] {J I : T → Type*}

def taggedSubmodule (U : ∀ t, Submodule R (J t → R)) : Submodule R ((Σ t, J t) → R) where
  carrier := {x | ∀ t, (fun j => x ⟨t, j⟩) ∈ U t}
  zero_mem' := fun t => (U t).zero_mem
  add_mem' := fun hx hy t => (U t).add_mem (hx t) (hy t)
  smul_mem' := fun c _ hx t => (U t).smul_mem c (hx t)

@[simp]
theorem mem_taggedSubmodule (U : ∀ t, Submodule R (J t → R)) (x : (Σ t, J t) → R) :
    x ∈ taggedSubmodule U ↔ ∀ t, (fun j => x ⟨t, j⟩) ∈ U t := Iff.rfl

def taggedSubmoduleEquiv (U : ∀ t, Submodule R (J t → R)) :
    (∀ t, U t) ≃ₗ[R] taggedSubmodule U where
  toFun x := ⟨fun j => (x j.1 : J j.1 → R) j.2, fun t => (x t).property⟩
  invFun x := fun t => ⟨fun j => (x : (Σ t, J t) → R) ⟨t, j⟩, x.property t⟩
  left_inv x := by
    funext t
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    funext j
    rfl
  map_add' x y := rfl
  map_smul' c x := rfl

@[simp]
theorem taggedSubmoduleEquiv_apply (U : ∀ t, Submodule R (J t → R))
    (x : ∀ t, U t) (t : T) (j : J t) :
    (taggedSubmoduleEquiv U x : (Σ t, J t) → R) ⟨t, j⟩ = (x t : J t → R) j := rfl

@[simp]
theorem taggedSubmoduleEquiv_symm_apply (U : ∀ t, Submodule R (J t → R))
    (x : taggedSubmodule U) (t : T) (j : J t) :
    ((taggedSubmoduleEquiv U).symm x t : J t → R) j =
      (x : (Σ t, J t) → R) ⟨t, j⟩ := rfl

variable [Fintype T]

noncomputable def taggedSubmoduleBasis (U : ∀ t, Submodule R (J t → R))
    (b : ∀ t, Basis (I t) R (U t)) : Basis (Σ t, I t) R (taggedSubmodule U) :=
  (Pi.basis b).map (taggedSubmoduleEquiv U)

theorem taggedSubmoduleBasis_apply [DecidableEq T]
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (t' : T) (j : J t') :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t', j⟩ =
      ((Pi.single (M := fun t => U t) t (b t i) t' : U t') : J t' → R) j := by
  rw [taggedSubmoduleBasis, Basis.map_apply, Pi.basis_apply]
  rfl

@[simp]
theorem taggedSubmoduleBasis_same
    (U : ∀ t, Submodule R (J t → R)) (b : ∀ t, Basis (I t) R (U t))
    (t : T) (i : I t) (j : J t) :
    (taggedSubmoduleBasis U b ⟨t, i⟩ : (Σ t, J t) → R) ⟨t, j⟩ = (b t i : J t → R) j := by
  classical
  rw [taggedSubmoduleBasis_apply, Pi.single_eq_same]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*}

noncomputable def rationalTagChartMatrix
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) :
    (Σ j, Fin (n j)) → (Σ j, J j) → ℚ :=
  fun a x => (Pi.single (M := fun j => J j → ℚ) a.1
    (b a.1 a.2 : J a.1 → ℚ)) x.1 x.2

theorem rationalTagChartMatrix_same
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) (j : Fin m) (a : Fin (n j)) (i : J j) :
    rationalTagChartMatrix W n b ⟨j, a⟩ ⟨j, i⟩ = (b j a : J j → ℚ) i := by
  simp [rationalTagChartMatrix]

theorem rationalTagChartMatrix_of_ne
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) (a : Σ j, Fin (n j)) (x : Σ j, J j)
    (h : x.1 ≠ a.1) : rationalTagChartMatrix W n b a x = 0 := by
  simp [rationalTagChartMatrix, Pi.single_eq_of_ne h]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRoundedGraphEnergy
namespace OAI

section

namespace Erdos3

theorem exists_unrounded_scalar (M l : ℕ) [NeZero M] (hl : 0 < l)
    (a : ℝ) (u : ℤ) (h : ((⌊(M : ℝ) * l * a⌋ : ℤ) : ZMod M) = (u : ZMod M)) :
    ∃ k : ℤ, 0 ≤ a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l ∧
      a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l < 1 / ((M : ℝ) * l) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u ⌊(M : ℝ) * l * a⌋ M).mp h.symm
  have hkR : (⌊(M : ℝ) * l * a⌋ : ℝ) = (u : ℝ) + (M : ℝ) * k := by
    have he : (⌊(M : ℝ) * l * a⌋ : ℝ) - (u : ℝ) = (M : ℝ) * k := by exact_mod_cast hk
    linarith
  have heq : a - (u : ℝ) / ((M : ℝ) * l) - (k : ℝ) / l =
      ((M : ℝ) * l * a - ⌊(M : ℝ) * l * a⌋) / ((M : ℝ) * l) := by
    rw [hkR]
    field_simp
    ring
  refine ⟨k, ?_, ?_⟩
  · rw [heq]
    exact div_nonneg (sub_nonneg.mpr (Int.floor_le _)) (by positivity)
  · rw [heq]
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith [Int.lt_floor_add_one ((M : ℝ) * l * a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem map_integer_coordinates {r : ℕ} {G : Type*} [AddCommGroup G]
    (Φ : (Fin r → ℤ) →+ G) (x : Fin r → ℤ) :
    Φ x = ∑ j, x j • Φ (Pi.single j 1) := by
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin r → ℤ) := by
    funext i
    simp [Pi.single_apply]
  calc
    Φ x = Φ (∑ j, x j • (Pi.single j 1 : Fin r → ℤ)) := congrArg Φ hx
    _ = _ := by simp only [map_sum, map_zsmul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def variableCoefficientLift {I : Type*} {M : I → ℕ}
    (l : I → ℕ) (b : ∀ i, ZMod (M i)) : I → ℝ :=
  fun i => ((b i).val : ℝ) / ((M i : ℝ) * l i)

theorem exists_coordinate_rounding_moduli {I : Type*}
    (l : I → ℕ) (hl : ∀ i, 0 < l i) (ε : I → ℝ) (hε : ∀ i, 0 < ε i)
    (hsmall : ∀ i, 2 * (l i : ℝ) * ε i ≤ 1) :
    ∃ M : I → ℕ, (∀ i, 0 < M i) ∧ (∀ i, (M i : ℝ) * l i * ε i ≤ 1) ∧
      ∀ i, 1 / ((M i : ℝ) * l i) ≤ 2 * ε i := by
  have hi (i : I) := exists_rounding_modulus_with_recovery (l i) (hl i) (hε i) (hsmall i)
  choose M hM hscale herror using hi
  exact ⟨M, hM, hscale, herror⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3

theorem sharedFree_rounding_small {A z : ℝ} (hA : 0 ≤ A) (hz : 0 ≤ z)
    (hbudget : z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A)
    (N l d : ℕ) [NeZero N] (hd : 1 ≤ d)
    (hl : (l : ℝ) ≤ Real.exp ((A + 2) ^ 4))
    (hN : Real.exp ((A + 2) ^ 5) ≤ (N : ℝ)) :
    2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
      ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ d)) ≤ 1 := by
  have hzA : z ≤ A := by
    have h3 : 0 ≤ (z + 2) ^ 3 := by positivity
    have h36 : 0 ≤ (z + 2) ^ 36 := by positivity
    linarith
  have h18 : (z + 2) ^ 18 ≤ (z + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hwA : (z + 2) ^ 3 + (z + 2) ^ 18 + z ≤ A := by linarith
  have hsum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤
      2 * Real.exp A := by
    linarith [Real.exp_le_exp.mpr hzA, Real.exp_le_exp.mpr hwA]
  have hpoly : (A + 2) ^ 4 + (A + 2) ^ 3 + A + 4 ≤ (A + 2) ^ 5 := by
    have hh : 0 ≤ A ^ 5 + 9 * A ^ 4 + 31 * A ^ 3 + 50 * A ^ 2 + 35 * A + 4 := by positivity
    nlinarith
  have hnum : 2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
      (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) ≤
        Real.exp ((A + 2) ^ 5) := by
    calc
      _ ≤ 2 * Real.exp ((A + 2) ^ 4) * (Real.exp ((A + 2) ^ 3) * (2 * Real.exp A)) := by
        gcongr
      _ = 4 * Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A) := by
        simp only [Real.exp_add]
        ring
      _ ≤ Real.exp 4 * Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A + 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hpoly
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hpower : (N : ℝ) ≤ (N : ℝ) ^ d := by
    simpa only [pow_one] using pow_le_pow_right₀ hN1 hd
  have hdenpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hquot := (div_le_one hdenpos).mpr (hnum.trans (hN.trans hpower))
  simpa only [mul_div_assoc] using hquot

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistLocalizedFourierSelection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def truncateTaggedFrequency (d : ℕ) (a : (Σ j, J j) → ℤ) : (Σ j, J j) → ℤ :=
  fun i => if i.1.val + 1 ≤ d then a i else 0

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProperAffineBoxRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def centeredScalarCenter (R k c : ℕ) : ℤ :=
  (c : ℤ) * (2 * (R / (2 * k) : ℕ) + 1) - R + (R / (2 * k) : ℕ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RoundedModelDensityBudget
namespace OAI

section

namespace Erdos3

theorem roundedModelScale_le_exp (P : ℝ) (d : ℕ) :
    (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1) ≤
      Real.exp (44 + 6 * max P 0 + 94 * d) := by
  have h2 : (2 ^ 14 : ℝ) ≤ Real.exp 28 := by
    calc
      (2 ^ 14 : ℝ) ≤ (Real.exp 2) ^ 14 :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (2 : ℝ)]) _
      _ = Real.exp 28 := by rw [← Real.exp_nat_mul]; norm_num
  have h16 : (16 : ℝ) ^ (d + 1) ≤ Real.exp (16 * ((d : ℝ) + 1)) := by
    calc
      (16 : ℝ) ^ (d + 1) ≤ (Real.exp 16) ^ (d + 1) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (16 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc
    (2 ^ 14 : ℝ) * (Real.exp (P + 13 * d)) ^ 6 * 16 ^ (d + 1) ≤
        Real.exp 28 * (Real.exp (P + 13 * d)) ^ 6 * Real.exp (16 * ((d : ℝ) + 1)) := by
      gcongr
    _ = Real.exp (44 + 6 * P + 94 * d) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      norm_num
      ring
    _ ≤ Real.exp (44 + 6 * max P 0 + 94 * d) := by
      apply Real.exp_le_exp.mpr
      nlinarith [le_max_left P 0]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

theorem affineBoxScale_le_exp {r V A B : ℕ} {R D S : ℝ}
    (hB : 0 < B) (hR : 0 ≤ R) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hr : (r : ℝ) ≤ R) (hV : (V : ℝ) ≤ Real.exp D * A)
    (hdense : Real.exp (-S) * A ≤ (B : ℝ)) :
    ((2 ^ r * V / B + 1 : ℕ) : ℝ) ≤ Real.exp (2 * R + D + S + 2) := by
  have hquot : ((2 ^ r * V / B + 1 : ℕ) : ℝ) * B ≤ (2 : ℝ) ^ r * V + B := by
    have h : (2 ^ r * V / B + 1) * B ≤ 2 ^ r * V + B := by
      calc
        _ = (2 ^ r * V / B) * B + B := by ring
        _ ≤ _ := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    exact_mod_cast h
  have htwo : (2 : ℝ) ^ r ≤ Real.exp (2 * R) := by
    calc
      _ ≤ (Real.exp 2) ^ r := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) _
      _ = Real.exp (2 * (r : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hr])
  have hA : (A : ℝ) ≤ Real.exp S * B := by
    calc
      _ = Real.exp S * (Real.exp (-S) * A) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdense (Real.exp_pos _).le
  have hprod : (2 : ℝ) ^ r * V ≤ Real.exp (2 * R + D + S) * B := by
    calc
      _ ≤ Real.exp (2 * R) * (Real.exp D * A) := by gcongr
      _ ≤ Real.exp (2 * R) * (Real.exp D * (Real.exp S * B)) := by gcongr
      _ = _ := by simp only [Real.exp_add]; ring
  have hplus : Real.exp (2 * R + D + S) + 1 ≤ Real.exp (2 * R + D + S + 2) := by
    have hone : 1 ≤ Real.exp (2 * R + D + S) := Real.one_le_exp_iff.mpr (by linarith)
    calc
      _ ≤ 2 * Real.exp (2 * R + D + S) := by linarith only [hone]
      _ ≤ Real.exp 2 * Real.exp (2 * R + D + S) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (mul_le_mul_iff_left₀ (by exact_mod_cast hB : (0 : ℝ) < B)).mp
  calc
    _ ≤ (2 : ℝ) ^ r * V + B := hquot
    _ ≤ Real.exp (2 * R + D + S) * B + B := add_le_add hprod (le_refl (B : ℝ))
    _ = (Real.exp (2 * R + D + S) + 1) * B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hplus (Nat.cast_nonneg _)

theorem affineBoxCellCount_le_exp {r k : ℕ} {R T : ℝ}
    (hT : 0 ≤ T) (hr : (r : ℝ) ≤ R) (hk : (k : ℝ) ≤ Real.exp T) :
    ((4 * k) ^ r : ℕ) ≤ Real.exp ((4 + T) * R) := by
  have hbase : (4 : ℝ) * k ≤ Real.exp (4 + T) := by
    calc
      _ ≤ Real.exp 4 * Real.exp T := by
        gcongr
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := (Real.exp_add _ _).symm
  calc
    (((4 * k) ^ r : ℕ) : ℝ) = ((4 : ℝ) * k) ^ r := by push_cast; rfl
    _ ≤ (Real.exp (4 + T)) ^ r := pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((4 + T) * (r : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr (by linarith))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticLocalFrequency
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {ι κ D V : Type} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V]

noncomputable def affineBasisCoefficient
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (i : ι) (d : D) : V :=
  ∑ j, B i j • β j d

noncomputable def affineBasisConstant
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V) (c : ι → ℝ) (d : D) : V :=
  α d + ∑ i, c i • affineBasisCoefficient B β i d

theorem affine_basis_coordinate_sum
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (v : ι → ℝ) (d : D) :
    (∑ j, B.equivFun.symm v j • β j d) = ∑ i, v i • affineBasisCoefficient B β i d := by
  classical
  rw [Basis.equivFun_symm_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, affineBasisCoefficient,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem affine_basis_change
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V)
    (c u : ι → ℝ) (d : D) :
    α d + ∑ j, B.equivFun.symm (c + u) j • β j d =
      affineBasisConstant B α β c d + ∑ i, u i • affineBasisCoefficient B β i d := by
  rw [affine_basis_coordinate_sum]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, affineBasisConstant, add_assoc]

omit [Fintype ι] in
theorem affineBasisCoefficient_mem
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (U : D → Submodule ℝ V)
    (hβ : ∀ j d, β j d ∈ U d) (i : ι) (d : D) :
    affineBasisCoefficient B β i d ∈ U d :=
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d))

theorem affineBasisConstant_mem
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V) (c : ι → ℝ)
    (U : D → Submodule ℝ V) (hα : ∀ d, α d ∈ U d) (hβ : ∀ j d, β j d ∈ U d) (d : D) :
    affineBasisConstant B α β c d ∈ U d :=
  Submodule.add_mem _ (hα d) (Submodule.sum_mem _
    (fun i _ => Submodule.smul_mem _ _ (affineBasisCoefficient_mem B β U hβ i d)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteRankTriangularFinset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def finiteRankCorrectionSolutions {I : Type*} [Fintype I]
    (A : Matrix I I ℝ) (c : I → ℝ) (B : ℝ) (q : ℕ) :
    Set ((I → ℝ) × (I → ℚ)) :=
  {sr | (∀ i, |sr.1 i| ≤ B) ∧
    (∀ i, ∃ z : ℤ, sr.2 i = (z : ℚ) / q) ∧
    ∀ i, c i = ∑ j, A i j * sr.1 j + (sr.2 i : ℝ)}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

abbrev SpatialMatrixBlockIndex (X : Type*) := Fin 2 × X × X

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FiniteSupportedPolynomialSubstitution
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {V W R : Type*} [CommSemiring R]

noncomputable def polynomialOfFiniteCoefficientVector (S : Finset (V →₀ ℕ))
    (c : S → R) : MvPolynomial V R :=
  ∑ α : S, MvPolynomial.monomial α.val (c α)

end Erdos3

end

end OAI
end


