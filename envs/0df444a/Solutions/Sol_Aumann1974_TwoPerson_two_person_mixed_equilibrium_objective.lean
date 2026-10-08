-- Prove2me | solution 1 for Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T20:45:23.962454+00:00
-- url     : https://prove2.me/submissions/4615a367-d9da-4f49-93c8-7f7e75760fab

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

set_option autoImplicit false

/- Complete checked body: SmallSubsets -/
section

open MeasureTheory Set

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The genuine nonatomic predicate supplies arbitrarily small positive measurable pieces. -/
theorem nonatomic_small_subset (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : NonAtomicOn μ ‹MeasurableSpace Ω›) (E : Set Ω)
    (hE : MeasurableSet E) (hpos : 0 < μ.real E) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ E ∧ 0 < μ.real F ∧ μ.real F ≤ ε := by
  classical
  by_contra h
  push Not at h
  let W : Set ℝ := {r | ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ E ∧
    0 < μ.real F ∧ r = μ.real F}
  have hW : W.Nonempty := ⟨μ.real E, E, hE, Subset.rfl, hpos, rfl⟩
  have hb : BddBelow W := by
    refine ⟨0, ?_⟩
    rintro r ⟨F, _, _, hF, rfl⟩
    exact hF.le
  have hl : ε ≤ sInf W := by
    apply le_csInf hW
    rintro r ⟨F, hF, hFE, hp, rfl⟩
    exact (h F hF hFE hp).le
  have hi : 0 < sInf W := lt_of_lt_of_le hε hl
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt hW (show sInf W < 2 * sInf W by linarith)
  obtain ⟨F, hF, hFE, hp, rfl⟩ := hr
  have hpm : 0 < μ F := by
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hp.ne')
  obtain ⟨B, hB, hBF, hBp, hBl⟩ := hμ F hF hpm
  have hBr : 0 < μ.real B := ENNReal.toReal_pos hBp.ne' (by finiteness)
  have hBrlt : μ.real B < μ.real F :=
    (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hBl
  have hdiff : μ.real (F \ B) = μ.real F - μ.real B := measureReal_sdiff hBF hB
  have hdiffpos : 0 < μ.real (F \ B) := by rw [hdiff]; linarith
  have h1 : sInf W ≤ μ.real B := csInf_le hb ⟨B, hB, hBF.trans hFE, hBr, rfl⟩
  have h2 : sInf W ≤ μ.real (F \ B) :=
    csInf_le hb ⟨F \ B, hF.diff hB, sdiff_subset.trans hFE, hdiffpos, rfl⟩
  linarith

/-- A measurable subset can capture at least half the supremum of all admissible masses.
This auxiliary statement does not require nonatomicity. -/
theorem exists_half_sup_subset (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (b : ℝ) (hb : 0 ≤ b) :
    ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ E ∧ μ.real F ≤ b ∧
      ∀ C : Set Ω, MeasurableSet C → C ⊆ E → μ.real C ≤ b →
        μ.real C ≤ 2 * μ.real F := by
  classical
  let W : Set ℝ := {r | ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ E ∧
    μ.real F ≤ b ∧ r = μ.real F}
  have hW : W.Nonempty := ⟨0, ∅, MeasurableSet.empty, empty_subset E, by simpa, by simp⟩
  have hbd : BddAbove W := by
    refine ⟨b, ?_⟩
    rintro r ⟨F, _, _, hF, rfl⟩
    exact hF
  have hs0 : 0 ≤ sSup W := le_csSup hbd ⟨∅, MeasurableSet.empty, empty_subset E,
    by simpa, by simp⟩
  by_cases hs : sSup W = 0
  · refine ⟨∅, MeasurableSet.empty, empty_subset E, by simpa, ?_⟩
    intro C hC hCE hCb
    have hh : μ.real C ≤ sSup W := le_csSup hbd ⟨C, hC, hCE, hCb, rfl⟩
    simpa [hs] using hh
  · have hsp : 0 < sSup W := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨r, hr, hlt⟩ := exists_lt_of_lt_csSup hW
      (show sSup W / 2 < sSup W by linarith)
    obtain ⟨F, hF, hFE, hFb, rfl⟩ := hr
    refine ⟨F, hF, hFE, hFb, ?_⟩
    intro C hC hCE hCb
    have hh : μ.real C ≤ sSup W := le_csSup hbd ⟨C, hC, hCE, hCb, rfl⟩
    linarith

end Aumann1974.TwoPersonProof

end

/- Complete checked body: NonatomicDivisibility -/
section

open MeasureTheory Set Filter Topology

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every prescribed mass up to that of a measurable set is attained by a measurable subset.
The proof builds increasing nearly maximal pieces; it uses genuine nonatomicity. -/
theorem nonatomic_divisible (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : NonAtomicOn μ ‹MeasurableSpace Ω›) (E : Set Ω) (hE : MeasurableSet E)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθE : θ ≤ μ.real E) :
    ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ E ∧ μ.real F = θ := by
  classical
  let good : Set (Set Ω) := {A | MeasurableSet A ∧ A ⊆ E ∧ μ.real A ≤ θ}
  have hstep : ∀ A : good, ∃ B : good, A.val ⊆ B.val ∧
      ∀ C : Set Ω, MeasurableSet C → C ⊆ E \ A.val →
        μ.real C ≤ θ - μ.real A.val →
        μ.real C ≤ 2 * (μ.real B.val - μ.real A.val) := by
    intro A
    obtain ⟨C, hC, hCA, hCb, hmax⟩ :=
      exists_half_sup_subset μ (E \ A.val) (θ - μ.real A.val) (by linarith [A.property.2.2])
    have hdisj : Disjoint A.val C := by
      apply Set.disjoint_left.mpr
      intro x hx hxc
      exact (hCA hxc).2 hx
    have hmass : μ.real (A.val ∪ C) = μ.real A.val + μ.real C :=
      measureReal_union hdisj hC
    have hgood : A.val ∪ C ∈ good := by
      refine ⟨A.property.1.union hC, union_subset A.property.2.1 (hCA.trans sdiff_subset), ?_⟩
      rw [hmass]
      linarith
    refine ⟨⟨A.val ∪ C, hgood⟩, subset_union_left, ?_⟩
    intro D hD hDA hDb
    have hh := hmax D hD hDA hDb
    change μ.real D ≤ 2 * (μ.real (A.val ∪ C) - μ.real A.val)
    rw [hmass]
    linarith
  choose next hnext using hstep
  let seed : good := ⟨∅, MeasurableSet.empty, empty_subset E, by simpa using hθ0⟩
  let a : ℕ → good := fun n => next^[n] seed
  have ha (n : ℕ) : a (n + 1) = next (a n) := by
    exact Function.iterate_succ_apply' next n seed
  have hmono : Monotone (fun n => (a n).val) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [ha]
    exact (hnext (a n)).1
  let F : Set Ω := ⋃ n, (a n).val
  have hF : MeasurableSet F := MeasurableSet.iUnion (fun n => (a n).property.1)
  have hFE : F ⊆ E := iUnion_subset (fun n => (a n).property.2.1)
  have hlim : Tendsto (fun n => μ.real (a n).val) atTop (𝓝 (μ.real F)) := by
    exact (ENNReal.tendsto_toReal (by finiteness)).comp
      (tendsto_measure_iUnion_atTop hmono)
  have hFb : μ.real F ≤ θ := le_of_tendsto hlim (Eventually.of_forall
    (fun n => (a n).property.2.2))
  refine ⟨F, hF, hFE, ?_⟩
  by_contra hne
  have hlt : μ.real F < θ := lt_of_le_of_ne hFb hne
  have hrem : 0 < μ.real (E \ F) := by
    rw [measureReal_sdiff hFE hF]
    linarith
  obtain ⟨C, hC, hCF, hCp, hCb⟩ := nonatomic_small_subset μ hμ (E \ F)
    (hE.diff hF) hrem (θ - μ.real F) (by linarith)
  have hineq (n : ℕ) : μ.real C ≤ 2 * (μ.real (a (n + 1)).val - μ.real (a n).val) := by
    rw [ha]
    apply (hnext (a n)).2 C hC
    · intro x hx
      exact ⟨(hCF hx).1, fun hxa => (hCF hx).2 (mem_iUnion.mpr ⟨n, hxa⟩)⟩
    · have hm : μ.real (a n).val ≤ μ.real F :=
        measureReal_mono (subset_iUnion (fun n => (a n).val) n)
      linarith
  have hlim' : Tendsto (fun n => μ.real (a (n + 1)).val) atTop (𝓝 (μ.real F)) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun n => 2 * (μ.real (a (n + 1)).val - μ.real (a n).val))
      atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using (hlim'.sub hlim).const_mul 2
  have hh : μ.real C ≤ 0 := ge_of_tendsto hd (Eventually.of_forall hineq)
  linarith

end Aumann1974.TwoPersonProof

end

/- Complete checked body: DyadicPartitions -/
section

open MeasureTheory Set

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable partition into equally likely dyadic cells, represented by its cell index. -/
structure DyadicPartition (μ : Measure Ω) (n : ℕ) where
  index : Ω → ℕ
  measurable_index : Measurable index
  index_lt : ∀ ω, index ω < 2 ^ n
  mass : ∀ i < 2 ^ n, μ.real {ω | index ω = i} = (1 / 2 : ℝ) ^ n

namespace DyadicPartition

theorem measurable_fiber {μ : Measure Ω} {n : ℕ} (p : DyadicPartition μ n) (i : ℕ) :
    MeasurableSet {ω | p.index ω = i} := p.measurable_index (measurableSet_singleton i)

def zero (μ : Measure Ω) [IsProbabilityMeasure μ] : DyadicPartition μ 0 where
  index := fun _ => 0
  measurable_index := measurable_const
  index_lt := by simp
  mass := by
    intro i hi
    have : i = 0 := by simpa using hi
    subst i
    simp

theorem exists_next (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : NonAtomicOn μ ‹MeasurableSpace Ω›) {n : ℕ} (p : DyadicPartition μ n) :
    ∃ q : DyadicPartition μ (n + 1),
      ∀ ω, 2 * p.index ω ≤ q.index ω ∧ q.index ω ≤ 2 * p.index ω + 1 := by
  classical
  have cuts (i : ℕ) : ∃ C : Set Ω, MeasurableSet C ∧ C ⊆ {ω | p.index ω = i} ∧
      μ.real C = μ.real {ω | p.index ω = i} / 2 := by
    apply nonatomic_divisible μ hμ _ (p.measurable_fiber i)
    · positivity
    · have := measureReal_nonneg (μ := μ) (s := {ω | p.index ω = i})
      linarith
  choose C hC using cuts
  let D : Set Ω := ⋃ i, C i
  have hD : MeasurableSet D := MeasurableSet.iUnion (fun i => (hC i).1)
  have hDi (ω : Ω) : ω ∈ D ↔ ω ∈ C (p.index ω) := by
    constructor
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      have he : p.index ω = i := (hC i).2.1 hi
      simpa only [he] using hi
    · intro h
      exact mem_iUnion.mpr ⟨p.index ω, h⟩
  let f : Ω → ℕ := fun ω => 2 * p.index ω + if ω ∈ D then 0 else 1
  have hfm : Measurable f := by
    exact (measurable_const.mul p.measurable_index).add
      (measurable_const.ite hD measurable_const)
  have hfe (i : ℕ) : {ω | f ω = 2 * i} = C i := by
    ext ω
    constructor
    · intro h
      by_cases hd : ω ∈ D
      · have he : p.index ω = i := by
          change 2 * p.index ω + (if ω ∈ D then 0 else 1) = 2 * i at h
          rw [if_pos hd] at h
          omega
        have hh := (hDi ω).mp hd
        simpa only [he] using hh
      · change 2 * p.index ω + (if ω ∈ D then 0 else 1) = 2 * i at h
        rw [if_neg hd] at h
        omega
    · intro h
      have he : p.index ω = i := (hC i).2.1 h
      have hd : ω ∈ D := mem_iUnion.mpr ⟨i, h⟩
      simp [f, hd, he]
  have hfo (i : ℕ) : {ω | f ω = 2 * i + 1} = {ω | p.index ω = i} \ C i := by
    ext ω
    constructor
    · intro h
      by_cases hd : ω ∈ D
      · change 2 * p.index ω + (if ω ∈ D then 0 else 1) = 2 * i + 1 at h
        rw [if_pos hd] at h
        omega
      · have he : p.index ω = i := by
          change 2 * p.index ω + (if ω ∈ D then 0 else 1) = 2 * i + 1 at h
          rw [if_neg hd] at h
          omega
        exact ⟨he, fun hc => hd (mem_iUnion.mpr ⟨i, hc⟩)⟩
    · rintro ⟨he, hc⟩
      change p.index ω = i at he
      have hd : ω ∉ D := by
        intro hd
        have hh := (hDi ω).mp hd
        exact hc (by simpa only [he] using hh)
      simp [f, hd, he]
  have hbound (ω : Ω) : f ω < 2 ^ (n + 1) := by
    have hh := p.index_lt ω
    dsimp [f]
    rw [pow_succ]
    split_ifs <;> omega
  have hmass (i : ℕ) (hi : i < 2 ^ (n + 1)) :
      μ.real {ω | f ω = i} = (1 / 2 : ℝ) ^ (n + 1) := by
    have hhalf : i / 2 < 2 ^ n := by rw [pow_succ] at hi; omega
    by_cases h : i % 2 = 0
    · have he : i = 2 * (i / 2) := by omega
      rw [he, hfe, (hC (i / 2)).2.2, p.mass _ hhalf, pow_succ]
      ring
    · have he : i = 2 * (i / 2) + 1 := by omega
      rw [he, hfo, measureReal_sdiff (hC (i / 2)).2.1 (hC (i / 2)).1,
        (hC (i / 2)).2.2, p.mass _ hhalf, pow_succ]
      ring
  refine ⟨⟨f, hfm, hbound, hmass⟩, ?_⟩
  intro ω
  change 2 * p.index ω ≤ f ω ∧ f ω ≤ 2 * p.index ω + 1
  dsimp [f]
  split_ifs <;> omega

theorem prefix_mass {μ : Measure Ω} [IsFiniteMeasure μ] {n : ℕ}
    (p : DyadicPartition μ n) (k : ℕ) (hk : k ≤ 2 ^ n) :
    μ.real {ω | p.index ω < k} = (k : ℝ) * (1 / 2 : ℝ) ^ n := by
  classical
  have he : {ω | p.index ω < k} = ⋃ i : Fin k, {ω | p.index ω = i.val} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨p.index ω, h⟩, rfl⟩
    · rintro ⟨i, hi⟩
      simpa only [hi] using i.isLt
  have hd : Pairwise (fun i j : Fin k =>
      Disjoint {ω | p.index ω = i.val} {ω | p.index ω = j.val}) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (Fin.ext (hi.symm.trans hj))
  rw [he, measureReal_iUnion_fintype hd (fun i => p.measurable_fiber i.val)]
  calc
    (∑ i : Fin k, μ.real {ω | p.index ω = i.val}) =
        ∑ _i : Fin k, (1 / 2 : ℝ) ^ n := by
      apply Finset.sum_congr rfl
      intro i _
      exact p.mass i.val (lt_of_lt_of_le i.isLt hk)
    _ = (k : ℝ) * (1 / 2 : ℝ) ^ n := by simp

end DyadicPartition

end Aumann1974.TwoPersonProof

end

/- Complete checked body: DyadicLimit -/
section

open MeasureTheory Set Filter Topology

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {Ω : Type*} [MeasurableSpace Ω]

theorem dyadic_scale_identity (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n = 1 := by
  calc
    ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n =
        (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by norm_cast
    _ = ((2 : ℝ) * (1 / 2)) ^ n := (mul_pow _ _ _).symm
    _ = 1 := by norm_num

noncomputable def dyadicFamily (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : NonAtomicOn μ ‹MeasurableSpace Ω›) : (n : ℕ) → DyadicPartition μ n
  | 0 => DyadicPartition.zero μ
  | n + 1 => (DyadicPartition.exists_next μ hμ (dyadicFamily μ hμ n)).choose

theorem dyadicFamily_refines (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : NonAtomicOn μ ‹MeasurableSpace Ω›) (n : ℕ) (ω : Ω) :
    2 * (dyadicFamily μ hμ n).index ω ≤ (dyadicFamily μ hμ (n + 1)).index ω ∧
      (dyadicFamily μ hμ (n + 1)).index ω ≤ 2 * (dyadicFamily μ hμ n).index ω + 1 :=
  (DyadicPartition.exists_next μ hμ (dyadicFamily μ hμ n)).choose_spec ω

/-- The dyadic indices locate a measurable real coordinate inside nested intervals
whose lengths tend to zero. All bounds hold at every sample point. -/
theorem exists_dyadic_coordinate (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : NonAtomicOn μ ‹MeasurableSpace Ω›) :
    ∃ (P : (n : ℕ) → DyadicPartition μ n) (U : Ω → ℝ),
      Measurable U ∧ (∀ ω, U ω ∈ Icc (0 : ℝ) 1) ∧
      ∀ n ω, (P n).index ω * (1 / 2 : ℝ) ^ n ≤ U ω ∧
        U ω ≤ (((P n).index ω : ℝ) + 1) * (1 / 2 : ℝ) ^ n := by
  let P := dyadicFamily μ hμ
  let a : ℕ → Ω → ℝ := fun n ω => (P n).index ω * (1 / 2 : ℝ) ^ n
  let b : ℕ → Ω → ℝ := fun n ω => (((P n).index ω : ℝ) + 1) * (1 / 2 : ℝ) ^ n
  have hd (n : ℕ) : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hab (n : ℕ) (ω : Ω) : a n ω ≤ b n ω := by
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_right (by linarith) (hd n)
  have hb1 (n : ℕ) (ω : Ω) : b n ω ≤ 1 := by
    have hidx : ((P n).index ω : ℝ) + 1 ≤ ((2 ^ n : ℕ) : ℝ) := by
      have hn : (P n).index ω + 1 ≤ 2 ^ n := by have := (P n).index_lt ω; omega
      exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_right hidx (hd n)
    rw [dyadic_scale_identity] at hh
    exact hh
  have hmono (ω : Ω) : Monotone (fun n => a n ω) := by
    apply monotone_nat_of_le_succ
    intro n
    have hidx : 2 * ((P n).index ω : ℝ) ≤ ((P (n + 1)).index ω : ℝ) := by
      exact_mod_cast (dyadicFamily_refines μ hμ n ω).1
    have hh := mul_le_mul_of_nonneg_right hidx (hd n)
    dsimp [a]
    rw [pow_succ]
    nlinarith
  have hanti (ω : Ω) : Antitone (fun n => b n ω) := by
    apply antitone_nat_of_succ_le
    intro n
    have hidx : ((P (n + 1)).index ω : ℝ) ≤ 2 * ((P n).index ω : ℝ) + 1 := by
      exact_mod_cast (dyadicFamily_refines μ hμ n ω).2
    have hh := mul_le_mul_of_nonneg_right hidx (hd n)
    dsimp [b]
    rw [pow_succ]
    nlinarith
  have hbd (ω : Ω) : BddAbove (range (fun n => a n ω)) := by
    refine ⟨1, ?_⟩
    rintro r ⟨n, rfl⟩
    exact (hab n ω).trans (hb1 n ω)
  let U : Ω → ℝ := fun ω => ⨆ n, a n ω
  have hUa (n : ℕ) (ω : Ω) : a n ω ≤ U ω := le_ciSup (hbd ω) n
  have hUb (n : ℕ) (ω : Ω) : U ω ≤ b n ω := by
    apply ciSup_le
    intro k
    rcases le_total k n with hkn | hnk
    · exact (hmono ω hkn).trans (hab n ω)
    · exact (hab k ω).trans (hanti ω hnk)
  have hUm : Measurable U := by
    apply Measurable.iSup
    intro n
    exact ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (P n).measurable_index).mul_const ((1 / 2 : ℝ) ^ n)
  refine ⟨P, U, hUm, ?_, fun n ω => ⟨hUa n ω, hUb n ω⟩⟩
  intro ω
  refine ⟨?_, (hUb 0 ω).trans (hb1 0 ω)⟩
  have hh : 0 ≤ a 0 ω := by dsimp [a]; positivity
  exact hh.trans (hUa 0 ω)

end Aumann1974.TwoPersonProof

end

/- Complete checked body: UniformCoordinate -/
section

open MeasureTheory Set Filter Topology

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {Ω : Type*} [MeasurableSpace Ω]

theorem dyadic_coordinate_cdf (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : (n : ℕ) → DyadicPartition μ n) (U : Ω → ℝ)
    (hU : ∀ n ω, (P n).index ω * (1 / 2 : ℝ) ^ n ≤ U ω ∧
      U ω ≤ (((P n).index ω : ℝ) + 1) * (1 / 2 : ℝ) ^ n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : μ.real {ω | U ω ≤ t} = t := by
  have hbounds (n : ℕ) :
      t - (1 / 2 : ℝ) ^ n ≤ μ.real {ω | U ω ≤ t} ∧
      μ.real {ω | U ω ≤ t} ≤ t + (1 / 2 : ℝ) ^ n := by
    let N : ℕ := 2 ^ n
    let d : ℝ := (1 / 2 : ℝ) ^ n
    let k : ℕ := ⌊(N : ℝ) * t⌋₊
    have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
    have hd : 0 < d := by dsimp [d]; positivity
    have hNd : (N : ℝ) * d = 1 := dyadic_scale_identity n
    have hprod : 0 ≤ (N : ℝ) * t := mul_nonneg hN.le ht0
    have hklo : (k : ℝ) ≤ (N : ℝ) * t := Nat.floor_le hprod
    have hkhi : (N : ℝ) * t < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkN : k < N := by
      have hh : (k : ℝ) < (N : ℝ) := hklo.trans_lt (by nlinarith)
      exact_mod_cast hh
    have hscale : ((N : ℝ) * t) * d = t := by
      calc
        ((N : ℝ) * t) * d = t * ((N : ℝ) * d) := by ring
        _ = t := by rw [hNd, mul_one]
    have hlo : (k : ℝ) * d ≤ t := by
      have hh := mul_le_mul_of_nonneg_right hklo hd.le
      rwa [hscale] at hh
    have hhi : t < ((k : ℝ) + 1) * d := by
      have hh := mul_lt_mul_of_pos_right hkhi hd
      rwa [hscale] at hh
    have hsublo : {ω | (P n).index ω < k} ⊆ {ω | U ω ≤ t} := by
      intro ω hω
      have hi : ((P n).index ω : ℝ) + 1 ≤ (k : ℝ) := by
        have hn : (P n).index ω + 1 ≤ k := hω
        exact_mod_cast hn
      exact ((hU n ω).2.trans (mul_le_mul_of_nonneg_right hi hd.le)).trans hlo
    have hsubhi : {ω | U ω ≤ t} ⊆ {ω | (P n).index ω < k + 1} := by
      intro ω hω
      have hh : ((P n).index ω : ℝ) * d < ((k : ℝ) + 1) * d :=
        ((hU n ω).1.trans hω).trans_lt hhi
      have hi : ((P n).index ω : ℝ) < (k : ℝ) + 1 := (mul_lt_mul_iff_left₀ hd).mp hh
      exact_mod_cast hi
    have hl : (k : ℝ) * d ≤ μ.real {ω | U ω ≤ t} := by
      rw [← (P n).prefix_mass k hkN.le]
      exact measureReal_mono hsublo
    have hu : μ.real {ω | U ω ≤ t} ≤ ((k : ℝ) + 1) * d := by
      have hh := measureReal_mono (μ := μ) hsubhi
      rw [(P n).prefix_mass (k + 1) (Nat.succ_le_of_lt hkN)] at hh
      simpa only [Nat.cast_add, Nat.cast_one] using hh
    dsimp [d] at *
    constructor <;> nlinarith
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun _n : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  apply le_antisymm
  · have hh := ge_of_tendsto (ht.add hp) (Eventually.of_forall (fun n => (hbounds n).2))
    simpa only [add_zero] using hh
  · have hh := le_of_tendsto (ht.sub hp) (Eventually.of_forall (fun n => (hbounds n).1))
    simpa only [sub_zero] using hh

/-- A nonatomic probability space has a measurable uniform coordinate, without any
countable-generation or standard-Borel assumption on its domain. -/
theorem exists_uniform_coordinate_full (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : NonAtomicOn μ ‹MeasurableSpace Ω›) :
    ∃ U : Ω → ℝ, Measurable U ∧ (∀ ω, U ω ∈ Icc (0 : ℝ) 1) ∧
      μ.map U = volume.restrict (Icc (0 : ℝ) 1) := by
  obtain ⟨P, U, hUm, hU, hbounds⟩ := exists_dyadic_coordinate μ hμ
  refine ⟨U, hUm, hU, ?_⟩
  have : IsProbabilityMeasure (μ.map U) := Measure.isProbabilityMeasure_map hUm.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hUm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have hi : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 (min t 1) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [hi, Real.volume_Icc, sub_zero]
  change μ {ω | U ω ≤ t} = ENNReal.ofReal (min t 1)
  by_cases ht0 : t < 0
  · have he : {ω | U ω ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hh
      linarith [(hU ω).1]
    rw [he, measure_empty, min_eq_left (by linarith), ENNReal.ofReal_of_nonpos ht0.le]
  · have ht : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : 1 ≤ t
    · have he : {ω | U ω ≤ t} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact (hU ω).2.trans ht1
      rw [he, measure_univ, min_eq_right ht1, ENNReal.ofReal_one]
    · have ht1' : t < 1 := lt_of_not_ge ht1
      have hc := dyadic_coordinate_cdf μ P U hbounds t ht ht1'
      rw [← ofReal_measureReal (μ := μ) (s := {ω | U ω ≤ t}), hc, min_eq_left ht1'.le]

omit [MeasurableSpace Ω] in
/-- The uniform coordinate can be chosen in the exact secret sub-sigma-field. -/
theorem exists_uniform_coordinate {mΩ m : MeasurableSpace Ω}
    (μ : Measure[mΩ] Ω) [@IsProbabilityMeasure Ω mΩ μ]
    (hm : m ≤ mΩ) (hμ : @NonAtomicOn Ω mΩ μ m) :
    ∃ U : Ω → ℝ, Measurable[m] U ∧ (∀ ω, U ω ∈ Icc (0 : ℝ) 1) ∧
      @Measure.map Ω ℝ mΩ _ U μ = volume.restrict (Icc (0 : ℝ) 1) := by
  let ν : @Measure Ω m := μ.trim hm
  have heq (E : Set Ω) (hE : MeasurableSet[m] E) : ν E = μ E :=
    trim_measurableSet_eq hm hE
  have hνprob : @IsProbabilityMeasure Ω m ν := ⟨by
    rw [heq univ MeasurableSet.univ, measure_univ]⟩
  have hν : @NonAtomicOn Ω m ν m := by
    intro E hE hp
    rw [heq E hE] at hp
    obtain ⟨F, hF, hFE, hFp, hFl⟩ := hμ E hE hp
    refine ⟨F, hF, hFE, ?_, ?_⟩
    · rwa [heq F hF]
    · rwa [heq F hF, heq E hE]
  obtain ⟨U, hUm, hU, hlaw⟩ := @exists_uniform_coordinate_full Ω m ν hνprob hν
  have hmap : @Measure.map Ω ℝ mΩ _ U μ = @Measure.map Ω ℝ m _ U ν := by
    apply Measure.ext
    intro E hE
    rw [Measure.map_apply (hUm.mono hm le_rfl) hE, Measure.map_apply hUm hE]
    exact (heq _ (hUm hE)).symm
  exact ⟨U, hUm, hU, hmap.trans hlaw⟩

end Aumann1974.TwoPersonProof

end

/- Complete checked body: NonatomicMeasures -/
section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem nonatomic_add (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hμ : NonAtomicOn μ m) (hν : NonAtomicOn ν m) :
    NonAtomicOn (μ + ν) m := by
  intro A hA hp
  rw [Measure.add_apply] at hp
  by_cases hpos : 0 < μ A
  · obtain ⟨B, hB, hBA, hBp, hBl⟩ := hμ A hA hpos
    refine ⟨B, hB, hBA, ?_, ?_⟩
    · rw [Measure.add_apply]
      exact hBp.trans_le (le_add_of_nonneg_right zero_le)
    · rw [Measure.add_apply, Measure.add_apply]
      have hνBA : ν B ≤ ν A := measure_mono hBA
      have hw : μ B + ν B ≤ μ B + ν A := by gcongr
      have ht : μ B + ν A < μ A + ν A :=
        ENNReal.add_lt_add_right (measure_ne_top ν A) hBl
      exact hw.trans_lt ht
  · have hμA : μ A = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hpos)
    have hνA : 0 < ν A := by simpa only [hμA, zero_add] using hp
    obtain ⟨B, hB, hBA, hBp, hBl⟩ := hν A hA hνA
    refine ⟨B, hB, hBA, ?_, ?_⟩
    · rw [Measure.add_apply]
      exact hBp.trans_le (le_add_of_nonneg_left zero_le)
    · rw [Measure.add_apply, Measure.add_apply]
      have hμBA : μ B ≤ μ A := measure_mono hBA
      have hw : μ B + ν B ≤ μ A + ν B := by gcongr
      have ht : μ A + ν B < μ A + ν A :=
        ENNReal.add_lt_add_left (measure_ne_top μ A) hBl
      exact hw.trans_lt ht

theorem nonatomic_smul (μ : Measure Ω) (m : MeasurableSpace Ω)
    (hμ : NonAtomicOn μ m) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    NonAtomicOn (c • μ) m := by
  intro A hA hp
  simp only [Measure.smul_apply, smul_eq_mul] at hp
  obtain ⟨B, hB, hBA, hBp, hBl⟩ := hμ A hA (ENNReal.mul_pos_iff.mp hp).2
  refine ⟨B, hB, hBA, ?_, ?_⟩
  · simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos_iff.mpr ⟨pos_iff_ne_zero.mpr hc0, hBp⟩
  · simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_mul_right hc0 hctop hBl

theorem nonatomic_restrict (μ : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hμ : NonAtomicOn μ m) (E : Set Ω) (hE : MeasurableSet[m] E) : NonAtomicOn (μ.restrict E) m := by
  intro A hA hp
  rw [Measure.restrict_apply (hm _ hA)] at hp
  obtain ⟨B, hB, hBE, hBp, hBl⟩ := hμ (A ∩ E) (hA.inter hE) hp
  · refine ⟨B, hB, hBE.trans inter_subset_left, ?_, ?_⟩
    · rw [Measure.restrict_apply (hm _ hB), inter_eq_left.mpr (hBE.trans inter_subset_right)]
      exact hBp
    · rw [Measure.restrict_apply (hm _ hB),
        inter_eq_left.mpr (hBE.trans inter_subset_right), Measure.restrict_apply (hm _ hA)]
      exact hBl

noncomputable def meanMeasure (μ ν : Measure Ω) : Measure Ω := (2 : ℝ≥0∞)⁻¹ • (μ + ν)

instance meanMeasure_probability (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (meanMeasure μ ν) := by
  constructor
  simp only [meanMeasure, Measure.smul_apply, Measure.add_apply, measure_univ,
    smul_eq_mul, mul_add, mul_one]
  exact ENNReal.inv_two_add_inv_two

theorem meanMeasure_nonatomic (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (m : MeasurableSpace Ω)
    (hμ : NonAtomicOn μ m) (hν : NonAtomicOn ν m) : NonAtomicOn (meanMeasure μ ν) m := by
  exact nonatomic_smul (μ + ν) m (nonatomic_add μ ν m hμ hν) _ (by norm_num) (by norm_num)

theorem two_smul_meanMeasure (μ ν : Measure Ω) :
    (2 : ℝ≥0∞) • meanMeasure μ ν = μ + ν := by
  have h : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [meanMeasure, smul_smul, h, one_smul]

end Aumann1974.TwoPersonProof

end

/- Complete checked body: ScalarRotation -/
section

set_option autoImplicit false

open Set MeasureTheory intervalIntegral
open scoped Interval

namespace Aumann1974.TwoPersonProof

def windowMass (G : ℝ → ℝ) (α s : ℝ) : ℝ :=
  G (s + α) - G s + G (s + α - 1)

theorem continuous_windowMass {G : ℝ → ℝ} (hG : Continuous G) (α : ℝ) :
    Continuous (windowMass G α) := by
  exact (hG.comp (continuous_id.add_const α)).sub hG |>.add
    (hG.comp ((continuous_id.add_const α).sub (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))))

theorem integral_windowMass {G : ℝ → ℝ} (hG : Continuous G)
    (hzero : ∀ x, x ≤ 0 → G x = 0) (hone : ∀ x, 1 ≤ x → G x = 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (∫ s in (0 : ℝ)..1, windowMass G α s) = α := by
  have ht1 : (∫ s in (0 : ℝ)..1, G (s + α)) = ∫ s in α..1 + α, G s := by
    rw [integral_comp_add_right, zero_add]
  have ht2 : (∫ s in (0 : ℝ)..1, G (s + α - 1)) = ∫ s in α - 1..α, G s := by
    have h := integral_comp_add_right G (α - 1) (a := 0) (b := 1)
    simpa only [zero_add, show 1 + (α - 1) = α by ring, add_sub_assoc] using h
  have hz : (∫ s in α - 1..(0 : ℝ), G s) = 0 := by
    calc
      _ = ∫ s in α - 1..(0 : ℝ), (0 : ℝ) := by
        apply integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : α - 1 ≤ 0)] at hs
        exact hzero s hs.2
      _ = 0 := by simp
  have ho : (∫ s in (1 : ℝ)..1 + α, G s) = α := by
    calc
      _ = ∫ s in (1 : ℝ)..1 + α, (1 : ℝ) := by
        apply integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : 1 ≤ 1 + α)] at hs
        exact hone s hs.1
      _ = α := by simp
  have hsplit0 := integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := volume) (α - 1) 0) (hG.intervalIntegrable (μ := volume) 0 α)
  have hsplit1 := integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := volume) α 1) (hG.intervalIntegrable (μ := volume) 1 (1 + α))
  have hsplit := integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := volume) 0 α) (hG.intervalIntegrable (μ := volume) α 1)
  have hi1 : IntervalIntegrable (fun s : ℝ => G (s + α)) volume 0 1 :=
    (hG.comp (continuous_id.add_const α)).intervalIntegrable (μ := volume) 0 1
  have hi2 : IntervalIntegrable (fun s : ℝ => G (s + α - 1)) volume 0 1 :=
    (hG.comp ((continuous_id.add_const α).sub
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))).intervalIntegrable
        (μ := volume) 0 1
  unfold windowMass
  rw [integral_add (hi1.sub (hG.intervalIntegrable (μ := volume) 0 1)) hi2,
    integral_sub hi1 (hG.intervalIntegrable (μ := volume) 0 1), ht1, ht2]
  rw [hz, zero_add] at hsplit0
  rw [ho] at hsplit1
  linarith

theorem exists_rotation_mass {G : ℝ → ℝ} (hG : Continuous G)
    (hzero : ∀ x, x ≤ 0 → G x = 0) (hone : ∀ x, 1 ≤ x → G x = 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, windowMass G α s = α := by
  obtain ⟨s, hs, he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (f := windowMass G α) (g := fun _ => (1 : ℝ))
    (continuous_windowMass hG α).continuousOn intervalIntegrable_const
    (by intro x hx; norm_num)
  refine ⟨s, ?_, ?_⟩
  · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  · simp only [mul_one, intervalIntegral.integral_const, sub_zero, one_smul] at he
    rw [integral_windowMass hG hzero hone hα0 hα1] at he
    exact he.symm

end Aumann1974.TwoPersonProof

end

/- Complete checked body: RealCommonWindow -/
section

set_option autoImplicit false

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Aumann1974.TwoPersonProof

noncomputable def unitIntervalMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance unitIntervalMeasure_probability : IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  simp [unitIntervalMeasure]

theorem unit_cdf_eq (x : ℝ) :
    cdf unitIntervalMeasure x = max (min x 1) 0 := by
  rw [cdf_eq_real, unitIntervalMeasure, measureReal_restrict_apply measurableSet_Iic]
  have he : Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 (min x 1) := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [he, Real.volume_real_Icc, sub_zero]

theorem unit_cdf_sub_le {a b : ℝ} (hab : a ≤ b) :
    cdf unitIntervalMeasure b - cdf unitIntervalMeasure a ≤ b - a := by
  rw [unit_cdf_eq, unit_cdf_eq]
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem cdf_sum_relation (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hsum : μ + ν = (2 : ℝ≥0∞) • unitIntervalMeasure) (x : ℝ) :
    cdf μ x + cdf ν x = 2 * cdf unitIntervalMeasure x := by
  have h := congrArg (fun m : Measure ℝ => m.real (Iic x)) hsum
  simpa [cdf_eq_real, measureReal_add_apply] using h

theorem cdf_zero_of_sum (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hsum : μ + ν = (2 : ℝ≥0∞) • unitIntervalMeasure)
    {x : ℝ} (hx : x ≤ 0) : cdf μ x = 0 := by
  have he := cdf_sum_relation μ ν hsum x
  rw [unit_cdf_eq, min_eq_left (by linarith : x ≤ 1), max_eq_right hx] at he
  have hp := cdf_nonneg μ x
  have hq := cdf_nonneg ν x
  linarith

theorem cdf_one_of_sum (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hsum : μ + ν = (2 : ℝ≥0∞) • unitIntervalMeasure)
    {x : ℝ} (hx : 1 ≤ x) : cdf μ x = 1 := by
  have he := cdf_sum_relation μ ν hsum x
  rw [unit_cdf_eq, min_eq_right hx, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)] at he
  have hp := cdf_le_one μ x
  have hq := cdf_le_one ν x
  linarith

theorem cdf_lipschitz_of_sum (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hsum : μ + ν = (2 : ℝ≥0∞) • unitIntervalMeasure) :
    LipschitzWith 2 (cdf μ) := by
  have hinc : ∀ a b : ℝ, a ≤ b → cdf μ b - cdf μ a ≤ 2 * (b - a) := by
    intro a b hab
    have ha := cdf_sum_relation μ ν hsum a
    have hb := cdf_sum_relation μ ν hsum b
    have hq := monotone_cdf ν hab
    have hu := unit_cdf_sub_le hab
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rcases le_total a b with hab | hba
  · rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (monotone_cdf μ hab)),
      Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hinc a b hab
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (monotone_cdf μ hba)),
      Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hinc b a hba

def windowSet (α s : ℝ) : Set ℝ := Ioc s (s + α) ∪ Ioc (s - 1) (s + α - 1)

theorem measurableSet_windowSet (α s : ℝ) : MeasurableSet (windowSet α s) :=
  measurableSet_Ioc.union measurableSet_Ioc

theorem real_Ioc_eq_cdf_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) : μ.real (Ioc a b) = cdf μ b - cdf μ a := by
  have h := congrArg ENNReal.toReal ((cdf μ).measure_Ioc a b)
  rw [measure_cdf, ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf μ hab))] at h
  exact h

theorem real_windowSet (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hzero : ∀ x, x ≤ 0 → cdf μ x = 0) {α s : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs1 : s ≤ 1) :
    μ.real (windowSet α s) = windowMass (cdf μ) α s := by
  have hd : Disjoint (Ioc s (s + α)) (Ioc (s - 1) (s + α - 1)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have := hx.1
    have := hy.2
    linarith
  rw [windowSet, measureReal_union hd measurableSet_Ioc,
    real_Ioc_eq_cdf_sub μ (by linarith : s ≤ s + α),
    real_Ioc_eq_cdf_sub μ (by linarith : s - 1 ≤ s + α - 1),
    hzero (s - 1) (by linarith), sub_zero]
  rfl

theorem unit_window_mass {α s : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : windowMass (cdf unitIntervalMeasure) α s = α := by
  unfold windowMass
  rw [unit_cdf_eq, unit_cdf_eq, unit_cdf_eq,
    min_eq_left hs1, max_eq_left hs0]
  rcases le_total (s + α) 1 with h | h
  · rw [min_eq_left h, max_eq_left (by linarith : 0 ≤ s + α),
      min_eq_left (by linarith : s + α - 1 ≤ 1),
      max_eq_right (by linarith : s + α - 1 ≤ 0)]
    ring
  · rw [min_eq_right h, max_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      min_eq_left (by linarith : s + α - 1 ≤ 1),
      max_eq_left (by linarith : 0 ≤ s + α - 1)]
    ring

theorem exists_common_real_window (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hsum : μ + ν = (2 : ℝ≥0∞) • unitIntervalMeasure)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ E = ENNReal.ofReal α ∧ ν E = ENNReal.ofReal α := by
  have hz : ∀ x, x ≤ 0 → cdf μ x = 0 := fun x hx => cdf_zero_of_sum μ ν hsum hx
  have ho : ∀ x, 1 ≤ x → cdf μ x = 1 := fun x hx => cdf_one_of_sum μ ν hsum hx
  obtain ⟨s, hs, he⟩ := exists_rotation_mass (cdf_lipschitz_of_sum μ ν hsum).continuous
    hz ho hα0 hα1
  have hswap : ν + μ = (2 : ℝ≥0∞) • unitIntervalMeasure := by rw [add_comm]; exact hsum
  have hz' : ∀ x, x ≤ 0 → cdf ν x = 0 := fun x hx => cdf_zero_of_sum ν μ hswap hx
  have hμ : μ.real (windowSet α s) = α :=
    (real_windowSet μ hz hα0 hα1 hs.2).trans he
  have hν : ν.real (windowSet α s) = α := by
    rw [real_windowSet ν hz' hα0 hα1 hs.2]
    have h0 := cdf_sum_relation μ ν hsum s
    have h1 := cdf_sum_relation μ ν hsum (s + α)
    have h2 := cdf_sum_relation μ ν hsum (s + α - 1)
    have hu := unit_window_mass hα0 hα1 hs.1 hs.2
    unfold windowMass at he hu ⊢
    linarith
  refine ⟨windowSet α s, measurableSet_windowSet α s, ?_, ?_⟩
  · rw [← ofReal_measureReal, hμ]
  · rw [← ofReal_measureReal, hν]

end Aumann1974.TwoPersonProof

end

/- Complete checked body: ObjectiveFibers -/
section

set_option autoImplicit false

open Set MeasureTheory

namespace Aumann1974.TwoPersonProof

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def HasCommonSplit (μ ν : Measure Ω) (m : MeasurableSpace Ω) : Prop :=
  ∀ E : Set Ω, MeasurableSet[m] E → μ.real E = ν.real E →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ μ.real E →
      ∃ B : Set Ω, MeasurableSet[m] B ∧ B ⊆ E ∧ μ.real B = θ ∧ ν.real B = θ

theorem common_fibers_fin (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (hsplit : HasCommonSplit μ ν m) (n : ℕ) :
    ∀ E : Set Ω, MeasurableSet[m] E → μ.real E = ν.real E →
      ∀ w : Fin (n + 1) → ℝ, (∀ a, 0 ≤ w a) → (∑ a, w a) = μ.real E →
        ∃ f : Ω → Fin (n + 1), ∀ a,
          MeasurableSet[m] ({ω | f ω = a} ∩ E) ∧
          μ.real ({ω | f ω = a} ∩ E) = w a ∧
          ν.real ({ω | f ω = a} ∩ E) = w a := by
  classical
  induction n with
  | zero =>
      intro E hE heq w _hw hsum
      refine ⟨fun _ => 0, ?_⟩
      intro a
      have ha : a = 0 := by apply Fin.ext; omega
      subst a
      have hsum0 : w 0 = μ.real E := by simpa using hsum
      simpa only [ofPred_true, univ_inter] using
        And.intro hE (And.intro hsum0.symm (heq.symm.trans hsum0.symm))
  | succ n ih =>
      intro E hE heq w hw hsum
      have hw0 : w 0 ≤ μ.real E := by
        rw [← hsum]
        exact Finset.single_le_sum (fun a _ => hw a) (Finset.mem_univ 0)
      obtain ⟨B, hB, hBE, hμB, hνB⟩ := hsplit E hE heq (w 0) (hw 0) hw0
      have hμR : μ.real (E \ B) = μ.real E - w 0 := by
        rw [measureReal_sdiff hBE (hm _ hB), hμB]
      have hνR : ν.real (E \ B) = ν.real E - w 0 := by
        rw [measureReal_sdiff hBE (hm _ hB), hνB]
      have heqR : μ.real (E \ B) = ν.real (E \ B) := by rw [hμR, hνR, heq]
      have hsumR : (∑ a : Fin (n + 1), w a.succ) = μ.real (E \ B) := by
        rw [Fin.sum_univ_succ] at hsum
        rw [hμR]
        linarith
      obtain ⟨f, hf⟩ := ih (E \ B) (hE.diff hB) heqR
        (fun a => w a.succ) (fun a => hw a.succ) hsumR
      let g : Ω → Fin (n + 1 + 1) := fun ω => if ω ∈ B then 0 else (f ω).succ
      refine ⟨g, ?_⟩
      intro a
      refine Fin.cases ?_ (fun b => ?_) a
      · have hset : {ω | g ω = 0} ∩ E = B := by
          ext ω
          by_cases hω : ω ∈ B
          · simp [g, hω, hBE hω]
          · simp [g, hω]
        rw [hset]
        exact ⟨hB, hμB, hνB⟩
      · have hne : (0 : Fin (n + 1 + 1)) ≠ b.succ := Ne.symm (Fin.succ_ne_zero b)
        have hset : {ω | g ω = b.succ} ∩ E = {ω | f ω = b} ∩ (E \ B) := by
          ext ω
          by_cases hω : ω ∈ B
          · simp [g, hω, hne]
          · simp [g, hω]
        rw [hset]
        exact hf b

theorem common_fibers_finite (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (hsplit : HasCommonSplit μ ν m)
    {A : Type*} [Fintype A] [Nonempty A] (E : Set Ω) (hE : MeasurableSet[m] E)
    (heq : μ.real E = ν.real E) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hsum : (∑ a, w a) = μ.real E) :
    ∃ f : Ω → A, ∀ a, MeasurableSet[m] ({ω | f ω = a} ∩ E) ∧
      μ.real ({ω | f ω = a} ∩ E) = w a ∧ ν.real ({ω | f ω = a} ∩ E) = w a := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e : A ≃ Fin (n + 1) := (Fintype.equivFin A).trans (finCongr hn)
  have hsum' : (∑ a : Fin (n + 1), w (e.symm a)) = μ.real E := by
    rw [e.symm.sum_comp]
    exact hsum
  obtain ⟨f, hf⟩ := common_fibers_fin μ ν m hm hsplit n E hE heq
    (fun a => w (e.symm a)) (fun a => hw (e.symm a)) hsum'
  refine ⟨fun ω => e.symm (f ω), ?_⟩
  intro a
  have hset : {ω | e.symm (f ω) = a} = {ω | f ω = e a} := by
    ext ω
    exact e.symm_apply_eq
  rw [hset]
  simpa only [e.symm_apply_apply] using hf (e a)

theorem exists_common_fibers (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hsplit : HasCommonSplit μ ν m) {A : Type*} [Fintype A] [Nonempty A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : (∑ a, w a) = 1) :
    ∃ f : Ω → A, ∀ a, MeasurableSet[m] {ω | f ω = a} ∧
      μ.real {ω | f ω = a} = w a ∧ ν.real {ω | f ω = a} = w a := by
  obtain ⟨f, hf⟩ := common_fibers_finite μ ν m hm hsplit univ MeasurableSet.univ
    (by simp) w hw (by simpa using hsum)
  exact ⟨f, fun a => by simpa only [inter_univ] using hf a⟩

end Aumann1974.TwoPersonProof

end

/- Complete checked body: CommonSubsets -/
section

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem common_event_probability (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hμ : NonAtomicOn μ m) (hν : NonAtomicOn ν m)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ F : Set Ω, MeasurableSet[m] F ∧ μ F = ENNReal.ofReal α ∧ ν F = ENNReal.ofReal α := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨U, hUm, _hU, hlaw⟩ := exists_uniform_coordinate (meanMeasure μ ν) hm
    (meanMeasure_nonatomic μ ν m hμ hν)
  have hU : Measurable U := hUm.mono hm le_rfl
  have : IsProbabilityMeasure (μ.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have : IsProbabilityMeasure (ν.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  have hsum : μ.map U + ν.map U = (2 : ℝ≥0∞) • unitIntervalMeasure := by
    calc
      _ = (μ + ν).map U := (Measure.map_add μ ν hU).symm
      _ = ((2 : ℝ≥0∞) • meanMeasure μ ν).map U := by rw [two_smul_meanMeasure]
      _ = (2 : ℝ≥0∞) • (meanMeasure μ ν).map U := Measure.map_smul _ _ _
      _ = (2 : ℝ≥0∞) • unitIntervalMeasure := by rw [hlaw]; rfl
  obtain ⟨E, hE, hμE, hνE⟩ := exists_common_real_window (μ.map U) (ν.map U) hsum hα0 hα1
  refine ⟨U ⁻¹' E, hUm hE, ?_, ?_⟩
  · rwa [Measure.map_apply hU hE] at hμE
  · rwa [Measure.map_apply hU hE] at hνE

theorem exists_common_subset (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hμ : NonAtomicOn μ m) (hν : NonAtomicOn ν m) : HasCommonSplit μ ν m := by
  let : MeasurableSpace Ω := mΩ
  intro E hE heq θ hθ0 hθE
  by_cases hmass : μ.real E = 0
  · have hθ : θ = 0 := by linarith
    exact ⟨∅, @MeasurableSet.empty Ω m, empty_subset E, by simp [hθ], by simp [hθ]⟩
  have hpos : 0 < μ.real E := lt_of_le_of_ne measureReal_nonneg (Ne.symm hmass)
  have hμ0 : μ E ≠ 0 := (measureReal_ne_zero_iff).mp hmass
  have hν0 : ν E ≠ 0 := (measureReal_ne_zero_iff).mp (by rwa [← heq])
  let μE : Measure Ω := (μ E)⁻¹ • μ.restrict E
  let νE : Measure Ω := (ν E)⁻¹ • ν.restrict E
  have : IsProbabilityMeasure μE := by
    constructor
    simp only [μE, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hμ0 (by finiteness)
  have : IsProbabilityMeasure νE := by
    constructor
    simp only [νE, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hν0 (by finiteness)
  have hμN : NonAtomicOn μE m := nonatomic_smul (μ.restrict E) m
    (nonatomic_restrict μ m hm hμ E hE) (μ E)⁻¹ (by simp) (by simpa using hμ0)
  have hνN : NonAtomicOn νE m := nonatomic_smul (ν.restrict E) m
    (nonatomic_restrict ν m hm hν E hE) (ν E)⁻¹ (by simp) (by simpa using hν0)
  have hα0 : 0 ≤ θ / μ.real E := div_nonneg hθ0 hpos.le
  have hα1 : θ / μ.real E ≤ 1 := (div_le_one hpos).mpr hθE
  obtain ⟨A, hA, hμA, hνA⟩ := common_event_probability μE νE m hm hμN hνN hα0 hα1
  have hμR : μE.real A = θ / μ.real E := by
    rw [measureReal_def, hμA, ENNReal.toReal_ofReal hα0]
  have hνR : νE.real A = θ / μ.real E := by
    rw [measureReal_def, hνA, ENNReal.toReal_ofReal hα0]
  dsimp only [μE] at hμR
  dsimp only [νE] at hνR
  rw [measureReal_ennreal_smul_apply, measureReal_restrict_apply (hm _ hA),
    ENNReal.toReal_inv] at hμR
  rw [measureReal_ennreal_smul_apply, measureReal_restrict_apply (hm _ hA),
    ENNReal.toReal_inv] at hνR
  change (μ.real E)⁻¹ * μ.real (A ∩ E) = θ / μ.real E at hμR
  change (ν.real E)⁻¹ * ν.real (A ∩ E) = θ / μ.real E at hνR
  rw [← heq] at hνR
  field_simp [hpos.ne'] at hμR hνR
  exact ⟨A ∩ E, hA.inter hE, inter_subset_right, hμR, hνR⟩

end Aumann1974.TwoPersonProof

end

/- Complete checked body: ObjectiveStrategies -/
section

set_option autoImplicit false

open Set MeasureTheory

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

theorem objective_mixed_realization {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R) (i : Fin 2)
    {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : (∑ a, w a) = 1) :
    ∃ t : Ω → A, IsObjectiveStrategy R t ∧ IsMixed R i t ∧
      ∀ j a, (R.p j).real {ω | t ω = a} = w a := by
  obtain ⟨m, hsecret, hnonatomic⟩ := hII i
  have hm : m ≤ mΩ := fun E hE => R.J_le i _ (hsecret E hE).1
  obtain ⟨t, ht⟩ := exists_common_fibers (R.p 0) (R.p 1) m hm
    (exists_common_subset (R.p 0) (R.p 1) m hm (hnonatomic 0) (hnonatomic 1)) w hw hsum
  have hmass : ∀ j : Fin 2, ∀ a, (R.p j).real {ω | t ω = a} = w a := by
    intro j a
    fin_cases j
    · exact (ht a).2.1
    · exact (ht a).2.2
  refine ⟨t, ?_, ?_, hmass⟩
  · intro a j k
    rw [← ofReal_measureReal, ← ofReal_measureReal, hmass j a, hmass k a]
  · intro a
    exact hsecret _ (ht a).1

end Aumann1974.TwoPersonProof

end

/- Complete checked body: AttributedAumann -/
section

set_option autoImplicit false

namespace AumannSourceProfile
-- Prove2me | solution 1 for Aumann1974.TwoPerson.prob_profile_factor
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:27:03.162333+00:00
-- url     : https://prove2.me/submissions/4edeb6bf-6f4d-4cae-aa53-f53b41668b95


namespace AumannFactor
open MeasureTheory Aumann1974.TwoPerson Finset

lemma factor_with {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    (R:RandomizingStructure ι Ω mΩ) (i:ι) (A:ι→Set Ω)
    (hm:∀j,MeasurableSet[R.J j] (A j))
    (hs:∀j,j≠i→IsSecret R j (A j)) (B:Set Ω) (hB:MeasurableSet[R.J i] B)
    (T:Finset ι) (hi:i∉T) :
    R.p i {ω|ω∈B ∧ ∀j∈T,ω∈A j}=R.p i B*∏j∈T,R.p i (A j) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert j T hj ih =>
    have hji:j≠i:=by intro he;subst j;exact hi (mem_insert_self _ _)
    have hiT:i∉T:=fun h=>hi (mem_insert_of_mem h)
    let D:Set Ω:={ω|ω∈B ∧ ∀k∈T,ω∈A k}
    have hD:MeasurableSet[⨆(k:ι)(_ : k≠j),R.J k] D:=by
      have he:D=B∩⋂k∈T,A k:=by ext ω;simp [D]
      rw [he]
      have hleft:MeasurableSet[⨆(k:ι)(_ : k≠j),R.J k] B:=by
        have hle:R.J i≤⨆(k:ι)(_ : k≠j),R.J k:=le_iSup_of_le i (le_iSup_of_le hji.symm le_rfl)
        exact hle _ hB
      apply hleft.inter
      apply MeasurableSet.biInter (Finset.countable_toSet T)
      intro k hk
      have hkj:k≠j:=by intro he;subst k;exact hj hk
      have hle:R.J k≤⨆(k:ι)(_ : k≠j),R.J k:=le_iSup_of_le k (le_iSup_of_le hkj le_rfl)
      exact hle _ (hm k)
    have hh : {ω|ω∈B ∧ ∀k∈insert j T,ω∈A k}=A j∩D:=by
      ext ω;simp [D];tauto
    rw [hh,(hs j hji).2 i hji.symm D hD]
    rw [show R.p i D=R.p i B*∏k∈T,R.p i (A k) from ih hiT,Finset.prod_insert hj]
    ring

lemma factor_all {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    (R:RandomizingStructure ι Ω mΩ) (i:ι) (A:ι→Set Ω)
    (hm:∀j,MeasurableSet[R.J j] (A j))
    (hs:∀j,j≠i→IsSecret R j (A j)) :
    R.p i (⋂j,A j)=∏j,R.p i (A j) := by
  have hh:=factor_with R i A hm hs (A i) (hm i) (univ.erase i) (by simp)
  have he:{ω|ω∈A i ∧ ∀j∈univ.erase i,ω∈A j}=(⋂j,A j):=by
    ext ω;simp only [Set.mem_ofPred_eq,Set.mem_iInter,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨hi,h⟩ j
      by_cases hj:j=i
      · simpa [hj] using hi
      · exact h j hj
    · intro h;exact ⟨h i,fun j _=>h j⟩
  rw [he] at hh
  simpa only [Finset.mul_prod_erase univ (fun j=>R.p i (A j)) (Finset.mem_univ i)] using hh

lemma secret_univ {ι Ω:Type*} {mΩ:MeasurableSpace Ω} (R:RandomizingStructure ι Ω mΩ) (i:ι) :
    IsSecret R i Set.univ := by
  refine ⟨MeasurableSet.univ,?_⟩
  intro j hj B hB
  simp

lemma independent {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    {S:ι→Type*} (R:RandomizingStructure ι Ω mΩ) (s:∀j,Ω→S j)
    (hs:∀j,IsMixed R j (s j)) : IsUncorrelated R s := by
  intro a i B hB
  apply factor_all R i B
  · intro j
    rcases hB j with h|h
    · rw [h];exact (hs j (a j)).1
    · rw [h];exact MeasurableSet.univ
  · intro j hj
    rcases hB j with h|h
    · rw [h];exact hs j (a j)
    · rw [h];exact secret_univ R j

lemma profile {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    {S:ι→Type*} (R:RandomizingStructure ι Ω mΩ) (s:∀j,Ω→S j)
    (hs:∀j,IsStrategy R j (s j)) (a:∀j,S j) (i:ι)
    (hmix:∀j,j≠i→IsMixed R j (s j)) :
    R.p i {ω|∀j,s j ω=a j}=R.p i {ω|s i ω=a i}*R.p i {ω|∀j,j≠i→s j ω=a j} ∧
    R.p i {ω|s i ω=a i}*R.p i {ω|∀j,j≠i→s j ω=a j}=∏j,R.p i {ω|s j ω=a j} := by
  let A:ι→Set Ω:=fun j=>{ω|s j ω=a j}
  have hm:∀j,MeasurableSet[R.J j] (A j):=fun j=>hs j (a j)
  have hsec:∀j,j≠i→IsSecret R j (A j):=fun j hj=>hmix j hj (a j)
  have hall:=factor_all R i A hm hsec
  have hrest:=factor_with R i A hm hsec Set.univ MeasurableSet.univ (univ.erase i) (by simp)
  simp only [Set.mem_univ,true_and,Finset.mem_erase,Finset.mem_univ,and_true,measure_univ,one_mul] at hrest
  have hproduct:R.p i (A i)*R.p i {ω|∀j,j≠i→ω∈A j}=∏j,R.p i (A j):=by
    rw [hrest,Finset.mul_prod_erase univ (fun j=>R.p i (A j)) (Finset.mem_univ i)]
  constructor
  · simpa only [A,Set.iInter_ofPred,Set.mem_ofPred_eq] using hall.trans hproduct.symm
  · exact hproduct

end AumannFactor

open MeasureTheory Aumann1974.TwoPerson

theorem checked_prob_profile_factor {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure ι Ω mΩ) (_hII : AssumptionII R)
    (s : ∀ j, Ω → S j) (hs : ∀ j, IsStrategy R j (s j)) (a : ∀ j, S j) (i : ι)
    (hmix : ∀ j, j ≠ i → IsMixed R j (s j)) :
    R.p i {ω | ∀ j, s j ω = a j} =
        R.p i {ω | s i ω = a i} * R.p i {ω | ∀ j, j ≠ i → s j ω = a j} ∧
      R.p i {ω | s i ω = a i} * R.p i {ω | ∀ j, j ≠ i → s j ω = a j} =
        ∏ j, R.p i {ω | s j ω = a j} := by
  exact AumannFactor.profile R s hs a i hmix
end AumannSourceProfile

namespace AumannSourceIndependent
-- Prove2me | solution 1 for Aumann1974.TwoPerson.mixed_strategies_independent
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:27:02.408878+00:00
-- url     : https://prove2.me/submissions/016140a0-edc6-4431-9a5d-5f033d7f9770


namespace AumannFactor
open MeasureTheory Aumann1974.TwoPerson Finset

lemma factor_with {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    (R:RandomizingStructure ι Ω mΩ) (i:ι) (A:ι→Set Ω)
    (hm:∀j,MeasurableSet[R.J j] (A j))
    (hs:∀j,j≠i→IsSecret R j (A j)) (B:Set Ω) (hB:MeasurableSet[R.J i] B)
    (T:Finset ι) (hi:i∉T) :
    R.p i {ω|ω∈B ∧ ∀j∈T,ω∈A j}=R.p i B*∏j∈T,R.p i (A j) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert j T hj ih =>
    have hji:j≠i:=by intro he;subst j;exact hi (mem_insert_self _ _)
    have hiT:i∉T:=fun h=>hi (mem_insert_of_mem h)
    let D:Set Ω:={ω|ω∈B ∧ ∀k∈T,ω∈A k}
    have hD:MeasurableSet[⨆(k:ι)(_ : k≠j),R.J k] D:=by
      have he:D=B∩⋂k∈T,A k:=by ext ω;simp [D]
      rw [he]
      have hleft:MeasurableSet[⨆(k:ι)(_ : k≠j),R.J k] B:=by
        have hle:R.J i≤⨆(k:ι)(_ : k≠j),R.J k:=le_iSup_of_le i (le_iSup_of_le hji.symm le_rfl)
        exact hle _ hB
      apply hleft.inter
      apply MeasurableSet.biInter (Finset.countable_toSet T)
      intro k hk
      have hkj:k≠j:=by intro he;subst k;exact hj hk
      have hle:R.J k≤⨆(k:ι)(_ : k≠j),R.J k:=le_iSup_of_le k (le_iSup_of_le hkj le_rfl)
      exact hle _ (hm k)
    have hh : {ω|ω∈B ∧ ∀k∈insert j T,ω∈A k}=A j∩D:=by
      ext ω;simp [D];tauto
    rw [hh,(hs j hji).2 i hji.symm D hD]
    rw [show R.p i D=R.p i B*∏k∈T,R.p i (A k) from ih hiT,Finset.prod_insert hj]
    ring

lemma factor_all {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    (R:RandomizingStructure ι Ω mΩ) (i:ι) (A:ι→Set Ω)
    (hm:∀j,MeasurableSet[R.J j] (A j))
    (hs:∀j,j≠i→IsSecret R j (A j)) :
    R.p i (⋂j,A j)=∏j,R.p i (A j) := by
  have hh:=factor_with R i A hm hs (A i) (hm i) (univ.erase i) (by simp)
  have he:{ω|ω∈A i ∧ ∀j∈univ.erase i,ω∈A j}=(⋂j,A j):=by
    ext ω;simp only [Set.mem_ofPred_eq,Set.mem_iInter,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨hi,h⟩ j
      by_cases hj:j=i
      · simpa [hj] using hi
      · exact h j hj
    · intro h;exact ⟨h i,fun j _=>h j⟩
  rw [he] at hh
  simpa only [Finset.mul_prod_erase univ (fun j=>R.p i (A j)) (Finset.mem_univ i)] using hh

lemma secret_univ {ι Ω:Type*} {mΩ:MeasurableSpace Ω} (R:RandomizingStructure ι Ω mΩ) (i:ι) :
    IsSecret R i Set.univ := by
  refine ⟨MeasurableSet.univ,?_⟩
  intro j hj B hB
  simp

lemma independent {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    {S:ι→Type*} (R:RandomizingStructure ι Ω mΩ) (s:∀j,Ω→S j)
    (hs:∀j,IsMixed R j (s j)) : IsUncorrelated R s := by
  intro a i B hB
  apply factor_all R i B
  · intro j
    rcases hB j with h|h
    · rw [h];exact (hs j (a j)).1
    · rw [h];exact MeasurableSet.univ
  · intro j hj
    rcases hB j with h|h
    · rw [h];exact hs j (a j)
    · rw [h];exact secret_univ R j

lemma profile {ι Ω:Type*} [Fintype ι] [DecidableEq ι] {mΩ:MeasurableSpace Ω}
    {S:ι→Type*} (R:RandomizingStructure ι Ω mΩ) (s:∀j,Ω→S j)
    (hs:∀j,IsStrategy R j (s j)) (a:∀j,S j) (i:ι)
    (hmix:∀j,j≠i→IsMixed R j (s j)) :
    R.p i {ω|∀j,s j ω=a j}=R.p i {ω|s i ω=a i}*R.p i {ω|∀j,j≠i→s j ω=a j} ∧
    R.p i {ω|s i ω=a i}*R.p i {ω|∀j,j≠i→s j ω=a j}=∏j,R.p i {ω|s j ω=a j} := by
  let A:ι→Set Ω:=fun j=>{ω|s j ω=a j}
  have hm:∀j,MeasurableSet[R.J j] (A j):=fun j=>hs j (a j)
  have hsec:∀j,j≠i→IsSecret R j (A j):=fun j hj=>hmix j hj (a j)
  have hall:=factor_all R i A hm hsec
  have hrest:=factor_with R i A hm hsec Set.univ MeasurableSet.univ (univ.erase i) (by simp)
  simp only [Set.mem_univ,true_and,Finset.mem_erase,Finset.mem_univ,and_true,measure_univ,one_mul] at hrest
  have hproduct:R.p i (A i)*R.p i {ω|∀j,j≠i→ω∈A j}=∏j,R.p i (A j):=by
    rw [hrest,Finset.mul_prod_erase univ (fun j=>R.p i (A j)) (Finset.mem_univ i)]
  constructor
  · simpa only [A,Set.iInter_ofPred,Set.mem_ofPred_eq] using hall.trans hproduct.symm
  · exact hproduct

end AumannFactor

open MeasureTheory Aumann1974.TwoPerson

theorem checked_mixed_strategies_independent {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure ι Ω mΩ) (_hII : AssumptionII R)
    (s : ∀ j, Ω → S j) (hmix : ∀ j, IsMixed R j (s j)) :
    IsUncorrelated R s := by
  exact AumannFactor.independent R s hmix
end AumannSourceIndependent

end

/- Complete checked body: FinitePayoffs -/
section

set_option autoImplicit false

open Set MeasureTheory

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

theorem sum_real_fibers {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Ω → A)
    (hs : ∀ a, MeasurableSet {ω | s ω = a}) :
    (∑ a, μ.real {ω | s ω = a}) = 1 := by
  classical
  have hd : Pairwise (fun a b : A => Disjoint {ω | s ω = a} {ω | s ω = b}) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have hcover : (⋃ a : A, {ω | s ω = a}) = univ := by ext ω; simp
  have h := measureReal_iUnion_fintype (μ := μ) hd hs
  rw [hcover] at h
  simpa using h.symm

theorem integral_finite_fibers {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Ω → A)
    (hs : ∀ a, MeasurableSet {ω | s ω = a}) (f : A → ℝ) :
    (∫ ω, f (s ω) ∂μ) = ∑ a, μ.real {ω | s ω = a} * f a := by
  classical
  have he : (fun ω => f (s ω)) =
      (fun ω => ∑ a : A, ({ω | s ω = a}).indicator (fun _ => f a) ω) := by
    ext ω
    simp [Set.indicator, eq_comm]
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_indicator (hs a), setIntegral_const, smul_eq_mul]
  · intro a _
    exact (integrable_const (f a)).indicator (hs a)

noncomputable def finitePayoff {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] {X : Type*} (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (ρ : ∀ i, S i → ℝ) (i : ι) : ℝ :=
  ∑ a : (∀ j, S j), payoffFn u g i a * ∏ j, ρ j (a j)

noncomputable def strategyWeights {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : ι → Type*} (R : RandomizingStructure ι Ω mΩ)
    (s : ∀ j, Ω → S j) (i j : ι) (a : S j) : ℝ := (R.p i).real {ω | s j ω = a}

theorem strategyWeights_nonneg {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : ι → Type*} (R : RandomizingStructure ι Ω mΩ)
    (s : ∀ j, Ω → S j) (i j : ι) (a : S j) : 0 ≤ strategyWeights R s i j a :=
  measureReal_nonneg

theorem strategyWeights_sum {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : ι → Type*} [∀ j, Fintype (S j)] (R : RandomizingStructure ι Ω mΩ)
    (s : ∀ j, Ω → S j) (hs : ∀ j, IsStrategy R j (s j)) (i j : ι) :
    (∑ a, strategyWeights R s i j a) = 1 := by
  exact sum_real_fibers (R.p i) (s j) (fun a => R.J_le j _ (hs j a))

theorem payoff_finite_formula {ι Ω X : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (u : ι → X → ℝ) (g : (∀ i, S i) → X) (s : ∀ i, Ω → S i)
    (hs : ∀ i, IsStrategy R i (s i)) (i : ι)
    (hmix : ∀ j, j ≠ i → IsMixed R j (s j)) :
    H R u g s i = finitePayoff u g (strategyWeights R s i) i := by
  classical
  have hset (a : ∀ j, S j) : {ω | (fun j => s j ω) = a} = {ω | ∀ j, s j ω = a j} := by
    ext ω
    simp only [mem_ofPred_eq, funext_iff]
  have hmeas (a : ∀ j, S j) : MeasurableSet {ω | (fun j => s j ω) = a} := by
    rw [hset, show {ω | ∀ j, s j ω = a j} = ⋂ j, {ω | s j ω = a j} by ext ω; simp]
    exact MeasurableSet.iInter (fun j => R.J_le j _ (hs j (a j)))
  unfold H finitePayoff
  rw [integral_finite_fibers (R.p i) (fun ω j => s j ω) hmeas]
  apply Finset.sum_congr rfl
  intro a _
  have hp := AumannSourceProfile.checked_prob_profile_factor R hII s hs a i hmix
  have hh := hp.1.trans hp.2
  rw [hset, measureReal_def, hh]
  simp only [ENNReal.toReal_prod, strategyWeights, measureReal_def]
  ring

theorem indifferent_of_average {A : Type*} [Fintype A] (w f : A → ℝ) (v : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : (∑ a, w a) = 1) (hbound : ∀ a, f a ≤ v)
    (havg : (∑ a, w a * f a) = v) : ∀ a, 0 < w a → f a = v := by
  classical
  have hzero : (∑ a, w a * (v - f a)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, havg, sub_self]
  intro a ha
  have hle : w a * (v - f a) ≤ 0 := by
    rw [← hzero]
    exact Finset.single_le_sum (fun b _ => mul_nonneg (hw b) (sub_nonneg.mpr (hbound b)))
      (Finset.mem_univ a)
  nlinarith [hbound a]

theorem average_of_indifferent {A : Type*} [Fintype A] (w f : A → ℝ) (v : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : (∑ a, w a) = 1)
    (hind : ∀ a, 0 < w a → f a = v) : (∑ a, w a * f a) = v := by
  classical
  calc
    _ = ∑ a, w a * v := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : w a = 0
      · simp only [ha, zero_mul]
      · rw [hind a (lt_of_le_of_ne (hw a) (Ne.symm ha))]
    _ = v := by rw [← Finset.sum_mul, hsum, one_mul]

end Aumann1974.TwoPersonProof

end

/- Complete checked body: FiniteMixture -/
section

set_option autoImplicit false

open Set MeasureTheory
open scoped Classical

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
  [∀ i, Fintype (S i)] {X : Type*}

open Classical in
noncomputable def purePayoff (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (ρ : ∀ i, S i → ℝ) (i : ι) (c : S i) : ℝ :=
  ∑ a : (∀ j, S j), if a i = c then
    payoffFn u g i a * ∏ j ∈ Finset.univ.erase i, ρ j (a j) else 0

theorem finitePayoff_weighted (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (ρ : ∀ i, S i → ℝ) (i : ι) :
    finitePayoff u g ρ i = ∑ c, ρ i c * purePayoff u g ρ i c := by
  classical
  symm
  unfold purePayoff finitePayoff
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ρ j (a j)) (Finset.mem_univ i)]
  ring

theorem purePayoff_congr (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (ρ σ : ∀ i, S i → ℝ) (i : ι) (h : ∀ j, j ≠ i → ρ j = σ j) (c : S i) :
    purePayoff u g ρ i c = purePayoff u g σ i c := by
  classical
  unfold purePayoff
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [h j (Finset.mem_erase.mp hj).1]
  · rfl

theorem finitePayoff_pure (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (ρ : ∀ i, S i → ℝ) (i : ι) (c : S i) :
    finitePayoff u g (Function.update ρ i (fun a => if a = c then 1 else 0)) i =
      purePayoff u g ρ i c := by
  classical
  rw [finitePayoff_weighted]
  have hother : ∀ j, j ≠ i →
      Function.update ρ i (fun a => if a = c then (1 : ℝ) else 0) j = ρ j := by
    intro j hj
    exact Function.update_of_ne hj _ _
  simp_rw [purePayoff_congr u g _ ρ i hother, Function.update_self]
  simp

theorem finitePayoff_bound (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (ρ σ : ∀ i, S i → ℝ) (i : ι) (v : ℝ)
    (hother : ∀ j, j ≠ i → σ j = ρ j)
    (hσ0 : ∀ a, 0 ≤ σ i a) (hσsum : (∑ a, σ i a) = 1)
    (hpure : ∀ a, purePayoff u g ρ i a ≤ v) : finitePayoff u g σ i ≤ v := by
  rw [finitePayoff_weighted]
  simp_rw [purePayoff_congr u g σ ρ i hother]
  calc
    _ ≤ ∑ a, σ i a * v := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
      (hpure a) (hσ0 a))
    _ = v := by rw [← Finset.sum_mul, hσsum, one_mul]

theorem finitePayoff_of_indifferent (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (ρ σ : ∀ i, S i → ℝ) (i : ι) (v : ℝ)
    (hother : ∀ j, j ≠ i → σ j = ρ j)
    (hσ0 : ∀ a, 0 ≤ σ i a) (hσsum : (∑ a, σ i a) = 1)
    (hpure : ∀ a, 0 < σ i a → purePayoff u g ρ i a = v) :
    finitePayoff u g σ i = v := by
  rw [finitePayoff_weighted]
  simp_rw [purePayoff_congr u g σ ρ i hother]
  exact average_of_indifferent (σ i) (purePayoff u g ρ i) v hσ0 hσsum hpure

end Aumann1974.TwoPersonProof

end

/- Complete checked body: EquilibriumAtoms -/
section

set_option autoImplicit false

open Set MeasureTheory
open scoped Classical

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

variable {ι Ω X : Type*} [Fintype ι] [DecidableEq ι]
  {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem strategy_const (R : RandomizingStructure ι Ω mΩ) (i : ι) (a : S i) :
    IsStrategy R i (fun _ => a) := by
  classical
  intro b
  by_cases h : a = b <;> simp [h]

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem strategy_update (R : RandomizingStructure ι Ω mΩ) (s : ∀ j, Ω → S j)
    (hs : ∀ j, IsStrategy R j (s j)) (i : ι) (t : Ω → S i)
    (ht : IsStrategy R i t) : ∀ j, IsStrategy R j (Function.update s i t j) := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using ht
  · simpa only [Function.update_of_ne hj] using hs j

omit [Fintype ι] [∀ i, Fintype (S i)] in
theorem strategyWeights_update_const (R : RandomizingStructure ι Ω mΩ)
    (s : ∀ j, Ω → S j) (i : ι) (a : S i) :
    strategyWeights R (Function.update s i (fun _ => a)) i =
      Function.update (strategyWeights R s i) i (fun b => if b = a then 1 else 0) := by
  classical
  ext j b
  by_cases hj : j = i
  · subst j
    by_cases hb : b = a
    · simp [strategyWeights, hb]
    · simp [strategyWeights, hb, Ne.symm hb]
  · simp only [strategyWeights, Function.update_of_ne hj]

theorem purePayoff_eq_const_payoff (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (u : ι → X → ℝ) (g : (∀ i, S i) → X) (s : ∀ j, Ω → S j)
    (hs : ∀ j, IsStrategy R j (s j)) (i : ι)
    (hmix : ∀ j, j ≠ i → IsMixed R j (s j)) (a : S i) :
    purePayoff u g (strategyWeights R s i) i a =
      H R u g (Function.update s i (fun _ => a)) i := by
  have hstr := strategy_update R s hs i (fun _ => a) (strategy_const R i a)
  have hm : ∀ j, j ≠ i → IsMixed R j (Function.update s i (fun _ => a) j) := by
    intro j hj
    simpa only [Function.update_of_ne hj] using hmix j hj
  have he := payoff_finite_formula R hII u g (Function.update s i (fun _ => a)) hstr i hm
  rw [strategyWeights_update_const, finitePayoff_pure] at he
  exact he.symm

theorem equilibrium_pure_le (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (u : ι → X → ℝ) (g : (∀ i, S i) → X) (s : ∀ j, Ω → S j)
    (hs : IsEquilibrium R u g s) (hmix : ∀ j, IsMixed R j (s j)) (i : ι) (a : S i) :
    purePayoff u g (strategyWeights R s i) i a ≤ H R u g s i := by
  rw [purePayoff_eq_const_payoff R hII u g s hs.1 i (fun j _ => hmix j)]
  exact hs.2 i (fun _ => a) (strategy_const R i a)

theorem equilibrium_active_pure_eq (R : RandomizingStructure ι Ω mΩ)
    (hII : AssumptionII R) (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (s : ∀ j, Ω → S j) (hs : IsEquilibrium R u g s) (hmix : ∀ j, IsMixed R j (s j))
    (i : ι) (a : S i) (ha : 0 < strategyWeights R s i i a) :
    purePayoff u g (strategyWeights R s i) i a = H R u g s i := by
  have hH := payoff_finite_formula R hII u g s hs.1 i (fun j _ => hmix j)
  have havg : (∑ b, strategyWeights R s i i b * purePayoff u g (strategyWeights R s i) i b) =
      H R u g s i := (finitePayoff_weighted u g (strategyWeights R s i) i).symm.trans hH.symm
  exact indifferent_of_average (strategyWeights R s i i) (purePayoff u g (strategyWeights R s i) i)
    (H R u g s i) (fun b => strategyWeights_nonneg R s i i b)
    (strategyWeights_sum R s hs.1 i i) (equilibrium_pure_le R hII u g s hs hmix i) havg a ha

end Aumann1974.TwoPersonProof

end

/- Complete checked body: ObjectiveEquilibrium -/
section

set_option autoImplicit false

open Set MeasureTheory

namespace Aumann1974.TwoPersonProof

open Aumann1974.TwoPerson

theorem two_person_objective_equilibrium {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s : ∀ i, Ω → S i) (hs : IsEquilibrium R u g s) (hmix : ∀ i, IsMixed R i (s i)) :
    ∃ t : ∀ i, Ω → S i, IsEquilibrium R u g t ∧
      (∀ i, IsObjectiveStrategy R (t i) ∧ IsMixed R i (t i)) ∧
      (fun i => H R u g s i) = fun i => H R u g t i := by
  classical
  have hex (i : Fin 2) := objective_mixed_realization R hII i
    (strategyWeights R s i.rev i) (fun a => strategyWeights_nonneg R s i.rev i a)
    (strategyWeights_sum R s hs.1 i.rev i)
  choose t hobj hm ht using hex
  have hstr : ∀ i, IsStrategy R i (t i) := fun i a => (hm i a).1
  have hother : ∀ i j : Fin 2, j ≠ i → strategyWeights R t i j = strategyWeights R s i j := by
    intro i j hji
    have he : j.rev = i := by fin_cases i <;> fin_cases j <;> simp_all
    funext a
    change (R.p i).real {ω | t j ω = a} = (R.p i).real {ω | s j ω = a}
    rw [ht j i a]
    simp only [strategyWeights, he]
  have hsupport : ∀ (i : Fin 2) (a : S i), 0 < strategyWeights R t i i a →
      0 < strategyWeights R s i i a := by
    intro i a ha
    change 0 < (R.p i).real {ω | t i ω = a} at ha
    rw [ht i i a] at ha
    have hmeas : MeasurableSet[mΩ] {ω | s i ω = a} := R.J_le i _ (hs.1 i a)
    have he : R.p i {ω | s i ω = a} = 0 ↔ R.p i.rev {ω | s i ω = a} = 0 := by
      fin_cases i
      · simpa using h52 _ hmeas
      · simpa using (h52 _ hmeas).symm
    have hcross : R.p i.rev {ω | s i ω = a} ≠ 0 := by
      intro hz
      simp only [strategyWeights, measureReal_def, hz, ENNReal.toReal_zero] at ha
      exact (lt_irrefl 0) ha
    exact ENNReal.toReal_pos (mt he.mp hcross) (by finiteness)
  have hpay (i : Fin 2) : H R u g t i = H R u g s i := by
    rw [payoff_finite_formula R hII u g t hstr i (fun j _ => hm j)]
    apply finitePayoff_of_indifferent u g (strategyWeights R s i) (strategyWeights R t i)
      i (H R u g s i) (hother i) (fun a => strategyWeights_nonneg R t i i a)
      (strategyWeights_sum R t hstr i i)
    intro a ha
    exact equilibrium_active_pure_eq R hII u g s hs hmix i a (hsupport i a ha)
  have heq : IsEquilibrium R u g t := by
    refine ⟨hstr, ?_⟩
    intro i d hd
    have hstr' := strategy_update R t hstr i d hd
    have hm' : ∀ j, j ≠ i → IsMixed R j (Function.update t i d j) := by
      intro j hj
      simpa only [Function.update_of_ne hj] using hm j
    rw [hpay i, payoff_finite_formula R hII u g (Function.update t i d) hstr' i hm']
    apply finitePayoff_bound u g (strategyWeights R s i)
      (strategyWeights R (Function.update t i d) i) i (H R u g s i) ?_
      (fun a => strategyWeights_nonneg R (Function.update t i d) i i a)
      (strategyWeights_sum R (Function.update t i d) hstr' i i)
      (equilibrium_pure_le R hII u g s hs hmix i)
    intro j hj
    funext a
    change (R.p i).real {ω | Function.update t i d j ω = a} =
      (R.p i).real {ω | s j ω = a}
    rw [Function.update_of_ne hj]
    exact congrFun (hother i j hj) a
  exact ⟨t, heq, fun i => ⟨hobj i, hm i⟩, funext (fun i => (hpay i).symm)⟩

end Aumann1974.TwoPersonProof

end

/- Complete checked body: AumannRoot -/
section

set_option autoImplicit false

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Proposition 5.1** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 78, PDF p. 12): let `G` be a 2-person game (not necessarily 0-sum,
footnote 16), and assume that
(5.2) for any event `B`, `p₁(B) = 0` if and only if `p₂(B) = 0`.
Then for each equilibrium point `s` in mixed strategies, there is an equilibrium point `t` in
objective mixed strategies such that `H(s) = H(t)`.

**Formalization Note.** The two players `1, 2` are `0, 1 : Fin 2`. The game has finite pure
strategy sets `S 0`, `S 1`, a finite outcome set `X`, an outcome function `g` onto `X` and
utilities `u`; the randomizing structure `R` satisfies Assumption II (standing assumption,
p. 75). (5.2) is imposed for every `ℬ`-measurable `B` (the paper's events). An equilibrium point
(`IsEquilibrium`) is a profile of strategies against which no player gains by deviating to
**any** strategy. `s` is assumed mixed for both players; the conclusion requires `t` to be both
objective and mixed for both players. `H(s) = H(t)` is equality of payoff vectors: each player's
payoff is computed under that player's own `pᵢ`. -/
theorem two_person_mixed_equilibrium_objective {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (hg : Function.Surjective g) (u : Fin 2 → X → ℝ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s : ∀ i, Ω → S i) (hs : IsEquilibrium R u g s) (hmix : ∀ i, IsMixed R i (s i)) :
    ∃ t : ∀ i, Ω → S i, IsEquilibrium R u g t ∧
      (∀ i, IsObjectiveStrategy R (t i) ∧ IsMixed R i (t i)) ∧
      (fun i => H R u g s i) = fun i => H R u g t i := by
  classical
  let ω₀ : Ω := Classical.choice (nonempty_of_isProbabilityMeasure (R.p 0))
  obtain ⟨a, _ha⟩ := hg (g (fun i => s i ω₀))
  have : ∀ i, Nonempty (S i) := fun i => ⟨a i⟩
  exact Aumann1974.TwoPersonProof.two_person_objective_equilibrium R hII g u h52 s hs hmix

end Aumann1974.TwoPerson

end

open Aumann1974.TwoPerson
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


theorem solution {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : RandomizingStructure (Fin 2) Ω mΩ) (hII : AssumptionII R)
    (g : (∀ i, S i) → X) (hg : Function.Surjective g) (u : Fin 2 → X → ℝ)
    (h52 : ∀ B : Set Ω, MeasurableSet[mΩ] B → (R.p 0 B = 0 ↔ R.p 1 B = 0))
    (s : ∀ i, Ω → S i) (hs : IsEquilibrium R u g s) (hmix : ∀ i, IsMixed R i (s i)) :
    ∃ t : ∀ i, Ω → S i, IsEquilibrium R u g t ∧
      (∀ i, IsObjectiveStrategy R (t i) ∧ IsMixed R i (t i)) ∧
      (fun i => H R u g s i) = fun i => H R u g t i := by
  exact Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective R hII g hg u h52 s hs hmix

#print axioms Aumann1974.TwoPerson.two_person_mixed_equilibrium_objective
#print axioms solution
