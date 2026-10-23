-- Prove2me | solution 1 for AssortRotation.Concealment.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T05:46:49.773913+00:00
-- url     : https://prove2.me/submissions/af706adf-e213-4c38-94a5-51dd396e57fc

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model
import Theorems.Thm_AssortRotation_Concealment_theorem_1_a
import Theorems.Thm_AssortRotation_Concealment_remark_1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace AssortRotation.Concealment.RootBridge

noncomputable section

variable {Ω : Type*} {N : ℕ}

/-- Decreasing weight, with the original product index breaking ties. -/
def Before (w : Fin N → ℝ) (i j : Fin N) : Prop :=
  w j < w i ∨ (w i = w j ∧ i ≤ j)

theorem before_weight_le (w : Fin N → ℝ) {i j : Fin N} (h : Before w i j) :
    w j ≤ w i := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

instance beforeTrans (w : Fin N → ℝ) : IsTrans (Fin N) (Before w) where
  trans i j k hij hjk := by
    rcases hij with hij | ⟨hij, hij'⟩ <;>
      rcases hjk with hjk | ⟨hjk, hjk'⟩
    · exact Or.inl (hjk.trans hij)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨hij.trans hjk, hij'.trans hjk'⟩

instance beforeAntisymm (w : Fin N → ℝ) : Std.Antisymm (Before w) where
  antisymm i j hij hji := by
    rcases hij with hij | ⟨hij, hij'⟩ <;>
      rcases hji with hji | ⟨hji, hji'⟩
    · exact (lt_asymm hij hji).elim
    · exact (by linarith : False).elim
    · exact (by linarith : False).elim
    · exact le_antisymm hij' hji'

instance beforeTotal (w : Fin N → ℝ) : Std.Total (Before w) where
  total i j := by
    rcases lt_trichotomy (w i) (w j) with h | h | h
    · exact Or.inr (Or.inl h)
    · rcases le_total i j with hij | hji
      · exact Or.inl (Or.inr ⟨h, hij⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hji⟩)
    · exact Or.inl (Or.inl h)

def orderedIndices (w : Fin N → ℝ) (S : Finset (Fin N)) : List (Fin N) := by
  classical
  exact S.sort (Before w)

theorem ordered_nodup (w : Fin N → ℝ) (S : Finset (Fin N)) :
    (orderedIndices w S).Nodup := by
  classical
  exact S.sort_nodup (Before w)

theorem ordered_toFinset (w : Fin N → ℝ) (S : Finset (Fin N)) :
    (orderedIndices w S).toFinset = S := by
  classical
  exact S.sort_toFinset (Before w)

theorem ordered_pairwise (w : Fin N → ℝ) (S : Finset (Fin N)) :
    (orderedIndices w S).Pairwise (Before w) := by
  classical
  exact S.pairwise_sort (Before w)

theorem ordered_perm (w : Fin N → ℝ) (S : Finset (Fin N)) :
    (orderedIndices w S).Perm (S.sort (· ≤ ·)) := by
  classical
  exact (S.sort_perm_toList (Before w)).trans
    (S.sort_perm_toList (· ≤ ·)).symm

theorem before_not_reverse_strict (w : Fin N → ℝ) {i j : Fin N}
    (h : Before w i j) : ¬(w i < w j ∨ (w j = w i ∧ j < i)) := by
  rcases h with h | ⟨h, h'⟩
  · rintro (hr | ⟨hr, _⟩) <;> linarith
  · rintro (hr | ⟨_, hr⟩)
    · linarith
    · exact (not_lt_of_ge h') hr

theorem before_strict_of_ne (w : Fin N → ℝ) {i j : Fin N}
    (h : Before w i j) (hne : i ≠ j) :
    w j < w i ∨ (w i = w j ∧ i < j) := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h
  · rcases lt_or_eq_of_le h' with hlt | heq
    · exact Or.inr ⟨h, hlt⟩
    · exact (hne heq).elim

/-- Removing the canonical first index gives the exact rank recursion, including ties. -/
theorem rank_head (p : Fin N → ℝ) (X : Fin N → Ω → ℝ) (ω : Ω)
    (i : Fin N) (I : List (Fin N))
    (hs : (i :: I).Pairwise (Before (fun j => X j ω - p j))) :
    rankIn p X (insert i I.toFinset) ω i = 0 := by
  classical
  unfold rankIn
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  rcases Finset.mem_filter.mp hj with ⟨hj, hr⟩
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simp at hr
  · exact before_not_reverse_strict _
      ((List.pairwise_cons.mp hs).1 j (List.mem_toFinset.mp hj)) hr

theorem rank_tail (p : Fin N → ℝ) (X : Fin N → Ω → ℝ) (ω : Ω)
    (i : Fin N) (I : List (Fin N)) (hn : (i :: I).Nodup)
    (hs : (i :: I).Pairwise (Before (fun j => X j ω - p j)))
    (j : Fin N) (hj : j ∈ I.toFinset) :
    rankIn p X (insert i I.toFinset) ω j = rankIn p X I.toFinset ω j + 1 := by
  classical
  have hnot : i ∉ I.toFinset := by
    simpa using (List.nodup_cons.mp hn).1
  have hne : i ≠ j := by
    intro h
    exact hnot (h.symm ▸ hj)
  have hr : X j ω - p j < X i ω - p i ∨
      (X i ω - p i = X j ω - p j ∧ i < j) :=
    before_strict_of_ne _
      ((List.pairwise_cons.mp hs).1 j (List.mem_toFinset.mp hj)) hne
  simp [rankIn, Finset.filter_insert, hr, hnot]

/-- The canonical list and the model's finite-set revenue agree at every starting rank. -/
theorem fixedRevAux_eq_rank_sum (v : ℕ → ℝ) (p : Fin N → ℝ)
    (X : Fin N → Ω → ℝ) (ω : Ω) (I : List (Fin N))
    (hn : I.Nodup) (hs : I.Pairwise (Before (fun j => X j ω - p j))) (k : ℕ) :
    fixedRevAux v (I.map (fun i => (p i, X i ω))) k =
      ∑ i ∈ I.toFinset,
        if 0 ≤ v (k + rankIn p X I.toFinset ω i) + X i ω - p i then p i else 0 := by
  classical
  induction I generalizing k with
  | nil => simp [fixedRevAux]
  | cons i I ih =>
    have hnot : i ∉ I.toFinset := by
      simpa using (List.nodup_cons.mp hn).1
    have hzero := rank_head p X ω i I hs
    have hsucc := rank_tail p X ω i I hn hs
    simp only [List.map_cons, fixedRevAux, List.toFinset_cons]
    rw [Finset.sum_insert hnot, hzero, Nat.add_zero,
      ih (hn := (List.nodup_cons.mp hn).2)
        (hs := (List.pairwise_cons.mp hs).2) (k := k + 1)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsucc j hj]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem canonical_fixed (v : ℕ → ℝ) (p : Fin N → ℝ) (X : Fin N → Ω → ℝ)
    (S : Finset (Fin N)) (ω : Ω) :
    fixedRev v ((orderedIndices (fun i => X i ω - p i) S).map
      (fun i => (p i, X i ω))) = RfSet v p X S ω := by
  classical
  simpa only [fixedRev, RfSet, ordered_toFinset, Nat.zero_add] using
    fixedRevAux_eq_rank_sum v p X ω (orderedIndices (fun i => X i ω - p i) S)
      (ordered_nodup _ _) (ordered_pairwise _ _) 0

/-- Interface to the existing proved pathwise milestone. The optimality assumption is unnecessary. -/
theorem pathwise_set (v : ℕ → ℝ) (hv : MarginalUtility v)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (X : Fin N → Ω → ℝ)
    (S : Finset (Fin N)) (ω : Ω) (L : List (ℝ × ℝ))
    (hL : L.Perm (products p X S ω))
    (hdec : L.Pairwise (fun a b => b.1 ≤ a.1)) :
    RfSet v p X S ω ≤ seqRev v L 0 := by
  classical
  let I := orderedIndices (fun i => X i ω - p i) S
  let L' := I.map (fun i => (p i, X i ω))
  have hperm : L'.Perm L :=
    ((ordered_perm (fun i => X i ω - p i) S).map
      (fun i => (p i, X i ω))).trans hL.symm
  have hprice : ∀ a ∈ L, 0 ≤ a.1 := by
    intro a ha
    have : a ∈ products p X S ω := hL.mem_iff.mp ha
    rcases List.mem_map.mp this with ⟨i, _, rfl⟩
    exact hp i
  have hsorted : L'.Pairwise (fun a b => b.2 - b.1 ≤ a.2 - a.1) := by
    apply List.pairwise_map.mpr
    exact (ordered_pairwise (fun i => X i ω - p i) S).imp
      (fun {_ _} h => before_weight_le _ h)
  rw [← canonical_fixed v p X S ω]
  exact theorem_1_a v hv L hprice hdec L' hperm hsorted

/-- Extend Remark 1 to a finite suffix, using the proved append-product theorem. -/
theorem append_many (v : ℕ → ℝ) (hv : MarginalUtility v)
    (L T : List (ℝ × ℝ)) (hT : ∀ a ∈ T, 0 ≤ a.1) :
    seqRev v L 0 ≤ seqRev v (L ++ T) 0 := by
  induction T using List.reverseRecOn with
  | nil => simp
  | append_singleton T a ih =>
    have hT' : ∀ b ∈ T, 0 ≤ b.1 := by
      intro b hb
      exact hT b (List.mem_append.mpr (Or.inl hb))
    have ha : 0 ≤ a.1 := hT a (by simp)
    exact (ih hT').trans (by
      simpa only [List.append_assoc] using remark_1 v hv (L ++ T) a ha)

/-- A complete nodup index list is exactly the enumeration of one fixed permutation. -/
theorem permutation_of_list (J : List (Fin N)) (hn : J.Nodup)
    (hall : ∀ i : Fin N, i ∈ J) :
    ∃ τ : Equiv.Perm (Fin N), List.ofFn τ = J := by
  classical
  have hset : J.toFinset = Finset.univ := by
    ext i
    simp [hall i]
  have hlen : J.length = N := by
    have hc := congrArg Finset.card hset
    simpa only [List.toFinset_card_of_nodup hn, Finset.card_univ, Fintype.card_fin] using hc
  let e : Fin N ≃ Fin J.length := (finCongr hlen).symm
  have hg : Function.Bijective J.get := by
    refine ⟨hn.injective_get, ?_⟩
    intro i
    exact List.mem_iff_get.mp (hall i)
  let τ : Equiv.Perm (Fin N) := e.trans (Equiv.ofBijective J.get hg)
  refine ⟨τ, ?_⟩
  apply List.ext_get
  · simpa using hlen.symm
  · intro n h₁ h₂
    simp only [List.get_ofFn]
    change J.get (e (Fin.cast _ ⟨n, h₁⟩)) = J.get ⟨n, h₂⟩
    apply congrArg J.get
    apply Fin.ext
    rfl

/-- Price sorting uses only `p,S`; the resulting full permutation cannot depend on `ω`. -/
theorem fixed_permutation_dominates (v : ℕ → ℝ) (hv : MarginalUtility v)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (X : Fin N → Ω → ℝ)
    (S : Finset (Fin N)) :
    ∃ τ : Equiv.Perm (Fin N), ∀ ω, RfSet v p X S ω ≤ RsPerm v p X τ ω := by
  classical
  let I := orderedIndices p S
  let T := Sᶜ.sort (· ≤ ·)
  let J := I ++ T
  have hn : J.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨ordered_nodup p S, Sᶜ.sort_nodup (· ≤ ·), ?_⟩
    intro i hi j hj hij
    subst j
    have hiS : i ∈ S := by
      have : i ∈ I.toFinset := List.mem_toFinset.mpr hi
      simpa only [I, ordered_toFinset] using this
    have hiC : i ∈ Sᶜ := by simpa only [T, Finset.mem_sort] using hj
    exact (Finset.mem_compl.mp hiC) hiS
  have hall : ∀ i : Fin N, i ∈ J := by
    intro i
    by_cases hi : i ∈ S
    · apply List.mem_append.mpr
      left
      apply List.mem_toFinset.mp
      simpa only [I, ordered_toFinset] using hi
    · apply List.mem_append.mpr
      right
      simpa only [T, Finset.mem_sort, Finset.mem_compl] using hi
  obtain ⟨τ, hτ⟩ := permutation_of_list J hn hall
  refine ⟨τ, ?_⟩
  intro ω
  let f : Fin N → ℝ × ℝ := fun i => (p i, X i ω)
  have hperm : (I.map f).Perm (products p X S ω) := (ordered_perm p S).map f
  have hdec : (I.map f).Pairwise (fun a b => b.1 ≤ a.1) := by
    apply List.pairwise_map.mpr
    exact (ordered_pairwise p S).imp (fun {_ _} h => before_weight_le p h)
  have hsuffix : ∀ a ∈ T.map f, 0 ≤ a.1 := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨i, _, rfl⟩
    exact hp i
  have hfull : List.ofFn (fun j => (p (τ j), X (τ j) ω)) = I.map f ++ T.map f := by
    change List.ofFn (fun j => f (τ j)) = I.map f ++ T.map f
    rw [List.ofFn_comp' τ f, hτ]
    exact List.map_append
  calc
    RfSet v p X S ω ≤ seqRev v (I.map f) 0 :=
      pathwise_set v hv p hp X S ω (I.map f) hperm hdec
    _ ≤ seqRev v (I.map f ++ T.map f) 0 := append_many v hv _ _ hsuffix
    _ = RsPerm v p X τ ω := by rw [RsPerm, hfull]

theorem rf_nonneg (v : ℕ → ℝ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Fin N → Ω → ℝ) (S : Finset (Fin N)) (ω : Ω) :
    0 ≤ RfSet v p X S ω := by
  classical
  unfold RfSet
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hp i
  · exact le_rfl

/-- Revenue is bounded by the finite sum of prices, independently of all valuation shocks. -/
theorem seq_bounds (v : ℕ → ℝ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Fin N → Ω → ℝ) (ω : Ω) (I : List (Fin N)) (k : ℕ) :
    0 ≤ seqRev v (I.map (fun i => (p i, X i ω))) k ∧
    seqRev v (I.map (fun i => (p i, X i ω))) k ≤ (I.map p).sum := by
  induction I generalizing k with
  | nil => simp [seqRev]
  | cons i I ih =>
    simp only [List.map_cons, List.sum_cons, seqRev]
    split_ifs with h
    · exact ⟨add_nonneg (hp i) (ih (k + 1)).1,
        add_le_add le_rfl (ih (k + 1)).2⟩
    · exact ⟨(ih k).1, (ih k).2.trans (le_add_of_nonneg_left (hp i))⟩

variable [MeasurableSpace Ω]

/-- Measurability only involves fixed lists and scalar purchase tests. -/
theorem measurable_seq (v : ℕ → ℝ) (p : Fin N → ℝ) (X : Fin N → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (I : List (Fin N)) (k : ℕ) :
    Measurable (fun ω => seqRev v (I.map (fun i => (p i, X i ω))) k) := by
  classical
  induction I generalizing k with
  | nil => simpa only [List.map_nil, seqRev] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  | cons i I ih =>
    have hs : MeasurableSet {ω : Ω | 0 ≤ v k + X i ω - p i} :=
      measurableSet_le measurable_const ((measurable_const.add (hXm i)).sub measurable_const)
    change Measurable
      (Set.piecewise {ω : Ω | 0 ≤ v k + X i ω - p i}
        (fun ω => p i + seqRev v (I.map (fun j => (p j, X j ω))) (k + 1))
        (fun ω => seqRev v (I.map (fun j => (p j, X j ω))) k))
    exact (measurable_const.add (ih (k + 1))).piecewise hs (ih k)

theorem integrable_seq (μ : Measure Ω) [IsFiniteMeasure μ]
    (v : ℕ → ℝ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Fin N → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (I : List (Fin N)) (k : ℕ) :
    Integrable (fun ω => seqRev v (I.map (fun i => (p i, X i ω))) k) μ := by
  apply (integrable_const ((I.map p).sum)).mono'
    (measurable_seq v p X hXm I k).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (seq_bounds v p hp X ω I k).1]
  exact (seq_bounds v p hp X ω I k).2

theorem integrable_rsPerm (μ : Measure Ω) [IsFiniteMeasure μ]
    (v : ℕ → ℝ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Fin N → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (τ : Equiv.Perm (Fin N)) :
    Integrable (RsPerm v p X τ) μ := by
  change Integrable (fun ω => seqRev v (List.ofFn fun j => (p (τ j), X (τ j) ω)) 0) μ
  simpa only [List.map_ofFn, Function.comp_def] using
    integrable_seq μ v p hp X hXm (List.ofFn τ) 0

/-- Integrate each fixed strategy's deterministic comparator, then take the finite supremum. -/
theorem expected_domination (μ : Measure Ω) [IsFiniteMeasure μ]
    (v : ℕ → ℝ) (hv : MarginalUtility v)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Fin N → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) :
    ERfStar μ v p X ≤ ERsStar μ v p X := by
  classical
  unfold ERfStar
  apply Finset.sup'_le
  intro S hS
  obtain ⟨τ, hτ⟩ := fixed_permutation_dominates v hv p hp X S
  have hi : (∫ ω, RfSet v p X S ω ∂μ) ≤ ∫ ω, RsPerm v p X τ ω ∂μ :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall (rf_nonneg v p hp X S))
      (integrable_rsPerm μ v p hp X hXm τ)
      (Filter.Eventually.of_forall hτ)
  apply hi.trans
  unfold ERsStar
  exact Finset.le_sup' (fun σ : Equiv.Perm (Fin N) => ∫ ω, RsPerm v p X σ ω ∂μ) (Finset.mem_univ τ)

end
end AssortRotation.Concealment.RootBridge

open AssortRotation.Concealment AssortRotation.Concealment.RootBridge

/-- Exact root target. The unused shock hypotheses are preserved verbatim. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (v : ℕ → ℝ) (hv : MarginalUtility v) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (X : Fin N → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hXi : ∀ i, Integrable (X i) μ)
    (hind : iIndepFun X μ) (hcont : ∀ i, NullSingletonClass (μ.map (X i))) :
    (∀ S : Finset (Fin N), (∫ ω, RfSet v p X S ω ∂μ = ERfStar μ v p X) →
      ∀ ω : Ω, ∀ L : List (ℝ × ℝ), L.Perm (products p X S ω) →
        L.Pairwise (fun a b => b.1 ≤ a.1) → RfSet v p X S ω ≤ seqRev v L 0) ∧
    ERfStar μ v p X ≤ ERsStar μ v p X := by
  refine ⟨?_, expected_domination μ v hv p hp X hXm⟩
  intro S hS ω L hL hdec
  exact pathwise_set v hv p hp X S ω L hL hdec

#print axioms solution
