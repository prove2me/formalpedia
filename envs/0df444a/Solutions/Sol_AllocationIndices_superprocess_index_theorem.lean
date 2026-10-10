-- Prove2me | solution 1 for AllocationIndices.superprocess_index_theorem
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T00:03:53.333658+00:00
-- url     : https://prove2.me/submissions/fe211b5b-b2a0-4c3e-b09e-9ae17969cf9b

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of the canonical Condition-D superprocess index theorem.
All custom proof bodies are included; only canonical definitions and Mathlib
are imported. Retirement and finite-mixture arguments are independently reconstructed.
-/
import Mathlib
import Definitions.Def_AllocationIndices_Superprocess
import Definitions.Def_GittinsIndex

/- Complete module: FiniteStopLoss -/
section

open scoped BigOperators

namespace AllocationIndices.Proof

lemma sum_slope_masses (d : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (d (k + 1) - d k)) = d N - d 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

lemma sum_slope_mass_mul (d v : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (d (k + 1) - d k) * v k) =
      d (N + 1) * v N - d 0 * v 0 -
        ∑ k ∈ Finset.range N, d (k + 1) * (v (k + 1) - v k) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

lemma finite_stopLoss_representation (d t : ℕ → ℝ) (N : ℕ)
    (hd0 : d 0 = 0) (hdN : d (N + 1) = 1) (m : ℝ) :
    (∑ k ∈ Finset.range (N + 1), (d (k + 1) - d k) * max (t k) m) =
      max (t N) m -
        ∑ k ∈ Finset.range N, d (k + 1) * (max (t (k + 1)) m - max (t k) m) := by
  rw [sum_slope_mass_mul, hd0, hdN]
  ring

lemma finite_slope_probability (d : ℕ → ℝ) (N : ℕ)
    (hd0 : d 0 = 0) (hdN : d (N + 1) = 1)
    (hmono : ∀ k ≤ N, d k ≤ d (k + 1)) :
    (∀ k ∈ Finset.range (N + 1), 0 ≤ d (k + 1) - d k) ∧
      (∑ k ∈ Finset.range (N + 1), (d (k + 1) - d k)) = 1 := by
  constructor
  · intro k hk
    exact sub_nonneg.mpr (hmono k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  · rw [sum_slope_masses, hd0, hdN]
    norm_num

lemma finite_stopLoss_at_node (d t f : ℕ → ℝ) (N j : ℕ)
    (hd0 : d 0 = 0) (hdN : d (N + 1) = 1) (hfN : f N = t N)
    (ht : Monotone t) (hj : j ≤ N)
    (hslope : ∀ k < N, d (k + 1) * (t (k + 1) - t k) = f (k + 1) - f k) :
    (∑ k ∈ Finset.range (N + 1), (d (k + 1) - d k) * max (t k) (t j)) = f j := by
  rw [finite_stopLoss_representation d t N hd0 hdN, max_eq_left (ht hj)]
  have hsum : (∑ k ∈ Finset.range N,
      d (k + 1) * (max (t (k + 1)) (t j) - max (t k) (t j))) = f N - f j := by
    rw [← Finset.sum_range_add_sum_Ico _ hj]
    have hz : (∑ k ∈ Finset.range j,
        d (k + 1) * (max (t (k + 1)) (t j) - max (t k) (t j))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkj : k < j := Finset.mem_range.mp hk
      rw [max_eq_right (ht (by omega)), max_eq_right (ht (by omega))]
      ring
    rw [hz, zero_add]
    calc
      _ = ∑ k ∈ Finset.Ico j N, (f (k + 1) - f k) := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hjk, hkN⟩ := Finset.mem_Ico.mp hk
        rw [max_eq_left (ht (by omega)), max_eq_left (ht hjk)]
        exact hslope k hkN
      _ = f N - f j := by
        rw [Finset.sum_Ico_eq_sub _ hj, sum_slope_masses, sum_slope_masses]
        ring
  rw [hsum, hfN]
  ring

lemma finite_stopLoss_monotone {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    Monotone (fun m : ℝ => ∑ k ∈ s, w k * max (t k) m) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (max_le_max_left _ hab) (hw k hk)

lemma finite_stopLoss_abs_sub_le {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hs : ∑ k ∈ s, w k = 1) (a b : ℝ) :
    |(∑ k ∈ s, w k * max (t k) a) - (∑ k ∈ s, w k * max (t k) b)| ≤ |a - b| := by
  calc
    _ = |∑ k ∈ s, w k * (max (t k) a - max (t k) b)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ s, |w k * (max (t k) a - max (t k) b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, w k * |a - b| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (hw k hk)]
      apply mul_le_mul_of_nonneg_left _ (hw k hk)
      simpa only [max_comm] using abs_max_sub_max_le_abs a b (t k)
    _ = |a - b| := by rw [← Finset.sum_mul, hs, one_mul]

lemma monotone_grid_approximation (v f : ℝ → ℝ) (hv : Monotone v)
    (hf : Monotone f) (hLip : ∀ a b, |f a - f b| ≤ |a - b|)
    {l m u h : ℝ} (hlm : l ≤ m) (hmu : m ≤ u) (hmesh : u - l ≤ h)
    (hl : v l = f l) (hu : v u = f u) : |v m - f m| ≤ h := by
  have hvl := hv hlm
  have hvu := hv hmu
  have hfl := hf hlm
  have hfu := hf hmu
  rw [hl] at hvl
  rw [hu] at hvu
  have hspan := hLip u l
  rw [abs_of_nonneg (sub_nonneg.mpr (hf (hlm.trans hmu))),
    abs_of_nonneg (sub_nonneg.mpr (hlm.trans hmu))] at hspan
  rw [abs_le]
  constructor <;> linarith

end AllocationIndices.Proof

end

/- Complete module: RetirementMesh -/
section

open scoped BigOperators

namespace AllocationIndices.Proof

noncomputable def meshNode (L h : ℝ) (k : ℕ) : ℝ := L + k * h
noncomputable def meshSlope (f : ℝ → ℝ) (L h : ℝ) (k : ℕ) : ℝ :=
  (f (meshNode L h (k + 1)) - f (meshNode L h k)) / h

lemma meshNode_step (L h : ℝ) (k : ℕ) :
    meshNode L h (k + 1) - meshNode L h k = h := by
  simp only [meshNode, Nat.cast_add, Nat.cast_one]
  ring

lemma meshNode_strictMono (L : ℝ) {h : ℝ} (hh : 0 < h) :
    StrictMono (meshNode L h) := by
  intro i j hij
  change L + (i : ℝ) * h < L + (j : ℝ) * h
  linarith [mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij : (i : ℝ) < j) hh]

lemma meshSlope_nonneg_le_one (f : ℝ → ℝ) (L : ℝ) {h : ℝ} (hh : 0 < h)
    (hf : Monotone f) (hLip : ∀ a b, |f a - f b| ≤ |a - b|) (k : ℕ) :
    0 ≤ meshSlope f L h k ∧ meshSlope f L h k ≤ 1 := by
  have hstep : meshNode L h k ≤ meshNode L h (k + 1) :=
    (meshNode_strictMono L hh (Nat.lt_succ_self k)).le
  have hnonneg : 0 ≤ f (meshNode L h (k + 1)) - f (meshNode L h k) :=
    sub_nonneg.mpr (hf hstep)
  have hbound := hLip (meshNode L h (k + 1)) (meshNode L h k)
  rw [abs_of_nonneg hnonneg, meshNode_step, abs_of_pos hh] at hbound
  constructor
  · exact div_nonneg hnonneg hh.le
  · exact (div_le_one hh).mpr hbound

lemma meshSlope_mono (f : ℝ → ℝ) (L : ℝ) {h : ℝ} (hh : 0 < h)
    (hf : ConvexOn ℝ Set.univ f) : Monotone (meshSlope f L h) := by
  apply monotone_nat_of_le_succ
  intro k
  have hmono := meshNode_strictMono L hh
  have hs := hf.slope_mono_adjacent (Set.mem_univ (meshNode L h k))
    (Set.mem_univ (meshNode L h (k + 1 + 1)))
    (hmono (Nat.lt_succ_self k)) (hmono (Nat.lt_succ_self (k + 1)))
  simpa only [meshNode_step, meshSlope] using hs

lemma meshSlope_step (f : ℝ → ℝ) (L : ℝ) {h : ℝ} (hh : 0 < h) (k : ℕ) :
    meshSlope f L h k * (meshNode L h (k + 1) - meshNode L h k) =
      f (meshNode L h (k + 1)) - f (meshNode L h k) := by
  rw [meshNode_step, meshSlope, div_mul_cancel₀ _ hh.ne']

noncomputable def cumulativeMeshSlope (f : ℝ → ℝ) (L h : ℝ) (N k : ℕ) : ℝ :=
  if k = 0 then 0 else if k ≤ N then meshSlope f L h (k - 1) else 1

@[simp] lemma cumulativeMeshSlope_zero (f : ℝ → ℝ) (L h : ℝ) (N : ℕ) :
    cumulativeMeshSlope f L h N 0 = 0 := by simp [cumulativeMeshSlope]

@[simp] lemma cumulativeMeshSlope_last (f : ℝ → ℝ) (L h : ℝ) (N : ℕ) :
    cumulativeMeshSlope f L h N (N + 1) = 1 := by simp [cumulativeMeshSlope]

lemma cumulativeMeshSlope_succ (f : ℝ → ℝ) (L h : ℝ) {N k : ℕ} (hk : k < N) :
    cumulativeMeshSlope f L h N (k + 1) = meshSlope f L h k := by
  simp [cumulativeMeshSlope, Nat.succ_le_iff.mpr hk]

lemma cumulativeMeshSlope_adjacent (f : ℝ → ℝ) (L : ℝ) {h : ℝ} (hh : 0 < h)
    (hf : Monotone f) (hLip : ∀ a b, |f a - f b| ≤ |a - b|)
    (hconv : ConvexOn ℝ Set.univ f) (N k : ℕ) (hk : k ≤ N) :
    cumulativeMeshSlope f L h N k ≤ cumulativeMeshSlope f L h N (k + 1) := by
  by_cases hk0 : k = 0
  · subst k
    by_cases hN : N = 0
    · subst N
      simp
    · rw [cumulativeMeshSlope_zero, cumulativeMeshSlope_succ f L h (by omega)]
      exact (meshSlope_nonneg_le_one f L hh hf hLip 0).1
  · by_cases hkN : k = N
    · subst k
      rw [cumulativeMeshSlope_last]
      simp only [cumulativeMeshSlope, hk0, ↓reduceIte, le_refl]
      exact (meshSlope_nonneg_le_one f L hh hf hLip (N - 1)).2
    · rw [cumulativeMeshSlope_succ f L h (by omega)]
      simp only [cumulativeMeshSlope, hk0, ↓reduceIte, hk]
      exact meshSlope_mono f L hh hconv (by omega)

lemma mesh_probability_and_nodes (f : ℝ → ℝ) (L : ℝ) {h : ℝ} (hh : 0 < h)
    (hf : Monotone f) (hLip : ∀ a b, |f a - f b| ≤ |a - b|)
    (hconv : ConvexOn ℝ Set.univ f) (N : ℕ) (hfN : f (meshNode L h N) = meshNode L h N) :
    let d := cumulativeMeshSlope f L h N
    (∀ k ∈ Finset.range (N + 1), 0 ≤ d (k + 1) - d k) ∧
    (∑ k ∈ Finset.range (N + 1), (d (k + 1) - d k)) = 1 ∧
    (∀ j ≤ N, (∑ k ∈ Finset.range (N + 1),
      (d (k + 1) - d k) * max (meshNode L h k) (meshNode L h j)) = f (meshNode L h j)) := by
  dsimp only
  obtain ⟨hp, hs⟩ := finite_slope_probability (cumulativeMeshSlope f L h N) N
    (cumulativeMeshSlope_zero ..) (cumulativeMeshSlope_last ..)
    (cumulativeMeshSlope_adjacent f L hh hf hLip hconv N)
  refine ⟨hp, hs, ?_⟩
  intro j hj
  apply finite_stopLoss_at_node _ _ (fun k => f (meshNode L h k)) N j
    (cumulativeMeshSlope_zero ..) (cumulativeMeshSlope_last ..) hfN
    (meshNode_strictMono L hh).monotone hj
  intro k hk
  rw [cumulativeMeshSlope_succ f L h hk]
  exact meshSlope_step f L hh k

lemma exists_mesh_interval (L h m : ℝ) (N : ℕ) (hN : 0 < N)
    (hl : meshNode L h 0 ≤ m) (hu : m ≤ meshNode L h N) :
    ∃ j < N, meshNode L h j ≤ m ∧ m ≤ meshNode L h (j + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, hl, hu⟩
    · by_cases hm : m ≤ meshNode L h N
      · obtain ⟨j, hj, hjl, hju⟩ := ih (by omega) hm
        exact ⟨j, by omega, hjl, hju⟩
      · exact ⟨N, by omega, (lt_of_not_ge hm).le, hu⟩

lemma mesh_stopLoss_approximation (f : ℝ → ℝ) (L : ℝ) {h : ℝ} (hh : 0 < h)
    (hf : Monotone f) (hLip : ∀ a b, |f a - f b| ≤ |a - b|)
    (hconv : ConvexOn ℝ Set.univ f) (N : ℕ) (hN : 0 < N)
    (hfN : f (meshNode L h N) = meshNode L h N) (m : ℝ)
    (hl : meshNode L h 0 ≤ m) (hu : m ≤ meshNode L h N) :
    let d := cumulativeMeshSlope f L h N
    |(∑ k ∈ Finset.range (N + 1), (d (k + 1) - d k) * max (meshNode L h k) m) - f m| ≤ h := by
  dsimp only
  obtain ⟨hw, _, hnodes⟩ := mesh_probability_and_nodes f L hh hf hLip hconv N hfN
  obtain ⟨j, hj, hjl, hju⟩ := exists_mesh_interval L h m N hN hl hu
  apply monotone_grid_approximation _ f
    (finite_stopLoss_monotone _ _ _ hw) hf hLip hjl hju
    (le_of_eq (meshNode_step L h j)) (hnodes j (by omega)) (hnodes (j + 1) (by omega))

lemma meshSlope_eq_one_above (f : ℝ → ℝ) (L c : ℝ) {h : ℝ} (hh : 0 < h)
    (hid : ∀ m, c ≤ m → f m = m) (k : ℕ) (hc : c ≤ meshNode L h k) :
    meshSlope f L h k = 1 := by
  unfold meshSlope
  rw [hid _ (hc.trans ((meshNode_strictMono L hh (Nat.lt_succ_self k)).le)),
    hid _ hc, meshNode_step, div_self hh.ne']

lemma mesh_mass_eq_zero_above (f : ℝ → ℝ) (L c : ℝ) {h : ℝ} (hh : 0 < h)
    (hid : ∀ m, c ≤ m → f m = m) (hLc : L ≤ c) (N k : ℕ) (hk : k ≤ N)
    (habove : c + h < meshNode L h k) :
    cumulativeMeshSlope f L h N (k + 1) - cumulativeMeshSlope f L h N k = 0 := by
  cases k with
  | zero => simp only [meshNode, Nat.cast_zero, zero_mul, add_zero] at habove; linarith
  | succ j =>
    have hprev : c ≤ meshNode L h j := by
      have hstep := meshNode_step L h j
      change c + h < meshNode L h (j + 1) at habove
      linarith
    have hcur : c ≤ meshNode L h (j + 1) :=
      hprev.trans (meshNode_strictMono L hh (Nat.lt_succ_self j)).le
    rw [cumulativeMeshSlope_succ f L h (k := j) (by omega), meshSlope_eq_one_above f L c hh hid j hprev]
    by_cases hj : j + 1 < N
    · rw [cumulativeMeshSlope_succ f L h hj,
        meshSlope_eq_one_above f L c hh hid (j + 1) hcur]
      ring
    · have heq : j + 1 = N := by omega
      rw [show j + 1 + 1 = N + 1 by omega, cumulativeMeshSlope_last]
      ring

end AllocationIndices.Proof

end

/- Complete module: FiniteProductExpectation -/
section

open scoped BigOperators

namespace AllocationIndices.Proof

lemma finite_product_weights_sum {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (w : I → K → ℝ) (hw : ∀ i, ∑ k, w i k = 1) :
    (∑ z : I → K, ∏ i, w i (z i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [hw, Finset.prod_const_one]

lemma finite_product_weights_nonneg {I K : Type*} [Fintype I] (w : I → K → ℝ)
    (hw : ∀ i k, 0 ≤ w i k) (z : I → K) : 0 ≤ ∏ i, w i (z i) := by
  exact Finset.prod_nonneg fun i _ => hw i (z i)

lemma prod_split_at {I : Type*} [Fintype I] [DecidableEq I] (i : I) (f : I → ℝ) :
    (∏ j, f j) = f i * ∏ j : {j // j ≠ i}, f j := by
  let : Fintype {j : I // j = i} := Subtype.fintype (fun j => j = i)
  have hs := Fintype.prod_subtype_mul_prod_subtype (fun j => j = i) f
  have hsingle : (∏ j : {j // j = i}, f j) = f i := by
    rw [Fintype.prod_subsingleton _ ⟨i, rfl⟩]
  change (∏ j : {j : I // j = i}, f j) * (∏ j : {j : I // j ≠ i}, f j) = ∏ j, f j at hs
  rw [hsingle] at hs
  exact hs.symm

lemma finite_weighted_sum_split {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (i : I) (w : I → K → ℝ) (F : (I → K) → ℝ) :
    (∑ z : I → K, (∏ j, w j (z j)) * F z) =
      ∑ z : {j // j ≠ i} → K, (∏ j : {j // j ≠ i}, w j (z j)) *
        ∑ k, w i k * F ((Equiv.funSplitAt i K).symm (k, z)) := by
  rw [← (Equiv.funSplitAt i K).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [prod_split_at i]
  have hi : ((Equiv.funSplitAt i K).symm (k,z)) i = k := by simp
  have hj : ∀ j : {j // j ≠ i}, ((Equiv.funSplitAt i K).symm (k,z)) j = z j := by
    intro j
    simp [Equiv.funSplitAt, Equiv.piSplitAt, j.property]
  simp only [hi, hj]
  ring

end AllocationIndices.Proof

end

/- Complete module: FiniteMaximum -/
section

open scoped BigOperators

namespace AllocationIndices.Proof

noncomputable def finiteMaximum {I : Type*} [Fintype I] (L : ℝ) (f : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Option I => i.elim L f)

lemma le_finiteMaximum_base {I : Type*} [Fintype I] (L : ℝ) (f : I → ℝ) :
    L ≤ finiteMaximum L f := by
  exact Finset.le_sup' (fun i : Option I => i.elim L f) (Finset.mem_univ none)

lemma le_finiteMaximum {I : Type*} [Fintype I] (L : ℝ) (f : I → ℝ) (i : I) :
    f i ≤ finiteMaximum L f := by
  exact Finset.le_sup' (fun i : Option I => i.elim L f) (Finset.mem_univ (some i))

lemma finiteMaximum_le {I : Type*} [Fintype I] (L : ℝ) (f : I → ℝ) {c : ℝ}
    (hL : L ≤ c) (hf : ∀ i, f i ≤ c) : finiteMaximum L f ≤ c := by
  apply Finset.sup'_le
  intro i _
  cases i with
  | none => exact hL
  | some i => exact hf i

lemma finiteMaximum_split {I : Type*} [Fintype I] [DecidableEq I]
    (L : ℝ) (f : I → ℝ) (i : I) :
    finiteMaximum L f = max (f i) (finiteMaximum L (fun j : {j // j ≠ i} => f j)) := by
  apply le_antisymm
  · apply finiteMaximum_le
    · exact (le_finiteMaximum_base L _).trans (le_max_right _ _)
    · intro j
      by_cases hj : j = i
      · subst j
        exact le_max_left _ _
      · exact (le_finiteMaximum L (fun j : {j // j ≠ i} => f j) ⟨j,hj⟩).trans (le_max_right _ _)
  · apply max_le
    · exact le_finiteMaximum L f i
    · exact finiteMaximum_le L _ (le_finiteMaximum_base L f) (fun j => le_finiteMaximum L f j)

end AllocationIndices.Proof

end

/- Complete module: FiniteWhittleValue -/
section

open scoped BigOperators

namespace AllocationIndices.Proof

noncomputable def finiteWhittleValue {I K S : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (w : S → K → ℝ) (t : K → ℝ) (L : ℝ) (x : I → S) : ℝ :=
  ∑ z : I → K, (∏ j, w (x j) (z j)) * finiteMaximum L (fun j => t (z j))

lemma finiteWhittleValue_split {I K S : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (w : S → K → ℝ) (t : K → ℝ) (L : ℝ) (x : I → S) (i : I) :
    finiteWhittleValue w t L x =
      ∑ z : {j // j ≠ i} → K, (∏ j : {j // j ≠ i}, w (x j) (z j)) *
        ∑ k, w (x i) k * max (t k) (finiteMaximum L (fun j => t (z j))) := by
  unfold finiteWhittleValue
  rw [finite_weighted_sum_split i]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [finiteMaximum_split L _ i]
  congr 1
  · simp
  · congr 1
    funext j
    simp [Equiv.funSplitAt, Equiv.piSplitAt, j.property]

lemma finiteWhittleValue_update_split {I K S : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (w : S → K → ℝ) (t : K → ℝ) (L : ℝ) (x : I → S) (i : I) (y : S) :
    finiteWhittleValue w t L (Function.update x i y) =
      ∑ z : {j // j ≠ i} → K, (∏ j : {j // j ≠ i}, w (x j) (z j)) *
        ∑ k, w y k * max (t k) (finiteMaximum L (fun j => t (z j))) := by
  rw [finiteWhittleValue_split w t L _ i]
  simp only [Function.update_self]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [Function.update_of_ne j.property]

lemma finiteWhittleValue_bounds {I K S : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (w : S → K → ℝ) (t : K → ℝ) (L U : ℝ) (hLU : L ≤ U)
    (hw : ∀ x k, 0 ≤ w x k) (hs : ∀ x, ∑ k, w x k = 1)
    (ht : ∀ k, t k ≤ U) (x : I → S) :
    L ≤ finiteWhittleValue w t L x ∧ finiteWhittleValue w t L x ≤ U := by
  have hsum := finite_product_weights_sum (fun i k => w (x i) k) (fun i => hs (x i))
  have hpos := finite_product_weights_nonneg (fun i k => w (x i) k) (fun i k => hw (x i) k)
  constructor
  · calc
      L = ∑ z : I → K, (∏ j, w (x j) (z j)) * L := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ finiteWhittleValue w t L x := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (le_finiteMaximum_base L _) (hpos z)
  · calc
      finiteWhittleValue w t L x ≤ ∑ z : I → K, (∏ j, w (x j) (z j)) * U := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (finiteMaximum_le L _ hLU (fun j => ht (z j))) (hpos z)
      _ = U := by rw [← Finset.sum_mul, hsum, one_mul]

end AllocationIndices.Proof

end

/- Complete module: SFASIntegrals -/
section

open MeasureTheory ProbabilityTheory

namespace AllocationIndices.Proof

variable {S U : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] [MeasurableSpace U] [Countable U]
  [MeasurableSingletonClass U] {n : ℕ}

lemma integrable_bounded_countable {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) : Integrable f μ := by
  exact Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf x)

def appendHistory {t : ℕ} (h : SFASHistory n S U t) (c : Fin n × U) (y : S) :
    SFASHistory n S U (t + 1) :=
  (Fin.snoc h.1 (h.2, c), Function.update h.2 c.1 y)

def actionStateKernel (D : DecisionProcess S U) (t : ℕ) :
    Kernel (SFASHistory n S U t × (Fin n × U)) S :=
  Kernel.mk (fun p => D.step p.2.2 (p.1.2 p.2.1)) (measurable_of_countable _)

instance actionStateKernel_markov (D : DecisionProcess S U) (t : ℕ) :
    IsMarkovKernel (actionStateKernel (n := n) D t) :=
  ⟨fun p => (D.markov p.2.2).isProbabilityMeasure _⟩

lemma sfas_integral_succ (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (x : Fin n → S) (t : ℕ) (f : SFASHistory n S U (t + 1) → ℝ)
    (C : ℝ) (hf : ∀ h, |f h| ≤ C) :
    (∫ h, f h ∂sfasMeasure D π x (t + 1)) =
      ∫ h, ∫ c, ∫ y, f (appendHistory h c y) ∂D.step c.2 (h.2 c.1)
        ∂π.select t h ∂sfasMeasure D π x t := by
  rw [sfasMeasure, integral_map_of_stronglyMeasurable measurable_sfasSnoc
    (measurable_of_countable f).stronglyMeasurable]
  change (∫ p, f (appendHistory p.1 p.2.1 p.2.2)
    ∂(sfasMeasure D π x t).compProd (sfasStepKernel D π t)) = _
  rw [Measure.integral_compProd (integrable_bounded_countable
    ((sfasMeasure D π x t).compProd (sfasStepKernel D π t))
    (fun p => f (appendHistory p.1 p.2.1 p.2.2)) C
    (fun p => hf (appendHistory p.1 p.2.1 p.2.2)))]
  apply integral_congr_ae
  filter_upwards [] with h
  change (∫ p, f (appendHistory h p.1 p.2)
    ∂((π.select t).compProd (actionStateKernel D t)) h) = _
  rw [ProbabilityTheory.integral_compProd
    (integrable_bounded_countable (((π.select t).compProd (actionStateKernel D t)) h)
      (fun p => f (appendHistory h p.1 p.2)) C
      (fun p => hf (appendHistory h p.1 p.2)))]
  rfl

end AllocationIndices.Proof

end

/- Complete module: SFASVerification -/
section

open MeasureTheory ProbabilityTheory

namespace AllocationIndices.Proof

noncomputable section

variable {S U : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] [MeasurableSpace U] [Countable U]
  [MeasurableSingletonClass U] {n : ℕ}

lemma abs_integral_bounded {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  simpa [Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hf x)

def stateExpectation (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (V : (Fin n → S) → ℝ) (x : Fin n → S) (t : ℕ) : ℝ :=
  ∫ h, V h.2 ∂sfasMeasure D π x t

def actionValue (D : DecisionProcess S U) (a : ℝ) (V : (Fin n → S) → ℝ)
    (x : Fin n → S) (c : Fin n × U) : ℝ :=
  D.reward (x c.1) c.2 + a * ∫ y, V (Function.update x c.1 y) ∂D.step c.2 (x c.1)

omit [Countable S] [MeasurableSingletonClass S] [MeasurableSpace U]
  [Countable U] [MeasurableSingletonClass U] in
lemma actionValue_bound (D : DecisionProcess S U) (a : ℝ) (V : (Fin n → S) → ℝ)
    (R C : ℝ) (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (x : Fin n → S) (c : Fin n × U) : |actionValue D a V x c| ≤ R + |a| * C := by
  apply (abs_add_le _ _).trans
  exact add_le_add (hr _ _) (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_integral_bounded _ _ C (fun y => hV _)) (abs_nonneg a))

omit [Countable S] in
lemma stateExpectation_zero (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (V : (Fin n → S) → ℝ) (x : Fin n → S) : stateExpectation D π V x 0 = V x := by
  simp [stateExpectation, sfasMeasure]

lemma stateExpectation_bound (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (V : (Fin n → S) → ℝ) (C : ℝ) (hV : ∀ x, |V x| ≤ C)
    (x : Fin n → S) (t : ℕ) : |stateExpectation D π V x t| ≤ C :=
  abs_integral_bounded _ _ C (fun h => hV h.2)

lemma roundReward_bound (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (R : ℝ) (hr : ∀ x u, |D.reward x u| ≤ R) (x : Fin n → S) (t : ℕ) :
    |sfasRoundReward D π x t| ≤ R :=
  abs_integral_bounded _ _ R (fun _ => hr _ _)

lemma reward_potential_step (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (a : ℝ) (V : (Fin n → S) → ℝ) (R C : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (x : Fin n → S) (t : ℕ) :
    sfasRoundReward D π x t + a * stateExpectation D π V x (t + 1) =
      ∫ h, ∫ c, actionValue D a V h.2 c ∂π.select t h ∂sfasMeasure D π x t := by
  let f : SFASHistory n S U (t + 1) → ℝ := fun h =>
    D.reward ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2.1)) ((h.1 (Fin.last t)).2.2)
  have hf : ∀ h, |f h| ≤ R := fun _ => hr _ _
  have hv : ∀ h : SFASHistory n S U (t + 1), |V h.2| ≤ C := fun h => hV h.2
  have hb : ∀ h, |f h + a * V h.2| ≤ R + |a| * C := by
    intro h
    exact (abs_add_le _ _).trans (add_le_add (hf h) (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv h) (abs_nonneg a)))
  change (∫ h, f h ∂sfasMeasure D π x (t + 1)) +
    a * (∫ h, V h.2 ∂sfasMeasure D π x (t + 1)) = _
  rw [← integral_const_mul, ← integral_add
    (integrable_bounded_countable _ f R hf)
    ((integrable_bounded_countable _ _ C hv).const_mul a)]
  rw [sfas_integral_succ D π x t _ _ hb]
  apply integral_congr_ae
  filter_upwards [] with h
  apply integral_congr_ae
  filter_upwards [] with c
  simp only [f, appendHistory, Fin.snoc_last]
  rw [integral_add (integrable_const _)
    ((integrable_bounded_countable _ _ C (fun y => hV _)).const_mul a),
    integral_const_mul]
  simp [actionValue]


omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U] in
lemma summable_discounted_bounded (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (f : ℕ → ℝ) (C : ℝ) (hf : ∀ t, |f t| ≤ C) :
    Summable (fun t => a ^ t * f t) := by
  apply ((summable_geometric_of_lt_one ha ha1).mul_right C).of_norm_bounded
  intro t
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha t)] using
    mul_le_mul_of_nonneg_left (hf t) (pow_nonneg ha t)

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U] in
lemma discounted_sequence_upper (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (r v : ℕ → ℝ) (R C ε : ℝ)
    (hr : ∀ t, |r t| ≤ R) (hv : ∀ t, |v t| ≤ C)
    (hstep : ∀ t, r t + a * v (t + 1) ≤ v t + ε) :
    (∑' t, a ^ t * r t) ≤ v 0 + ε / (1 - a) := by
  have sr := summable_discounted_bounded a ha ha1 r R hr
  have sv := summable_discounted_bounded a ha ha1 v C hv
  have sn : Summable (fun t => a ^ (t + 1) * v (t + 1)) :=
    (summable_nat_add_iff 1).2 sv
  have se := (summable_geometric_of_lt_one ha ha1).mul_right ε
  have hsum := Summable.tsum_le_tsum (fun t => show
      a ^ t * r t + a ^ (t + 1) * v (t + 1) ≤ a ^ t * v t + a ^ t * ε by
    have h := mul_le_mul_of_nonneg_left (hstep t) (pow_nonneg ha t)
    simpa only [mul_add, pow_succ, mul_assoc] using h) (sr.add sn) (sv.add se)
  rw [sr.tsum_add sn, sv.tsum_add se, tsum_mul_right,
    tsum_geometric_of_lt_one ha ha1] at hsum
  have hv0 := sv.tsum_eq_zero_add
  simp only [pow_zero, one_mul] at hv0
  rw [div_eq_mul_inv]
  nlinarith

lemma policy_step_upper (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (a : ℝ) (V : (Fin n → S) → ℝ) (R C ε : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hb : ∀ t (h : SFASHistory n S U t),
      ∀ᵐ c ∂π.select t h, actionValue D a V h.2 c ≤ V h.2 + ε)
    (x : Fin n → S) (t : ℕ) :
    sfasRoundReward D π x t + a * stateExpectation D π V x (t + 1) ≤
      stateExpectation D π V x t + ε := by
  rw [reward_potential_step D π a V R C hr hV]
  have hi : ∀ h : SFASHistory n S U t,
      Integrable (fun c => actionValue D a V h.2 c) (π.select t h) := fun h =>
    integrable_bounded_countable _ _ _ (actionValue_bound D a V R C hr hV h.2)
  have hbnd : ∀ h : SFASHistory n S U t,
      |∫ c, actionValue D a V h.2 c ∂π.select t h| ≤ R + |a| * C := fun h =>
    abs_integral_bounded _ _ _ (actionValue_bound D a V R C hr hV h.2)
  have hle : (∫ h, ∫ c, actionValue D a V h.2 c ∂π.select t h
      ∂sfasMeasure D π x t) ≤ ∫ h, V h.2 + ε ∂sfasMeasure D π x t := by
    apply integral_mono_ae (integrable_bounded_countable _ _ _ hbnd)
      ((integrable_bounded_countable _ _ C (fun h => hV h.2)).add (integrable_const ε))
    filter_upwards [] with h
    simpa using integral_mono_ae (hi h) (integrable_const (V h.2 + ε)) (hb t h)
  simpa [integral_add (integrable_bounded_countable _ _ C (fun h : SFASHistory n S U t => hV h.2))
    (integrable_const ε), stateExpectation] using hle

lemma policy_value_upper (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C ε : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hb : ∀ t (h : SFASHistory n S U t),
      ∀ᵐ c ∂π.select t h, actionValue D a V h.2 c ≤ V h.2 + ε)
    (x : Fin n → S) : sfasValue D a π x ≤ V x + ε / (1 - a) := by
  have h := discounted_sequence_upper a ha ha1 (sfasRoundReward D π x)
    (stateExpectation D π V x) R C ε (roundReward_bound D π R hr x)
    (stateExpectation_bound D π V C hV x) (policy_step_upper D π a V R C ε hr hV hb x)
  simpa [sfasValue, stateExpectation_zero] using h

lemma feasible_policy_value_upper (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (hπ : IsFeasiblePolicy D π) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (V : (Fin n → S) → ℝ) (R C ε : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hb : ∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x + ε)
    (x : Fin n → S) : sfasValue D a π x ≤ V x + ε / (1 - a) := by
  apply policy_value_upper D π a ha ha1 V R C ε hr hV _ x
  intro t h
  have hc : ∀ᵐ c ∂π.select t h, c.2 ∈ D.avail (h.2 c.1) := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (Set.Countable.measurableSet (Set.to_countable _))).2 (hπ t h)
  filter_upwards [hc] with c hc
  exact hb h.2 c hc


lemma policy_step_lower (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (a : ℝ) (V : (Fin n → S) → ℝ) (R C ε : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hb : ∀ t (h : SFASHistory n S U t),
      ∀ᵐ c ∂π.select t h, V h.2 - ε ≤ actionValue D a V h.2 c)
    (x : Fin n → S) (t : ℕ) :
    stateExpectation D π V x t - ε ≤
      sfasRoundReward D π x t + a * stateExpectation D π V x (t + 1) := by
  rw [reward_potential_step D π a V R C hr hV]
  have hi : ∀ h : SFASHistory n S U t,
      Integrable (fun c => actionValue D a V h.2 c) (π.select t h) := fun h =>
    integrable_bounded_countable _ _ _ (actionValue_bound D a V R C hr hV h.2)
  have hbnd : ∀ h : SFASHistory n S U t,
      |∫ c, actionValue D a V h.2 c ∂π.select t h| ≤ R + |a| * C := fun h =>
    abs_integral_bounded _ _ _ (actionValue_bound D a V R C hr hV h.2)
  have hle : (∫ h, V h.2 - ε ∂sfasMeasure D π x t) ≤
      ∫ h, ∫ c, actionValue D a V h.2 c ∂π.select t h ∂sfasMeasure D π x t := by
    apply integral_mono_ae
      ((integrable_bounded_countable _ _ C (fun h => hV h.2)).sub (integrable_const ε))
      (integrable_bounded_countable _ _ _ hbnd)
    filter_upwards [] with h
    simpa using integral_mono_ae (integrable_const (V h.2 - ε)) (hi h) (hb t h)
  simpa [integral_sub (integrable_bounded_countable _ _ C
    (fun h : SFASHistory n S U t => hV h.2)) (integrable_const ε), stateExpectation] using hle

lemma policy_value_lower (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C ε : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hb : ∀ t (h : SFASHistory n S U t),
      ∀ᵐ c ∂π.select t h, V h.2 - ε ≤ actionValue D a V h.2 c)
    (x : Fin n → S) : V x - ε / (1 - a) ≤ sfasValue D a π x := by
  have h := discounted_sequence_upper a ha ha1 (fun t => -sfasRoundReward D π x t)
    (fun t => -stateExpectation D π V x t) R C ε
    (fun t => by simpa using roundReward_bound D π R hr x t)
    (fun t => by simpa using stateExpectation_bound D π V C hV x t)
    (fun t => by have h := policy_step_lower D π a V R C ε hr hV hb x t; linarith)
  simp only [mul_neg, tsum_neg, stateExpectation_zero] at h
  change V x - ε / (1 - a) ≤ ∑' t, a ^ t * sfasRoundReward D π x t
  linarith

end
end AllocationIndices.Proof

end

/- Complete module: FiniteWhittleBellman -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U K : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [Fintype K] {n : ℕ}

def finiteStopLoss (w : S → K → ℝ) (t : K → ℝ) (x : S) (m : ℝ) : ℝ :=
  ∑ k, w x k * max (t k) m

lemma finiteWhittle_action_identity (D : DecisionProcess S U) (a L H C : ℝ)
    (w : S → K → ℝ) (t : K → ℝ) (hLU : L ≤ H)
    (hs : ∀ x, ∑ k, w x k = 1) (ht : ∀ k, t k ≤ H)
    (hb : ∀ y m, L ≤ m → m ≤ H → |finiteStopLoss w t y m| ≤ C)
    (x : Fin n → S) (i : Fin n) (u : U) :
    actionValue D a (finiteWhittleValue w t L) x (i,u) =
      ∑ z : {j : Fin n // j ≠ i} → K, (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) *
        (D.reward (x i) u + a * ∫ y, finiteStopLoss w t y
          (finiteMaximum L (fun j => t (z j))) ∂D.step u (x i)) := by
  have hi : ∀ z : {j : Fin n // j ≠ i} → K,
      Integrable (fun y => finiteStopLoss w t y (finiteMaximum L (fun j => t (z j))))
        (D.step u (x i)) := fun z => integrable_bounded_countable _ _ C
          (fun y => hb y _ (le_finiteMaximum_base L _)
            (finiteMaximum_le L _ hLU (fun j => ht (z j))))
  unfold actionValue
  simp only [finiteWhittleValue_update_split]
  change D.reward (x i) u + a * (∫ y, ∑ z : {j : Fin n // j ≠ i} → K,
      (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) * finiteStopLoss w t y (finiteMaximum L (fun j => t (z j)))
      ∂D.step u (x i)) = _
  rw [integral_finsetSum _ (fun z _ => (hi z).const_mul _)]
  simp only [integral_const_mul]
  have hp := finite_product_weights_sum (fun j : {j : Fin n // j ≠ i} => w (x j))
    (fun j => hs (x j))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma finiteWhittle_action_upper (D : DecisionProcess S U) (a L H C ε : ℝ)
    (w : S → K → ℝ) (t : K → ℝ) (hLH : L ≤ H)
    (hw : ∀ y k, 0 ≤ w y k) (hs : ∀ y, ∑ k, w y k = 1) (ht : ∀ k, t k ≤ H)
    (hb : ∀ y m, L ≤ m → m ≤ H → |finiteStopLoss w t y m| ≤ C)
    (x : Fin n → S) (i : Fin n) (u : U)
    (hr : ∀ z : {j : Fin n // j ≠ i} → K,
      (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) ≠ 0 →
      D.reward (x i) u + a * ∫ y, finiteStopLoss w t y (finiteMaximum L (fun j => t (z j)))
        ∂D.step u (x i) ≤ finiteStopLoss w t (x i) (finiteMaximum L (fun j => t (z j))) + ε) :
    actionValue D a (finiteWhittleValue w t L) x (i,u) ≤ finiteWhittleValue w t L x + ε := by
  rw [finiteWhittle_action_identity D a L H C w t hLH hs ht hb x i u,
    finiteWhittleValue_split w t L x i]
  have hp := finite_product_weights_sum (fun j : {j : Fin n // j ≠ i} => w (x j))
    (fun j => hs (x j))
  calc
    _ ≤ ∑ z : {j : Fin n // j ≠ i} → K, (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) *
        (finiteStopLoss w t (x i) (finiteMaximum L (fun j => t (z j))) + ε) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hr z hz) (Finset.prod_nonneg (fun j _ => hw _ _))
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul,
        finiteStopLoss]

lemma finiteWhittle_action_lower (D : DecisionProcess S U) (a L H C ε : ℝ)
    (w : S → K → ℝ) (t : K → ℝ) (hLH : L ≤ H)
    (hw : ∀ y k, 0 ≤ w y k) (hs : ∀ y, ∑ k, w y k = 1) (ht : ∀ k, t k ≤ H)
    (hb : ∀ y m, L ≤ m → m ≤ H → |finiteStopLoss w t y m| ≤ C)
    (x : Fin n → S) (i : Fin n) (u : U)
    (hr : ∀ z : {j : Fin n // j ≠ i} → K,
      (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) ≠ 0 →
      finiteStopLoss w t (x i) (finiteMaximum L (fun j => t (z j))) - ε ≤
      D.reward (x i) u + a * ∫ y, finiteStopLoss w t y (finiteMaximum L (fun j => t (z j)))
        ∂D.step u (x i)) :
    finiteWhittleValue w t L x - ε ≤ actionValue D a (finiteWhittleValue w t L) x (i,u) := by
  rw [finiteWhittle_action_identity D a L H C w t hLH hs ht hb x i u,
    finiteWhittleValue_split w t L x i]
  have hp := finite_product_weights_sum (fun j : {j : Fin n // j ≠ i} => w (x j))
    (fun j => hs (x j))
  calc
    _ = ∑ z : {j : Fin n // j ≠ i} → K, (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) *
        (finiteStopLoss w t (x i) (finiteMaximum L (fun j => t (z j))) - ε) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, finiteStopLoss]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : (∏ j : {j : Fin n // j ≠ i}, w (x j) (z j)) = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hr z hz) (Finset.prod_nonneg (fun j _ => hw _ _))

end
end AllocationIndices.Proof

end

/- Complete module: MeshWeights -/
section

namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*}

def meshWeights (f : S → ℝ → ℝ) (L h : ℝ) (N : ℕ) (x : S) (k : Fin (N+1)) : ℝ :=
  cumulativeMeshSlope (f x) L h N (k.val+1) - cumulativeMeshSlope (f x) L h N k.val

def meshNodes (L h : ℝ) (N : ℕ) (k : Fin (N+1)) : ℝ := meshNode L h k.val

lemma meshWeights_probability (f : S → ℝ → ℝ) (L h : ℝ) (N : ℕ) (hh : 0 < h)
    (hf : ∀ x, Monotone (f x)) (hlip : ∀ x a b, |f x a-f x b| ≤ |a-b|)
    (hconv : ∀ x, ConvexOn ℝ Set.univ (f x))
    (hend : ∀ x, f x (meshNode L h N) = meshNode L h N) :
    (∀ x k, 0 ≤ meshWeights f L h N x k) ∧ (∀ x, ∑ k, meshWeights f L h N x k = 1) := by
  constructor
  · intro x k
    exact (mesh_probability_and_nodes (f x) L hh (hf x) (hlip x) (hconv x) N (hend x)).1
      k.val (Finset.mem_range.mpr k.isLt)
  · intro x
    unfold meshWeights
    rw [Fin.sum_univ_eq_sum_range (fun k => cumulativeMeshSlope (f x) L h N (k+1) -
      cumulativeMeshSlope (f x) L h N k)]
    exact
      (mesh_probability_and_nodes (f x) L hh (hf x) (hlip x) (hconv x) N (hend x)).2.1

lemma meshWeights_approximation (f : S → ℝ → ℝ) (L h : ℝ) (N : ℕ) (hN : 0 < N)
    (hh : 0 < h) (hf : ∀ x, Monotone (f x))
    (hlip : ∀ x a b, |f x a-f x b| ≤ |a-b|)
    (hconv : ∀ x, ConvexOn ℝ Set.univ (f x))
    (hend : ∀ x, f x (meshNode L h N) = meshNode L h N)
    (x : S) (m : ℝ) (hLm : L ≤ m) (hmH : m ≤ meshNode L h N) :
    |finiteStopLoss (meshWeights f L h N) (meshNodes L h N) x m - f x m| ≤ h := by
  unfold finiteStopLoss meshWeights meshNodes
  rw [Fin.sum_univ_eq_sum_range (fun k => (cumulativeMeshSlope (f x) L h N (k+1) -
    cumulativeMeshSlope (f x) L h N k) * max (meshNode L h k) m)]
  exact
    mesh_stopLoss_approximation (f x) L hh (hf x) (hlip x) (hconv x) N hN (hend x) m
      (by simpa [meshNode] using hLm) hmH

lemma meshWeights_support (f : S → ℝ → ℝ) (L h : ℝ) (N : ℕ) (hh : 0 < h)
    (c : S → ℝ) (hc : ∀ x, L ≤ c x) (hid : ∀ x m, c x ≤ m → f x m = m)
    (x : S) (k : Fin (N+1)) (hk : meshWeights f L h N x k ≠ 0) :
    meshNodes L h N k ≤ c x + h := by
  by_contra h
  exact hk (mesh_mass_eq_zero_above (f x) L (c x) hh (hid x) (hc x) N k.val
    (Nat.le_of_lt_succ k.isLt) (lt_of_not_ge h))

lemma finiteStopLoss_interval {K : Type*} [Fintype K] (w : S → K → ℝ) (t : K → ℝ)
    (L H : ℝ) (hw : ∀ x k, 0 ≤ w x k) (hs : ∀ x, ∑ k, w x k = 1)
    (ht : ∀ k, t k ≤ H) (x : S) (m : ℝ) (hLm : L ≤ m) (hmH : m ≤ H) :
    L ≤ finiteStopLoss w t x m ∧ finiteStopLoss w t x m ≤ H := by
  constructor
  · calc
      L = ∑ k, w x k * L := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ finiteStopLoss w t x m := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hLm.trans (le_max_right _ _)) (hw x k)
  · calc
      finiteStopLoss w t x m ≤ ∑ k, w x k * H := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (max_le (ht k) hmH) (hw x k)
      _ = H := by rw [← Finset.sum_mul, hs, one_mul]

lemma finiteStopLoss_bound {K : Type*} [Fintype K] (w : S → K → ℝ) (t : K → ℝ)
    (L H : ℝ) (hw : ∀ x k, 0 ≤ w x k) (hs : ∀ x, ∑ k, w x k = 1)
    (ht : ∀ k, t k ≤ H) (x : S) (m : ℝ) (hLm : L ≤ m) (hmH : m ≤ H) :
    |finiteStopLoss w t x m| ≤ max |L| |H| := by
  obtain ⟨hl,hh⟩ := finiteStopLoss_interval w t L H hw hs ht x m hLm hmH
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le L, le_max_left |L| |H|]
  · exact hh.trans ((le_abs_self H).trans (le_max_right _ _))

end
end AllocationIndices.Proof

end

/- Complete module: ApproximateBellman -/
section

open MeasureTheory ProbabilityTheory Filter
namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma integral_approximation_bound (μ : Measure S) [IsProbabilityMeasure μ]
    (V W : S → ℝ) (B C h : ℝ) (hV : ∀ y, |V y| ≤ B) (hW : ∀ y, |W y| ≤ C)
    (he : ∀ y, |W y - V y| ≤ h) :
    |(∫ y, W y ∂μ) - ∫ y, V y ∂μ| ≤ h := by
  rw [← integral_sub (integrable_bounded_countable μ W C hW)
    (integrable_bounded_countable μ V B hV)]
  exact abs_integral_bounded μ _ h he

lemma approximate_bellman_upper (μ : Measure S) [IsProbabilityMeasure μ]
    (V W : S → ℝ) (B C h a r : ℝ) (ha : 0 ≤ a)
    (hV : ∀ y, |V y| ≤ B) (hW : ∀ y, |W y| ≤ C)
    (he : ∀ y, |W y - V y| ≤ h) (x : S)
    (hr : r + a * ∫ y, V y ∂μ ≤ V x) :
    r + a * ∫ y, W y ∂μ ≤ W x + (1+a)*h := by
  have hi := (abs_le.mp (integral_approximation_bound μ V W B C h hV hW he)).2
  have hx := (abs_le.mp (he x)).1
  have hm := mul_le_mul_of_nonneg_left hi ha
  nlinarith

lemma approximate_bellman_lower (μ : Measure S) [IsProbabilityMeasure μ]
    (V W : S → ℝ) (B C h a r δ : ℝ) (ha : 0 ≤ a)
    (hV : ∀ y, |V y| ≤ B) (hW : ∀ y, |W y| ≤ C)
    (he : ∀ y, |W y - V y| ≤ h) (x : S)
    (hr : V x - δ ≤ r + a * ∫ y, V y ∂μ) :
    W x - (δ+(1+a)*h) ≤ r + a * ∫ y, W y ∂μ := by
  have hi := (abs_le.mp (integral_approximation_bound μ V W B C h hV hW he)).1
  have hx := (abs_le.mp (he x)).2
  have hm := mul_le_mul_of_nonneg_left hi ha
  nlinarith

end
end AllocationIndices.Proof

end

/- Complete module: WhittleMeshPotential -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  {n : ℕ}

lemma exists_whittle_mesh_potential (D : DecisionProcess S U) (a L h C : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hh : 0 < h) (N : ℕ) (hN : 0 < N)
    (f : S → ℝ → ℝ) (c : S → ℝ) (g : S → U)
    (hf : ∀ x, Monotone (f x)) (hlip : ∀ x p q, |f x p-f x q| ≤ |p-q|)
    (hconv : ∀ x, ConvexOn ℝ Set.univ (f x))
    (hend : ∀ x, f x (meshNode L h N) = meshNode L h N)
    (hc : ∀ x, L ≤ c x) (hid : ∀ x m, c x ≤ m → f x m = m)
    (hb : ∀ x m, L ≤ m → m ≤ meshNode L h N → |f x m| ≤ C)
    (hu : ∀ x u m, u ∈ D.avail x → L ≤ m → m ≤ meshNode L h N →
      D.reward x u + a * ∫ y, f y m ∂D.step u x ≤ f x m)
    (hl : ∀ x m, L ≤ m → m ≤ meshNode L h N → m ≤ c x+h →
      f x m - (1+a)*h ≤ D.reward x (g x) + a * ∫ y, f y m ∂D.step (g x) x) :
    ∃ (V : (Fin n → S) → ℝ) (B : ℝ), (∀ x, |V x| ≤ B) ∧
      (∀ x (i : Fin n) u, u ∈ D.avail (x i) → actionValue D a V x (i,u) ≤ V x+2*h) ∧
      (∀ x (i : Fin n), (∀ j, c (x j) ≤ c (x i)) →
        V x-4*h ≤ actionValue D a V x (i,g (x i))) := by
  let H := meshNode L h N
  let w := meshWeights f L h N
  let t := meshNodes L h N
  let B := max |L| |H|
  obtain ⟨hw,hs⟩ := meshWeights_probability f L h N hh hf hlip hconv hend
  have ht : ∀ k : Fin (N+1), t k ≤ H := by
    intro k
    exact (meshNode_strictMono L hh).monotone (Nat.le_of_lt_succ k.isLt)
  have hLH : L ≤ H := by
    change L ≤ L+(N:ℝ)*h
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg N) hh.le)
  have hvb : ∀ y m, L ≤ m → m ≤ H → |finiteStopLoss w t y m| ≤ B :=
    finiteStopLoss_bound w t L H hw hs ht
  have herr : ∀ y m, L ≤ m → m ≤ H → |finiteStopLoss w t y m-f y m| ≤ h :=
    meshWeights_approximation f L h N hN hh hf hlip hconv hend
  refine ⟨finiteWhittleValue w t L,B,?_,?_,?_⟩
  · intro x
    obtain ⟨hl,hu⟩ := finiteWhittleValue_bounds w t L H hLH hw hs ht x
    apply abs_le.mpr
    constructor
    · dsimp [B]; linarith [neg_abs_le L, le_max_left |L| |H|]
    · exact hu.trans ((le_abs_self H).trans (le_max_right _ _))
  · intro x i u hux
    apply finiteWhittle_action_upper D a L H B (2*h) w t hLH hw hs ht hvb x i u
    intro z _
    let m := finiteMaximum L (fun j => t (z j))
    have hmL : L ≤ m := le_finiteMaximum_base L _
    have hmH : m ≤ H := finiteMaximum_le L _ hLH (fun j => ht (z j))
    have happrox := approximate_bellman_upper (D.step u (x i)) (fun y => f y m)
      (fun y => finiteStopLoss w t y m) C B h a (D.reward (x i) u) ha
      (fun y => hb y m hmL hmH) (fun y => hvb y m hmL hmH)
      (fun y => herr y m hmL hmH) (x i) (hu (x i) u m hux hmL hmH)
    have hsmall : (1+a)*h ≤ 2*h := by nlinarith
    exact happrox.trans (add_le_add_right hsmall _)
  · intro x i hmax
    apply finiteWhittle_action_lower D a L H B (4*h) w t hLH hw hs ht hvb x i (g (x i))
    intro z hz
    let m := finiteMaximum L (fun j => t (z j))
    have hmL : L ≤ m := le_finiteMaximum_base L _
    have hmH : m ≤ H := finiteMaximum_le L _ hLH (fun j => ht (z j))
    have hmc : m ≤ c (x i)+h := by
      apply finiteMaximum_le
      · linarith [hc (x i)]
      · intro j
        have hwj : w (x j) (z j) ≠ 0 := (Finset.prod_ne_zero_iff.mp hz) j (Finset.mem_univ _)
        exact (meshWeights_support f L h N hh c hc hid (x j) (z j) hwj).trans
          (add_le_add_left (hmax j) h)
    have happrox := approximate_bellman_lower (D.step (g (x i)) (x i)) (fun y => f y m)
      (fun y => finiteStopLoss w t y m) C B h a (D.reward (x i) (g (x i))) ((1+a)*h) ha
      (fun y => hb y m hmL hmH) (fun y => hvb y m hmL hmH)
      (fun y => herr y m hmL hmH) (x i) (hl (x i) m hmL hmH hmc)
    have hsmall : (1+a)*h+(1+a)*h ≤ 4*h := by nlinarith
    exact (sub_le_sub_left hsmall _).trans happrox

end
end AllocationIndices.Proof

end

/- Complete module: RetirementValue -/
section

open MeasureTheory ProbabilityTheory

namespace AllocationIndices.Proof

noncomputable section

variable {S U : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U]
  [MeasurableSingletonClass U]

def retirementIter (D : DecisionProcess S U) (a m : ℝ) : ℕ → S → ℝ
  | 0 => fun _ => m
  | t + 1 => fun x => max m ((D.avail x).sup' (D.avail_nonempty x)
      (fun u => D.reward x u + a * ∫ y, retirementIter D a m t y ∂D.step u x))

def retirementValue (D : DecisionProcess S U) (a m : ℝ) (x : S) : ℝ :=
  ⨆ t : ℕ, retirementIter D a m t x

def retirementContinue (D : DecisionProcess S U) (a m : ℝ) (x : S) (u : U) : ℝ :=
  D.reward x u + a * ∫ y, retirementValue D a m y ∂D.step u x

end
end AllocationIndices.Proof

end

/- Complete module: RetirementBellman -/
section

open MeasureTheory ProbabilityTheory Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S]

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementIter_bound (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) :
    ∀ t x, |retirementIter D a m t x| ≤ C := by
  intro t
  induction t with
  | zero => intro x; exact hm
  | succ t ih =>
    intro x
    rw [abs_le] at hm ⊢
    rw [retirementIter]
    constructor
    · exact hm.1.trans (le_max_left _ _)
    · apply max_le hm.2
      apply Finset.sup'_le
      intro u _
      have hi := abs_integral_bounded (D.step u x) (retirementIter D a m t) C ih
      have hu := (abs_le.mp (hr x u)).2
      exact (add_le_add hu (mul_le_mul_of_nonneg_left (abs_le.mp hi).2 ha)).trans hC

lemma retirementIter_mono (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    Monotone (fun t => retirementIter D a m t x) := by
  have hi := retirementIter_bound D a m R C ha hm hC hr
  have hs : ∀ t x, retirementIter D a m t x ≤ retirementIter D a m (t + 1) x := by
    intro t
    induction t with
    | zero => intro x; exact le_max_left _ _
    | succ t ih =>
      intro x
      apply max_le_max le_rfl
      apply Finset.sup'_le
      intro u hu
      apply Finset.le_sup'_of_le _ hu
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ ha
      apply integral_mono_ae
        (integrable_bounded_countable _ _ C (hi t))
        (integrable_bounded_countable _ _ C (hi (t + 1)))
      exact Eventually.of_forall ih
  exact monotone_nat_of_le_succ (fun t => hs t x)

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementIter_le_value (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (t : ℕ) (x : S) :
    retirementIter D a m t x ≤ retirementValue D a m x := by
  unfold retirementValue
  apply le_ciSup _ t
  exact ⟨C, by rintro _ ⟨k, rfl⟩; exact (abs_le.mp (retirementIter_bound D a m R C ha hm hC hr k x)).2⟩

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementValue_bound (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    |retirementValue D a m x| ≤ C := by
  rw [abs_le]
  constructor
  · exact (abs_le.mp hm).1.trans (retirementIter_le_value D a m R C ha hm hC hr 0 x)
  · apply ciSup_le
    intro t
    exact (abs_le.mp (retirementIter_bound D a m R C ha hm hC hr t x)).2


lemma retirementIter_tendsto (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    Tendsto (fun t => retirementIter D a m t x) atTop (nhds (retirementValue D a m x)) := by
  apply tendsto_atTop_ciSup (retirementIter_mono D a m R C ha hm hC hr x)
  exact ⟨C, by rintro _ ⟨t, rfl⟩; exact (abs_le.mp (retirementIter_bound D a m R C ha hm hC hr t x)).2⟩

lemma retirementIntegral_tendsto (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) (u : U) :
    Tendsto (fun t => ∫ y, retirementIter D a m t y ∂D.step u x) atTop
      (nhds (∫ y, retirementValue D a m y ∂D.step u x)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun t => (measurable_of_countable _).aestronglyMeasurable) (integrable_const C)
  · intro t
    exact Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using
      (retirementIter_bound D a m R C ha hm hC hr t y))
  · exact Eventually.of_forall (retirementIter_tendsto D a m R C ha hm hC hr)

lemma retirementContinue_le_value (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) (u : U) (hu : u ∈ D.avail x) :
    retirementContinue D a m x u ≤ retirementValue D a m x := by
  apply le_of_tendsto ((retirementIntegral_tendsto D a m R C ha hm hC hr x u).const_mul a
    |>.const_add (D.reward x u))
  apply Eventually.of_forall
  intro t
  apply le_trans _ (retirementIter_le_value D a m R C ha hm hC hr (t + 1) x)
  exact le_trans (Finset.le_sup' (fun v => D.reward x v +
    a * ∫ y, retirementIter D a m t y ∂D.step v x) hu)
    (le_max_right m _)

lemma retirementValue_bellman (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    retirementValue D a m x = max m ((D.avail x).sup' (D.avail_nonempty x)
      (retirementContinue D a m x)) := by
  have hi := retirementIter_bound D a m R C ha hm hC hr
  have hv := retirementValue_bound D a m R C ha hm hC hr
  apply le_antisymm
  · apply ciSup_le
    intro t
    cases t with
    | zero => exact le_max_left _ _
    | succ t =>
      apply max_le_max le_rfl
      apply Finset.sup'_le
      intro u hu
      apply Finset.le_sup'_of_le _ hu
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ ha
      apply integral_mono_ae (integrable_bounded_countable _ _ C (hi t))
        (integrable_bounded_countable _ _ C hv)
      exact Eventually.of_forall (retirementIter_le_value D a m R C ha hm hC hr t)
  · apply max_le (retirementIter_le_value D a m R C ha hm hC hr 0 x)
    apply Finset.sup'_le
    exact retirementContinue_le_value D a m R C ha hm hC hr x

end
end AllocationIndices.Proof

end

/- Complete module: RetirementRegularity -/
section

open MeasureTheory ProbabilityTheory Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma retirementIter_parameter_mono (D : DecisionProcess S U) (a m q R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hq : |q| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hmq : m ≤ q) :
    ∀ t x, retirementIter D a m t x ≤ retirementIter D a q t x := by
  intro t
  induction t with
  | zero => intro x; exact hmq
  | succ t ih =>
    intro x
    apply max_le_max hmq
    apply Finset.sup'_le
    intro u hu
    apply Finset.le_sup'_of_le _ hu
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ ha
    apply integral_mono_ae
      (integrable_bounded_countable _ _ C (retirementIter_bound D a m R C ha hm hC hr t))
      (integrable_bounded_countable _ _ C (retirementIter_bound D a q R C ha hq hC hr t))
    exact Eventually.of_forall ih

lemma retirementValue_parameter_mono (D : DecisionProcess S U) (a m q R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hq : |q| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hmq : m ≤ q) (x : S) :
    retirementValue D a m x ≤ retirementValue D a q x := by
  apply ciSup_le
  intro t
  exact (retirementIter_parameter_mono D a m q R C ha hm hq hC hr hmq t x).trans
    (retirementIter_le_value D a q R C ha hq hC hr t x)

lemma retirementIter_parameter_shift (D : DecisionProcess S U) (a m q R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hm : |m| ≤ C) (hq : |q| ≤ C)
    (hC : R + a * C ≤ C) (hr : ∀ x u, |D.reward x u| ≤ R) (hmq : m ≤ q) :
    ∀ t x, retirementIter D a q t x ≤ retirementIter D a m t x + (q - m) := by
  intro t
  induction t with
  | zero => intro x; simp [retirementIter]
  | succ t ih =>
    intro x
    change max q _ ≤ max m _ + (q - m)
    apply max_le
    · linarith [le_max_left m ((D.avail x).sup' (D.avail_nonempty x)
        (fun u => D.reward x u + a * ∫ y, retirementIter D a m t y ∂D.step u x))]
    · apply Finset.sup'_le
      intro u hu
      have im := integrable_bounded_countable (D.step u x) _ C
        (retirementIter_bound D a m R C ha hm hC hr t)
      have iq := integrable_bounded_countable (D.step u x) _ C
        (retirementIter_bound D a q R C ha hq hC hr t)
      have hineq := integral_mono_ae iq (im.add (integrable_const (q - m)))
        (Eventually.of_forall ih)
      simp only [Pi.add_apply] at hineq
      rw [integral_add im (integrable_const (q - m))] at hineq
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hineq
      have hcont : D.reward x u + a * ∫ y, retirementIter D a m t y ∂D.step u x ≤
          max m ((D.avail x).sup' (D.avail_nonempty x)
            (fun u => D.reward x u + a * ∫ y, retirementIter D a m t y ∂D.step u x)) :=
        le_trans (Finset.le_sup' (fun v => D.reward x v +
          a * ∫ y, retirementIter D a m t y ∂D.step v x) hu) (le_max_right m _)
      have haDelta : a * (q - m) ≤ q - m := mul_le_of_le_one_left (sub_nonneg.mpr hmq) ha1
      nlinarith

lemma retirementValue_parameter_shift (D : DecisionProcess S U) (a m q R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hm : |m| ≤ C) (hq : |q| ≤ C)
    (hC : R + a * C ≤ C) (hr : ∀ x u, |D.reward x u| ≤ R) (hmq : m ≤ q) (x : S) :
    retirementValue D a q x ≤ retirementValue D a m x + (q - m) := by
  apply ciSup_le
  intro t
  exact (retirementIter_parameter_shift D a m q R C ha ha1 hm hq hC hr hmq t x).trans
    (add_le_add (retirementIter_le_value D a m R C ha hm hC hr t x) le_rfl)


omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma retirement_common_bound (a R B : ℝ) (ha1 : a < 1) (hB : 0 ≤ B) :
    ∃ C : ℝ, B ≤ C ∧ R + a * C ≤ C := by
  refine ⟨B + |R| / (1 - a), ?_, ?_⟩
  · exact le_add_of_nonneg_right (div_nonneg (abs_nonneg R) (by linarith))
  · have heq := div_mul_cancel₀ |R| (ne_of_gt (show 0 < 1 - a by linarith))
    have habs := le_abs_self R
    nlinarith

lemma retirementValue_monotone (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    Monotone (fun m => retirementValue D a m x) := by
  intro m q hmq
  obtain ⟨C, hB, hC⟩ := retirement_common_bound a R (|m| + |q|) ha1
    (add_nonneg (abs_nonneg m) (abs_nonneg q))
  exact retirementValue_parameter_mono D a m q R C ha
    (by linarith [abs_nonneg q]) (by linarith [abs_nonneg m]) hC hr hmq x

lemma retirementValue_lipschitz (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) (m q : ℝ) :
    |retirementValue D a m x - retirementValue D a q x| ≤ |m - q| := by
  obtain ⟨C, hB, hC⟩ := retirement_common_bound a R (|m| + |q|) ha1
    (add_nonneg (abs_nonneg m) (abs_nonneg q))
  have hm : |m| ≤ C := by linarith [abs_nonneg q]
  have hq : |q| ≤ C := by linarith [abs_nonneg m]
  rcases le_total m q with hmq | hqm
  · have hmono := retirementValue_parameter_mono D a m q R C ha hm hq hC hr hmq x
    have hshift := retirementValue_parameter_shift D a m q R C ha ha1.le hm hq hC hr hmq x
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hmq)]
    linarith
  · have hmono := retirementValue_parameter_mono D a q m R C ha hq hm hC hr hqm x
    have hshift := retirementValue_parameter_shift D a q m R C ha ha1.le hq hm hC hr hqm x
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hqm)]
    linarith

end
end AllocationIndices.Proof

end

/- Complete module: RetirementConvex -/
section

open MeasureTheory ProbabilityTheory Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma retirementIter_parameter_convex (D : DecisionProcess S U) (a m q R C b c : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hq : |q| ≤ C) (hp : |b * m + c * q| ≤ C)
    (hC : R + a * C ≤ C) (hr : ∀ x u, |D.reward x u| ≤ R)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : b + c = 1) :
    ∀ t x, retirementIter D a (b * m + c * q) t x ≤
      b * retirementIter D a m t x + c * retirementIter D a q t x := by
  intro t
  induction t with
  | zero => intro x; exact le_rfl
  | succ t ih =>
    intro x
    let vm := retirementIter D a m (t + 1) x
    let vq := retirementIter D a q (t + 1) x
    change max (b * m + c * q) _ ≤ b * vm + c * vq
    apply max_le
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hc)
    · apply Finset.sup'_le
      intro u hu
      have im := integrable_bounded_countable (D.step u x) _ C
        (retirementIter_bound D a m R C ha hm hC hr t)
      have iq := integrable_bounded_countable (D.step u x) _ C
        (retirementIter_bound D a q R C ha hq hC hr t)
      have ip := integrable_bounded_countable (D.step u x) _ C
        (retirementIter_bound D a (b * m + c * q) R C ha hp hC hr t)
      have hineq := integral_mono_ae ip ((im.const_mul b).add (iq.const_mul c))
        (Eventually.of_forall ih)
      simp only [Pi.add_apply] at hineq
      rw [integral_add (im.const_mul b) (iq.const_mul c), integral_const_mul,
        integral_const_mul] at hineq
      have hcm : D.reward x u + a * ∫ y, retirementIter D a m t y ∂D.step u x ≤ vm :=
        le_trans (Finset.le_sup' (fun v => D.reward x v +
          a * ∫ y, retirementIter D a m t y ∂D.step v x) hu) (le_max_right m _)
      have hcq : D.reward x u + a * ∫ y, retirementIter D a q t y ∂D.step u x ≤ vq :=
        le_trans (Finset.le_sup' (fun v => D.reward x v +
          a * ∫ y, retirementIter D a q t y ∂D.step v x) hu) (le_max_right q _)
      have hcont := add_le_add (mul_le_mul_of_nonneg_left hcm hb)
        (mul_le_mul_of_nonneg_left hcq hc)
      have hscaled := mul_le_mul_of_nonneg_left hineq ha
      calc
        _ ≤ D.reward x u + a * (b * (∫ y, retirementIter D a m t y ∂D.step u x) +
          c * (∫ y, retirementIter D a q t y ∂D.step u x)) := add_le_add le_rfl hscaled
        _ = b * (D.reward x u + a * ∫ y, retirementIter D a m t y ∂D.step u x) +
          c * (D.reward x u + a * ∫ y, retirementIter D a q t y ∂D.step u x) := by
            nlinarith [congrArg (fun z => z * D.reward x u) hbc]
        _ ≤ _ := hcont

lemma retirementValue_convex (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    ConvexOn ℝ Set.univ (fun m => retirementValue D a m x) := by
  refine ⟨convex_univ, ?_⟩
  intro m _ q _ b c hb hc hbc
  simp only [smul_eq_mul]
  obtain ⟨C, hB, hC⟩ := retirement_common_bound a R
    (|m| + |q| + |b * m + c * q|) ha1 (by positivity)
  have hm : |m| ≤ C := by linarith [abs_nonneg q, abs_nonneg (b * m + c * q)]
  have hq : |q| ≤ C := by linarith [abs_nonneg m, abs_nonneg (b * m + c * q)]
  have hp : |b * m + c * q| ≤ C := by linarith [abs_nonneg m, abs_nonneg q]
  apply ciSup_le
  intro t
  exact (retirementIter_parameter_convex D a m q R C b c ha hm hq hp hC hr hb hc hbc t x).trans
    (add_le_add (mul_le_mul_of_nonneg_left (retirementIter_le_value D a m R C ha hm hC hr t x) hb)
      (mul_le_mul_of_nonneg_left (retirementIter_le_value D a q R C ha hq hC hr t x) hc))

end
end AllocationIndices.Proof

end

/- Complete module: RetirementEndpoints -/
section

open MeasureTheory ProbabilityTheory Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementIter_eq_self (D : DecisionProcess S U) (a m R : ℝ)
    (hr : ∀ x u, D.reward x u ≤ R) (hm : R + a * m ≤ m) :
    ∀ t x, retirementIter D a m t x = m := by
  intro t
  induction t with
  | zero => intro x; rfl
  | succ t ih =>
    intro x
    rw [retirementIter]
    apply max_eq_left
    apply Finset.sup'_le
    intro u _
    simp only [ih, integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith [hr x u]

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementValue_eq_self (D : DecisionProcess S U) (a m R : ℝ)
    (hr : ∀ x u, D.reward x u ≤ R) (hm : R + a * m ≤ m) (x : S) :
    retirementValue D a m x = m := by
  simp [retirementValue, retirementIter_eq_self D a m R hr hm]

lemma retirementValue_lower_bound (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    -R / (1 - a) ≤ retirementValue D a m x := by
  let : Nonempty S := ⟨x⟩
  let z : ℝ := ⨅ y, retirementValue D a m y
  have hv := retirementValue_bound D a m R C ha hm hC hr
  have hbdd : BddBelow (Set.range (retirementValue D a m)) :=
    ⟨-C, by rintro _ ⟨y, rfl⟩; exact (abs_le.mp (hv y)).1⟩
  have hz : ∀ y, z ≤ retirementValue D a m y := fun y => ciInf_le hbdd y
  have hineq : -R + a * z ≤ z := by
    apply le_ciInf
    intro y
    obtain ⟨u, hu⟩ := D.avail_nonempty y
    have hint : z ≤ ∫ w, retirementValue D a m w ∂D.step u y := by
      simpa using integral_mono_ae (μ := D.step u y) (integrable_const z)
        (integrable_bounded_countable _ _ C hv) (Eventually.of_forall hz)
    have hcont := retirementContinue_le_value D a m R C ha hm hC hr y u hu
    have hre := (abs_le.mp (hr y u)).1
    have hh := mul_le_mul_of_nonneg_left hint ha
    dsimp [retirementContinue] at hcont
    linarith
  apply le_trans _ (hz x)
  apply (div_le_iff₀ (show 0 < 1 - a by linarith)).2
  nlinarith

lemma retirementValue_no_retirement (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hmlow : m < -R / (1 - a)) (x : S) :
    retirementValue D a m x = (D.avail x).sup' (D.avail_nonempty x)
      (retirementContinue D a m x) := by
  have hv := retirementValue_bellman D a m R C ha hm hC hr x
  have hl := retirementValue_lower_bound D a m R C ha ha1 hm hC hr x
  have hgt : m < retirementValue D a m x := hmlow.trans_le hl
  rcases le_total m ((D.avail x).sup' (D.avail_nonempty x) (retirementContinue D a m x)) with h | h
  · simpa [max_eq_right h] using hv
  · rw [max_eq_left h] at hv
    linarith

end
end AllocationIndices.Proof

end

/- Complete module: RetirementComparison -/
section

open MeasureTheory ProbabilityTheory Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma retirementValue_le_super (D : DecisionProcess S U) (a m R C B : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (V : S → ℝ) (hV : ∀ x, |V x| ≤ B)
    (hmV : ∀ x, m ≤ V x)
    (hsuper : ∀ x u, u ∈ D.avail x → D.reward x u + a * ∫ y, V y ∂D.step u x ≤ V x)
    (x : S) : retirementValue D a m x ≤ V x := by
  have hi : ∀ t x, retirementIter D a m t x ≤ V x := by
    intro t
    induction t with
    | zero => exact hmV
    | succ t ih =>
      intro y
      apply max_le (hmV y)
      apply Finset.sup'_le
      intro u hu
      apply le_trans _ (hsuper y u hu)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ ha
      apply integral_mono_ae
        (integrable_bounded_countable _ _ C (retirementIter_bound D a m R C ha hm hC hr t))
        (integrable_bounded_countable _ _ B hV)
      exact Eventually.of_forall ih
  exact ciSup_le (fun t => hi t x)

lemma retirementValue_constant_below (D : DecisionProcess S U) (a m q R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : ∀ x u, |D.reward x u| ≤ R)
    (hm : m ≤ -R / (1 - a)) (hq : q ≤ -R / (1 - a)) (x : S) :
    retirementValue D a m x = retirementValue D a q x := by
  obtain ⟨C, hB, hC⟩ := retirement_common_bound a R (|m| + |q|) ha1 (by positivity)
  have hmC : |m| ≤ C := by linarith [abs_nonneg q]
  have hqC : |q| ≤ C := by linarith [abs_nonneg m]
  have hvM := retirementValue_bound D a m R C ha hmC hC hr
  have hvQ := retirementValue_bound D a q R C ha hqC hC hr
  apply le_antisymm
  · exact retirementValue_le_super D a m R C C ha hmC hC hr _ hvQ
      (fun y => hm.trans (retirementValue_lower_bound D a q R C ha ha1 hqC hC hr y))
      (retirementContinue_le_value D a q R C ha hqC hC hr) x
  · exact retirementValue_le_super D a q R C C ha hqC hC hr _ hvM
      (fun y => hq.trans (retirementValue_lower_bound D a m R C ha ha1 hmC hC hr y))
      (retirementContinue_le_value D a m R C ha hmC hC hr) x

end
end AllocationIndices.Proof

end

/- Complete module: GittinsStoppedBounds -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Proof

lemma stopped_sum_abs_bound {S : Type*} (f : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (ω : ℕ → S) {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) :
    |discountedStoppedSum a f τ ω| ≤ M / (1 - a) := by
  have hg := (hasSum_geometric_of_lt_one ha0 ha1).mul_right M
  have hb : ∀ t : ℕ, ‖if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0‖ ≤ a ^ t * M := by
    intro t
    split_ifs
    · simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 t)] using
        mul_le_mul_of_nonneg_left (hf (ω t)) (pow_nonneg ha0 t)
    · simp only [norm_zero]
      positivity
  have hout := tsum_of_norm_bounded hg hb
  simpa only [discountedStoppedSum, Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using hout

lemma stopped_sum_summable {S : Type*} (f : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (ω : ℕ → S) {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hM : 0 ≤ M)
    (hf : ∀ x, |f x| ≤ M) :
    Summable (fun t : ℕ => if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) := by
  apply ((summable_geometric_of_lt_one ha0 ha1).mul_right M).of_norm_bounded
  intro t
  split_ifs
  · simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 t)] using
      mul_le_mul_of_nonneg_left (hf (ω t)) (pow_nonneg ha0 t)
  · simp only [norm_zero]
    positivity

lemma stopped_discount_lower {S : Type*} (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hτ : 1 ≤ τ ω) :
    1 ≤ discountedStoppedSum a (fun _ : S => 1) τ ω := by
  have hs := stopped_sum_summable (fun _ : S => (1 : ℝ)) τ ω ha0 ha1
    (show (0 : ℝ) ≤ 1 by norm_num) (fun _ => by norm_num)
  have ht : (0 : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) hτ
  have hle := hs.le_tsum 0 (fun t _ => by split_ifs <;> positivity)
  simpa only [Nat.cast_zero, ht, ↓reduceIte, pow_zero, one_mul, discountedStoppedSum] using hle

lemma trajectoryFiltration_le {S : Type*} [MeasurableSpace S] (t : ℕ) :
    trajectoryFiltration S t ≤ (inferInstance : MeasurableSpace (ℕ → S)) := by
  exact (measurable_pi_lambda _ fun i => measurable_pi_apply i.val).comap_le

lemma measurable_stopped_sum {S : Type*} [MeasurableSpace S] (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (a : ℝ) :
    Measurable (discountedStoppedSum a f τ) := by
  apply Measurable.tsum
  intro t
  apply Measurable.ite _ ((hf.comp (measurable_pi_apply t)).const_mul _) measurable_const
  have hset : MeasurableSet {ω : ℕ → S | τ ω ≤ (t : ℕ∞)} :=
    trajectoryFiltration_le t _ (hτ t)
  simpa only [Set.compl_ofPred, not_le] using hset.compl

lemma integrable_stopped_sum {S : Type*} [MeasurableSpace S] (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (μ : Measure (ℕ → S)) [IsFiniteMeasure μ]
    {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M) :
    Integrable (discountedStoppedSum a f τ) μ := by
  apply Integrable.of_bound (measurable_stopped_sum f hf τ hτ a).aestronglyMeasurable (M / (1 - a))
  exact Filter.Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using stopped_sum_abs_bound f τ ω ha0 ha1 hM hbound

lemma stopped_discount_integral_lower {S : Type*} [MeasurableSpace S]
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hpos : ∀ ω, 1 ≤ τ ω)
    (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ] {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    1 ≤ ∫ ω, discountedStoppedSum a (fun _ : S => 1) τ ω ∂μ := by
  have hi := integrable_stopped_sum (fun _ : S => (1 : ℝ)) measurable_const τ hτ μ
    ha0 ha1 (show (0 : ℝ) ≤ 1 by norm_num) (fun _ => by norm_num)
  have := integral_mono (integrable_const (1 : ℝ)) hi
    (fun ω => stopped_discount_lower τ ω ha0 ha1 (hpos ω))
  simpa using this

end AllocationIndices.Proof

end

/- Complete module: MarkovIntegrals -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped BigOperators

namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

instance markovChainMeasure_probability (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure
  infer_instance

lemma markov_weighted_next_integral (P : Kernel S S) [IsMarkovKernel P] (x : S) (t : ℕ)
    (h : (Finset.Iic t → S) → ℝ) (f : S → ℝ) (B C : ℝ)
    (hh : ∀ z, |h z| ≤ B) (hf : ∀ y, |f y| ≤ C) :
    (∫ ω, h (fun i => ω i.val) * f (ω (t + 1)) ∂markovChainMeasure P x) =
      ∫ ω, h (fun i => ω i.val) * (∫ y, f y ∂P (ω t)) ∂markovChainMeasure P x := by
  let μ := markovChainMeasure P x
  let F : (Finset.Iic t → S) × S → ℝ := fun z => h z.1 * f z.2
  have hF : ∀ z, |F z| ≤ B * C := fun z => by
    rw [abs_mul]
    exact mul_le_mul (hh z.1) (hf z.2) (abs_nonneg _) ((abs_nonneg _).trans (hh z.1))
  have heq := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => S) (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := t)
  have hint := Measure.integral_compProd
    (integrable_bounded_countable (μ.map (fun ω (i : Finset.Iic t) => ω i.val) ⊗ₘ markovChainStep P t)
      F (B * C) hF)
  change (μ.map (fun ω (i : Finset.Iic t) => ω i.val) ⊗ₘ markovChainStep P t) =
    μ.map (fun ω => ((fun i : Finset.Iic t => ω i.val), ω (t + 1))) at heq
  rw [heq] at hint
  rw [integral_map_of_stronglyMeasurable (by fun_prop)
    (measurable_of_countable F).stronglyMeasurable] at hint
  rw [integral_map_of_stronglyMeasurable (by fun_prop)
    (measurable_of_countable (fun z => ∫ y, F (z, y) ∂markovChainStep P t z)).stronglyMeasurable] at hint
  simpa only [F, μ, markovChainStep, Kernel.comap_apply, integral_const_mul] using hint


lemma markov_event_next_integral (P : Kernel S S) [IsMarkovKernel P] (x : S) (t : ℕ)
    (A : Set (ℕ → S)) (hA : MeasurableSet[trajectoryFiltration S t] A)
    (f : S → ℝ) (C : ℝ) (hf : ∀ y, |f y| ≤ C) :
    (∫ ω, A.indicator (fun ω => f (ω (t + 1))) ω ∂markovChainMeasure P x) =
      ∫ ω, A.indicator (fun ω => ∫ y, f y ∂P (ω t)) ω ∂markovChainMeasure P x := by
  obtain ⟨B, _, rfl⟩ := hA
  have hh : ∀ z : Finset.Iic t → S, |B.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ B <;> simp [hz]
  have h := markov_weighted_next_integral P x t (B.indicator (fun _ => 1)) f 1 C hh hf
  convert h using 1 <;> apply integral_congr_ae <;> filter_upwards [] with ω <;>
    by_cases hω : (fun i : Finset.Iic t => ω i.val) ∈ B <;> simp [hω]

lemma markov_initial_integral (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (f : S → ℝ) : (∫ ω, f (ω 0) ∂markovChainMeasure P x) = f x := by
  simp only [markovChainMeasure, Kernel.trajMeasure, Measure.map_dirac]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  rw [Kernel.integral_traj (X := fun _ => S) (κ := markovChainStep P)
    (f := fun ω => f (ω 0)) _
    ((measurable_of_countable f).comp (measurable_pi_apply 0)).aestronglyMeasurable]
  simp [Function.updateFinset]

end
end AllocationIndices.Proof

end

/- Complete module: StoppedExpectations -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section

variable {S : Type*} [MeasurableSpace S]

def stoppedRound (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (t : ℕ) (ω : ℕ → S) : ℝ :=
  if (t : ℕ∞) < τ ω then f (ω t) else 0

lemma stoppedRound_measurable (f : S → ℝ) (hf : Measurable f)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    Measurable (stoppedRound f τ t) := by
  apply Measurable.ite _ (hf.comp (measurable_pi_apply t)) measurable_const
  have hset : MeasurableSet {ω : ℕ → S | τ ω ≤ (t : ℕ∞)} :=
    trajectoryFiltration_le t _ (hτ t)
  simpa only [Set.compl_ofPred, not_le] using hset.compl

omit [MeasurableSpace S] in
lemma stoppedRound_bound (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (M : ℝ)
    (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (t : ℕ) (ω : ℕ → S) :
    |stoppedRound f τ t ω| ≤ M := by
  unfold stoppedRound
  split_ifs
  · exact hf _
  · simpa using hM

lemma stoppedRound_integrable (f : S → ℝ) (hf : Measurable f)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M)
    (μ : Measure (ℕ → S)) [IsFiniteMeasure μ] (t : ℕ) :
    Integrable (stoppedRound f τ t) μ := by
  apply Integrable.of_bound (stoppedRound_measurable f hf τ hτ t).aestronglyMeasurable M
  exact Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using
    (stoppedRound_bound f τ M hM hbound t ω))

lemma integral_stopped_sum_eq_tsum (f : S → ℝ) (hf : Measurable f)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M)
    (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (∫ ω, discountedStoppedSum a f τ ω ∂μ) =
      ∑' t, a ^ t * ∫ ω, stoppedRound f τ t ω ∂μ := by
  have hi : ∀ t, Integrable (fun ω => a ^ t * stoppedRound f τ t ω) μ := fun t =>
    (stoppedRound_integrable f hf τ hτ M hM hbound μ t).const_mul _
  have hs : Summable (fun t => ∫ ω, ‖a ^ t * stoppedRound f τ t ω‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun t => integral_nonneg (fun _ => norm_nonneg _)) _
      ((summable_geometric_of_lt_one ha ha1).mul_right M)
    intro t
    have hb : ∀ᵐ ω ∂μ, ‖a ^ t * stoppedRound f τ t ω‖ ≤ a ^ t * M :=
      Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha t)] using
          mul_le_mul_of_nonneg_left (stoppedRound_bound f τ M hM hbound t ω) (pow_nonneg ha t))
    simpa using integral_mono_ae (hi t).norm (integrable_const (a ^ t * M)) hb
  have heq := integral_tsum_of_summable_integral_norm hi hs
  simp only [integral_const_mul] at heq
  rw [heq]
  apply integral_congr_ae
  filter_upwards [] with ω
  apply tsum_congr
  intro t
  simp only [stoppedRound, mul_ite, mul_zero]

end
end AllocationIndices.Proof

end

/- Complete module: StoppedVerification -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

def markovContinue (P : Kernel S S) (a : ℝ) (f W : S → ℝ) (x : S) : ℝ :=
  f x + a * ∫ y, W y ∂P x

def stoppedAfter (W : S → ℝ) (τ : (ℕ → S) → ℕ∞) (t : ℕ) (ω : ℕ → S) : ℝ :=
  if (t : ℕ∞) < τ ω then W (ω (t + 1)) else 0

lemma stoppedAfter_integrable (W : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (C : ℝ) (hC : 0 ≤ C) (hW : ∀ x, |W x| ≤ C)
    (μ : Measure (ℕ → S)) [IsFiniteMeasure μ] (t : ℕ) : Integrable (stoppedAfter W τ t) μ := by
  have hset : MeasurableSet {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
    have h := trajectoryFiltration_le t _ (hτ t)
    simpa only [Set.compl_ofPred, not_le] using h.compl
  apply Integrable.of_bound
    ((Measurable.ite hset ((measurable_of_countable W).comp (measurable_pi_apply (t + 1)))
      measurable_const).aestronglyMeasurable) C
  apply Eventually.of_forall
  intro ω
  change |if (t : ℕ∞) < τ ω then W (ω (t + 1)) else 0| ≤ C
  split_ifs
  · exact hW _
  · simpa using hC

lemma stopped_reward_after_identity (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (a : ℝ) (f W : S → ℝ) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ M) (hW : ∀ x, |W x| ≤ C)
    (t : ℕ) :
    (∫ ω, stoppedRound f τ t ω ∂markovChainMeasure P x) +
      a * (∫ ω, stoppedAfter W τ t ω ∂markovChainMeasure P x) =
      ∫ ω, stoppedRound (markovContinue P a f W) τ t ω ∂markovChainMeasure P x := by
  have hset : MeasurableSet[trajectoryFiltration S t] {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
    simpa only [Set.compl_ofPred, not_le] using (hτ t).compl
  have hm := markov_event_next_integral P x t _ hset W C hW
  simp only [Set.indicator, Set.mem_ofPred_eq] at hm
  change (∫ ω, stoppedAfter W τ t ω ∂markovChainMeasure P x) =
    ∫ ω, (if (t : ℕ∞) < τ ω then ∫ y, W y ∂P (ω t) else 0) ∂markovChainMeasure P x at hm
  rw [hm, ← integral_const_mul, ← integral_add]
  · apply integral_congr_ae
    filter_upwards [] with ω
    unfold stoppedRound markovContinue
    split_ifs <;> simp
  · exact stoppedRound_integrable f (measurable_of_countable _) τ hτ M hM hf _ t
  · apply Integrable.const_mul
    exact stoppedRound_integrable (fun z => ∫ y, W y ∂P z) (measurable_of_countable _) τ hτ C hC
      (fun z => abs_integral_bounded _ _ C hW) _ t

lemma stopped_step_upper (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (a : ℝ) (ha : 0 ≤ a) (f W : S → ℝ) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ M) (hW : ∀ x, |W x| ≤ C)
    (hW0 : ∀ x, 0 ≤ W x) (t : ℕ) :
    (∫ ω, stoppedRound f τ t ω ∂markovChainMeasure P x) +
      a * (∫ ω, stoppedRound W τ (t + 1) ω ∂markovChainMeasure P x) ≤
      ∫ ω, stoppedRound (markovContinue P a f W) τ t ω ∂markovChainMeasure P x := by
  rw [← stopped_reward_after_identity P x a f W τ hτ M C hM hC hf hW t]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ ha
  apply integral_mono_ae
    (stoppedRound_integrable W (measurable_of_countable _) τ hτ C hC hW _ (t + 1))
    (stoppedAfter_integrable W τ hτ C hC hW _ t)
  apply Eventually.of_forall
  intro ω
  unfold stoppedRound stoppedAfter
  split_ifs with hnext hnow hnow
  · exact le_rfl
  · exact (hnow (lt_trans (by exact_mod_cast Nat.lt_succ_self t) hnext)).elim
  · exact hW0 _
  · exact le_rfl

end
end AllocationIndices.Proof

end

/- Complete module: StoppedUpper -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

omit [Countable S] [MeasurableSingletonClass S] in
lemma markovContinue_bound (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (f W : S → ℝ)
    (M C : ℝ) (hf : ∀ x, |f x| ≤ M) (hW : ∀ x, |W x| ≤ C) (x : S) :
    |markovContinue P a f W x| ≤ M + |a| * C := by
  apply (abs_add_le _ _).trans
  apply add_le_add (hf x)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_integral_bounded _ _ C hW) (abs_nonneg a)

lemma stoppedRound_initial_integral (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (hpos : ∀ ω, 1 ≤ τ ω) :
    (∫ ω, stoppedRound f τ 0 ω ∂markovChainMeasure P x) = f x := by
  have hτ : ∀ ω, (0 : ℕ∞) < τ ω := fun ω => lt_of_lt_of_le (by norm_num) (hpos ω)
  simpa only [stoppedRound, Nat.cast_zero, hτ, ↓reduceIte] using markov_initial_integral P x f

lemma stopped_verification_upper (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f W : S → ℝ)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hpos : ∀ ω, 1 ≤ τ ω)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ M) (hW : ∀ x, |W x| ≤ C)
    (hW0 : ∀ x, 0 ≤ W x) (hbell : ∀ y, markovContinue P a f W y ≤ W y) :
    (∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x) ≤ markovContinue P a f W x := by
  let μ := markovChainMeasure P x
  let q := markovContinue P a f W
  let r : ℕ → ℝ := fun t => ∫ ω, stoppedRound f τ t ω ∂μ
  let v : ℕ → ℝ := fun t => if t = 0 then q x else ∫ ω, stoppedRound W τ t ω ∂μ
  have hq := markovContinue_bound P a f W M C hf hW
  have hr : ∀ t, |r t| ≤ M := fun t => abs_integral_bounded _ _ M
    (stoppedRound_bound f τ M hM hf t)
  have hv : ∀ t, |v t| ≤ |q x| + C := by
    intro t
    dsimp [v]
    split_ifs
    · linarith
    · have h := abs_integral_bounded μ (stoppedRound W τ t) C (stoppedRound_bound W τ C hC hW t)
      linarith [abs_nonneg (q x)]
  have hs : ∀ t, r t + a * v (t + 1) ≤ v t + 0 := by
    intro t
    have h := stopped_step_upper P x a ha f W τ hτ M C hM hC hf hW hW0 t
    cases t with
    | zero =>
      rw [stoppedRound_initial_integral P x q τ hpos] at h
      simpa [r, v, μ, q] using h
    | succ t =>
      have hle : (∫ ω, stoppedRound q τ (t + 1) ω ∂μ) ≤
          ∫ ω, stoppedRound W τ (t + 1) ω ∂μ := by
        apply integral_mono_ae
          (stoppedRound_integrable q (measurable_of_countable _) τ hτ (M + |a| * C) (by positivity) hq μ _)
          (stoppedRound_integrable W (measurable_of_countable _) τ hτ C hC hW μ _)
        apply Eventually.of_forall
        intro ω
        unfold stoppedRound
        split_ifs
        · exact hbell _
        · exact le_rfl
      have hh := h.trans hle
      simpa [r, v, μ, q] using hh
  have hfinal := discounted_sequence_upper a ha ha1 r v M (|q x| + C) 0 hr hv hs
  rw [integral_stopped_sum_eq_tsum f (measurable_of_countable _) τ hτ M hM hf μ a ha ha1]
  simpa [r, v, q] using hfinal

end
end AllocationIndices.Proof

end

/- Complete module: RetirementSurplus -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

def retirementSurplus (D : DecisionProcess S U) (a m : ℝ) (x : S) : ℝ :=
  retirementValue D a m x - m

def retirementBestExcess (D : DecisionProcess S U) (a m : ℝ) (x : S) : ℝ :=
  (D.avail x).sup' (D.avail_nonempty x) (retirementContinue D a m x) - m

def retirementGreedy (D : DecisionProcess S U) (a m : ℝ) (x : S) : U :=
  Classical.choose ((D.avail x).exists_mem_eq_sup' (D.avail_nonempty x) (retirementContinue D a m x))

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementGreedy_feasible (D : DecisionProcess S U) (a m : ℝ) :
    D.IsFeasibleStationary (retirementGreedy D a m) :=
  fun x => (Classical.choose_spec ((D.avail x).exists_mem_eq_sup'
    (D.avail_nonempty x) (retirementContinue D a m x))).1

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementGreedy_max (D : DecisionProcess S U) (a m : ℝ) (x : S) :
    (D.avail x).sup' (D.avail_nonempty x) (retirementContinue D a m x) =
      retirementContinue D a m x (retirementGreedy D a m x) :=
  (Classical.choose_spec ((D.avail x).exists_mem_eq_sup'
    (D.avail_nonempty x) (retirementContinue D a m x))).2

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementSurplus_nonneg (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) : 0 ≤ retirementSurplus D a m x :=
  sub_nonneg.mpr (retirementIter_le_value D a m R C ha hm hC hr 0 x)

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementSurplus_bound (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) : |retirementSurplus D a m x| ≤ C + |m| := by
  have h := (abs_add_le (retirementValue D a m x) (-m)).trans
    (add_le_add (retirementValue_bound D a m R C ha hm hC hr x) le_rfl)
  simpa only [retirementSurplus, sub_eq_add_neg, abs_neg] using h

lemma markovContinue_stationary_shift (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (g : S → U) (x : S) :
    markovContinue (stationaryKernel D g) a (fun y => D.reward y (g y) - (1 - a) * m)
      (retirementSurplus D a m) x = retirementContinue D a m x (g x) - m := by
  change D.reward x (g x) - (1 - a) * m +
    a * (∫ y, retirementValue D a m y - m ∂D.step (g x) x) = _
  rw [integral_sub (integrable_bounded_countable _ _ C
    (retirementValue_bound D a m R C ha hm hC hr)) (integrable_const m)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold retirementContinue
  ring

lemma retirementSurplus_bellman (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    retirementSurplus D a m x = max 0 (retirementBestExcess D a m x) := by
  unfold retirementSurplus retirementBestExcess
  rw [retirementValue_bellman D a m R C ha hm hC hr x, ← max_sub_sub_right, sub_self]

lemma retirementSurplus_greedy_bellman (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    retirementSurplus D a m x = max 0
      (markovContinue (stationaryKernel D (retirementGreedy D a m)) a
        (fun y => D.reward y (retirementGreedy D a m y) - (1 - a) * m)
        (retirementSurplus D a m) x) := by
  rw [markovContinue_stationary_shift D a m R C ha hm hC hr]
  rw [retirementSurplus_bellman D a m R C ha hm hC hr]
  rw [retirementBestExcess, retirementGreedy_max]

end
end AllocationIndices.Proof

end

/- Complete module: FirstZeroStopping -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

def firstZero (W : S → ℝ) : (ℕ → S) → ℕ∞ :=
  hittingAfter (fun t ω => W (ω t)) {0} 1

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma firstZero_positive (W : S → ℝ) (ω : ℕ → S) : 1 ≤ firstZero W ω :=
  le_hittingAfter ω

lemma firstZero_stopping (W : S → ℝ) : IsTrajStoppingTime (firstZero W) := by
  intro n
  refine ⟨{h : Finset.Iic n → S | ∃ j : Finset.Iic n, 1 ≤ j.val ∧ W (h j) = 0},
    Set.Countable.measurableSet (Set.to_countable _), ?_⟩
  ext ω
  change (∃ j : Finset.Iic n, 1 ≤ j.val ∧ W (ω j.val) = 0) ↔
    hittingAfter (fun t ω => W (ω t)) {0} 1 ω ≤ WithTop.some n
  rw [hittingAfter_le_iff (i := n) (n := (1 : ℕ)) (u := fun (t : ℕ) (ω : ℕ → S) => W (ω t)) (s := {0}) (ω := ω)]
  simp only [Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, hW⟩
    exact ⟨j.val, ⟨hj, Finset.mem_Iic.mp j.property⟩, hW⟩
  · rintro ⟨j, ⟨hj, hjn⟩, hW⟩
    exact ⟨⟨j, Finset.mem_Iic.mpr hjn⟩, hj, hW⟩

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma firstZero_alive_ne (W : S → ℝ) (ω : ℕ → S) (t : ℕ)
    (ht : 1 ≤ t) (halive : (t : ℕ∞) < firstZero W ω) : W (ω t) ≠ 0 :=
  notMem_of_lt_hittingAfter halive ht

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma firstZero_next_zero (W : S → ℝ) (ω : ℕ → S) (t : ℕ)
    (halive : (t : ℕ∞) < firstZero W ω) (hstop : firstZero W ω ≤ (t + 1 : ℕ)) :
    W (ω (t + 1)) = 0 := by
  obtain ⟨j, ⟨hj1, hjt⟩, hjW⟩ := hittingAfter_le_iff.mp hstop
  have hjgt : t < j := by
    by_contra h
    have hjle : j ≤ t := by omega
    have hhit : firstZero W ω ≤ (j : ℕ) := hittingAfter_le_of_mem hj1 hjW
    exact (not_le.mpr halive) (hhit.trans (by exact_mod_cast hjle))
  have hj : j = t + 1 := by omega
  simpa [hj] using hjW

end
end AllocationIndices.Proof

end

/- Complete module: StoppedEquality -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma stoppedAfter_firstZero (W : S → ℝ) (t : ℕ) (ω : ℕ → S) :
    stoppedAfter W (firstZero W) t ω = stoppedRound W (firstZero W) (t + 1) ω := by
  unfold stoppedAfter stoppedRound
  by_cases hnow : (t : ℕ∞) < firstZero W ω
  · by_cases hnext : ((t + 1 : ℕ) : ℕ∞) < firstZero W ω
    · simp only [if_pos hnow, if_pos hnext]
    · have hz := firstZero_next_zero W ω t hnow (le_of_not_gt hnext)
      simp only [if_pos hnow, if_neg hnext, hz]
  · have hnext : ¬ ((t + 1 : ℕ) : ℕ∞) < firstZero W ω := fun h =>
      hnow (lt_trans (by exact_mod_cast Nat.lt_succ_self t) h)
    simp only [if_neg hnow, if_neg hnext]

lemma stopped_verification_eq (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (f W : S → ℝ)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ M) (hW : ∀ x, |W x| ≤ C)
    (hbell : ∀ y, W y = max 0 (markovContinue P a f W y)) :
    (∫ ω, discountedStoppedSum a f (firstZero W) ω ∂markovChainMeasure P x) =
      markovContinue P a f W x := by
  let μ := markovChainMeasure P x
  let q := markovContinue P a f W
  let τ := firstZero W
  have hτ := firstZero_stopping W
  let r : ℕ → ℝ := fun t => ∫ ω, stoppedRound f τ t ω ∂μ
  let v : ℕ → ℝ := fun t => if t = 0 then q x else ∫ ω, stoppedRound W τ t ω ∂μ
  have hr : ∀ t, |r t| ≤ M := fun t => abs_integral_bounded _ _ M
    (stoppedRound_bound f τ M hM hf t)
  have hv : ∀ t, |v t| ≤ |q x| + C := by
    intro t
    dsimp [v]
    split_ifs
    · linarith
    · have h := abs_integral_bounded μ (stoppedRound W τ t) C (stoppedRound_bound W τ C hC hW t)
      linarith [abs_nonneg (q x)]
  have hs : ∀ t, r t + a * v (t + 1) = v t := by
    intro t
    have h := stopped_reward_after_identity P x a f W τ hτ M C hM hC hf hW t
    simp only [τ, stoppedAfter_firstZero] at h
    cases t with
    | zero =>
      rw [stoppedRound_initial_integral P x q (firstZero W) (firstZero_positive W)] at h
      simpa [r, v, μ, q, τ] using h
    | succ t =>
      have hround : stoppedRound q τ (t + 1) = stoppedRound W τ (t + 1) := by
        funext ω
        unfold stoppedRound
        split_ifs with halive
        · have hne := firstZero_alive_ne W ω (t + 1) (by omega) halive
          have hb : W (ω (t + 1)) = max 0 (q (ω (t + 1))) := hbell (ω (t + 1))
          rcases le_total 0 (q (ω (t + 1))) with hq | hq
          · simpa only [max_eq_right hq] using hb.symm
          · exact (hne (hb.trans (max_eq_left hq))).elim
        · rfl
      change _ = ∫ ω, stoppedRound q τ (t + 1) ω ∂μ at h
      rw [hround] at h
      simpa [r, v, μ, q, τ] using h
  have hu := discounted_sequence_upper a ha ha1 r v M (|q x| + C) 0 hr hv
    (fun t => by linarith [hs t])
  have hl := discounted_sequence_upper a ha ha1 (fun t => -r t) (fun t => -v t)
    M (|q x| + C) 0 (fun t => by simpa using hr t) (fun t => by simpa using hv t)
    (fun t => by linarith [hs t])
  simp only [mul_neg, tsum_neg, zero_div, add_zero] at hu hl
  rw [integral_stopped_sum_eq_tsum f (measurable_of_countable _) τ hτ M hM hf μ a ha ha1]
  change (∑' t, a ^ t * r t) = q x
  have hv0 : v 0 = q x := by simp [v]
  linarith

end
end AllocationIndices.Proof

end

/- Complete module: GittinsRatioBounds -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Proof

lemma stopped_sum_abs_le_discount {S : Type*} (f : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (ω : ℕ → S) {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hf : ∀ x, |f x| ≤ M) :
    |discountedStoppedSum a f τ ω| ≤ M * discountedStoppedSum a (fun _ : S => 1) τ ω := by
  have hs := stopped_sum_summable (fun _ : S => (1 : ℝ)) τ ω ha0 ha1
    (show (0 : ℝ) ≤ 1 by norm_num) (fun _ => by norm_num)
  have hb : ∀ t : ℕ, ‖if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0‖ ≤
      M * (if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) := by
    intro t
    split_ifs
    · simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 t), mul_one, mul_comm] using
        mul_le_mul_of_nonneg_left (hf (ω t)) (pow_nonneg ha0 t)
    · simp
  have hout := tsum_of_norm_bounded (hs.hasSum.mul_left M) hb
  simpa only [discountedStoppedSum, Real.norm_eq_abs] using hout

lemma stopped_ratio_abs_bound {S : Type*} [MeasurableSpace S] (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (hpos : ∀ ω, 1 ≤ τ ω) (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M) :
    |(∫ ω, discountedStoppedSum a f τ ω ∂μ) /
      (∫ ω, discountedStoppedSum a (fun _ : S => 1) τ ω ∂μ)| ≤ M := by
  have hfi := integrable_stopped_sum f hf τ hτ μ ha0 ha1 hM hbound
  have hdi := integrable_stopped_sum (fun _ : S => (1 : ℝ)) measurable_const τ hτ μ
    ha0 ha1 (show (0 : ℝ) ≤ 1 by norm_num) (fun _ => by norm_num)
  have hd := stopped_discount_integral_lower τ hτ hpos μ ha0 ha1
  have hnum : |∫ ω, discountedStoppedSum a f τ ω ∂μ| ≤
      M * (∫ ω, discountedStoppedSum a (fun _ : S => 1) τ ω ∂μ) := by
    calc
      _ ≤ ∫ ω, |discountedStoppedSum a f τ ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, M * discountedStoppedSum a (fun _ : S => 1) τ ω ∂μ :=
        integral_mono hfi.abs (hdi.const_mul M)
          (fun ω => stopped_sum_abs_le_discount f τ ω ha0 ha1 hbound)
      _ = _ := integral_const_mul _ _
  rw [abs_div, abs_of_pos (by linarith : 0 < ∫ ω, discountedStoppedSum a (fun _ : S => 1) τ ω ∂μ)]
  exact (div_le_iff₀ (by linarith)).mpr hnum

lemma gittinsIndex_abs_bound {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (f : S → ℝ) (hf : Measurable f)
    {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M) (x : S) : |gittinsIndex P f a x| ≤ M := by
  let : IsProbabilityMeasure (markovChainMeasure P x) := by
    unfold markovChainMeasure
    infer_instance
  let A : Set ℝ := {z | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    z = (∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum a (fun _ => 1) τ ω ∂markovChainMeasure P x)}
  have hA : A.Nonempty := by
    refine ⟨_, fun _ => 1, ?_, fun _ => le_rfl, rfl⟩
    intro n
    by_cases hn : (1 : ℕ∞) ≤ (n : ℕ∞) <;> simp [hn]
  have hb : ∀ z ∈ A, |z| ≤ M := by
    intro z hz
    obtain ⟨τ, hτ, hpos, rfl⟩ := hz
    exact stopped_ratio_abs_bound f hf τ hτ hpos (markovChainMeasure P x) ha0 ha1 hM hbound
  have hupper : BddAbove A := ⟨M, fun z hz => (abs_le.mp (hb z hz)).2⟩
  change |sSup A| ≤ M
  rw [abs_le]
  constructor
  · obtain ⟨z, hz⟩ := hA
    exact (abs_le.mp (hb z hz)).1.trans (le_csSup hupper hz)
  · exact csSup_le hA (fun z hz => (abs_le.mp (hb z hz)).2)

end AllocationIndices.Proof

end

/- Complete module: StoppedShift -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma stopped_sum_sub_const (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (a lam M : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) :
    discountedStoppedSum a (fun y => f y - lam) τ ω =
      discountedStoppedSum a f τ ω - lam * discountedStoppedSum a (fun _ => 1) τ ω := by
  have hs := stopped_sum_summable f τ ω ha ha1 hM hf
  have ht := stopped_sum_summable (fun _ : S => (1 : ℝ)) τ ω ha ha1 (show (0 : ℝ) ≤ 1 by norm_num) (fun _ => by norm_num)
  unfold discountedStoppedSum
  rw [← tsum_mul_left, ← hs.tsum_sub (ht.mul_left lam)]
  apply tsum_congr
  intro t
  split_ifs <;> ring

lemma integral_stopped_sub_const (f : S → ℝ) (hf : Measurable f)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (a lam M : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M) :
    (∫ ω, discountedStoppedSum a (fun y => f y - lam) τ ω ∂μ) =
      (∫ ω, discountedStoppedSum a f τ ω ∂μ) -
        lam * (∫ ω, discountedStoppedSum a (fun _ => 1) τ ω ∂μ) := by
  simp_rw [stopped_sum_sub_const f τ _ a lam M ha ha1 hM hbound]
  rw [integral_sub (integrable_stopped_sum f hf τ hτ μ ha ha1 hM hbound)
    ((integrable_stopped_sum (fun _ : S => (1 : ℝ)) measurable_const τ hτ μ ha ha1
      (show (0 : ℝ) ≤ 1 by norm_num) (fun _ => by norm_num)).const_mul lam), integral_const_mul]

lemma stopped_discount_integral_upper (τ : (ℕ → S) → ℕ∞)
    (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (∫ ω, discountedStoppedSum a (fun _ : S => 1) τ ω ∂μ) ≤ 1 / (1 - a) := by
  apply le_trans (le_abs_self _)
  exact abs_integral_bounded μ _ _ (fun ω => stopped_sum_abs_bound (fun _ : S => 1) τ ω ha ha1
    (show (0 : ℝ) ≤ 1 by norm_num) (fun _ => by norm_num))

end
end AllocationIndices.Proof

end

/- Complete module: RetirementStopped -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma retirement_stopped_upper (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (g : S → U) (hg : D.IsFeasibleStationary g)
    (x : S) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hpos : ∀ ω, 1 ≤ τ ω) :
    (∫ ω, discountedStoppedSum a (fun y => D.reward y (g y) - (1 - a) * m) τ ω
      ∂markovChainMeasure (stationaryKernel D g) x) ≤ retirementBestExcess D a m x := by
  have hC0 : 0 ≤ C := (abs_nonneg m).trans hm
  have hf : ∀ y, |D.reward y (g y) - (1 - a) * m| ≤ R + |(1 - a) * m| := fun y => by
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (D.reward y (g y)) (-((1 - a) * m))).trans (add_le_add (hr y (g y)) le_rfl)
  have hbell : ∀ y, markovContinue (stationaryKernel D g) a
      (fun y => D.reward y (g y) - (1 - a) * m) (retirementSurplus D a m) y ≤
      retirementSurplus D a m y := by
    intro y
    rw [markovContinue_stationary_shift D a m R C ha hm hC hr]
    exact sub_le_sub_right (retirementContinue_le_value D a m R C ha hm hC hr y (g y) (hg y)) m
  have h := stopped_verification_upper (stationaryKernel D g) x a ha ha1
    (fun y => D.reward y (g y) - (1 - a) * m) (retirementSurplus D a m) τ hτ hpos
    (R + |(1 - a) * m|) (C + |m|) (by positivity) (by positivity) hf
    (retirementSurplus_bound D a m R C ha hm hC hr)
    (retirementSurplus_nonneg D a m R C ha hm hC hr) hbell
  rw [markovContinue_stationary_shift D a m R C ha hm hC hr] at h
  exact h.trans (sub_le_sub_right (Finset.le_sup' _ (hg x)) m)

lemma retirement_stopped_greedy_eq (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    (∫ ω, discountedStoppedSum a
      (fun y => D.reward y (retirementGreedy D a m y) - (1 - a) * m)
      (firstZero (retirementSurplus D a m)) ω
      ∂markovChainMeasure (stationaryKernel D (retirementGreedy D a m)) x) =
      retirementBestExcess D a m x := by
  have hC0 : 0 ≤ C := (abs_nonneg m).trans hm
  have hf : ∀ y, |D.reward y (retirementGreedy D a m y) - (1 - a) * m| ≤ R + |(1 - a) * m| := fun y => by
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (D.reward y (retirementGreedy D a m y)) (-((1 - a) * m))).trans
        (add_le_add (hr y _) le_rfl)
  have h := stopped_verification_eq (stationaryKernel D (retirementGreedy D a m)) x a ha ha1
    (fun y => D.reward y (retirementGreedy D a m y) - (1 - a) * m) (retirementSurplus D a m)
    (R + |(1 - a) * m|) (C + |m|) (by positivity) (by positivity) hf
    (retirementSurplus_bound D a m R C ha hm hC hr)
    (retirementSurplus_greedy_bellman D a m R C ha hm hC hr)
  rw [markovContinue_stationary_shift D a m R C ha hm hC hr] at h
  simpa only [retirementBestExcess, retirementGreedy_max] using h

end
end AllocationIndices.Proof

end

/- Complete module: SuperIndexOrder -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

omit [Countable S] [MeasurableSingletonClass S] in
lemma feasible_stationary_with_initial (D : DecisionProcess S U) (x : S) (u : U)
    (hu : u ∈ D.avail x) : ∃ g : S → U, D.IsFeasibleStationary g ∧ g x = u := by
  classical
  let g : S → U := fun y => (D.avail_nonempty y).choose
  refine ⟨Function.update g x u, ?_, by simp⟩
  intro y
  by_cases hy : y = x
  · subst y; simpa using hu
  · simp only [Function.update_of_ne hy]
    exact (D.avail_nonempty y).choose_spec

lemma superIndex_le_of_stationary_le (D : DecisionProcess S U) (a B : ℝ) (x : S) (u : U)
    (hu : u ∈ D.avail x)
    (h : ∀ g : S → U, D.IsFeasibleStationary g →
      gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x ≤ B) :
    superIndex D a x u ≤ B := by
  obtain ⟨g, hg, hgu⟩ := feasible_stationary_with_initial D x u hu
  let : Nonempty {g : S → U // D.IsFeasibleStationary g ∧ g x = u} := ⟨⟨g, hg, hgu⟩⟩
  exact ciSup_le (fun g => h g g.2.1)

lemma superIndexMax_le_of_stationary_le (D : DecisionProcess S U) (a B : ℝ) (x : S)
    (h : ∀ g : S → U, D.IsFeasibleStationary g →
      gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x ≤ B) :
    superIndexMax D a x ≤ B := by
  apply Finset.sup'_le
  intro u hu
  exact superIndex_le_of_stationary_le D a B x u hu h

lemma stationaryIndex_le_superIndexMax (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (g : S → U) (hg : D.IsFeasibleStationary g) (x : S) :
    gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x ≤ superIndexMax D a x := by
  have hb : BddAbove (Set.range (fun p : {g' : S → U // D.IsFeasibleStationary g' ∧ g' x = g x} =>
      gittinsIndex (stationaryKernel D p) (stationaryReward D p) a x)) := by
    refine ⟨R, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (abs_le.mp (gittinsIndex_abs_bound (stationaryKernel D p) (stationaryReward D p)
      (measurable_of_countable _) ha ha1 hR (fun y => hr y (p.val y)) x)).2
  have hs : gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x ≤ superIndex D a x (g x) :=
    le_ciSup hb ⟨g, hg, rfl⟩
  exact hs.trans (Finset.le_sup' _ (hg x))

lemma stopped_ratio_le_gittinsIndex (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (a R : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R)
    (hf : ∀ x, |f x| ≤ R) (x : S)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hpos : ∀ ω, 1 ≤ τ ω) :
    (∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum a (fun _ => 1) τ ω ∂markovChainMeasure P x) ≤
      gittinsIndex P f a x := by
  unfold gittinsIndex
  apply le_csSup
  swap
  · exact ⟨τ, hτ, hpos, rfl⟩
  refine ⟨R, ?_⟩
  rintro z ⟨σ, hσ, hσpos, rfl⟩
  exact (abs_le.mp (stopped_ratio_abs_bound f (measurable_of_countable _) σ hσ hσpos
    (markovChainMeasure P x) ha ha1 hR hf)).2


omit [Countable S] [MeasurableSingletonClass S] in
lemma gittinsIndex_le_of_ratios (P : Kernel S S) [IsMarkovKernel P] (f : S → ℝ)
    (a B : ℝ) (x : S)
    (h : ∀ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      (∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum a (fun _ => 1) τ ω ∂markovChainMeasure P x) ≤ B) :
    gittinsIndex P f a x ≤ B := by
  apply csSup_le
  · refine ⟨_, fun _ => 1, ?_, fun _ => le_rfl, rfl⟩
    intro n
    by_cases hn : (1 : ℕ∞) ≤ (n : ℕ∞) <;> simp [hn]
  · rintro z ⟨τ, hτ, hpos, rfl⟩
    exact h τ hτ hpos

end
end AllocationIndices.Proof

end

/- Complete module: RetirementIndex -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm Filter

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma ratio_upper_of_net_nonpos (N T a lam b : ℝ) (ha1 : a < 1)
    (hT : 1 ≤ T) (hTupper : T ≤ 1 / (1 - a)) (hb : b ≤ 0)
    (hnet : N - lam * T ≤ b) : N / T ≤ lam + (1 - a) * b := by
  have hTpos : 0 < T := by linarith
  have hTscaled : T * (1 - a) ≤ 1 := (le_div_iff₀ (by linarith : 0 < 1 - a)).mp hTupper
  have hbscaled := mul_le_mul_of_nonpos_left hTscaled hb
  apply (div_le_iff₀ hTpos).mpr
  nlinarith

lemma retirement_index_upper (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) (hb : retirementBestExcess D a m x ≤ 0) :
    superIndexMax D a x ≤ (1 - a) * m + (1 - a) * retirementBestExcess D a m x := by
  apply superIndexMax_le_of_stationary_le
  intro g hg
  apply gittinsIndex_le_of_ratios
  intro τ hτ hpos
  have hnet := retirement_stopped_upper D a m R C ha ha1 hR hm hC hr g hg x τ hτ hpos
  rw [integral_stopped_sub_const (fun y => D.reward y (g y)) (measurable_of_countable _)
    τ hτ _ a ((1 - a) * m) R ha ha1 hR (fun y => hr y (g y))] at hnet
  exact ratio_upper_of_net_nonpos _ _ a ((1 - a) * m) _ ha1
    (stopped_discount_integral_lower τ hτ hpos _ ha ha1)
    (stopped_discount_integral_upper τ _ a ha ha1) hb hnet

lemma retirement_greedy_ratio (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    ∃ N T : ℝ, 1 ≤ T ∧ N - (1 - a) * m * T = retirementBestExcess D a m x ∧
      N / T ≤ superIndexMax D a x := by
  let g := retirementGreedy D a m
  let τ := firstZero (retirementSurplus D a m)
  let μ := markovChainMeasure (stationaryKernel D g) x
  let N := ∫ ω, discountedStoppedSum a (stationaryReward D g) τ ω ∂μ
  let T := ∫ ω, discountedStoppedSum a (fun _ : S => 1) τ ω ∂μ
  have hτ := firstZero_stopping (retirementSurplus D a m)
  have hpos := firstZero_positive (retirementSurplus D a m)
  refine ⟨N, T, stopped_discount_integral_lower τ hτ hpos μ ha ha1, ?_, ?_⟩
  · have h := retirement_stopped_greedy_eq D a m R C ha ha1 hR hm hC hr x
    rw [integral_stopped_sub_const _ (measurable_of_countable _) τ hτ μ a ((1 - a) * m) R ha ha1 hR
      (fun y => hr y (g y))] at h
    exact h
  · exact (stopped_ratio_le_gittinsIndex (stationaryKernel D g) (stationaryReward D g) a R ha ha1 hR
      (fun y => hr y (g y)) x τ hτ hpos).trans
        (stationaryIndex_le_superIndexMax D a R ha ha1 hR hr g (retirementGreedy_feasible D a m) x)

lemma retirement_index_ge_iff (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    (1 - a) * m ≤ superIndexMax D a x ↔ 0 ≤ retirementBestExcess D a m x := by
  constructor
  · intro h
    by_contra hn
    have hb : retirementBestExcess D a m x < 0 := lt_of_not_ge hn
    have hu := retirement_index_upper D a m R C ha ha1 hR hm hC hr x hb.le
    have hneg := mul_neg_of_pos_of_neg (show 0 < 1 - a by linarith) hb
    linarith
  · intro hb
    obtain ⟨N, T, hT, heq, hle⟩ := retirement_greedy_ratio D a m R C ha ha1 hR hm hC hr x
    apply le_trans _ hle
    apply (le_div_iff₀ (show 0 < T by linarith)).mpr
    linarith

lemma retirement_index_le_iff (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    superIndexMax D a x ≤ (1 - a) * m ↔ retirementBestExcess D a m x ≤ 0 := by
  constructor
  · intro h
    by_contra hn
    have hb : 0 < retirementBestExcess D a m x := lt_of_not_ge hn
    obtain ⟨N, T, hT, heq, hle⟩ := retirement_greedy_ratio D a m R C ha ha1 hR hm hC hr x
    have hlt : (1 - a) * m < N / T := (lt_div_iff₀ (by linarith)).mpr (by linarith)
    linarith
  · intro hb
    have hu := retirement_index_upper D a m R C ha ha1 hR hm hC hr x hb
    have hneg := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - a by linarith) hb
    linarith

lemma retirement_active_of_index_ge (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) (hindex : (1 - a) * m ≤ superIndexMax D a x) :
    ∃ u ∈ D.avail x, retirementContinue D a m x u = retirementValue D a m x := by
  have hb := (retirement_index_ge_iff D a m R C ha ha1 hR hm hC hr x).mp hindex
  have hsup : m ≤ (D.avail x).sup' (D.avail_nonempty x) (retirementContinue D a m x) :=
    sub_nonneg.mp hb
  refine ⟨retirementGreedy D a m x, retirementGreedy_feasible D a m x, ?_⟩
  rw [retirementValue_bellman D a m R C ha hm hC hr, max_eq_right hsup, retirementGreedy_max]

lemma retirementValue_eq_of_index_le (D : DecisionProcess S U) (a m R C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) (hindex : superIndexMax D a x ≤ (1 - a) * m) :
    retirementValue D a m x = m := by
  have hb := (retirement_index_le_iff D a m R C ha ha1 hR hm hC hr x).mp hindex
  have hsup := sub_nonpos.mp hb
  rw [retirementValue_bellman D a m R C ha hm hC hr, max_eq_left hsup]

end
end AllocationIndices.Proof

end

/- Complete module: RetirementIndexBounds -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma superIndexMax_abs_bound (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    |superIndexMax D a x| ≤ R := by
  rw [abs_le]
  constructor
  · let g := retirementGreedy D a 0
    have hg := retirementGreedy_feasible D a 0
    have h := gittinsIndex_abs_bound (stationaryKernel D g) (stationaryReward D g)
      (measurable_of_countable _) ha ha1 hR (fun y => hr y (g y)) x
    exact (abs_le.mp h).1.trans (stationaryIndex_le_superIndexMax D a R ha ha1 hR hr g hg x)
  · apply superIndexMax_le_of_stationary_le
    intro g _
    exact (abs_le.mp (gittinsIndex_abs_bound (stationaryKernel D g) (stationaryReward D g)
      (measurable_of_countable _) ha ha1 hR (fun y => hr y (g y)) x)).2

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementValue_ge_self (D : DecisionProcess S U) (a m R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    m ≤ retirementValue D a m x := by
  obtain ⟨C, hm, hC⟩ := retirement_common_bound a R |m| ha1 (abs_nonneg m)
  exact retirementIter_le_value D a m R C ha hm hC hr 0 x

lemma retirementValue_eq_of_cutoff_le (D : DecisionProcess S U) (a m R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (x : S) (hm : superIndexMax D a x / (1 - a) ≤ m) : retirementValue D a m x = m := by
  obtain ⟨C, hmC, hC⟩ := retirement_common_bound a R |m| ha1 (abs_nonneg m)
  apply retirementValue_eq_of_index_le D a m R C ha ha1 hR hmC hC hr x
  have h := (div_le_iff₀ (show 0 < 1 - a by linarith)).mp hm
  nlinarith

lemma retirement_active_of_le_cutoff (D : DecisionProcess S U) (a m R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (x : S) (hm : m ≤ superIndexMax D a x / (1 - a)) :
    ∃ u ∈ D.avail x, retirementContinue D a m x u = retirementValue D a m x := by
  obtain ⟨C, hmC, hC⟩ := retirement_common_bound a R |m| ha1 (abs_nonneg m)
  apply retirement_active_of_index_ge D a m R C ha ha1 hR hmC hC hr x
  have h := (le_div_iff₀ (show 0 < 1 - a by linarith)).mp hm
  nlinarith

end
end AllocationIndices.Proof

end

/- Complete module: SFASStationaryOptimal -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U] {n : ℕ}

def deterministicSFAS (g : (Fin n → S) → Fin n × U) : SFASPolicy n S U where
  select t := Kernel.deterministic (fun h : SFASHistory n S U t => g h.2)
    (measurable_of_countable _)
  markov _ := inferInstance

lemma deterministicSFAS_feasible (D : DecisionProcess S U)
    (g : (Fin n → S) → Fin n × U) (hg : ∀ x, (g x).2 ∈ D.avail (x (g x).1)) :
    IsFeasiblePolicy D (deterministicSFAS g) := by
  intro t h
  simp [deterministicSFAS, Kernel.deterministic_apply, hg]

lemma deterministicSFAS_optimal (D : DecisionProcess S U) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (g : (Fin n → S) → Fin n × U) (hg : ∀ x, (g x).2 ∈ D.avail (x (g x).1))
    (hu : ∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x)
    (he : ∀ x, actionValue D a V x (g x) = V x) :
    IsOptimalSFASPolicy D a (deterministicSFAS g) ∧
      ∀ x, sfasValue D a (deterministicSFAS g) x = V x := by
  have hf := deterministicSFAS_feasible D g hg
  let : Nonempty {π : SFASPolicy n S U // IsFeasiblePolicy D π} :=
    ⟨⟨deterministicSFAS g, hf⟩⟩
  have hupper : ∀ (π : SFASPolicy n S U), IsFeasiblePolicy D π → ∀ x,
      sfasValue D a π x ≤ V x := by
    intro π hπ x
    simpa using feasible_policy_value_upper D π hπ a ha ha1 V R C 0 hr hV
      (fun x c hc => by simpa using hu x c hc) x
  have hvalue : ∀ x, sfasValue D a (deterministicSFAS g) x = V x := by
    intro x
    apply le_antisymm (hupper _ hf x)
    have hl := policy_value_lower D (deterministicSFAS g) a ha ha1 V R C 0 hr hV
      (fun t h => by simp [deterministicSFAS, Kernel.deterministic_apply, he]) x
    simpa using hl
  refine ⟨⟨hf, ?_⟩, hvalue⟩
  intro x
  rw [hvalue x]
  apply le_antisymm
  · have h := le_ciSup (f := fun π : {π : SFASPolicy n S U // IsFeasiblePolicy D π} =>
        sfasValue D a π x) (show BddAbove (Set.range fun π :
        {π : SFASPolicy n S U // IsFeasiblePolicy D π} => sfasValue D a π x) from
        ⟨V x, by rintro _ ⟨π, rfl⟩; exact hupper π π.2 x⟩)
        (⟨deterministicSFAS g, hf⟩ : {π : SFASPolicy n S U // IsFeasiblePolicy D π})
    simpa [hvalue] using h
  · apply ciSup_le
    intro π
    exact hupper π π.2 x

lemma exists_optimalSFAS_prescribed (D : DecisionProcess S U) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hu : ∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x)
    (he : ∀ x, ∃ c, c.2 ∈ D.avail (x c.1) ∧ actionValue D a V x c = V x)
    (x : Fin n → S) (c : Fin n × U) (hc : c.2 ∈ D.avail (x c.1))
    (hcV : actionValue D a V x c = V x) :
    ∃ π : SFASPolicy n S U, IsOptimalSFASPolicy D a π ∧
      (π.select 0) ((fun i => Fin.elim0 i),x) {c} = 1 := by
  classical
  choose g hg he using he
  let g' := Function.update g x c
  have hg' : ∀ y, (g' y).2 ∈ D.avail (y (g' y).1) := by
    intro y
    by_cases h : y = x
    · subst y; simpa [g'] using hc
    · simpa [g', Function.update_of_ne h] using hg y
  have he' : ∀ y, actionValue D a V y (g' y) = V y := by
    intro y
    by_cases h : y = x
    · subst y; simpa [g'] using hcV
    · simpa [g', Function.update_of_ne h] using he y
  refine ⟨deterministicSFAS g',
    (deterministicSFAS_optimal D a ha ha1 V R C hr hV g' hg' hu he').1, ?_⟩
  simp [deterministicSFAS, Kernel.deterministic_apply, g']

end
end AllocationIndices.Proof

end

/- Complete module: SFASJointProcess -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U] {n : ℕ}

def jointDecisionProcess (D : DecisionProcess S U) [NeZero n] :
    DecisionProcess (Fin n → S) (Fin n × U) := by
  classical
  exact {
  step c := Kernel.mk (fun x => (D.step c.2 (x c.1)).map (Function.update x c.1))
    (measurable_of_countable _)
  reward x c := D.reward (x c.1) c.2
  avail x := Finset.univ.filter (fun c => c.2 ∈ D.avail (x c.1))
  avail_nonempty x := by
    obtain ⟨u, hu⟩ := D.avail_nonempty (x 0)
    exact ⟨(0,u), by simpa using hu⟩
  markov c := ⟨fun x => Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩ }

omit [MeasurableSpace U] [MeasurableSingletonClass U] in
lemma jointDecisionProcess_actionValue (D : DecisionProcess S U) [NeZero n]
    (a m : ℝ) (x : Fin n → S) (c : Fin n × U) :
    retirementContinue (jointDecisionProcess D) a m x c =
      actionValue D a (retirementValue (jointDecisionProcess D) a m) x c := by
  unfold retirementContinue actionValue
  congr 1
  congr 1
  change (∫ y, retirementValue (jointDecisionProcess D) a m y
    ∂(D.step c.2 (x c.1)).map (Function.update x c.1)) = _
  exact integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable

lemma exists_optimalSFAS_of_bound (D : DecisionProcess S U) [NeZero n]
    (a m R C : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hm : |m| ≤ C) (hC : R + a * C ≤ C)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hmlow : m < -R / (1-a)) :
    ∃ π : SFASPolicy n S U, IsOptimalSFASPolicy D a π := by
  let J := jointDecisionProcess (n := n) D
  let V := retirementValue J a m
  have hj : ∀ x c, |J.reward x c| ≤ R := fun x c => hr _ _
  have hv : ∀ x, |V x| ≤ C := retirementValue_bound J a m R C ha hm hC hj
  have he : ∀ x, ∃ c, c ∈ J.avail x ∧ retirementContinue J a m x c = V x := by
    intro x
    obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_sup' (J.avail_nonempty x)
      (retirementContinue J a m x)
    refine ⟨c, hc, ?_⟩
    exact he.symm.trans (retirementValue_no_retirement J a m R C ha ha1 hm hC hj hmlow x).symm
  choose g hg he using he
  have hg' : ∀ x, (g x).2 ∈ D.avail (x (g x).1) := by
    intro x
    simpa [J, jointDecisionProcess] using hg x
  have hu : ∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x := by
    intro x c hc
    rw [← jointDecisionProcess_actionValue D a m x c]
    exact retirementContinue_le_value J a m R C ha hm hC hj x c
      (by simpa [J, jointDecisionProcess] using hc)
  have hgval : ∀ x, actionValue D a V x (g x) = V x := by
    intro x
    rw [← jointDecisionProcess_actionValue D a m x (g x)]
    exact he x
  exact ⟨deterministicSFAS g, (deterministicSFAS_optimal D a ha ha1 V R C hr hv
    g hg' hu hgval).1⟩

lemma exists_optimalSFAS (D : DecisionProcess S U) [NeZero n]
    (hD : D.BoundedRewards) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    ∃ π : SFASPolicy n S U, IsOptimalSFASPolicy D a π := by
  obtain ⟨R, hr⟩ := hD
  let m := -R / (1-a) - 1
  obtain ⟨C, hm, hC⟩ := retirement_common_bound a R |m| ha1 (abs_nonneg m)
  exact exists_optimalSFAS_of_bound D a m R C ha ha1 hm hC hr (by dsimp [m]; linarith)

end
end AllocationIndices.Proof

end

/- Complete module: RetirementUniqueness -/
section

open MeasureTheory ProbabilityTheory Filter
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma retirement_sub_le_super (D : DecisionProcess S U) (a m B C : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (V W : S → ℝ)
    (hV : ∀ x, |V x| ≤ B) (hW : ∀ x, |W x| ≤ C)
    (hsub : ∀ x, V x ≤ max m ((D.avail x).sup' (D.avail_nonempty x)
      (fun u => D.reward x u + a * ∫ y, V y ∂D.step u x)))
    (hmW : ∀ x, m ≤ W x)
    (hsuper : ∀ x u, u ∈ D.avail x → D.reward x u + a * ∫ y, W y ∂D.step u x ≤ W x)
    (x : S) : V x ≤ W x := by
  let : Nonempty S := ⟨x⟩
  let M := ⨆ y, V y - W y
  have hb : BddAbove (Set.range fun y => V y-W y) := by
    refine ⟨B+C, ?_⟩
    rintro _ ⟨y,rfl⟩
    linarith [(abs_le.mp (hV y)).2, (abs_le.mp (hW y)).1]
  have hm : ∀ y, V y - W y ≤ M := fun y => le_ciSup hb y
  have hupper : ∀ y, V y - W y ≤ max 0 (a*M) := by
    intro y
    have hq : ∀ u ∈ D.avail y, D.reward y u + a * ∫ z, V z ∂D.step u y ≤
        W y + a*M := by
      intro u hu
      have hi := integral_mono_ae (μ := D.step u y)
        (integrable_bounded_countable _ _ B hV)
        ((integrable_bounded_countable _ _ C hW).add (integrable_const M))
        (Eventually.of_forall fun z => show V z ≤ W z + M by linarith [hm z])
      simp only [Pi.add_apply] at hi
      rw [integral_add (integrable_bounded_countable _ _ C hW) (integrable_const M)] at hi
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
      have hi' := mul_le_mul_of_nonneg_left hi ha
      linarith [hsuper y u hu]
    have hq' := Finset.sup'_le (D.avail_nonempty y) _ hq
    have hh : max m ((D.avail y).sup' (D.avail_nonempty y)
        (fun u => D.reward y u + a * ∫ z, V z ∂D.step u y)) ≤ W y + max 0 (a*M) := by
      apply max_le
      · linarith [hmW y, le_max_left (0:ℝ) (a*M)]
      · linarith [le_max_right (0:ℝ) (a*M)]
    linarith [hsub y]
  have hM : M ≤ max 0 (a*M) := ciSup_le hupper
  have hnonpos : M ≤ 0 := by
    by_contra hh
    have hpos : 0 < M := lt_of_not_ge hh
    rw [max_eq_right (mul_nonneg ha hpos.le)] at hM
    nlinarith
  linarith [hm x]

end
end AllocationIndices.Proof

end

/- Complete module: SFASStandardSlice -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Fintype U] [Nonempty U] [MeasurableSingletonClass U]

instance sumUnitMeasurableSingleton : MeasurableSingletonClass (S ⊕ Unit) := by
  constructor
  intro x
  cases x <;> simp [measurableSet_sum_iff, Set.preimage]

def standardState (x : S) : Fin 2 → S ⊕ Unit := ![Sum.inl x, Sum.inr ()]

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma standard_update_left (x y : S) :
    Function.update (standardState x) 0 (Sum.inl y) = standardState y := by
  funext i
  fin_cases i <;> simp [standardState]

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
lemma standard_update_right (x : S) :
    Function.update (standardState x) 1 (Sum.inr ()) = standardState x := by
  funext i
  fin_cases i <;> simp [standardState]

omit [MeasurableSpace U] [MeasurableSingletonClass U] in
lemma standard_action_left (D : DecisionProcess S U) (a lam : ℝ)
    (V : (Fin 2 → S ⊕ Unit) → ℝ) (x : S) (u : U) :
    actionValue (withStandard D lam) a V (standardState x) (0,u) =
      D.reward x u + a * ∫ y, V (standardState y) ∂D.step u x := by
  unfold actionValue
  simp only [standardState, Matrix.cons_val_zero, withStandard, Sum.elim_inl]
  change D.reward x u + a * (∫ y, V (Function.update (standardState x) 0 y)
    ∂(D.step u).map Sum.inl x) = _
  rw [Kernel.map_apply _ measurable_inl]
  rw [integral_map_of_stronglyMeasurable measurable_inl
    (measurable_of_countable _).stronglyMeasurable]
  simp only [standard_update_left]
  rfl

omit [MeasurableSpace U] [MeasurableSingletonClass U] in
lemma standard_action_right (D : DecisionProcess S U) (a lam : ℝ)
    (V : (Fin 2 → S ⊕ Unit) → ℝ) (x : S) (u : U) :
    actionValue (withStandard D lam) a V (standardState x) (1,u) =
      lam + a * V (standardState x) := by
  unfold actionValue
  simp only [standardState, Matrix.cons_val_one, Matrix.cons_val_zero, withStandard,
    Sum.elim_inr]
  change lam + a * (∫ y, V (Function.update (standardState x) 1 y)
    ∂(Kernel.const Unit (Measure.dirac ())).map Sum.inr ()) = _
  rw [Kernel.map_apply _ measurable_inr]
  rw [integral_map_of_stronglyMeasurable measurable_inr
    (measurable_of_countable _).stronglyMeasurable]
  simp only [Kernel.const_apply, integral_dirac]
  rw [standard_update_right]
  rfl

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Fintype U] [Nonempty U] [MeasurableSingletonClass U] in
lemma standard_bellman_scalar (a lam v q : ℝ) (ha : a < 1)
    (h : v = max (lam + a*v) q) : v = max (lam/(1-a)) q := by
  have hd : 0 < 1-a := by linarith
  have hm : lam/(1-a) ≤ v := by
    apply (div_le_iff₀ hd).2
    have hh := le_max_left (lam+a*v) q
    rw [← h] at hh
    nlinarith
  have hq : q ≤ v := by rw [h]; exact le_max_right _ _
  apply le_antisymm _ (max_le hm hq)
  rcases le_total (lam+a*v) q with he | he
  · rw [max_eq_right he] at h
    rw [h]
    exact le_max_right _ _
  · rw [max_eq_left he] at h
    have hv : v = lam/(1-a) := (eq_div_iff hd.ne').2 (by nlinarith)
    rw [hv]
    exact le_max_left _ _

omit [MeasurableSpace U] [MeasurableSingletonClass U] in
lemma standard_slice_bellman (D : DecisionProcess S U) (a lam : ℝ) (ha1 : a < 1)
    (V : (Fin 2 → S ⊕ Unit) → ℝ)
    (hu : ∀ x c, c.2 ∈ (withStandard D lam).avail (x c.1) →
      actionValue (withStandard D lam) a V x c ≤ V x)
    (he : ∀ x, ∃ c, c.2 ∈ (withStandard D lam).avail (x c.1) ∧
      actionValue (withStandard D lam) a V x c = V x) (x : S) :
    V (standardState x) = max (lam/(1-a))
      ((D.avail x).sup' (D.avail_nonempty x)
        (fun u => D.reward x u + a * ∫ y, V (standardState y) ∂D.step u x)) := by
  apply standard_bellman_scalar a lam _ _ ha1
  have hleft : lam + a*V (standardState x) ≤ V (standardState x) := by
    have h := hu (standardState x) (1,Classical.arbitrary U) (by
      simp [withStandard, standardState])
    simpa only [standard_action_right] using h
  have hright : (D.avail x).sup' (D.avail_nonempty x)
      (fun u => D.reward x u + a * ∫ y, V (standardState y) ∂D.step u x) ≤
      V (standardState x) := by
    apply Finset.sup'_le
    intro u hu'
    have h := hu (standardState x) (0,u) (by simpa [withStandard, standardState] using hu')
    simpa only [standard_action_left] using h
  apply le_antisymm _ (max_le hleft hright)
  obtain ⟨⟨i,u⟩, hc, he⟩ := he (standardState x)
  fin_cases i
  · change actionValue (withStandard D lam) a V (standardState x) (0,u) = _ at he
    rw [standard_action_left] at he
    apply le_trans (le_of_eq he.symm)
    apply le_trans (Finset.le_sup' (fun u => D.reward x u + a * ∫ y, V (standardState y) ∂D.step u x)
      (show u ∈ D.avail x by simpa [withStandard, standardState] using hc))
    exact le_max_right _ _
  · change actionValue (withStandard D lam) a V (standardState x) (1,u) = _ at he
    rw [standard_action_right] at he
    exact (le_of_eq he.symm).trans (le_max_left _ _)

omit [MeasurableSpace U] [MeasurableSingletonClass U] in
lemma standard_slice_eq_retirement (D : DecisionProcess S U) (hD : D.BoundedRewards)
    (a lam B : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (V : (Fin 2 → S ⊕ Unit) → ℝ) (hV : ∀ x, |V x| ≤ B)
    (hu : ∀ x c, c.2 ∈ (withStandard D lam).avail (x c.1) →
      actionValue (withStandard D lam) a V x c ≤ V x)
    (he : ∀ x, ∃ c, c.2 ∈ (withStandard D lam).avail (x c.1) ∧
      actionValue (withStandard D lam) a V x c = V x) (x : S) :
    V (standardState x) = retirementValue D a (lam/(1-a)) x := by
  obtain ⟨R,hr⟩ := hD
  let m := lam/(1-a)
  obtain ⟨C, hm, hC⟩ := retirement_common_bound a R |m| ha1 (abs_nonneg m)
  have hb := retirementValue_bound D a m R C ha hm hC hr
  have hbell := standard_slice_bellman D a lam ha1 V hu he
  have hmV : ∀ y, m ≤ V (standardState y) := by
    intro y
    rw [hbell y]
    exact le_max_left _ _
  have hsV : ∀ y u, u ∈ D.avail y → D.reward y u +
      a * ∫ z, V (standardState z) ∂D.step u y ≤ V (standardState y) := by
    intro y u hc
    have hh := hu (standardState y) (0,u) (by simpa [withStandard, standardState] using hc)
    simpa only [standard_action_left] using hh
  apply le_antisymm
  · apply retirement_sub_le_super D a m B C ha ha1 (fun y => V (standardState y))
      (retirementValue D a m) (fun y => hV _) hb
      (fun y => (hbell y).le)
    · intro y
      exact retirementIter_le_value D a m R C ha hm hC hr 0 y
    · exact retirementContinue_le_value D a m R C ha hm hC hr
  · exact retirementValue_le_super D a m R C B ha hm hC hr _
      (fun y => hV _) hmV hsV x

end
end AllocationIndices.Proof

end

/- Complete module: SFASBellmanExistence -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U] {n : ℕ}

omit [MeasurableSpace U] [MeasurableSingletonClass U] in
lemma exists_bounded_sfas_bellman (D : DecisionProcess S U) [NeZero n]
    (hD : D.BoundedRewards) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    ∃ (V : (Fin n → S) → ℝ) (B : ℝ), (∀ x, |V x| ≤ B) ∧
      (∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x) ∧
      (∀ x, ∃ c, c.2 ∈ D.avail (x c.1) ∧ actionValue D a V x c = V x) := by
  obtain ⟨R, hr⟩ := hD
  let m := -R/(1-a)-1
  obtain ⟨C, hm, hC⟩ := retirement_common_bound a R |m| ha1 (abs_nonneg m)
  let J := jointDecisionProcess (n := n) D
  let V := retirementValue J a m
  have hj : ∀ x c, |J.reward x c| ≤ R := fun x c => hr _ _
  refine ⟨V,C,retirementValue_bound J a m R C ha hm hC hj, ?_, ?_⟩
  · intro x c hc
    rw [← jointDecisionProcess_actionValue D a m x c]
    exact retirementContinue_le_value J a m R C ha hm hC hj x c
      (by simpa [J, jointDecisionProcess] using hc)
  · intro x
    obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_sup' (J.avail_nonempty x)
      (retirementContinue J a m x)
    refine ⟨c, by simpa [J, jointDecisionProcess] using hc, ?_⟩
    rw [← jointDecisionProcess_actionValue D a m x c]
    exact he.symm.trans (retirementValue_no_retirement J a m R C ha ha1 hm hC hj
      (by dsimp [m]; linarith) x).symm

end
end AllocationIndices.Proof

end

/- Complete module: SFASFirstStep -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section

lemma discounted_sequence_first_upper (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (r v : ℕ → ℝ) (R C : ℝ) (hr : ∀ t, |r t| ≤ R) (hv : ∀ t, |v t| ≤ C)
    (hstep : ∀ t, r (t+1) + a * v (t+2) ≤ v (t+1)) :
    (∑' t, a^t*r t) ≤ r 0 + a*v 1 := by
  have h := discounted_sequence_upper a ha ha1 (fun t => r (t+1))
    (fun t => v (t+1)) R C 0 (fun t => hr _) (fun t => hv _)
    (fun t => by simpa [Nat.add_assoc] using hstep t)
  simp only [zero_div, add_zero, zero_add] at h
  have hs := summable_discounted_bounded a ha ha1 r R hr
  have he := hs.tsum_eq_zero_add
  simp only [pow_zero, one_mul] at he
  rw [he]
  have ht : (∑' t, a^(t+1)*r (t+1)) = a * ∑' t, a^t*r (t+1) := by
    rw [← tsum_mul_left]
    congr 1
    funext t
    rw [pow_succ]
    ring
  rw [ht]
  exact add_le_add_right (mul_le_mul_of_nonneg_left h ha) _

variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U] {n : ℕ}

lemma policy_first_step_upper (D : DecisionProcess S U) (π : SFASPolicy n S U)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hb : ∀ t (h : SFASHistory n S U t),
      ∀ᵐ c ∂π.select t h, actionValue D a V h.2 c ≤ V h.2)
    (x : Fin n → S) :
    sfasValue D a π x ≤ ∫ c, actionValue D a V x c
      ∂π.select 0 ((fun i => Fin.elim0 i), x) := by
  have hs := discounted_sequence_first_upper a ha ha1 (sfasRoundReward D π x)
    (stateExpectation D π V x) R C (roundReward_bound D π R hr x)
    (stateExpectation_bound D π V C hV x) (fun t => by
      simpa using policy_step_upper D π a V R C 0 hr hV
        (fun t h => by simpa using hb t h) x (t+1))
  change sfasValue D a π x ≤ _ at hs
  rw [reward_potential_step D π a V R C hr hV x 0] at hs
  simpa [sfasMeasure] using hs

end
end AllocationIndices.Proof

end

/- Complete module: SFASOptimalAction -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U] {n : ℕ}

lemma optimal_value_eq_bellman (D : DecisionProcess S U) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hu : ∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x)
    (he : ∀ x, ∃ c, c.2 ∈ D.avail (x c.1) ∧ actionValue D a V x c = V x)
    (π : SFASPolicy n S U) (hπ : IsOptimalSFASPolicy D a π) (x : Fin n → S) :
    sfasValue D a π x = V x := by
  choose g hg he using he
  obtain ⟨ho,hv⟩ := deterministicSFAS_optimal D a ha ha1 V R C hr hV g hg hu he
  exact (hπ.2 x).trans ((ho.2 x).symm.trans (hv x))

lemma optimal_first_action_lower (D : DecisionProcess S U) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hu : ∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x)
    (he : ∀ x, ∃ c, c.2 ∈ D.avail (x c.1) ∧ actionValue D a V x c = V x)
    (π : SFASPolicy n S U) (hπ : IsOptimalSFASPolicy D a π) (x : Fin n → S) :
    V x ≤ ∫ c, actionValue D a V x c ∂π.select 0 ((fun i => Fin.elim0 i),x) := by
  rw [← optimal_value_eq_bellman D a ha ha1 V R C hr hV hu he π hπ x]
  apply policy_first_step_upper D π a ha ha1 V R C hr hV _ x
  intro t h
  have hc : ∀ᵐ c ∂π.select t h, c.2 ∈ D.avail (h.2 c.1) := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (Set.Countable.measurableSet (Set.to_countable _))).2 (hπ.1 t h)
  filter_upwards [hc] with c hc
  exact hu h.2 c hc

lemma optimal_forced_action_eq (D : DecisionProcess S U) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (V : (Fin n → S) → ℝ) (R C : ℝ)
    (hr : ∀ x u, |D.reward x u| ≤ R) (hV : ∀ x, |V x| ≤ C)
    (hu : ∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x)
    (he : ∀ x, ∃ c, c.2 ∈ D.avail (x c.1) ∧ actionValue D a V x c = V x)
    (π : SFASPolicy n S U) (hπ : IsOptimalSFASPolicy D a π)
    (x : Fin n → S) (c : Fin n × U) (hc : c.2 ∈ D.avail (x c.1))
    (hforce : (π.select 0) ((fun i => Fin.elim0 i),x) {c} = 1) :
    actionValue D a V x c = V x := by
  apply le_antisymm (hu x c hc)
  have hl := optimal_first_action_lower D a ha ha1 V R C hr hV hu he π hπ x
  have hae : ∀ᵐ d ∂π.select 0 ((fun i => Fin.elim0 i),x), d = c := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (measurableSet_singleton c)).2 hforce
  have hi : (∫ d, actionValue D a V x d ∂π.select 0 ((fun i => Fin.elim0 i),x)) =
      actionValue D a V x c := by
    calc
      _ = ∫ _, actionValue D a V x c ∂π.select 0 ((fun i => Fin.elim0 i),x) :=
        integral_congr_ae (hae.mono fun d hd => by rw [hd])
      _ = _ := by simp
  rwa [hi] at hl

end
end AllocationIndices.Proof

end

/- Complete module: ConditionDRetirement -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Fintype U] [Nonempty U] [MeasurableSingletonClass U]

omit [Countable S] [MeasurableSingletonClass S] [MeasurableSpace U]
  [MeasurableSingletonClass U] in
lemma withStandard_boundedRewards (D : DecisionProcess S U) (hD : D.BoundedRewards) (lam : ℝ) :
    (withStandard D lam).BoundedRewards := by
  obtain ⟨R,hr⟩ := hD
  refine ⟨max R |lam|, ?_⟩
  intro x u
  cases x with
  | inl x => exact (hr x u).trans (le_max_left _ _)
  | inr x => exact le_max_right _ _

lemma conditionD_retirementContinue (D : DecisionProcess S U) (hD : D.BoundedRewards)
    (a m : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (g : S → U) (hg : IsConditionDControl D a g)
    (x : S) (hactive : ∃ u, u ∈ D.avail x ∧
      retirementContinue D a m x u = retirementValue D a m x) :
    retirementContinue D a m x (g x) = retirementValue D a m x := by
  let lam := (1-a)*m
  have hm : lam/(1-a) = m := by dsimp [lam]; exact mul_div_cancel_left₀ m (by linarith)
  let E := withStandard D lam
  have hE := withStandard_boundedRewards D hD lam
  obtain ⟨V,B,hV,hu,he⟩ := exists_bounded_sfas_bellman (n := 2) E hE a ha ha1
  have hv : ∀ y, V (standardState y) = retirementValue D a m y := by
    intro y
    simpa only [hm] using standard_slice_eq_retirement D hD a lam B ha ha1 V hV hu he y
  obtain ⟨R,hr⟩ := hE
  have hcont : ∀ y u, actionValue E a V (standardState y) (0,u) =
      retirementContinue D a m y u := by
    intro y u
    rw [standard_action_left]
    simp only [hv, retirementContinue]
  obtain ⟨u,hux,huxV⟩ := hactive
  have hc : (0,u).2 ∈ E.avail ((standardState x) (0,u).1) := by
    simpa [E,withStandard,standardState] using hux
  obtain ⟨π,hπ,hforce⟩ := exists_optimalSFAS_prescribed E a ha ha1 V R B hr hV hu he
    (standardState x) (0,u) hc (by rw [hcont,huxV,hv])
  have hselect : OptimalToSelect D a lam x := by
    refine ⟨π,hπ,le_antisymm prob_le_one ?_⟩
    have hmono := measure_mono (μ := π.select 0 (standardStart x)) (show ({(0,u)} : Set (Fin 2 × U)) ⊆ {c | c.1=0} by
      intro c hc; rcases hc with rfl; rfl)
    rw [← hforce]
    exact hmono
  obtain ⟨ρ,hρ,hforceρ⟩ := hg.2 x lam hselect
  have hgc : (0,g x).2 ∈ E.avail ((standardState x) (0,g x).1) := by
    simpa [E,withStandard,standardState] using hg.1 x
  have hh := optimal_forced_action_eq E a ha ha1 V R B hr hV hu he ρ hρ
    (standardState x) (0,g x) hgc hforceρ
  rwa [hcont,hv] at hh

end
end AllocationIndices.Proof

end

/- Complete module: RetirementFamily -/
section

open MeasureTheory ProbabilityTheory

namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

def retirementCutoff (D : DecisionProcess S U) (a : ℝ) (x : S) : ℝ :=
  superIndexMax D a x / (1 - a)

lemma retirementCutoff_bounds (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R) (x : S) :
    -R / (1 - a) ≤ retirementCutoff D a x ∧ retirementCutoff D a x ≤ R / (1 - a) := by
  have h := abs_le.mp (superIndexMax_abs_bound D a R ha ha1 hR hr x)
  exact ⟨div_le_div_of_nonneg_right h.1 (by linarith),
    div_le_div_of_nonneg_right h.2 (by linarith)⟩

omit [Countable S] [MeasurableSingletonClass S] in
lemma retirementValue_interval_bound (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : ∀ x u, |D.reward x u| ≤ R)
    (m : ℝ) (hmL : -R / (1 - a) ≤ m) (hmH : m ≤ R / (1 - a)) (x : S) :
    |retirementValue D a m x| ≤ R / (1 - a) := by
  have hm : |m| ≤ R / (1 - a) := abs_le.mpr ⟨by simpa only [neg_div] using hmL, hmH⟩
  have hC : R + a * (R / (1 - a)) ≤ R / (1 - a) := by
    have h := div_mul_cancel₀ R (ne_of_gt (show 0 < 1 - a by linarith))
    nlinarith
  exact retirementValue_bound D a m R (R / (1 - a)) ha hm hC hr x

lemma retirementValue_above_cutoff (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (x : S) (m : ℝ) (hm : retirementCutoff D a x ≤ m) : retirementValue D a m x = m :=
  retirementValue_eq_of_cutoff_le D a m R ha ha1 hR hr x hm

lemma retirementContinue_monotone (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hr : ∀ x u, |D.reward x u| ≤ R)
    (x : S) (u : U) : Monotone (fun m => retirementContinue D a m x u) := by
  intro m q hmq
  obtain ⟨C, hB, hC⟩ := retirement_common_bound a R (|m| + |q|) ha1 (by positivity)
  have hm : |m| ≤ C := by linarith [abs_nonneg q]
  have hq : |q| ≤ C := by linarith [abs_nonneg m]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ ha
  apply integral_mono_ae
    (integrable_bounded_countable _ _ C (retirementValue_bound D a m R C ha hm hC hr))
    (integrable_bounded_countable _ _ C (retirementValue_bound D a q R C ha hq hC hr))
  exact Filter.Eventually.of_forall (fun y => retirementValue_monotone D a R ha ha1 hr y hmq)

variable [MeasurableSpace U] [Fintype U] [Nonempty U] [MeasurableSingletonClass U]

lemma conditionD_below_cutoff (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (g : S → U) (hg : IsConditionDControl D a g) (x : S) (m : ℝ)
    (hm : m ≤ retirementCutoff D a x) :
    retirementContinue D a m x (g x) = retirementValue D a m x := by
  apply conditionD_retirementContinue D ⟨R, hr⟩ a m ha ha1 g hg x
  exact retirement_active_of_le_cutoff D a m R ha ha1 hR hr x hm

lemma conditionD_near_cutoff_sharp (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (g : S → U) (hg : IsConditionDControl D a g) (x : S) (m h : ℝ)
    (hh : 0 ≤ h) (hm : m ≤ retirementCutoff D a x + h) :
    retirementValue D a m x - retirementContinue D a m x (g x) ≤ h := by
  by_cases hmc : m ≤ retirementCutoff D a x
  · rw [conditionD_below_cutoff D a R ha ha1 hR hr g hg x m hmc, sub_self]
    exact hh
  · have hcm : retirementCutoff D a x ≤ m := (lt_of_not_ge hmc).le
    have hcont := retirementContinue_monotone D a R ha ha1 hr x (g x) hcm
    have heq := conditionD_below_cutoff D a R ha ha1 hR hr g hg x (retirementCutoff D a x) le_rfl
    have hlip := retirementValue_lipschitz D a R ha ha1 hr x m (retirementCutoff D a x)
    rw [abs_of_nonneg (sub_nonneg.mpr hcm)] at hlip
    have hdiff := (le_abs_self _).trans hlip
    linarith

lemma conditionD_near_cutoff (D : DecisionProcess S U) (a R : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 ≤ R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (g : S → U) (hg : IsConditionDControl D a g) (x : S) (m h : ℝ)
    (hh : 0 ≤ h) (hm : m ≤ retirementCutoff D a x + h) :
    retirementValue D a m x - retirementContinue D a m x (g x) ≤ (1 + a) * h := by
  have hsharp := conditionD_near_cutoff_sharp D a R ha ha1 hR hr g hg x m h hh hm
  nlinarith

end
end AllocationIndices.Proof

end

/- Complete module: SFASRetirementPotential -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Fintype U] [Nonempty U] [MeasurableSingletonClass U] {n : ℕ}

lemma exists_retirement_mesh_potential (D : DecisionProcess S U) (a R h : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hR : 0 < R) (hr : ∀ x u, |D.reward x u| ≤ R)
    (g : S → U) (hg : IsConditionDControl D a g) (N : ℕ) (hN : 0 < N) (hh : 0 < h)
    (hmesh : meshNode (-R/(1-a)) h N = R/(1-a)) :
    ∃ (V : (Fin n → S) → ℝ) (B : ℝ), (∀ x, |V x| ≤ B) ∧
      (∀ x (i : Fin n) u, u ∈ D.avail (x i) → actionValue D a V x (i,u) ≤ V x+2*h) ∧
      (∀ x (i : Fin n), (∀ j, superIndexMax D a (x j) ≤ superIndexMax D a (x i)) →
        V x-4*h ≤ actionValue D a V x (i,g (x i))) := by
  have hden : 0 < 1-a := by linarith
  have hC : R + a*(R/(1-a)) ≤ R/(1-a) := by
    have heq := div_mul_cancel₀ R hden.ne'
    nlinarith
  obtain ⟨V,B,hV,hu,hl⟩ := exists_whittle_mesh_potential (n := n) D a (-R/(1-a)) h (R/(1-a))
    ha ha1.le hh N hN (fun x m => retirementValue D a m x) (retirementCutoff D a) g
    (retirementValue_monotone D a R ha ha1 hr)
    (retirementValue_lipschitz D a R ha ha1 hr)
    (retirementValue_convex D a R ha ha1 hr)
    (fun x => by
      rw [hmesh]
      exact retirementValue_above_cutoff D a R ha ha1 hR.le hr x _
        (retirementCutoff_bounds D a R ha ha1 hR.le hr x).2)
    (fun x => (retirementCutoff_bounds D a R ha ha1 hR.le hr x).1)
    (retirementValue_above_cutoff D a R ha ha1 hR.le hr)
    (fun x m hmL hmH => retirementValue_interval_bound D a R ha ha1 hr m hmL
      (by simpa only [hmesh] using hmH) x)
    (fun x u m hux hmL hmH => by
      have hm : |m| ≤ R/(1-a) := abs_le.mpr ⟨by simpa only [neg_div] using hmL,
        by simpa only [hmesh] using hmH⟩
      exact retirementContinue_le_value D a m R (R/(1-a)) ha hm hC hr x u hux)
    (fun x m _ _ hmc => by
      have heq := conditionD_near_cutoff D a R ha ha1 hR.le hr g hg x m h hh.le hmc
      dsimp [retirementContinue] at heq
      linarith)
  refine ⟨V,B,hV,hu,?_⟩
  intro x i hmax
  apply hl x i
  intro j
  exact div_le_div_of_nonneg_right (hmax j) hden.le

end
end AllocationIndices.Proof

end

/- Complete module: SFASApproximateOptimal -/
section

open MeasureTheory ProbabilityTheory
namespace AllocationIndices.Proof
noncomputable section
variable {S U : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U] {n : ℕ}

lemma optimalSFAS_of_approximate_bellman (D : DecisionProcess S U) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (R : ℝ) (hr : ∀ x u, |D.reward x u| ≤ R)
    (π : SFASPolicy n S U) (hπ : IsFeasiblePolicy D π)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (V : (Fin n → S) → ℝ) (B : ℝ),
      (∀ x, |V x| ≤ B) ∧
      (∀ x c, c.2 ∈ D.avail (x c.1) → actionValue D a V x c ≤ V x+ε) ∧
      (∀ t (h : SFASHistory n S U t),
        ∀ᵐ c ∂π.select t h, V h.2-ε ≤ actionValue D a V h.2 c)) :
    IsOptimalSFASPolicy D a π := by
  have hdom : ∀ (ρ : SFASPolicy n S U), IsFeasiblePolicy D ρ → ∀ x,
      sfasValue D a ρ x ≤ sfasValue D a π x := by
    intro ρ hρ x
    by_contra hnot
    have hgap : 0 < sfasValue D a ρ x - sfasValue D a π x := by linarith
    let ε := (sfasValue D a ρ x - sfasValue D a π x)*(1-a)/4
    have heps : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨V,B,hV,hu,hl⟩ := happrox ε heps
    have hρv := feasible_policy_value_upper D ρ hρ a ha ha1 V R B ε hr hV hu x
    have hπv := policy_value_lower D π a ha ha1 V R B ε hr hV hl x
    have heq : ε/(1-a) = (sfasValue D a ρ x - sfasValue D a π x)/4 := by
      dsimp [ε]
      field_simp [show (1-a) ≠ 0 by linarith]
    rw [heq] at hρv hπv
    linarith
  refine ⟨hπ, ?_⟩
  intro x
  let : Nonempty {ρ : SFASPolicy n S U // IsFeasiblePolicy D ρ} := ⟨⟨π,hπ⟩⟩
  apply le_antisymm
  · exact le_ciSup (show BddAbove (Set.range fun ρ :
        {ρ : SFASPolicy n S U // IsFeasiblePolicy D ρ} => sfasValue D a ρ x) from
        ⟨sfasValue D a π x, by rintro _ ⟨ρ,rfl⟩; exact hdom ρ ρ.2 x⟩)
      (⟨π,hπ⟩ : {ρ : SFASPolicy n S U // IsFeasiblePolicy D ρ})
  · exact ciSup_le (fun ρ => hdom ρ ρ.2 x)

end
end AllocationIndices.Proof

end

/- Complete module: SFASRoot -/
section

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices
noncomputable section
open Proof

theorem superprocess_index_theorem {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] (D : DecisionProcess S U) (hD : D.BoundedRewards)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {g : S → U} (hg : IsConditionDControl D a g)
    {n : ℕ} {π : SFASPolicy n S U} (hπ : IsSuperIndexPolicy D a g π) :
    IsOptimalSFASPolicy D a π := by
  obtain ⟨R₀,hr₀⟩ := hD
  let R := |R₀|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hr : ∀ x u, |D.reward x u| ≤ R := by
    intro x u
    exact (hr₀ x u).trans (by dsimp [R]; linarith [le_abs_self R₀])
  have hfeasible : IsFeasiblePolicy D π := by
    intro t h
    apply le_antisymm prob_le_one
    rw [← hπ t h]
    apply measure_mono
    intro c hc
    change c.2 ∈ D.avail (h.2 c.1)
    rw [hc.1]
    exact hg.1 _
  apply optimalSFAS_of_approximate_bellman D a ha0.le ha1 R hr π hfeasible
  intro ε heps
  let L := -R/(1-a)
  let H := R/(1-a)
  have hd : 0 < 1-a := by linarith
  have hwidth : 0 < H-L := by
    have hp := div_pos hR hd
    dsimp [H,L]
    rw [neg_div]
    linarith
  obtain ⟨N,hNg⟩ := exists_nat_gt (max (1:ℝ) (4*(H-L)/ε))
  have hNr : (0:ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hNg)
  have hN : 0 < N := by exact_mod_cast hNr
  let h := (H-L)/(N:ℝ)
  have hh : 0 < h := div_pos hwidth hNr
  have h4 : 4*h < ε := by
    have hNg' := (le_max_right (1:ℝ) (4*(H-L)/ε)).trans_lt hNg
    have hh' := (div_lt_iff₀ heps).mp hNg'
    dsimp [h]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hNr).2
    nlinarith
  have hmesh : meshNode (-R/(1-a)) h N = R/(1-a) := by
    dsimp [meshNode,h,H,L]
    field_simp
    ring
  obtain ⟨V,B,hV,hu,hl⟩ := exists_retirement_mesh_potential (n := n) D a R h ha0.le ha1 hR hr
    g hg N hN hh hmesh
  refine ⟨V,B,hV,?_,?_⟩
  · intro x c hc
    exact (hu x c.1 c.2 hc).trans (by linarith)
  · intro t hist
    have hsel : ∀ᵐ c ∂π.select t hist, c.2 = g (hist.2 c.1) ∧
        ∀ j, superIndexMax D a (hist.2 j) ≤ superIndexMax D a (hist.2 c.1) := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff (Set.Countable.measurableSet (Set.to_countable _))).2 (hπ t hist)
    filter_upwards [hsel] with c hc
    have hv := hl hist.2 c.1 hc.2
    rw [← hc.1] at hv
    exact (by linarith : V hist.2-ε ≤ V hist.2-4*h).trans hv

end
end AllocationIndices

theorem solution {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] (D : AllocationIndices.DecisionProcess S U)
    (hD : D.BoundedRewards) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {g : S → U}
    (hg : AllocationIndices.IsConditionDControl D a g) {n : ℕ}
    {π : AllocationIndices.SFASPolicy n S U} (hπ : AllocationIndices.IsSuperIndexPolicy D a g π) :
    AllocationIndices.IsOptimalSFASPolicy D a π :=
  AllocationIndices.superprocess_index_theorem D hD ha0 ha1 hg hπ

end
