-- Prove2me | solution 1 for AugLagLLC.Feas.caratheodory_cones
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-19T14:38:01.440184+00:00
-- url     : https://prove2.me/submissions/2caa1bb0-6371-41a2-b581-1627e03e66cf

import Mathlib

set_option maxHeartbeats 1600000
set_option autoImplicit false

theorem solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι κ : Type*} [Fintype ι] (a : ι → V) (b : κ → V) (J₀ : Finset κ)
    (α : ι → ℝ) (β : κ → ℝ) (hβ : ∀ j ∈ J₀, 0 ≤ β j) :
    ∃ (I : Finset ι) (J : Finset κ), J ⊆ J₀ ∧
      ∃ (α' : ι → ℝ) (β' : κ → ℝ), (∀ j ∈ J, 0 ≤ β' j) ∧
        ∑ i, α i • a i + ∑ j ∈ J₀, β j • b j =
          ∑ i ∈ I, α' i • a i + ∑ j ∈ J, β' j • b j ∧
        LinearIndependent ℝ (Sum.elim (fun i : I => a i) (fun j : J => b j)) := by
  classical
  let T : V := ∑ i, α i • a i + ∑ j ∈ J₀, β j • b j
  let P : Finset ι → Finset κ → (ι → ℝ) → (κ → ℝ) → Prop :=
    fun I J α' β' =>
      J ⊆ J₀ ∧ (∀ j ∈ J, 0 < β' j) ∧ (∀ j ∉ J, β' j = 0) ∧ (∀ i ∉ I, α' i = 0) ∧
        T = ∑ i ∈ I, α' i • a i + ∑ j ∈ J, β' j • b j
  have hex : ∃ I J α' β', P I J α' β' := by
    refine ⟨Finset.univ.filter (fun i => α i ≠ 0), J₀.filter (fun j => β j ≠ 0),
      α, (fun j => if j ∈ J₀ then β j else 0), ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.filter_subset _ _
    · intro j hj
      obtain ⟨hj0, hjne⟩ := Finset.mem_filter.mp hj
      have hpos : 0 < β j := lt_of_le_of_ne (hβ j hj0) (Ne.symm hjne)
      simpa [hj0] using hpos
    · intro j hj
      by_cases hj0 : j ∈ J₀
      · have hz : β j = 0 := by
          by_contra hne
          exact hj (Finset.mem_filter.mpr ⟨hj0, hne⟩)
        simp [hj0, hz]
      · simp [hj0]
    · intro i hi
      by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
    · have h1 : (∑ i ∈ Finset.univ.filter (fun i => α i ≠ 0), α i • a i) = ∑ i, α i • a i := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro x _ hx
        have hz : α x = 0 := by
          by_contra hne
          exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)
        simp [hz]
      have h2a : (∑ j ∈ J₀.filter (fun j => β j ≠ 0), (if j ∈ J₀ then β j else 0) • b j)
          = ∑ j ∈ J₀, (if j ∈ J₀ then β j else 0) • b j := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro x hxJ0 hxnot
        have hz : β x = 0 := by
          by_contra hne
          exact hxnot (Finset.mem_filter.mpr ⟨hxJ0, hne⟩)
        simp [hxJ0, hz]
      have h2b : (∑ j ∈ J₀, (if j ∈ J₀ then β j else 0) • b j) = ∑ j ∈ J₀, β j • b j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [hj]
      have h2 := h2a.trans h2b
      simp only [T]
      rw [← h1, ← h2]
  have hQ : ∃ n, ∃ I J α' β', P I J α' β' ∧ I.card + J.card = n := by
    obtain ⟨I, J, α', β', h⟩ := hex
    exact ⟨_, I, J, α', β', h, rfl⟩
  let m := Nat.find hQ
  obtain ⟨I, J, α', β', hP, hcard⟩ := Nat.find_spec hQ
  have hmin : ∀ (I' : Finset ι) (J' : Finset κ) (α'' : ι → ℝ) (β'' : κ → ℝ),
      P I' J' α'' β'' → m ≤ I'.card + J'.card := by
    intro I' J' α'' β'' h
    exact Nat.find_min' hQ ⟨I', J', α'', β'', h, rfl⟩
  obtain ⟨hJsub, hβpos, hβzero, hαzero, heq⟩ := hP
  have hαne : ∀ i ∈ I, α' i ≠ 0 := by
    intro i hi hz
    have hP' : P (I.erase i) J α' β' := by
      refine ⟨hJsub, hβpos, hβzero, ?_, ?_⟩
      · intro x hx
        by_cases hxi : x = i
        · subst hxi
          exact hz
        · exact hαzero x (fun hxI => hx (Finset.mem_erase.mpr ⟨hxi, hxI⟩))
      · have hsum : (∑ x ∈ I.erase i, α' x • a x) = ∑ x ∈ I, α' x • a x := by
          refine Finset.sum_subset (Finset.erase_subset _ _) ?_
          intro x hxI hxnot
          have hxi : x = i := by
            by_contra hne
            exact hxnot (Finset.mem_erase.mpr ⟨hne, hxI⟩)
          subst hxi
          simp [hz]
        rw [heq, hsum]
    have hlt : (I.erase i).card < I.card := Finset.card_erase_lt_of_mem hi
    have hm := hmin (I.erase i) J α' β' hP'
    omega
  refine ⟨I, J, hJsub, α', β', fun j hj => (hβpos j hj).le, heq, ?_⟩
  by_contra hnotLI
  rw [Fintype.not_linearIndependent_iff] at hnotLI
  obtain ⟨g, hgsum, x0, hgx0⟩ := hnotLI
  let u : ι → ℝ := fun i => if h : i ∈ I then g (Sum.inl ⟨i, h⟩) else 0
  let v : κ → ℝ := fun j => if h : j ∈ J then g (Sum.inr ⟨j, h⟩) else 0
  have hu0 : ∀ i ∉ I, u i = 0 := fun i hi => by simp [u, hi]
  have hv0 : ∀ j ∉ J, v j = 0 := fun j hj => by simp [v, hj]
  have hrel : (∑ i ∈ I, u i • a i) + (∑ j ∈ J, v j • b j) = 0 := by
    have h := hgsum
    rw [Fintype.sum_sum_type] at h
    rw [← Finset.sum_coe_sort I (fun i => u i • a i),
      ← Finset.sum_coe_sort J (fun j => v j • b j)]
    simpa [u, v] using h
  by_cases hcase : ∃ j ∈ J, v j ≠ 0
  · obtain ⟨j₁, hj₁J, hvj₁⟩ := hcase
    let Tset : Finset ℝ := (J.filter (fun j => v j ≠ 0)).image (fun j => -β' j / v j)
    have hTne : Tset.Nonempty := by
      refine ⟨-β' j₁ / v j₁, ?_⟩
      exact Finset.mem_image.mpr ⟨j₁, Finset.mem_filter.mpr ⟨hj₁J, hvj₁⟩, rfl⟩
    let D : Finset ℝ := Tset.image (fun r => |r|)
    have hDne : D.Nonempty := hTne.image _
    obtain ⟨eps, hepsT, heps_abs⟩ := Finset.mem_image.mp (D.min'_mem hDne)
    have hle : ∀ r ∈ Tset, |eps| ≤ |r| := by
      intro r hr
      rw [heps_abs]
      exact D.min'_le _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
    obtain ⟨j₂, hj₂, heps_eq⟩ := Finset.mem_image.mp hepsT
    obtain ⟨hj₂J, hvj₂⟩ := Finset.mem_filter.mp hj₂
    have heps_ne : eps ≠ 0 := by
      rw [← heps_eq]
      exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt (hβpos j₂ hj₂J))) hvj₂
    let α'' : ι → ℝ := fun i => α' i + eps * u i
    let β'' : κ → ℝ := fun j => β' j + eps * v j
    have hβ''nn : ∀ j, 0 ≤ β'' j := by
      intro j
      by_cases hj : j ∈ J
      · by_cases hv : v j = 0
        · have hb : 0 < β' j := hβpos j hj
          have hz : β'' j = β' j := by simp [β'', hv]
          rw [hz]
          exact hb.le
        · have hcand : (-β' j / v j) ∈ Tset :=
            Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hv⟩, rfl⟩
          have hb : 0 < β' j := hβpos j hj
          have hc : |eps| ≤ β' j / |v j| := by
            have h := hle _ hcand
            calc |eps| ≤ |(-β' j / v j)| := h
              _ = β' j / |v j| := by rw [abs_div, abs_neg, abs_of_pos hb]
          obtain ⟨hb1, hb2⟩ := abs_le.mp hc
          rcases lt_or_gt_of_ne hv with hvneg | hvpos
          · have hbabs : β' j / |v j| = -β' j / v j := by
              rw [abs_of_neg hvneg]
              ring
            have hle2 : eps ≤ -β' j / v j := by
              rw [← hbabs]
              exact hb2
            have hmul : (-β' j / v j) * v j ≤ eps * v j :=
              mul_le_mul_of_nonpos_right hle2 hvneg.le
            have hr : (-β' j / v j) * v j = -β' j := by
              field_simp
            simp only [β'']
            linarith
          · have hbabs : -(β' j / |v j|) = -β' j / v j := by
              rw [abs_of_pos hvpos]
              ring
            have hle2 : -β' j / v j ≤ eps := by
              rw [← hbabs]
              exact hb1
            have hmul : (-β' j / v j) * v j ≤ eps * v j :=
              mul_le_mul_of_nonneg_right hle2 hvpos.le
            have hr : (-β' j / v j) * v j = -β' j := by
              field_simp
            simp only [β'']
            linarith
      · have hv : v j = 0 := hv0 j hj
        have hb : β' j = 0 := hβzero j hj
        have hz : β'' j = 0 := by simp [β'', hv, hb]
        rw [hz]
    have heq'' : T = ∑ i ∈ I, α'' i • a i + ∑ j ∈ J, β'' j • b j := by
      have e1 : (∑ i ∈ I, α'' i • a i)
          = (∑ i ∈ I, α' i • a i) + eps • (∑ i ∈ I, u i • a i) := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [α'']
        rw [add_smul, mul_smul]
      have e2 : (∑ j ∈ J, β'' j • b j)
          = (∑ j ∈ J, β' j • b j) + eps • (∑ j ∈ J, v j • b j) := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [β'']
        rw [add_smul, mul_smul]
      have hE : eps • (∑ i ∈ I, u i • a i) + eps • (∑ j ∈ J, v j • b j) = 0 := by
        rw [← smul_add, hrel, smul_zero]
      have hX : eps • (∑ i ∈ I, u i • a i) = -(eps • (∑ j ∈ J, v j • b j)) :=
        eq_neg_iff_add_eq_zero.mpr hE
      calc T = (∑ i ∈ I, α' i • a i) + (∑ j ∈ J, β' j • b j) := heq
        _ = ((∑ i ∈ I, α' i • a i) + eps • (∑ i ∈ I, u i • a i))
              + ((∑ j ∈ J, β' j • b j) + eps • (∑ j ∈ J, v j • b j)) := by
              rw [hX]
              abel
        _ = ∑ i ∈ I, α'' i • a i + ∑ j ∈ J, β'' j • b j := by
              rw [← e1, ← e2]
    let I'' : Finset ι := I.filter (fun i => α'' i ≠ 0)
    let J'' : Finset κ := J.filter (fun j => β'' j ≠ 0)
    have hP'' : P I'' J'' α'' β'' := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (Finset.filter_subset _ _).trans hJsub
      · intro j hj
        have h0 := hβ''nn j
        have hne := (Finset.mem_filter.mp hj).2
        exact lt_of_le_of_ne h0 (Ne.symm hne)
      · intro j hj
        by_contra hne
        have hjJ : j ∈ J := by
          by_contra hjJ
          have hz : β'' j = 0 := by
            rw [show β'' j = β' j + eps * v j from rfl, hv0 j hjJ, hβzero j hjJ]
            simp
          exact hne hz
        exact hj (Finset.mem_filter.mpr ⟨hjJ, hne⟩)
      · intro i hi
        by_contra hne
        have hiI : i ∈ I := by
          by_contra hiI
          have hz : α'' i = 0 := by
            rw [show α'' i = α' i + eps * u i from rfl, hu0 i hiI, hαzero i hiI]
            simp
          exact hne hz
        exact hi (Finset.mem_filter.mpr ⟨hiI, hne⟩)
      · have hs1 : (∑ i ∈ I'', α'' i • a i) = ∑ i ∈ I, α'' i • a i := by
          refine Finset.sum_subset (Finset.filter_subset _ _) ?_
          intro x hxI hxnot
          have hz : ¬ (α'' x ≠ 0) := fun hne => hxnot (Finset.mem_filter.mpr ⟨hxI, hne⟩)
          simp [not_not.mp hz]
        have hs2 : (∑ j ∈ J'', β'' j • b j) = ∑ j ∈ J, β'' j • b j := by
          refine Finset.sum_subset (Finset.filter_subset _ _) ?_
          intro x hxJ hxnot
          have hz : ¬ (β'' x ≠ 0) := fun hne => hxnot (Finset.mem_filter.mpr ⟨hxJ, hne⟩)
          simp [not_not.mp hz]
        rw [heq'', ← hs1, ← hs2]
    have hlt : I''.card + J''.card < m := by
      have hIle : I''.card ≤ I.card := Finset.card_le_card (Finset.filter_subset _ _)
      have hJssub : J'' ⊂ J := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
        intro heqset
        have hmem : j₂ ∈ J'' := by rw [heqset]; exact hj₂J
        have hb2 : β'' j₂ = 0 := by
          simp only [β'']
          rw [← heps_eq]
          field_simp
          ring
        exact (Finset.mem_filter.mp hmem).2 hb2
      have hJlt : J''.card < J.card := Finset.card_lt_card hJssub
      omega
    exact absurd (hmin I'' J'' α'' β'' hP'') (by omega)
  · push_neg at hcase
    have hZ : (∑ j ∈ J, v j • b j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hcase j hj, zero_smul]
    have hX0 : (∑ i ∈ I, u i • a i) = 0 := by
      have h := hrel
      rw [hZ, add_zero] at h
      exact h
    have hx : ∃ i ∈ I, u i ≠ 0 := by
      rcases x0 with i | j
      · refine ⟨i.1, i.2, ?_⟩
        have hui : u i.1 = g (Sum.inl i) := by simp [u, i.2]
        rw [hui]
        exact hgx0
      · exfalso
        have hvj : v j.1 = g (Sum.inr j) := by simp [v, j.2]
        have hzero : v j.1 = 0 := hcase j.1 j.2
        rw [hvj] at hzero
        exact hgx0 hzero
    obtain ⟨i₁, hi₁I, hu₁⟩ := hx
    have hα₁ : α' i₁ ≠ 0 := hαne i₁ hi₁I
    let τ : ℝ := -α' i₁ / u i₁
    have hτne : τ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα₁) hu₁
    let α'' : ι → ℝ := fun i => α' i + τ * u i
    let β'' : κ → ℝ := β'
    have hα''0 : α'' i₁ = 0 := by
      simp only [α'', τ]
      field_simp
      ring
    have hβ''pos : ∀ j ∈ J, 0 < β'' j := fun j hj => hβpos j hj
    have hβ''zero : ∀ j ∉ J, β'' j = 0 := fun j hj => hβzero j hj
    have heq'' : T = ∑ i ∈ I, α'' i • a i + ∑ j ∈ J, β'' j • b j := by
      have e1 : (∑ i ∈ I, α'' i • a i)
          = (∑ i ∈ I, α' i • a i) + τ • (∑ i ∈ I, u i • a i) := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [α'']
        rw [add_smul, mul_smul]
      rw [e1, hX0, smul_zero, add_zero]
      simpa [β''] using heq
    let I'' : Finset ι := I.filter (fun i => α'' i ≠ 0)
    have hP'' : P I'' J α'' β'' := by
      refine ⟨hJsub, hβ''pos, hβ''zero, ?_, ?_⟩
      · intro i hi
        by_contra hne
        have hiI : i ∈ I := by
          by_contra hiI
          have hz : α'' i = 0 := by
            rw [show α'' i = α' i + τ * u i from rfl, hu0 i hiI, hαzero i hiI]
            simp
          exact hne hz
        exact hi (Finset.mem_filter.mpr ⟨hiI, hne⟩)
      · have hs1 : (∑ i ∈ I'', α'' i • a i) = ∑ i ∈ I, α'' i • a i := by
          refine Finset.sum_subset (Finset.filter_subset _ _) ?_
          intro x hxI hxnot
          have hz : ¬ (α'' x ≠ 0) := fun hne => hxnot (Finset.mem_filter.mpr ⟨hxI, hne⟩)
          simp [not_not.mp hz]
        rw [heq'', ← hs1]
    have hlt : I''.card + J.card < m := by
      have hIssub : I'' ⊂ I := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
        intro heqset
        have hmem : i₁ ∈ I'' := by rw [heqset]; exact hi₁I
        exact (Finset.mem_filter.mp hmem).2 hα''0
      have hIlt : I''.card < I.card := Finset.card_lt_card hIssub
      omega
    exact absurd (hmin I'' J α'' β'' hP'') (by omega)
