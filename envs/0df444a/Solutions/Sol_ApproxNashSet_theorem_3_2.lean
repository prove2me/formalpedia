-- Prove2me | solution 1 for ApproxNashSet.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:02:16.300731+00:00
-- url     : https://prove2.me/submissions/1d87a5c8-a350-4f2e-9009-7a5e618fdd02

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

open ApproxNashSet in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (X : Set (Joint n)) (ε : ℝ) :
    epsNE f X ε = ⋂ i, epsArgMin (g n f i) X (cbar n i) ε := by
  have hgc : ∀ i x, g n f i x - ε • cbar n i =
      (minus n i x, -minus n i x, f i x - ε) := by
    intro i x
    simp only [g, cbar, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_sub_mk, sub_zero]
  ext xs
  simp only [Set.mem_iInter, epsNE, epsArgMin, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hX, hne⟩ i
    refine ⟨hX, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨⟨d1, d2, d3⟩, ⟨hd0, hdne⟩, rfl⟩, ⟨y, hy, hyz⟩⟩
    simp only [Set.mem_setOf_eq, Prod.le_def, Prod.fst_zero, Prod.snd_zero] at hd0
    simp only [Set.mem_singleton_iff] at hdne
    rw [hgc] at hyz
    unfold g at hyz
    simp only [Prod.mk_sub_mk, Prod.mk.injEq] at hyz
    obtain ⟨e1, e2, e3⟩ := hyz
    have hd1 : d1 = minus n i xs - minus n i y := by rw [e1]; abel
    have hd2 : d2 = -minus n i xs - -minus n i y := by rw [e2]; abel
    have hsum : d1 + d2 = 0 := by rw [hd1, hd2]; abel
    have hd1z : d1 = 0 := le_antisymm
      (by rw [eq_neg_of_add_eq_zero_left hsum]; exact neg_nonpos.mpr hd0.2.1) hd0.1
    have hd2z : d2 = 0 := le_antisymm
      (by rw [eq_neg_of_add_eq_zero_right hsum]; exact neg_nonpos.mpr hd0.1) hd0.2.1
    have hd3 : 0 < d3 := by
      rcases eq_or_lt_of_le hd0.2.2 with h | h
      · exact absurd (by rw [hd1z, hd2z, ← h]; rfl) hdne
      · exact h
    have hmy : minus n i y = minus n i xs := by rw [e1, hd1z, sub_zero]
    have hyeq : Function.update xs i (y i) = y := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Function.update_of_ne hj]
        exact (congrFun hmy ⟨j, hj⟩).symm
    have h := hne i (y i) (by rw [hyeq]; exact hy)
    rw [hyeq] at h
    linarith
  · intro h
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    refine ⟨(h i0).1, fun i xi hu => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hm : minus n i (Function.update xs i xi) = minus n i xs := by
      funext j
      simp [minus, Function.update_of_ne j.2]
    have hemp := (h i).2
    rw [Set.eq_empty_iff_forall_notMem] at hemp
    apply hemp (g n f i (Function.update xs i xi))
    refine ⟨⟨((0 : OthersStrat n i), (0 : OthersStrat n i),
      f i xs - ε - f i (Function.update xs i xi)), ⟨?_, ?_⟩, ?_⟩, ⟨_, hu, rfl⟩⟩
    · simp only [Set.mem_setOf_eq, Prod.le_def, Prod.fst_zero, Prod.snd_zero]
      exact ⟨le_rfl, le_rfl, by linarith⟩
    · simp only [Set.mem_singleton_iff]
      intro h0
      have := congrArg (fun p => p.2.2) h0
      simp only [Prod.snd_zero] at this
      linarith
    · simp only
      rw [hgc]
      simp only [g, hm, Prod.mk_sub_mk, sub_zero, sub_sub_cancel]
