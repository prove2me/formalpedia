-- Prove2me | Definitions.Def_SourceProof_2e016f6f64c5cb15d61c5cac
-- name    : SourceProof_2e016f6f64c5cb15d61c5cac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:16:15.209461+00:00
-- url     : https://prove2.me/theorems/a55d0ae6-8c13-425a-9ec2-3e60f17db0b8
-- title:
--   LevyStochCalc source module: SourceProof_2e016f6f64c5cb15d61c5cac
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.indep_futureSigma_rightCont` comes from the `LevyStochCalc.Driver.AugJointRightCont` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right-continuity of the augmented joint filtration of a Lévy driver

Write `𝔸 = augFiltration D.filtration P` for the `0`-clamped augmentation of the joint filtration
of a Lévy driver. Its germ field at a time `t ≥ 0` is already its field at `t`.

The driver's data over `(t, T]` measured from `t` — the Brownian increments `W u - W t` for
`u ∈ (t, T]` and the counts on the measurable regions inside `(t, T] × E` — generates the
σ-algebra `futureSigma t T`. Joined with `ℱ t` it contains `ℱ T`, and it is independent of the
germ field `ℱ₊ t`, the independence coming from the data of a grid starting at `t`. A σ-algebra
that contains `ℱ t`, sits inside the join `ℱ t ⊔ futureSigma t T` and is independent of
`futureSigma t T` differs from `ℱ t` only by null sets: the conditional expectation on `ℱ t` of
the indicator of one of its sets is that indicator, because the two integrate alike over the
π-system of intersections generating the join. Hence `ℱ₊ t ≤ aug (ℱ t)`, and since augmentation
commutes with the countable antitone infimum `⨅ n, ℱ (t + (n + 1)⁻¹)` this gives `𝔸₊ t = 𝔸 t`.
Below time `0` the filtration `𝔸` is constant, so `𝔸` is right-continuous.

## Main statements

* `LevyStochCalc.Probability.le_aug_of_indep_of_le_sup` — the σ-algebra criterion for lying in
  an augmentation.
* `LevyStochCalc.Driver.LevyDriver.filtration_le_sup_futureSigma` — `ℱ T ≤ ℱ t ⊔ futureSigma t T`.
* `LevyStochCalc.Driver.LevyDriver.indep_futureSigma_rightCont` — `futureSigma t T` against
  `ℱ₊ t`.
* `LevyStochCalc.Driver.LevyDriver.filtration_rightCont_le_aug` — `ℱ₊ t ≤ aug (ℱ t)`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_le_self` — `𝔸₊ t ≤ 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_eq` — `𝔸₊ t = 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.isRightContinuous_augFiltration` — `𝔸` is right-continuous.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

end LevyStochCalc.Probability

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Probability

variable (D : LevyDriver.{u, v, w} P d ν)


theorem _root_.Prove2MeSourceProof.h_2e016f6f64c5cb15d61c5cac {t T : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    Indep (D.futureSigma t T) (D.filtration.rightCont t) P := by
  classical
  set mfam : {u : ℝ // u ∈ Set.Ioc t T}
      ⊕ {C : Set (ℝ × E) // C ⊆ Set.Ioc t T ×ˢ Set.univ ∧ MeasurableSet C}
      → MeasurableSpace Ω := Sum.elim
    (fun u => ⨆ j : Fin d, D.incrementSigma j t (u : ℝ))
    (fun C => D.regionSigma (C : Set (ℝ × E))) with hmfam
  have hmfam_le : ∀ i, mfam i ≤ ‹MeasurableSpace Ω› := by
    rintro (u | C)
    · exact iSup_le fun j =>
        (LevyStochCalc.Brownian.comap_increment_le_sigmaBrownian _ t (u : ℝ)).trans (LevyStochCalc.Brownian.sigmaBrownian_le _)
    · exact (D.N.measurable_eval C.2.2).comap_le
  have hM : Indep (⨆ i, mfam i) (D.filtration.rightCont t) P := by
    refine _root_.Prove2MeSourceProof.h_8a8a05f465ef0d9ef147bb7f hmfam_le (D.filtration.rightCont.le t) fun S => ?_
    set G : Finset ℝ :=
      insert T (Finset.image (fun u : {u : ℝ // u ∈ Set.Ioc t T} => (u : ℝ)) S.toLeft) with hG
    have hGne : G.Nonempty := ⟨T, Finset.mem_insert_self _ _⟩
    have hGmem : ∀ x ∈ G, x ∈ Set.Ioc t T := by
      intro x hx
      rcases Finset.mem_insert.1 hx with h | h
      · subst h
        exact Set.mem_Ioc.2 ⟨htT, le_rfl⟩
      · obtain ⟨u, -, hu⟩ := Finset.mem_image.1 h
        exact hu ▸ u.2
    have hgpos : ∀ l, t < LevyStochCalc.Driver.gridOf G hGne l := by
      intro l
      by_cases hl : l < G.card
      · exact (hGmem _ (LevyStochCalc.Driver.gridOf_mem G hGne hl)).1
      · have hval : LevyStochCalc.Driver.gridOf G hGne l = G.max' hGne + ((l - G.card + 1 : ℕ) : ℝ) := by
          simp only [LevyStochCalc.Driver.gridOf, dif_neg hl]
        have hmax : t < G.max' hGne := (hGmem _ (G.max'_mem hGne)).1
        have hpos : (0 : ℝ) < ((l - G.card + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_pos (l - G.card)
        rw [hval]
        linarith
    set g : ℕ → ℝ := fun l => if l = 0 then t else LevyStochCalc.Driver.gridOf G hGne (l - 1) with hg
    have hg0 : g 0 = t := by simp [hg]
    have hgsucc : ∀ l, g (l + 1) = LevyStochCalc.Driver.gridOf G hGne l := by
      intro l
      simp [hg]
    have hg_mono : StrictMono g := by
      intro a b hab
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · have hb : b ≠ 0 := by omega
        simp only [hg, if_pos rfl, if_neg hb]
        exact hgpos _
      · have ha' : a ≠ 0 := by omega
        have hb' : b ≠ 0 := by omega
        simp only [hg, if_neg ha', if_neg hb']
        exact _root_.Prove2MeSourceProof.h_fa28f33c204968e110957a33 G hGne (by omega)
    refine indep_of_indep_of_le_left (D.indep_iSup_stepSigma_start
      (fun k : Fin S.toRight.card => ((S.toRight.equivFin.symm k : _) : Set (ℝ × E)))
      (fun k => (S.toRight.equivFin.symm k).1.2.2) hg_mono (by rw [hg0]; exact ht)
      (G.card + 1)) ?_
    refine iSup₂_le fun i hi => ?_
    match i with
    | Sum.inl a =>
      obtain ⟨l, hl, hgl⟩ := LevyStochCalc.Driver.exists_gridOf_eq G hGne
        (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨a, Finset.mem_toLeft.2 hi, rfl⟩))
      refine le_iSup₂_of_le l (by omega) ?_
      have hgl' : g (l + 1) = (a : ℝ) := by rw [hgsucc, hgl]
      simp only [hmfam, Sum.elim_inl]
      refine le_sup_of_le_left (iSup_le fun j => le_iSup_of_le j (le_of_eq ?_))
      rw [hg0, hgl']
    | Sum.inr b =>
      obtain ⟨l, hl, hgl⟩ := LevyStochCalc.Driver.exists_gridOf_eq G hGne (Finset.mem_insert_self T _)
      refine le_iSup₂_of_le l (by omega) ?_
      have hgT : g (l + 1) = T := by rw [hgsucc, hgl]
      simp only [hmfam, Sum.elim_inr]
      refine le_sup_of_le_right
        (le_iSup_of_le (S.toRight.equivFin ⟨b, Finset.mem_toRight.2 hi⟩) ?_)
      simp only [Equiv.symm_apply_apply]
      rw [hg0, hgT, Set.inter_eq_self_of_subset_left b.2.1]
  refine indep_of_indep_of_le_left hM (sup_le (iSup₂_le fun u hu => ?_) (iSup₂_le fun C hC => ?_))
  · exact le_iSup_of_le (Sum.inl ⟨u, hu⟩) (by simp [hmfam])
  · exact le_iSup_of_le (Sum.inr ⟨C, hC⟩) (by simp [hmfam])
end LevyDriver

end LevyStochCalc.Driver


