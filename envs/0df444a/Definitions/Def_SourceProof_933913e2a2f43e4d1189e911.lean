-- Prove2me | Definitions.Def_SourceProof_933913e2a2f43e4d1189e911
-- name    : SourceProof_933913e2a2f43e4d1189e911
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:41:45.595348+00:00
-- url     : https://prove2.me/theorems/bc0021bc-3afd-48c0-901f-4a2e009cbcef
-- title:
--   LevyStochCalc source module: SourceProof_933913e2a2f43e4d1189e911
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.indep_rightCont_zero_filtration` comes from the `LevyStochCalc.Driver.GermIndep` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_GermIndep_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The germ field of a Lévy driver

`Driver/ValueSigma.lean` gives the independence of `ℱ₊ 0` from the driver's data along a strictly
increasing grid of positive times. An arbitrary finite family of positive times is put in that
form by sorting it (`gridOf`), which turns the statement into one about arbitrary finite tuples.
Independence then passes to the supremum over finite subfamilies of the generators of `ℱ T`
(`indep_iSup_of_finset`), the two generators outside reach — Brownian values at non-positive times
and the part of a region in negative time — being almost surely constant and so dropping out.

## Main statements

* `LevyDriver.indep_valueTuple` — `ℱ₊ 0` against an arbitrary finite tuple of the driver's data.
* `LevyDriver.indep_rightCont_zero_filtration` — `ℱ₊ 0` against `ℱ T` for every `T > 0`.
* `LevyDriver.isTrivialSigma_rightCont_zero` — Blumenthal's 0-1 law itself.
* `LevyDriver.condExp_rightCont_nonpos` — the conditional expectation on `ℱ₊ s`, `s ≤ 0`, is the
  mean.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)


theorem _root_.Prove2MeSourceProof.h_933913e2a2f43e4d1189e911 {T : ℝ} (hT : 0 < T) :
    Indep (D.filtration.rightCont 0) (D.filtration T) P := by
  classical
  set mfam : {u : ℝ // 0 < u} ⊕ {B : Set (ℝ × E) // B ⊆ Set.Ioc 0 T ×ˢ Set.univ ∧ MeasurableSet B}
      → MeasurableSpace Ω := Sum.elim
    (fun u => ⨆ j : Fin d, MeasurableSpace.comap (fun ω => (D.W.W j).W (u : ℝ) ω) inferInstance)
    (fun B => D.regionSigma (B : Set (ℝ × E))) with hmfam
  have hmfam_le : ∀ i, mfam i ≤ ‹MeasurableSpace Ω› := by
    rintro (u | B)
    · exact iSup_le fun j => ((D.W.W j).measurable_eval _).comap_le
    · exact (D.N.measurable_eval B.2.2).comap_le
  -- the part of `ℱ T` the germ argument reaches, by finite subfamilies
  have hM : Indep (⨆ i, mfam i) (D.filtration.rightCont 0) P := by
    refine _root_.Prove2MeSourceProof.h_8a8a05f465ef0d9ef147bb7f hmfam_le (D.filtration.rightCont.le 0) fun S => ?_
    refine indep_of_indep_of_le_left (D.indep_valueTuple
      (fun i : Fin S.toRight.card => ((S.toRight.equivFin.symm i : _) : Set (ℝ × E)))
      (fun i => (S.toRight.equivFin.symm i).1.2.2) hT
      (fun i => (S.toRight.equivFin.symm i).1.2.1)
      (fun i : Fin S.toLeft.card => ((S.toLeft.equivFin.symm i : _) : ℝ))
      (fun i => (S.toLeft.equivFin.symm i).1.2)) ?_
    refine iSup₂_le fun i hi => ?_
    match i with
    | Sum.inl a =>
      refine le_sup_of_le_left (iSup_le fun j =>
        le_iSup_of_le (j, S.toLeft.equivFin ⟨a, Finset.mem_toLeft.2 hi⟩) ?_)
      simp
    | Sum.inr b =>
      refine le_sup_of_le_right
        (le_iSup_of_le (S.toRight.equivFin ⟨b, Finset.mem_toRight.2 hi⟩) ?_)
      simp [hmfam]
  -- everything else in `ℱ T` is null or conull
  have hbound : D.filtration T
      ≤ (⨆ i, mfam i) ⊔ LevyStochCalc.Probability.trivialSigma ‹MeasurableSpace Ω› P := by
    rw [D.filtration_apply, D.W.naturalFiltration_apply]
    refine sup_le (iSup_le fun j => ?_) ?_
    · rw [LevyStochCalc.Driver.LevyDriver.brownianNaturalFiltration_apply (D.W.W j) T]
      refine iSup₂_le fun u hu => ?_
      rcases lt_or_ge 0 u with hu0 | hu0
      · refine le_sup_of_le_left (le_iSup_of_le (Sum.inl ⟨u, hu0⟩) ?_)
        exact le_iSup (fun j : Fin d =>
          MeasurableSpace.comap (fun ω => (D.W.W j).W u ω) inferInstance) j
      · have hz : ∀ᵐ ω ∂P, (D.W.W j).W u ω = 0 := by
          rcases lt_or_eq_of_le hu0 with h | h
          · exact (D.W.W j).negative_zero u h
          · rw [h]; exact (D.W.W j).initial_zero
        exact le_sup_of_le_right
          (LevyStochCalc.Probability.comap_le_trivialSigma ((D.W.W j).measurable_eval u) hz)
    · rw [LevyStochCalc.Driver.LevyDriver.poissonNaturalFiltration_apply]
      refine iSup₂_le fun B hB => ?_
      have hIic : MeasurableSet (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ) :=
        hB.2.inter (measurableSet_Iic.prod MeasurableSet.univ)
      have hIoc : MeasurableSet (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) :=
        hB.2.inter (measurableSet_Ioc.prod MeasurableSet.univ)
      have hdisj : Disjoint (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ)
          (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) :=
        Set.disjoint_left.2 fun x hx hx' => absurd hx.2.1 (not_le.2 hx'.2.1.1)
      have hsplit : B = (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ)
          ∪ (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) := by
        rw [← Set.inter_union_distrib_left, ← Set.union_prod,
          Set.Iic_union_Ioc_eq_Iic hT.le]
        exact (Set.inter_eq_self_of_subset_left hB.1).symm
      have heq : (fun ω => D.N.N ω B)
          = fun ω => D.N.N ω (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ)
            + D.N.N ω (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) := by
        funext ω
        conv_lhs => rw [hsplit]
        exact measure_union hdisj hIoc
      change MeasurableSpace.comap (fun ω => D.N.N ω B) inferInstance ≤ _
      rw [heq]
      refine LevyStochCalc.Probability.comap_add_le ?_ ?_
      · exact le_sup_of_le_right (LevyStochCalc.Probability.comap_le_trivialSigma
          (D.N.measurable_eval hIic) (LevyStochCalc.Poisson.ae_count_Iic_zero_eq_zero D.N hB.2))
      · exact le_sup_of_le_left (le_iSup_of_le
          (Sum.inr ⟨B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ, Set.inter_subset_right, hIoc⟩) le_rfl)
  exact (indep_of_indep_of_le_left
    (LevyStochCalc.Probability.IsTrivialSigma.indep_sup (iSup_le hmfam_le)
      LevyStochCalc.Probability.trivialSigma_le (D.filtration.rightCont.le 0)
      LevyStochCalc.Probability.isTrivialSigma_trivialSigma hM) hbound).symm
end LevyDriver

end LevyStochCalc.Driver


