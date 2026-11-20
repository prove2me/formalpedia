-- Prove2me | Definitions.Def_SourceProof_d3bf983a7485d4d78e4c97f0
-- name    : SourceProof_d3bf983a7485d4d78e4c97f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:59:31.772993+00:00
-- url     : https://prove2.me/theorems/40bd1242-b1c5-441b-ac53-45912e94c90c
-- title:
--   LevyStochCalc source module: SourceProof_d3bf983a7485d4d78e4c97f0
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` comes from the `LevyStochCalc.Poisson.RandomMeasure` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
import Definitions.Def_SourceProof_2bca091e7cf20505d705cbb8
import Definitions.Def_SourceProof_aa709884346500393cc5eed1
import Definitions.Def_SourceProof_c2748d972d70936ce8379f88
import Definitions.Def_SourceProof_eaee7ee541e6cad5b69e0ba7
import Definitions.Def_SourceProof_f29a707fb082a851fb03f552

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson random measure on `[0, ∞) × E`

A *Poisson random measure* on the time-space `[0, ∞) × E` (where `E` is a
measurable mark space with σ-finite intensity `ν`), defined over a
probability space `(Ω, P)`, is a measurable family

  `N : Ω → Measure (ℝ × E)`

with the following properties:

* For each measurable `B ⊆ ℝ × E` with `(volume.restrict [0,∞) ⊗ ν)(B) < ∞`,
  `N(·, B) ~ Poisson` with mean equal to that intensity.
* For any pairwise-disjoint family of such sets, the random variables
  `(N(·, B_i))_i` are independent under `P`.

This is the time-aware structure required for the *compensated* integral
`∫_0^t ∫_E φ(s, e) Ñ(ds, de)` to be well-defined.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, Cambridge 2009, §2.3, Thm 2.3.1.
* Ikeda–Watanabe, *Stochastic Differential Equations and Diffusion Processes*,
  North-Holland 1989, §I.8.
* Sato, *Lévy Processes and Infinitely Divisible Distributions*,
  Cambridge 1999, §19.

## Construction

The intensity is `volume.restrict (Set.Ici 0) ⊗ ν` (Lebesgue restricted to `[0, ∞)` tensor `ν`
on the mark space). `PoissonRandomMeasure.exists_of_sigmaFinite` builds a Poisson random
measure by the Poisson recipe: the time-space is cut into the cells `[n, n+1) × sₘ` of a
σ-finite decomposition, each cell of positive intensity carries a Poisson number of
independent marks distributed according to the normalised intensity, and the cells are
superposed (`LevyStochCalc.Poisson.superposition`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_d3bf983a7485d4d78e4c97f0
    (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (PoissonRandomMeasure P ν) := by
  classical
  obtain ⟨s, hs_meas, hs_disj, hs_fin, hs_univ⟩ := LevyStochCalc.Poisson.sigmaFinite_decomposition E ν
  set Λ := LevyStochCalc.Poisson.referenceIntensity ν with hΛ
  -- the time-space cells `[n, n+1) × sₘ`
  let A : ℕ × ℕ → Set (ℝ × E) := fun q => Set.Ico (q.1 : ℝ) (q.1 + 1) ×ˢ s q.2
  have hA_meas : ∀ q, MeasurableSet (A q) := fun q => measurableSet_Ico.prod (hs_meas q.2)
  have hA_disj : Pairwise fun q q' => Disjoint (A q) (A q') := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ hne
    change Disjoint (Set.Ico (n : ℝ) (n + 1) ×ˢ s m) (Set.Ico (n' : ℝ) (n' + 1) ×ˢ s m')
    rw [Set.disjoint_prod]
    by_cases hn : n = n'
    · subst hn
      exact Or.inr (hs_disj fun h => hne (by rw [h]))
    · refine Or.inl (Set.Ico_disjoint_Ico.2 ?_)
      rcases lt_or_gt_of_ne hn with h | h
      · have : (n : ℝ) + 1 ≤ n' := by exact_mod_cast h
        exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
      · have : (n' : ℝ) + 1 ≤ n := by exact_mod_cast h
        exact (min_le_right _ _).trans (this.trans (le_max_left _ _))
  have hA_fin : ∀ q, Λ (A q) ≠ ⊤ := by
    intro q
    rw [hΛ, LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (hs_fin q.2).ne
    refine ne_top_of_le_ne_top (b := volume (Set.Ico (q.1 : ℝ) (q.1 + 1))) ?_
      (Measure.restrict_le_self _)
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  -- the cells of positive intensity, with their normalised intensities
  let ι := {q : ℕ × ℕ // Λ (A q) ≠ 0}
  let r : ι → ℝ≥0 := fun p => (Λ (A p.1)).toNNReal
  let ρ : ι → Measure (ℝ × E) := fun p => (Λ (A p.1))⁻¹ • Λ.restrict (A p.1)
  haveI : ∀ p, IsProbabilityMeasure (ρ p) := fun p => ⟨by
    change ((Λ (A p.1))⁻¹ • Λ.restrict (A p.1)) Set.univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel p.2 (hA_fin p.1)]⟩
  -- the superposition has intensity `Λ`
  have hcell : ∀ p : ι, (r p : ℝ≥0∞) • ρ p = Λ.restrict (A p.1) := by
    intro p
    change ((Λ (A p.1)).toNNReal : ℝ≥0∞) • ((Λ (A p.1))⁻¹ • Λ.restrict (A p.1)) = _
    rw [ENNReal.coe_toNNReal (hA_fin p.1), smul_smul, ENNReal.mul_inv_cancel p.2 (hA_fin p.1),
      one_smul]
  have hnull : Λ (⋃ p : ι, A p.1)ᶜ = 0 := by
    have hsub : (⋃ p : ι, A p.1)ᶜ
        ⊆ (Set.Ici (0 : ℝ) ×ˢ Set.univ)ᶜ ∪ ⋃ q : {q : ℕ × ℕ // Λ (A q) = 0}, A q.1 := by
      intro x hx
      by_cases hx0 : x ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ
      · right
        obtain ⟨m, hm⟩ : ∃ m, x.2 ∈ s m := by
          have := hs_univ ▸ Set.mem_univ x.2
          exact Set.mem_iUnion.1 this
        have hx1 : x.1 ∈ Set.Ici (0 : ℝ) := (Set.mem_prod.1 hx0).1
        have hxA : x ∈ A (⌊x.1⌋₊, m) :=
          Set.mem_prod.2 ⟨⟨Nat.floor_le hx1, Nat.lt_floor_add_one x.1⟩, hm⟩
        by_cases h0 : Λ (A (⌊x.1⌋₊, m)) = 0
        · exact Set.mem_iUnion.2 ⟨⟨_, h0⟩, hxA⟩
        · exact absurd (Set.mem_iUnion.2 ⟨⟨_, h0⟩, hxA⟩) hx
      · exact Or.inl hx0
    refine measure_mono_null hsub (measure_union_null ?_ (measure_iUnion_null fun q => q.2))
    rw [hΛ, LevyStochCalc.Poisson.referenceIntensity, Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_apply (measurableSet_Ici.prod MeasurableSet.univ).compl,
      Set.compl_inter_self, measure_empty]
  have hint : LevyStochCalc.Poisson.superIntensity r ρ = Λ := by
    unfold LevyStochCalc.Poisson.superIntensity
    simp_rw [hcell]
    rw [← Measure.restrict_iUnion (fun p q hpq => hA_disj (Subtype.val_injective.ne hpq))
      fun p => hA_meas p.1]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hnull)
  -- assembly
  refine ⟨ι → LevyStochCalc.Poisson.PieceSpace (ℝ × E), inferInstance, LevyStochCalc.Poisson.superLaw r ρ, inferInstance, ⟨?_⟩⟩
  have hN_meas : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
      Measurable fun ω : ι → LevyStochCalc.Poisson.PieceSpace (ℝ × E) => LevyStochCalc.Poisson.superposition ω B :=
    fun hB => LevyStochCalc.Poisson.measurable_superposition hB
  have hN_indep : ∀ {κ : Type} [Countable κ] (B : κ → Set (ℝ × E)), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      iIndepFun (fun i ω => LevyStochCalc.Poisson.superposition ω (B i)) (LevyStochCalc.Poisson.superLaw r ρ) :=
    fun B hB hd => _root_.Prove2MeSourceProof.h_eaee7ee541e6cad5b69e0ba7 r ρ hB hd
  exact
    { N := LevyStochCalc.Poisson.superposition
      measurable_eval := hN_meas
      integer_valued := fun hB hfin => _root_.Prove2MeSourceProof.h_f29a707fb082a851fb03f552 r ρ hB (by rwa [hint])
      infinite_at_infinite_intensity := fun hB hinf =>
        _root_.Prove2MeSourceProof.h_aa709884346500393cc5eed1 r ρ hB (by rwa [hint])
      poisson_law := fun hB hfin => by
        rw [_root_.Prove2MeSourceProof.h_c2748d972d70936ce8379f88 r ρ hB (by rwa [hint]), hint]
        rfl
      independent_disjoint := fun B hB hd => _root_.Prove2MeSourceProof.h_eaee7ee541e6cad5b69e0ba7 r ρ hB hd
      joint_past_future_independent := fun {t₁ t₂} _ h12 {S} hS _ => by
        have h := _root_.Prove2MeSourceProof.h_2bca091e7cf20505d705cbb8 hN_meas hN_indep
          (measurableSet_Ioc.prod hS : MeasurableSet (Set.Ioc t₁ t₂ ×ˢ S))
        refine indep_of_indep_of_le_left h (iSup₂_le fun C hC => le_iSup₂_of_le C ?_ le_rfl)
        exact ⟨(Set.disjoint_prod.2 (Or.inl (Set.Iic_disjoint_Ioc le_rfl))).mono_left hC.1,
          hC.2⟩ }
end LevyStochCalc.Poisson


