-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_StandardBorel_F000
-- name    : LevyStochCalc_Poisson_StandardBorel_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:05:54.167424+00:00
-- url     : https://prove2.me/theorems/1e6e590e-cfcb-47c2-86fe-35452794f182
-- title:
--   Source declarations: LevyStochCalc.Poisson.StandardBorel
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.StandardBorel. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
import Definitions.Def_SourceProof_2bca091e7cf20505d705cbb8
import Definitions.Def_SourceProof_aa709884346500393cc5eed1
import Definitions.Def_SourceProof_c2748d972d70936ce8379f88
import Definitions.Def_SourceProof_eaee7ee541e6cad5b69e0ba7
import Definitions.Def_SourceProof_f29a707fb082a851fb03f552
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson random measures on a standard Borel space

A σ-finite measure `μ` is the sum of its restrictions to the disjointed spanning sets
`Dₙ = disjointed (spanningSets μ) n`, each of finite mass. Normalising the pieces of positive
mass gives countably many probability measures `ρ p` and weights `r p = μ (D p)` with
`∑ₚ r p • ρ p = μ` (`exists_superIntensity_eq`).

For weights and probability measures whose superposition intensity `∑ₚ r p • ρ p` is the reference
intensity `volume.restrict [0, ∞) ⊗ ν`, the superposition of independent Poisson pieces is a
Poisson random measure with intensity `ν` on `ι → PieceSpace (ℝ × E)` under `superLaw r ρ`
(`PoissonRandomMeasure.ofSuperposition`). That space is a countable product of copies of
`ULift ℕ × (ℕ → ℝ × E)`, hence standard Borel when `E` is.

## Main definitions

* `LevyStochCalc.Poisson.PoissonRandomMeasure.ofSuperposition`: the superposition of independent
  Poisson pieces with total intensity `referenceIntensity ν`, as a Poisson random measure.

## Main statements

* `LevyStochCalc.Poisson.exists_superIntensity_eq`: every σ-finite measure is the intensity of a
  countable superposition of Poisson pieces.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_standardBorel`: for every σ-finite intensity
  `ν` on a standard Borel mark space, some standard Borel probability space carries a Poisson
  random measure with intensity `volume.restrict [0, ∞) ⊗ ν`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

/-- **A σ-finite measure as a superposition intensity.** Every σ-finite measure `μ` is
`∑ₚ r p • ρ p` for countably many weights `r p` and probability measures `ρ p`. -/
theorem exists_superIntensity_eq {𝓧 : Type u} [MeasurableSpace 𝓧] (μ : Measure 𝓧)
    [SigmaFinite μ] :
    ∃ (ι : Type) (_ : Countable ι) (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
      (_ : ∀ p, IsProbabilityMeasure (ρ p)), superIntensity r ρ = μ := by
  set D : ℕ → Set 𝓧 := disjointed (spanningSets μ)
  have hD_fin : ∀ n, μ (D n) ≠ ⊤ := fun n =>
    ((measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)).ne
  let ι := {n : ℕ // μ (D n) ≠ 0}
  let r : ι → ℝ≥0 := fun p => (μ (D p.1)).toNNReal
  let ρ : ι → Measure 𝓧 := fun p => (μ (D p.1))⁻¹ • μ.restrict (D p.1)
  have hρ : ∀ p, IsProbabilityMeasure (ρ p) := fun p => ⟨by
    change ((μ (D p.1))⁻¹ • μ.restrict (D p.1)) Set.univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel p.2 (hD_fin p.1)]⟩
  have hcell : ∀ p : ι, (r p : ℝ≥0∞) • ρ p = μ.restrict (D p.1) := by
    intro p
    change ((μ (D p.1)).toNNReal : ℝ≥0∞) • ((μ (D p.1))⁻¹ • μ.restrict (D p.1)) = _
    rw [ENNReal.coe_toNNReal (hD_fin p.1), smul_smul,
      ENNReal.mul_inv_cancel p.2 (hD_fin p.1), one_smul]
  refine ⟨ι, inferInstance, r, ρ, hρ, ?_⟩
  unfold superIntensity
  simp_rw [hcell]
  conv_rhs => rw [← sum_restrict_disjointed_spanningSets μ μ]
  ext B hB
  rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
  refine tsum_subtype_eq_of_support_subset (s := {n : ℕ | μ (D n) ≠ 0})
    (f := fun n => μ.restrict (D n) B) fun n hn h0 => hn ?_
  change μ.restrict (D n) B = 0
  rw [Measure.restrict_eq_zero.mpr h0, Measure.coe_zero, Pi.zero_apply]
variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Countable ι] {r : ι → ℝ≥0} {ρ : ι → Measure (ℝ × E)}
  [∀ p, IsProbabilityMeasure (ρ p)]

/-- The superposition of independent Poisson pieces with weights `r p` and mark laws `ρ p`, when
`∑ₚ r p • ρ p = volume.restrict [0, ∞) ⊗ ν`, as a Poisson random measure with intensity `ν`
under `superLaw r ρ`. -/
noncomputable def PoissonRandomMeasure.ofSuperposition
    (hint : superIntensity r ρ = referenceIntensity ν) :
    PoissonRandomMeasure (superLaw r ρ) ν where
  N := superposition
  measurable_eval hB := measurable_superposition hB
  integer_valued hB hfin := _root_.Prove2MeSourceProof.h_f29a707fb082a851fb03f552 r ρ hB (by rwa [hint])
  infinite_at_infinite_intensity hB hinf := _root_.Prove2MeSourceProof.h_aa709884346500393cc5eed1 r ρ hB (by rwa [hint])
  poisson_law hB hfin := by
    rw [_root_.Prove2MeSourceProof.h_c2748d972d70936ce8379f88 r ρ hB (by rwa [hint]), hint]
    rfl
  independent_disjoint B hB hd := _root_.Prove2MeSourceProof.h_eaee7ee541e6cad5b69e0ba7 r ρ hB hd
  joint_past_future_independent := fun {t₁ t₂} _ _ {S} hS _ => by
    have h := _root_.Prove2MeSourceProof.h_2bca091e7cf20505d705cbb8 (fun hB => measurable_superposition hB)
      (fun B hB hd => _root_.Prove2MeSourceProof.h_eaee7ee541e6cad5b69e0ba7 r ρ hB hd)
      (measurableSet_Ioc.prod hS : MeasurableSet (Set.Ioc t₁ t₂ ×ˢ S))
    refine indep_of_indep_of_le_left h (iSup₂_le fun C hC => le_iSup₂_of_le C ?_ le_rfl)
    exact ⟨(Set.disjoint_prod.2 (Or.inl (Set.Iic_disjoint_Ioc le_rfl))).mono_left hC.1, hC.2⟩
@[simp]
lemma PoissonRandomMeasure.ofSuperposition_N
    (hint : superIntensity r ρ = referenceIntensity ν) :
    (PoissonRandomMeasure.ofSuperposition hint).N = superposition := rfl
/-- **Poisson random measure on a standard Borel space.** For every σ-finite intensity `ν` on a
standard Borel mark space `E`, some standard Borel probability space carries a Poisson random
measure with intensity `volume.restrict [0, ∞) ⊗ ν`. -/
theorem PoissonRandomMeasure.exists_standardBorel (E : Type v) [MeasurableSpace E]
    [StandardBorelSpace E] (ν : Measure E) [SigmaFinite ν] :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P),
      StandardBorelSpace Ω ∧ Nonempty (PoissonRandomMeasure P ν) := by
  haveI : SigmaFinite (referenceIntensity ν) := by
    rw [referenceIntensity]
    infer_instance
  obtain ⟨ι, _, r, ρ, _, hint⟩ := exists_superIntensity_eq (referenceIntensity ν)
  haveI : StandardBorelSpace (PieceSpace (ℝ × E)) := inferInstance
  exact ⟨ι → PieceSpace (ℝ × E), inferInstance, superLaw r ρ, inferInstance,
    StandardBorelSpace.pi_countable, ⟨PoissonRandomMeasure.ofSuperposition hint⟩⟩
end LevyStochCalc.Poisson


