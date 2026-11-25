-- Prove2me | Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb
-- name    : SourceProof_6a141fa6412d14db4fc15aeb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:34:49.437053+00:00
-- url     : https://prove2.me/theorems/6e1879e7-f9c2-407f-93ea-834c1720435d
-- title:
--   StochLean source theorem: MeasureTheory.StronglyAdapted.isStronglyProgressive_of_rightContinuous

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F001

open private cappedRightGrid countable_range_cappedRightGrid measurable_cappedRightGrid tendsto_cappedRightGrid_nhdsWithin from Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F001
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Progressive measurability from right-continuous paths

For nonnegative real time, a strongly adapted process with right-continuous trajectories is
strongly progressive. The proof uses measurable countable-range right-grid approximations; it
does not strengthen right continuity to continuity.
-/

@[expose] public section

open NNReal TopologicalSpace
open scoped Topology

namespace MeasureTheory

namespace StronglyAdapted


theorem _root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X)
    (hright : ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω) :
    IsStronglyProgressive ℱ X := by
  intro i
  borelize E
  let U (n : ℕ) (p : Set.Iic i × Ω) := X (cappedRightGrid i n p.1) p.2
  have hU : ∀ n, StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)] (U n) := by
    intro n
    let q := cappedRightGrid i n
    let _ : Countable (Set.range q) := (countable_range_cappedRightGrid i n).to_subtype
    have h_str_meas :
        StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)]
          (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) := by
      refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
      · have hswap :
            (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) =
              (fun p : Ω × Set.range q => X ((p.2.1 : Set.Iic i) : ℝ≥0) p.1) ∘
                Prod.swap := rfl
        rw [hswap, measurable_swap_iff]
        exact measurable_from_prod_countable_left fun j =>
          (hX.stronglyMeasurable_le j.1.property).measurable
      · have hsep : IsSeparable
            (⋃ j : Set.range q, Set.range (X ((j.1 : Set.Iic i) : ℝ≥0))) :=
          .iUnion fun j => (hX.stronglyMeasurable_le j.1.property).isSeparable_range
        apply hsep.mono
        rintro _ ⟨p, rfl⟩
        exact Set.mem_iUnion.2 ⟨p.1, Set.mem_range_self p.2⟩
    have hfactor : U n =
        (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) ∘
          fun p : Set.Iic i × Ω =>
            (⟨q p.1, Set.mem_range_self p.1⟩, p.2) := rfl
    rw [hfactor]
    exact h_str_meas.comp_measurable <| Measurable.prodMk
      ((((measurable_cappedRightGrid i n).comp measurable_fst).subtype_mk)) measurable_snd
  refine stronglyMeasurable_of_tendsto Filter.atTop hU ?_
  rw [tendsto_pi_nhds]
  intro p
  exact (hright p.2 p.1).tendsto.comp (tendsto_cappedRightGrid_nhdsWithin i p.1)
end StronglyAdapted

end MeasureTheory


