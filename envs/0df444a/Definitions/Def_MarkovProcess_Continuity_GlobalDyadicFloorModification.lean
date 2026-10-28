-- Prove2me | Definitions.Def_MarkovProcess_Continuity_GlobalDyadicFloorModification
-- name    : MarkovProcess_Continuity_GlobalDyadicFloorModification
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T13:01:43.984365+00:00
-- url     : https://prove2.me/theorems/caf946d3-3860-4f1d-b64b-b10ecc543076
-- title:
--   MarkovProcess definitions: Continuity.GlobalDyadicFloorModification
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.GlobalDyadicFloorModification`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/GlobalDyadicFloorModification.lean#L1-L259

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.LocallyFinite

/-!
# A global continuous modification assembled from canonical unit paths

The nonnegative real half-line is covered by the closed unit intervals `[n, n + 1]`.  On each
piece we use the canonical dyadic-floor limit of the process shifted by `n`.  Exact endpoint
identities make these pieces compatible, so `Set.liftCover` gives an honest raw global path.
On the simultaneous probability-one event where every canonical unit piece is continuous, local
finiteness of the closed cover makes the raw path continuous.  A single constant global fallback
then gives a total path which is continuous for every sample.

No measurability of the path-valued map, path-space law, Markov property, or Hunt-process claim is
asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The `n`th closed unit interval in `ℝ≥0`. -/
def nnrealUnitInterval (n : ℕ) : Set ℝ≥0 := Set.Icc n (n + 1)

/-- Local coordinate in `[0,1]` on the `n`th closed unit interval. -/
def nnrealUnitCoordinate (n : ℕ) (x : nnrealUnitInterval n) : Set.Icc (0 : ℝ) 1 :=
  ⟨(x.1 : ℝ) - n, by
    constructor
    · exact sub_nonneg.mpr (by exact_mod_cast x.2.1)
    · rw [sub_le_iff_le_add]
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using! x.2.2⟩

/-- The canonical shifted unit path, expressed on the corresponding closed interval of `ℝ≥0`. -/
def globalDyadicFloorPiece (X : NNRat → Ω → E) (ω : Ω) (n : ℕ) :
    nnrealUnitInterval n → E :=
  fun x ↦ shiftedUnitDyadicFloorLimit n X ω (nnrealUnitCoordinate n x)



omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Canonical pieces agree wherever two closed unit intervals overlap. -/
theorem globalDyadicFloorPiece_eq_of_mem
    (X : NNRat → Ω → E) (ω : Ω) (n m : ℕ) (x : ℝ≥0)
    (hn : x ∈ nnrealUnitInterval n) (hm : x ∈ nnrealUnitInterval m) :
    globalDyadicFloorPiece X ω n ⟨x, hn⟩ = globalDyadicFloorPiece X ω m ⟨x, hm⟩ := by
  have hnm : n ≤ m + 1 := by exact_mod_cast hn.1.trans hm.2
  have hmn : m ≤ n + 1 := by exact_mod_cast hm.1.trans hn.2
  by_cases heq : n = m
  · subst m
    rfl
  by_cases hlt : n < m
  · have hmn' : m = n + 1 := by omega
    subst m
    have hmleft : (n : ℝ≥0) + 1 ≤ x := by
      simpa only [Nat.cast_add, Nat.cast_one] using hm.1
    have hx : x = (n : ℝ≥0) + 1 := le_antisymm hn.2 hmleft
    subst x
    have hleft : nnrealUnitCoordinate n ⟨(n + 1 : ℝ≥0), hn⟩ =
        (1 : Set.Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      norm_num [nnrealUnitCoordinate]
    have hright : nnrealUnitCoordinate (n + 1) ⟨(n + 1 : ℝ≥0), hm⟩ =
        (0 : Set.Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      norm_num [nnrealUnitCoordinate]
    rw [globalDyadicFloorPiece, globalDyadicFloorPiece, hleft, hright,
      shiftedUnitDyadicFloorLimit_one, shiftedUnitDyadicFloorLimit_zero]
    simp only [Nat.cast_add, Nat.cast_one]
  · have hnm' : n = m + 1 := by omega
    subst n
    exact (globalDyadicFloorPiece_eq_of_mem X ω m (m + 1) x hm hn).symm

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The closed unit intervals cover `ℝ≥0`. -/
theorem iUnion_nnrealUnitInterval : ⋃ n : ℕ, nnrealUnitInterval n = Set.univ := by
  apply Set.iUnion_eq_univ_iff.2
  intro x
  let n := ⌊(x : ℝ)⌋₊
  refine ⟨n, ?_⟩
  constructor
  · exact_mod_cast Nat.floor_le x.2
  · exact_mod_cast (Nat.lt_floor_add_one (x : ℝ)).le



omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The raw global path obtained by gluing the compatible canonical unit pieces. -/
def globalDyadicFloorLimit (X : NNRat → Ω → E) (ω : Ω) : ℝ≥0 → E :=
  Set.liftCover nnrealUnitInterval (globalDyadicFloorPiece X ω)
    (globalDyadicFloorPiece_eq_of_mem X ω) iUnion_nnrealUnitInterval









/-- A single global totalization: keep the raw path when it is continuous and otherwise use the
constant initial sample on the whole half-line. -/
def continuousGlobalDyadicFloorLimit (X : NNRat → Ω → E) (ω : Ω) : ℝ≥0 → E := by
  classical
  exact if Continuous (globalDyadicFloorLimit X ω) then globalDyadicFloorLimit X ω
    else fun _ ↦ X 0 ω





/-- The natural part of a nonnegative rational time. -/
def nnratNatFloor (t : NNRat) : ℕ := ⌊(t : ℝ)⌋₊

/-- The unit-interval remainder of a nonnegative rational time. -/
def nnratUnitRemainder (t : NNRat) : NNRat := t - nnratNatFloor t









end

end MarkovProcess


