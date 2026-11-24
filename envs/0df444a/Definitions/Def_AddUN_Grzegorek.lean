-- Prove2me | Definitions.Def_AddUN_Grzegorek
-- name    : AddUN_Grzegorek
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:24:20.888233+00:00
-- url     : https://prove2.me/theorems/129c3339-3818-4872-8aac-7b25b1993024
-- title:
--   Grzegorek
-- statement:
--   Definitions and structural lemmas for Grzegorek, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Grzegorek.lean

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
namespace AddUN
noncomputable def clopenEnum : ℕ → Clopens (ℕ → Bool) :=
  (exists_surjective_nat (Clopens (ℕ → Bool))).choose
open Classical in
/-- The `k`-th clopen set if its measure is at most `2⁻¹ ^ n`, and the empty set otherwise. -/
noncomputable def smallClopen (n k : ℕ) : Set (ℕ → Bool) :=
  if cantorMeasure (clopenEnum k) ≤ 2⁻¹ ^ n then clopenEnum k else ∅
def universalNull : Set ((ℕ → Bool) × (ℕ → ℕ)) :=
  {p | ∃ᶠ n in atTop, p.1 ∈ smallClopen n (p.2 n)}
end AddUN


