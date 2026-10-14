-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part10
-- name    : OAI_BinPackingGap_Part10
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T19:11:47.945135+00:00
-- url     : https://prove2.me/theorems/52833f3c-1af4-4f83-9f71-1d6685ac39a9
-- title:
--   Structural additive gap for bin packing, part 10 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 10 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Inventory/PhysicalPoolLift`, `Packing/ConstructLocalState`, `Packing/LocalTemplateBases`, `Configurations/ReductionFractional`, `Results/StructuralGap`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper. This part sets `maxHeartbeats` to 1000000, because the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/PhysicalPoolLift.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/ConstructLocalState.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/LocalTemplateBases.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Configurations/ReductionFractional.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Results/StructuralGap.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 10 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Inventory/PhysicalPoolLift.lean, Packing/ConstructLocalState.lean, Packing/LocalTemplateBases.lean, Configurations/ReductionFractional.lean, Results/StructuralGap.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper; `set_option maxHeartbeats 1000000` is set for this part (the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally).
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part09

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/PhysicalPoolLift.lean =====
namespace OAI

noncomputable section

open scoped BigOperators

namespace BinPackingGap

structure PoolTemplates (I : Instance) (T U F : Type*) where
  base : T → Finset I.Item
  globalPool : U → Finset I.Item
  flagPool : F → Finset I.Item
  globalSpecies : T → U
  flagSpecies : T → F
  global_nonempty : ∀ t, (globalPool (globalSpecies t)).Nonempty
  flag_nonempty : ∀ t, (flagPool (flagSpecies t)).Nonempty
  base_global : ∀ t, Disjoint (base t) (globalPool (globalSpecies t))
  base_flag : ∀ t, Disjoint (base t) (flagPool (flagSpecies t))
  global_flag : ∀ t,
    Disjoint (globalPool (globalSpecies t)) (flagPool (flagSpecies t))
  capacity : ∀ t (u : {i // i ∈ globalPool (globalSpecies t)})
    (f : {i // i ∈ flagPool (flagSpecies t)}),
    (∑ i ∈ base t ∪ {u.val, f.val}, I.size i) ≤ 1

namespace PoolTemplates

variable {I : Instance} {T U F : Type*} [Fintype T]

variable (D : PoolTemplates I T U F)

abbrev Globals (t : T) := {i // i ∈ D.globalPool (D.globalSpecies t)}
abbrev Flags (t : T) := {i // i ∈ D.flagPool (D.flagSpecies t)}
abbrev Sample := (t : T) × (D.Globals t × D.Flags t)

def column (t : T) (u : D.Globals t) (f : D.Flags t) : IndividualConfiguration I :=
  ⟨D.base t ∪ {u.val, f.val}, D.capacity t u f⟩

def sampleColumn (s : D.Sample) : IndividualConfiguration I :=
  D.column s.1 s.2.1 s.2.2

def templateMass (t : T) : ℝ :=
  1 / (2 * ((D.globalPool (D.globalSpecies t)).card : ℝ) *
    ((D.flagPool (D.flagSpecies t)).card : ℝ))

def sampleMass (s : D.Sample) : ℝ := D.templateMass s.1

def weights : IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward D.sampleColumn D.sampleMass

omit [Fintype T] in
theorem templateMass_nonneg (t : T) : 0 ≤ D.templateMass t := by
  unfold templateMass
  positivity

omit [Fintype T] in
theorem global_card_ne_zero (t : T) :
    ((D.globalPool (D.globalSpecies t)).card : ℝ) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr (D.global_nonempty t)).ne'

omit [Fintype T] in
theorem flag_card_ne_zero (t : T) :
    ((D.flagPool (D.flagSpecies t)).card : ℝ) ≠ 0 := by
  exact_mod_cast (Finset.card_pos.mpr (D.flag_nonempty t)).ne'

omit [Fintype T] in
theorem sum_templateMass (t : T) :
    (∑ _u : D.Globals t, ∑ _f : D.Flags t, D.templateMass t) = (1 / 2 : ℝ) := by
  have hu := D.global_card_ne_zero t
  have hf := D.flag_card_ne_zero t
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  unfold templateMass
  field_simp [hu, hf]

theorem objective_weights :
    FractionalCover.objective D.weights = (Fintype.card T : ℝ) / 2 := by
  rw [weights, FractionalCover.objective_pushforward]
  unfold FractionalCover.objective sampleMass
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, sum_templateMass]
  simp [div_eq_mul_inv]

theorem sum_pool_eq (S : Finset I.Item) (i : I.Item) (a : ℝ) :
    (∑ u : {j // j ∈ S}, if i = u.val then a else 0) =
      if i ∈ S then a else 0 := by
  classical
  by_cases hi : i ∈ S
  · have he : ∀ u : {j // j ∈ S}, i = u.val ↔ u = ⟨i, hi⟩ := by
      intro u
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        exact (congrArg Subtype.val h).symm
    simp only [he]
    simp [hi]
  · have he : ∀ u : {j // j ∈ S}, i ≠ u.val := by
      intro u h
      exact hi (h.symm ▸ u.property)
    simp [he, hi]

omit [Fintype T] in
theorem template_coverage (t : T) (i : I.Item) :
    (∑ u : D.Globals t, ∑ f : D.Flags t,
      (if i ∈ (D.column t u f).val then (1 : ℝ) else 0) * D.templateMass t) =
    (if i ∈ D.base t then (1 / 2 : ℝ) else 0) +
    (if i ∈ D.globalPool (D.globalSpecies t) then
      1 / (2 * ((D.globalPool (D.globalSpecies t)).card : ℝ)) else 0) +
    (if i ∈ D.flagPool (D.flagSpecies t) then
      1 / (2 * ((D.flagPool (D.flagSpecies t)).card : ℝ)) else 0) := by
  classical
  have hu := D.global_card_ne_zero t
  have hf := D.flag_card_ne_zero t
  by_cases hb : i ∈ D.base t
  · have hgu : i ∉ D.globalPool (D.globalSpecies t) :=
      fun h => Finset.disjoint_left.mp (D.base_global t) hb h
    have hfl : i ∉ D.flagPool (D.flagSpecies t) :=
      fun h => Finset.disjoint_left.mp (D.base_flag t) hb h
    simpa [column, hb, hgu, hfl] using D.sum_templateMass t
  · by_cases hg : i ∈ D.globalPool (D.globalSpecies t)
    · have hfl : i ∉ D.flagPool (D.flagSpecies t) :=
        fun h => Finset.disjoint_left.mp (D.global_flag t) hg h
      have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
          i ∈ (D.column t u f).val ↔ i = u.val := by
        intro u f
        have hn : i ≠ f.val := fun h => hfl (h.symm ▸ f.property)
        simp [column, hb, hn]
      simp only [hcol, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      simp_rw [sum_pool_eq]
      simp only [hb, hg, hfl, ite_false, ite_true, zero_add, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      unfold templateMass
      field_simp [hu, hf]
    · by_cases hfl : i ∈ D.flagPool (D.flagSpecies t)
      · have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
            i ∈ (D.column t u f).val ↔ i = f.val := by
          intro u f
          have hn : i ≠ u.val := fun h => hg (h.symm ▸ u.property)
          simp [column, hb, hn]
        simp only [hcol, ite_mul, one_mul, zero_mul]
        simp_rw [sum_pool_eq]
        simp only [hb, hg, hfl, ite_false, ite_true, zero_add,
          Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        unfold templateMass
        field_simp [hu, hf]
      · have hcol : ∀ u : D.Globals t, ∀ f : D.Flags t,
            i ∉ (D.column t u f).val := by
          intro u f
          have hnu : i ≠ u.val := fun h => hg (h.symm ▸ u.property)
          have hnf : i ≠ f.val := fun h => hfl (h.symm ▸ f.property)
          simp [column, hb, hnu, hnf]
        simp [hcol, hb, hg, hfl]

theorem sum_by_species {S : Type*} [Fintype S] [DecidableEq S]
    (species : T → S) (a : S → ℝ) :
    (∑ t, a (species t)) =
      ∑ s, ((Finset.univ.filter (fun t => species t = s)).card : ℝ) * a s := by
  classical
  calc
    (∑ t, a (species t)) = ∑ t, ∑ s, if species t = s then a s else 0 := by simp
    _ = ∑ s, ∑ t, if species t = s then a s else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp

theorem sum_pool_demands {S : Type*} [Fintype S] [DecidableEq S]
    (species : T → S) (pool : S → Finset I.Item)
    (hdemand : ∀ s, (Finset.univ.filter (fun t => species t = s)).card =
      2 * (pool s).card) (i : I.Item) :
    (∑ t, if i ∈ pool (species t) then
      1 / (2 * ((pool (species t)).card : ℝ)) else 0) =
    ∑ s, if i ∈ pool s then (1 : ℝ) else 0 := by
  classical
  rw [sum_by_species species (fun s =>
    if i ∈ pool s then 1 / (2 * ((pool s).card : ℝ)) else 0)]
  apply Finset.sum_congr rfl
  intro s _
  rw [hdemand s]
  by_cases hi : i ∈ pool s
  · have hs : ((pool s).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne'
    simp only [hi, ite_true, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hs]
  · simp [hi]

variable [Fintype U] [Fintype F] [DecidableEq U] [DecidableEq F]

theorem weights_feasible
    (labeled : Finset I.Item)
    (hbase : ∀ i, (Finset.univ.filter (fun t => i ∈ D.base t)).card =
      if i ∈ labeled then 2 else 0)
    (hglobal : ∀ u, (Finset.univ.filter (fun t => D.globalSpecies t = u)).card =
      2 * (D.globalPool u).card)
    (hflag : ∀ f, (Finset.univ.filter (fun t => D.flagSpecies t = f)).card =
      2 * (D.flagPool f).card)
    (hpartition : ∀ i,
      (if i ∈ labeled then (1 : ℝ) else 0) +
      (∑ u, if i ∈ D.globalPool u then (1 : ℝ) else 0) +
      (∑ f, if i ∈ D.flagPool f then (1 : ℝ) else 0) = 1) :
    IndividualFeasible I D.weights := by
  classical
  refine ⟨FractionalCover.pushforward_nonneg D.sampleColumn
    (fun s => D.templateMass_nonneg s.1), ?_⟩
  intro i
  change 1 ≤ ∑ H, individualMatrix I H i * D.weights H
  rw [weights, FractionalCover.coverage_pushforward]
  change 1 ≤ ∑ s : D.Sample,
    (if i ∈ (D.column s.1 s.2.1 s.2.2).val then (1 : ℝ) else 0) * D.templateMass s.1
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, template_coverage, Finset.sum_add_distrib]
  rw [sum_pool_demands D.globalSpecies D.globalPool hglobal,
    sum_pool_demands D.flagSpecies D.flagPool hflag]
  have hb : (∑ t, if i ∈ D.base t then (1 / 2 : ℝ) else 0) =
      if i ∈ labeled then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hbase]
    split_ifs <;> norm_num
  simpa only [hb, hpartition i] using (le_refl (1 : ℝ))

end PoolTemplates

end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/ConstructLocalState.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

def constructedLocalState (G : GraphInput) {d : ℕ} (T : CompetingTrees d)
    (hd : 0 < d) (R k : ℕ) (v : G.Vertex) (selected : Bool) :
    (ofCompetingTrees G T R k).LocalState v selected where
  localEquiv := LocalResourceAllocation.localEquiv G T hd R k v selected
  anchorEquiv := Classical.choose
    (LocalCompletionCoverage.exists_anchorEquiv G T hd R k v selected)
  completion_le_deadline := Classical.choose_spec
    (LocalCompletionCoverage.exists_anchorEquiv G T hd R k v selected)

end BinPackingGap.InventoryData

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/LocalTemplateBases.lean =====
namespace OAI

namespace BinPackingGap

open scoped BigOperators

theorem encoded_pattern_role_sum {n : ℕ} (p : Pattern) (v : Fin n) (w : Role → ℚ) :
    (∑ r, encodedSize (patternSubclass p r) (tableRoleLabel v v v r) (w r)) =
      1 + nu n * ∑ r, w r := by
  have hp : (∑ r, primaryScore (patternSubclass p r)) = 0 :=
    sum_primaryScore_eq_zero_of_coefficients _ (pattern_primaryCoeff_sum p)
  have hq : (∑ r, secondaryScore (patternSubclass p r) (tableRoleLabel v v v r)) = 0 := by
    rw [Role.sum_univ]
    cases p <;>
      simp [secondaryScore, patternSubclass, Subclass.role, tableRoleLabel] <;> ring
  have hpQ : (∑ r, (primaryScore (patternSubclass p r) : ℚ)) = 0 := by
    exact_mod_cast hp
  have hqQ : (∑ r, (secondaryScore (patternSubclass p r)
      (tableRoleLabel v v v r) : ℚ)) = 0 := by
    exact_mod_cast hq
  calc
    _ = (∑ _r : Role, (1 / 5 : ℚ)) +
        gamma * (∑ r, (primaryScore (patternSubclass p r) : ℚ)) +
        mu n * (∑ r, (secondaryScore (patternSubclass p r)
          (tableRoleLabel v v v r) : ℚ)) + nu n * ∑ r, w r := by
      simp only [encodedSize, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hpQ, hqQ]; norm_num

namespace InventoryData

variable (D : InventoryData)

def localTemplateItems {v : D.Vertex} (row : D.RowAt v) (anchor : D.AnchorAt v)
    (u : D.GlobalCopy) (l : D.LocalAt v) (flag : D.FlagCopy) : Role → D.Item
  | .x => ⟨.x, ⟨v, row⟩⟩
  | .anchor => ⟨.anchor, ⟨v, anchor⟩⟩
  | .«global» => ⟨.«global», u⟩
  | .«local» => ⟨.«local», ⟨v, l⟩⟩
  | .flag => ⟨.flag, flag⟩

@[simp] theorem localTemplateItems_role {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (r : Role) :
    D.itemRole (D.localTemplateItems row anchor u l flag r) = r := by
  cases r <;> rfl

theorem localTemplateItems_injective {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) :
    Function.Injective (D.localTemplateItems row anchor u l flag) := by
  intro r s h
  simpa only [localTemplateItems_role] using congrArg D.itemRole h

@[simp] theorem localTemplateItems_label {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (r : Role) :
    D.itemLabel (D.localTemplateItems row anchor u l flag r) =
      tableRoleLabel v v v r := by
  cases r <;> rfl

theorem localTemplate_coordinate_sum {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) :
    (∑ r, D.itemCoordinate (D.localTemplateItems row anchor u l flag r)) =
      D.rowCoordinate row + D.anchorCoordinate anchor + D.globalCoordinate u -
        D.localLength l := by
  rw [Role.sum_univ]
  simp only [localTemplateItems, itemCoordinate, localCoordinate, add_zero]
  ring

theorem localTemplate_size_sum {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (p : Pattern)
    (hpattern : ∀ r, D.itemSubclass (D.localTemplateItems row anchor u l flag r) =
      patternSubclass p r) :
    (∑ r, D.itemSize (D.localTemplateItems row anchor u l flag r)) =
      1 + nu D.graph.n * ∑ r,
        D.itemCoordinate (D.localTemplateItems row anchor u l flag r) := by
  simp only [itemSize, hpattern, localTemplateItems_label]
  exact encoded_pattern_role_sum p v _

def stateMainPattern {v : D.Vertex} : D.MBase v → Pattern
  | .inl (.inl _) => .plusTree
  | .inl (.inr (.inl _)) => .minusTree
  | .inl (.inr (.inr _)) => .plusTree
  | .inr _ => .mainJob

theorem stateMainTemplate_pattern {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) (r : Role) :
    D.itemSubclass (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r) = patternSubclass (D.stateMainPattern b) r := by
  rcases u with ⟨us, ui⟩
  rcases f with ⟨fs, fi⟩
  change us = D.stateMainGlobalSpecies selected b at hu
  change fs = D.stateFlagSpecies (.inl b) at hf
  subst us
  subst fs
  rcases b with (⟨node, copy⟩ | (⟨node, copy⟩ | padding)) | job
  all_goals cases r <;> rfl

theorem stateMainGlobal_coordinate {v : D.Vertex} (selected : Bool)
    (b : D.MBase v) (u : D.GlobalCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b) :
    D.globalCoordinate u = -D.stateMainLength selected b := by
  rcases u with ⟨us, ui⟩
  change us = D.stateMainGlobalSpecies selected b at hu
  subst us
  rcases b with (⟨node, copy⟩ | (⟨node, copy⟩ | padding)) | job <;> rfl

theorem stateMainTemplate_size_eq {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) :
    (∑ r, D.itemSize (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r)) =
      1 + nu D.graph.n * (D.rowCoordinate (D.stateMainRow v selected b) -
        D.stateMainLength selected b - D.localLength (.inl l) - D.deadline z) := by
  rw [D.localTemplate_size_sum _ _ _ _ _ (D.stateMainPattern b)
    (D.stateMainTemplate_pattern selected b z l u f hu hf)]
  rw [D.localTemplate_coordinate_sum, D.stateMainGlobal_coordinate selected b u hu]
  simp only [anchorCoordinate]
  ring

theorem stateMainTemplate_feasible_iff {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) :
    ((∑ r, D.itemSize (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r)) ≤ 1) ↔
      D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
        D.localLength (.inl l) ≤ D.deadline z := by
  rw [D.stateMainTemplate_size_eq selected b z l u f hu hf]
  have hnu := nu_pos D.graph.n
  constructor
  · intro h
    have hmul : nu D.graph.n *
        (D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
          D.localLength (.inl l) - D.deadline z) ≤ nu D.graph.n * 0 := by linarith
    exact sub_nonpos.mp (le_of_mul_le_mul_left hmul hnu)
  · intro h
    have hmul := mul_nonpos_of_nonneg_of_nonpos hnu.le (sub_nonpos.mpr h)
    linarith

theorem edgeTemplate_size_eq {v : D.Vertex} (short permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (short, j))
      (.inr j) u (.inr j) f r)) =
      1 + nu D.graph.n *
        ((if permit then 0 else Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) -
          (if short then Geometry.delta D.graph.edges.length D.R D.geometryBound D.L else 0)) := by
  rcases u with ⟨us, ui⟩
  rcases f with ⟨fs, fi⟩
  change us = .edge (D.jobPosition j).1 permit at hu
  change fs = .edge at hf
  subst us
  subst fs
  rw [D.localTemplate_size_sum _ _ _ _ _ .edgeJob (by intro r; cases r <;> rfl)]
  rw [D.localTemplate_coordinate_sum]
  simp only [rowCoordinate, rowBaseline, rowShort, anchorCoordinate,
    globalCoordinate, localLength]
  cases short <;> cases permit <;> simp <;> ring_nf <;> simp

theorem edgeTemplate_feasible_iff {v : D.Vertex} (short permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    ((∑ r, D.itemSize (D.localTemplateItems (.inr (short, j))
      (.inr j) u (.inr j) f r)) ≤ 1) ↔ short = true ∨ permit = true := by
  rw [D.edgeTemplate_size_eq short permit j u f hu hf]
  have hnu := nu_pos D.graph.n
  have hdelta := Geometry.delta_pos D.graph.edges.length D.R D.geometryBound D.L
  have hproduct := mul_pos hnu hdelta
  cases short <;> cases permit <;> simp <;> nlinarith

theorem edgeTemplate_short_feasible {v : D.Vertex} (permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (true, j))
      (.inr j) u (.inr j) f r)) ≤ 1 :=
  (D.edgeTemplate_feasible_iff true permit j u f hu hf).mpr (Or.inl rfl)

theorem edgeTemplate_long_feasible_iff {v : D.Vertex} (permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    ((∑ r, D.itemSize (D.localTemplateItems (.inr (false, j))
      (.inr j) u (.inr j) f r)) ≤ 1) ↔ permit = true := by
  simpa using D.edgeTemplate_feasible_iff false permit j u f hu hf

theorem stateEdgeTemplate_size_eq_one {v : D.Vertex} (selected : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 (!selected)) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (selected, j))
      (.inr j) u (.inr j) f r)) = 1 := by
  rw [D.edgeTemplate_size_eq selected (!selected) j u f hu hf]
  cases selected <;> simp

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

abbrev Template := Σ v : D.Vertex, Bool × D.LocalBin v

def templateGlobalSpecies (t : D.Template) : GlobalSpecies D.graph :=
  D.stateGlobalSpecies t.2.1 t.2.2

def templateFlagSpecies (t : D.Template) : FlagSpecies :=
  D.stateFlagSpecies t.2.2

def templateRowCopy (t : D.Template) : Σ v : D.Vertex, D.RowAt v :=
  ⟨t.1, D.stateRowEquiv t.1 t.2.1 t.2.2⟩

def templateAnchorCopy (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Σ v : D.Vertex, D.AnchorAt v :=
  ⟨t.1, (S t.1 t.2.1).anchorAtEquiv t.2.2⟩

def templateLocalCopy (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Σ v : D.Vertex, D.LocalAt v :=
  ⟨t.1, (S t.1 t.2.1).localAtEquiv t.2.2⟩

def templateBase (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Finset D.packingInstance.Item :=
  {D.itemEquiv ⟨.x, D.templateRowCopy t⟩,
   D.itemEquiv ⟨.anchor, D.templateAnchorCopy S t⟩,
   D.itemEquiv ⟨.«local», D.templateLocalCopy S t⟩}

theorem templateBase_subset_labeledItems (S : ∀ v s, D.LocalState v s)
    (t : D.Template) : D.templateBase S t ⊆ D.labeledItems := by
  intro i hi
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp

private theorem templateTagged_ne {r s : Role} (hrs : r ≠ s)
    (a : D.RoleCopies r) (b : D.RoleCopies s) :
    D.itemEquiv ⟨r, a⟩ ≠ D.itemEquiv ⟨s, b⟩ := by
  intro h
  exact hrs (congrArg (fun i : D.Item => i.1) (D.itemEquiv.injective h))

private theorem templateTagged_eq_iff (r : Role) (a b : D.RoleCopies r) :
    D.itemEquiv ⟨r, a⟩ = D.itemEquiv ⟨r, b⟩ ↔ a = b := by
  constructor
  · intro h
    exact sigma_mk_injective (β := D.RoleCopies) (i := r) (D.itemEquiv.injective h)
  · rintro rfl
    rfl

theorem card_templateBase (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    (D.templateBase S t).card = 3 := by
  unfold templateBase
  apply Finset.card_triple_eq_three_iff.mpr
  exact ⟨D.templateTagged_ne (by decide : Role.x ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.x ≠ .«local») _ _,
    D.templateTagged_ne (by decide : Role.anchor ≠ .«local») _ _⟩

def templateCopyEquiv {C : D.Vertex → Type*}
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) : D.Template ≃ Bool × (Σ v, C v) where
  toFun t := (t.2.1, ⟨t.1, e t.1 t.2.1 t.2.2⟩)
  invFun t := ⟨t.2.1, t.1, (e t.2.1 t.1).symm t.2.2⟩
  left_inv := by
    rintro ⟨v, s, b⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s, v, c⟩
    simp only [Equiv.apply_symm_apply]

@[simp] theorem templateCopyEquiv_apply {C : D.Vertex → Type*}
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) (t : D.Template) :
    D.templateCopyEquiv e t = (t.2.1, ⟨t.1, e t.1 t.2.1 t.2.2⟩) := rfl

private def templateFiberBoolEquiv {T C : Type*} (e : T ≃ Bool × C) (c : C) :
    {t : T // (e t).2 = c} ≃ Bool where
  toFun x := (e x.1).1
  invFun b := ⟨e.symm (b, c), by simp only [Equiv.apply_symm_apply]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply e.injective
    change e (e.symm ((e x.1).1, c)) = e x.1
    rw [e.apply_symm_apply]
    exact Prod.ext rfl x.2.symm
  right_inv := by
    intro b
    simp only [Equiv.apply_symm_apply]

theorem card_templateCopy_fiber {C : D.Vertex → Type*}
    [DecidableEq (Σ v, C v)]
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) (c : Σ v, C v) :
    ((Finset.univ : Finset D.Template).filter
      (fun t => (D.templateCopyEquiv e t).2 = c)).card = 2 := by
  classical
  rw [← Fintype.card_subtype (fun t : D.Template => (D.templateCopyEquiv e t).2 = c)]
  exact (Fintype.card_congr (templateFiberBoolEquiv (D.templateCopyEquiv e) c)).trans
    Fintype.card_bool

private theorem card_templatePredicate {C : Type*}
    (e : D.Template ≃ Bool × C) (c : C) (p : D.Template → Prop) [DecidablePred p]
    (hp : ∀ t, p t ↔ (e t).2 = c) :
    ((Finset.univ : Finset D.Template).filter p).card = 2 := by
  rw [← Fintype.card_subtype p]
  exact (Fintype.card_congr
    ((Equiv.subtypeEquivRight hp).trans (templateFiberBoolEquiv e c))).trans
      Fintype.card_bool

@[simp] theorem itemEquiv_x_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .x) :
    D.itemEquiv ⟨.x, c⟩ ∈ D.templateBase S t ↔ D.templateRowCopy t = c := by
  have hxa := D.templateTagged_ne (by decide : Role.x ≠ .anchor) c
    (D.templateAnchorCopy S t)
  have hxl := D.templateTagged_ne (by decide : Role.x ≠ .«local») c
    (D.templateLocalCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hxa, hxl, or_false]
  exact (D.templateTagged_eq_iff .x c (D.templateRowCopy t)).trans eq_comm

@[simp] theorem itemEquiv_anchor_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .anchor) :
    D.itemEquiv ⟨.anchor, c⟩ ∈ D.templateBase S t ↔ D.templateAnchorCopy S t = c := by
  have hax := D.templateTagged_ne (by decide : Role.anchor ≠ .x) c
    (D.templateRowCopy t)
  have hal := D.templateTagged_ne (by decide : Role.anchor ≠ .«local») c
    (D.templateLocalCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hax, hal,
    false_or, or_false]
  exact (D.templateTagged_eq_iff .anchor c (D.templateAnchorCopy S t)).trans eq_comm

@[simp] theorem itemEquiv_local_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .«local») :
    D.itemEquiv ⟨.«local», c⟩ ∈ D.templateBase S t ↔ D.templateLocalCopy S t = c := by
  have hlx := D.templateTagged_ne (by decide : Role.«local» ≠ .x) c
    (D.templateRowCopy t)
  have hla := D.templateTagged_ne (by decide : Role.«local» ≠ .anchor) c
    (D.templateAnchorCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hlx, hla, false_or]
  exact (D.templateTagged_eq_iff .«local» c (D.templateLocalCopy S t)).trans eq_comm

@[simp] theorem itemEquiv_global_not_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .«global») :
    D.itemEquiv ⟨.«global», c⟩ ∉ D.templateBase S t := by
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.templateTagged_ne (by decide : Role.«global» ≠ .x) _ _,
    D.templateTagged_ne (by decide : Role.«global» ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.«global» ≠ .«local») _ _⟩

@[simp] theorem itemEquiv_flag_not_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .flag) :
    D.itemEquiv ⟨.flag, c⟩ ∉ D.templateBase S t := by
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.templateTagged_ne (by decide : Role.flag ≠ .x) _ _,
    D.templateTagged_ne (by decide : Role.flag ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.flag ≠ .«local») _ _⟩

theorem templateBase_appearance_count (S : ∀ v s, D.LocalState v s)
    (i : D.packingInstance.Item) :
    ((Finset.univ : Finset D.Template).filter (fun t => i ∈ D.templateBase S t)).card =
      if i ∈ D.labeledItems then 2 else 0 := by
  classical
  obtain ⟨⟨r, c⟩, rfl⟩ := D.itemEquiv.surjective i
  cases r with
  | x =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate (D.templateCopyEquiv (fun v s => D.stateRowEquiv v s)) c
      (fun t => D.itemEquiv ⟨.x, c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateRowCopy] using
      D.itemEquiv_x_mem_templateBase S t c
  | anchor =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate
      (D.templateCopyEquiv (fun v s => (S v s).anchorAtEquiv)) c
      (fun t => D.itemEquiv ⟨.anchor, c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateAnchorCopy] using
      D.itemEquiv_anchor_mem_templateBase S t c
  | «global» => simp
  | «local» =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate
      (D.templateCopyEquiv (fun v s => (S v s).localAtEquiv)) c
      (fun t => D.itemEquiv ⟨.«local», c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateLocalCopy] using
      D.itemEquiv_local_mem_templateBase S t c
  | flag => simp

@[simp] theorem packingInstance_size_itemEquiv (i : D.Item) :
    D.packingInstance.size (D.itemEquiv i) = D.itemSize i := by
  change D.itemSize (D.itemEquiv.symm (D.itemEquiv i)) = D.itemSize i
  rw [Equiv.symm_apply_apply]

theorem templateBase_complete_eq_image (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy) :
    D.templateBase S t ∪ {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩} =
      Finset.univ.image (fun r => D.itemEquiv
        (D.localTemplateItems (D.stateRowEquiv t.1 t.2.1 t.2.2)
          ((S t.1 t.2.1).anchorAtEquiv t.2.2) u
          ((S t.1 t.2.1).localAtEquiv t.2.2) f r)) := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    simp only [Finset.mem_union, templateBase, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with (rfl | rfl | rfl) | (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨.x, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.anchor, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.«local», Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.«global», Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.flag, Finset.mem_univ _, rfl⟩
  · intro hi
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    cases r with
    | x =>
      apply Finset.mem_union_left
      exact Finset.mem_insert_self _ _
    | anchor =>
      apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      exact Finset.mem_insert_self _ _
    | «global» =>
      apply Finset.mem_union_right
      exact Finset.mem_insert_self _ _
    | «local» =>
      apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton_self _
    | flag =>
      apply Finset.mem_union_right
      apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton_self _

theorem templateBase_size_sum (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy) :
    (∑ i ∈ D.templateBase S t ∪
      {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩}, D.packingInstance.size i) =
    ∑ r, D.itemSize (D.localTemplateItems (D.stateRowEquiv t.1 t.2.1 t.2.2)
      ((S t.1 t.2.1).anchorAtEquiv t.2.2) u
      ((S t.1 t.2.1).localAtEquiv t.2.2) f r) := by
  rw [D.templateBase_complete_eq_image S t u f, Finset.sum_image]
  · simp only [packingInstance_size_itemEquiv]
  · intro r _ r' _ h
    exact D.localTemplateItems_injective _ _ _ _ _ (D.itemEquiv.injective h)

theorem templateBase_capacity (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.templateGlobalSpecies t) (hf : f.1 = D.templateFlagSpecies t) :
    (∑ i ∈ D.templateBase S t ∪
      {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩}, D.packingInstance.size i) ≤ 1 := by
  rw [D.templateBase_size_sum S t u f]
  rcases t with ⟨v, selected, b⟩
  rcases b with b | j
  · exact (D.stateMainTemplate_feasible_iff selected b ((S v selected).anchorEquiv b)
      ((S v selected).localEquiv b) u f hu hf).mpr
        ((S v selected).completion_le_deadline b)
  · exact (D.stateEdgeTemplate_size_eq_one selected j u f hu hf).le

end BinPackingGap.InventoryData

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Configurations/ReductionFractional.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem card_template : Fintype.card D.Template = 2 * D.B := by
  simp only [Template, Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool,
    D.card_localBin]
  rw [← Finset.mul_sum]
  rfl

def statePoolTemplates (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    PoolTemplates D.packingInstance D.Template (GlobalSpecies D.graph) FlagSpecies where
  base := D.templateBase S
  globalPool := D.physicalGlobalPool
  flagPool := D.physicalFlagPool
  globalSpecies := D.templateGlobalSpecies
  flagSpecies := D.templateFlagSpecies
  global_nonempty := by
    intro t
    apply (D.physicalGlobalPool_nonempty_iff _).mpr
    have hc := D.doubled_stateGlobalSpecies_count hn (D.templateGlobalSpecies t)
    have hp : 0 < (Finset.univ.filter (fun q : D.Template =>
        D.templateGlobalSpecies q = D.templateGlobalSpecies t)).card := by
      exact Finset.card_pos.mpr ⟨t, by simp⟩
    change (Finset.univ.filter (fun q : D.Template =>
      D.templateGlobalSpecies q = D.templateGlobalSpecies t)).card = _ at hc
    omega
  flag_nonempty := by
    intro t
    apply (D.physicalFlagPool_nonempty_iff _).mpr
    have hc := D.doubled_stateFlagSpecies_count (D.templateFlagSpecies t)
    have hp : 0 < (Finset.univ.filter (fun q : D.Template =>
        D.templateFlagSpecies q = D.templateFlagSpecies t)).card := by
      exact Finset.card_pos.mpr ⟨t, by simp⟩
    change (Finset.univ.filter (fun q : D.Template =>
      D.templateFlagSpecies q = D.templateFlagSpecies t)).card = _ at hc
    omega
  base_global := fun t =>
    (D.labeledItems_disjoint_physicalGlobalPool (D.templateGlobalSpecies t)).mono_left
      (D.templateBase_subset_labeledItems S t)
  base_flag := fun t =>
    (D.labeledItems_disjoint_physicalFlagPool (D.templateFlagSpecies t)).mono_left
      (D.templateBase_subset_labeledItems S t)
  global_flag := fun t => D.physicalGlobalPool_disjoint_physicalFlagPool
    (D.templateGlobalSpecies t) (D.templateFlagSpecies t)
  capacity := by
    intro t u f
    obtain ⟨j, hj⟩ := (D.mem_physicalGlobalPool (D.templateGlobalSpecies t) u.val).mp
      u.property
    obtain ⟨l, hl⟩ := (D.mem_physicalFlagPool (D.templateFlagSpecies t) f.val).mp
      f.property
    rw [← hj, ← hl]
    exact D.templateBase_capacity S t ⟨D.templateGlobalSpecies t, j⟩
      ⟨D.templateFlagSpecies t, l⟩ rfl rfl

theorem statePoolTemplates_feasible (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    IndividualFeasible D.packingInstance (D.statePoolTemplates hn S).weights := by
  apply (D.statePoolTemplates hn S).weights_feasible D.labeledItems
  · exact D.templateBase_appearance_count S
  · intro s
    change (Finset.univ.filter (fun t : D.Template =>
      D.templateGlobalSpecies t = s)).card = 2 * (D.physicalGlobalPool s).card
    rw [D.card_physicalGlobalPool]
    exact D.doubled_stateGlobalSpecies_count hn s
  · intro f
    change (Finset.univ.filter (fun t : D.Template =>
      D.templateFlagSpecies t = f)).card = 2 * (D.physicalFlagPool f).card
    rw [D.card_physicalFlagPool]
    exact D.doubled_stateFlagSpecies_count f
  · exact D.physicalInventory_indicator_partition

theorem statePoolTemplates_objective (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    FractionalCover.objective (D.statePoolTemplates hn S).weights = (D.B : ℝ) := by
  rw [(D.statePoolTemplates hn S).objective_weights, D.card_template]
  push_cast
  ring

theorem ofCompetingTrees_physical_witness (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ) (hn : G.n = 2 * k) :
    ∃ w : IndividualConfiguration (ofCompetingTrees G T R k).packingInstance → ℝ,
      IndividualFeasible (ofCompetingTrees G T R k).packingInstance w ∧
      FractionalCover.objective w = ((ofCompetingTrees G T R k).B : ℝ) := by
  let D := ofCompetingTrees G T R k
  let S : ∀ v s, D.LocalState v s := constructedLocalState G T hd R k
  exact ⟨(D.statePoolTemplates hn S).weights,
    D.statePoolTemplates_feasible hn S, D.statePoolTemplates_objective hn S⟩

theorem ofCompetingTrees_bothLP_eq (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ) (hn : G.n = 2 * k) :
    individualLP (ofCompetingTrees G T R k).packingInstance =
        ((ofCompetingTrees G T R k).B : ℝ) ∧
      typeLP (ofCompetingTrees G T R k).packingInstance =
        ((ofCompetingTrees G T R k).B : ℝ) := by
  obtain ⟨w, hw, hobj⟩ := ofCompetingTrees_physical_witness G T hd R k hn
  exact bothLP_eq_of_physical_witness _ _
    ((ofCompetingTrees G T R k).packingInstance_n (by change k ≤ G.n; omega))
    (fun i => ((ofCompetingTrees G T R k).packingInstance_size_mem_interval i).1)
    w hw hobj

end BinPackingGap.InventoryData

end

namespace BinPackingGap

theorem reduction_bothLP_eq (c : ℕ) (rho : ℝ) (G : GraphInput) (k : ℕ)
    (hn : G.n = 2 * k) :
    individualLP (reductionInstance c rho G k) =
        (reductionBinBound c rho G k : ℝ) ∧
      typeLP (reductionInstance c rho G k) =
        (reductionBinBound c rho G k : ℝ) :=
  InventoryData.ofCompetingTrees_bothLP_eq G (reductionTrees c rho)
    (depthDemand_pos c rho) _ k hn

end BinPackingGap

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Results/StructuralGap.lean =====
namespace OAI

namespace BinPackingGap

theorem completeFourGraph_reduction_bothLP_eq (c : ℕ) :
    individualLP (reductionInstance c (1 / 8) completeFourGraph 2) =
        (reductionBinBound c (1 / 8) completeFourGraph 2 : ℝ) ∧
      typeLP (reductionInstance c (1 / 8) completeFourGraph 2) =
        (reductionBinBound c (1 / 8) completeFourGraph 2 : ℝ) :=
  reduction_bothLP_eq c (1 / 8) completeFourGraph 2 (by decide)

theorem structural_additive_gap (c : ℕ) :
    ∃ I : Instance, ∃ B : ℕ,
      I.n = 5 * B ∧
      (∀ i, (1 / 6 : ℚ) < I.size i ∧ I.size i < 1) ∧
      B + c < opt I ∧ individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ) := by
  refine ⟨reductionInstance c (1 / 8) completeFourGraph 2,
    reductionBinBound c (1 / 8) completeFourGraph 2,
    reductionInstance_count c (1 / 8) completeFourGraph 2 (by decide),
    reductionInstance_size_bounds c (1 / 8) completeFourGraph 2,
    completeFourGraph_reduction_opt_gap c, ?_⟩
  exact completeFourGraph_reduction_bothLP_eq c

theorem exists_mirup_counterexample :
    ∃ I : Instance,
      Nat.ceil (individualLP I) + 1 < opt I ∧
        Nat.ceil (typeLP I) + 1 < opt I := by
  obtain ⟨I, B, _, _, hgap, hindividual, htype⟩ := structural_additive_gap 1
  refine ⟨I, ?_, ?_⟩
  · simpa only [hindividual, Nat.ceil_natCast] using hgap
  · simpa only [htype, Nat.ceil_natCast] using hgap

theorem individual_mirup_false :
    ¬ ∀ I : Instance, opt I ≤ Nat.ceil (individualLP I) + 1 := by
  intro h
  obtain ⟨I, hi, _⟩ := exists_mirup_counterexample
  exact (not_le_of_gt hi) (h I)

theorem type_mirup_false :
    ¬ ∀ I : Instance, opt I ≤ Nat.ceil (typeLP I) + 1 := by
  intro h
  obtain ⟨I, _, hi⟩ := exists_mirup_counterexample
  exact (not_le_of_gt hi) (h I)

end BinPackingGap

end OAI


