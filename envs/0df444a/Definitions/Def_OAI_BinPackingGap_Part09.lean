-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part09
-- name    : OAI_BinPackingGap_Part09
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T19:02:15.609023+00:00
-- url     : https://prove2.me/theorems/4eca7b98-934f-4ef5-9749-c8055efc3b07
-- title:
--   Structural additive gap for bin packing, part 9 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 9 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Configurations/K4Soundness`, `Packing/LocalJobCounts`, `Inventory/IntegralSpeciesCounts`, `Configurations/ConfigurationLP`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper. This part sets `maxHeartbeats` to 1000000, because the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Configurations/K4Soundness.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/LocalJobCounts.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/IntegralSpeciesCounts.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Configurations/ConfigurationLP.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 9 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Configurations/K4Soundness.lean, Packing/LocalJobCounts.lean, Inventory/IntegralSpeciesCounts.lean, Configurations/ConfigurationLP.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper; `set_option maxHeartbeats 1000000` is set for this part (the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally).
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part08

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- ===== Adapted from lean/OAI/Computability/BinPacking/Configurations/K4Soundness.lean =====
namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap

private def leftIncidencePosition (G : GraphInput) (R : ℕ) (edge : G.Edge) (j : Fin R) :
    G.IncidencePosition R (G.left edge) :=
  (⟨(edge, 0), G.endpoint_zero edge⟩, j)

private def rightIncidencePosition (G : GraphInput) (R : ℕ) (edge : G.Edge) (j : Fin R) :
    G.IncidencePosition R (G.right edge) :=
  (⟨(edge, 1), G.endpoint_one edge⟩, j)

theorem extractedCover_isCover (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) {b : ℕ} (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    G.IsCover (extractedCover c ρ G k p) := by
  classical
  let D := reductionInventory c ρ G k
  let Sleft : G.Edge → Finset (Fin D.R) := fun edge =>
    PackingCounts.goodRepetitions p D.itemEquiv (G.left edge) edge
  let Sright : G.Edge → Finset (Fin D.R) := fun edge =>
    PackingCounts.goodRepetitions p D.itemEquiv (G.right edge) edge
  let Lleft : G.Edge → Fin D.R → ℕ := fun edge j =>
    (D.edgeLongTuplesAt p edge (0, j)).card
  let Lright : G.Edge → Fin D.R → ℕ := fun edge j =>
    (D.edgeLongTuplesAt p edge (1, j)).card
  have hL : 1 ≤ D.L := Nat.succ_le_of_lt (reductionInventory_height_pos c ρ G k)
  apply thresholdCover_isCover G (PackingCounts.xplus p D.itemEquiv)
    Sleft Sright Lleft Lright (depthDemand_one_le c ρ) (depthDemand_ge_72 c ρ)
    (reductionInventory_R c ρ G k)
  · intro edge
    exact PackingCounts.goodRepetitions_card_ge_real p D.itemEquiv hL (G.left edge) edge
  · intro edge
    exact PackingCounts.goodRepetitions_card_ge_real p D.itemEquiv hL (G.right edge) edge
  · intro edge j hj
    have hj' : (edge, j) ∉ PackingCounts.excludedAt p D.itemEquiv (G.left edge) :=
      (mem_nonexcludedRepetitions _ _).mp hj
    exact D.long_matches_at_nonexcluded (reductionInventory_plus_height c ρ G k)
      (reductionInventory_minus_height c ρ G k) hL hk p hb (G.left edge)
      (leftIncidencePosition G D.R edge j) hj'
  · intro edge j hj
    have hj' : (edge, j) ∉ PackingCounts.excludedAt p D.itemEquiv (G.right edge) :=
      (mem_nonexcludedRepetitions _ _).mp hj
    exact D.long_matches_at_nonexcluded (reductionInventory_plus_height c ρ G k)
      (reductionInventory_minus_height c ρ G k) hL hk p hb (G.right edge)
      (rightIncidencePosition G D.R edge j) hj'
  · intro edge
    have hcap := D.edge_long_matches_capacity hk p hb edge Finset.univ
    have htwo : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    change (∑ j : Fin D.R, Lleft edge j) + (∑ j : Fin D.R, Lright edge j) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c
    simpa [htwo, Lleft, Lright] using hcap

theorem packing_extracts_cover (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : GraphInput) (k : ℕ) (hk : k ≤ G.n) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    ∃ C : Finset G.Vertex, G.IsCover C ∧ (C.card : ℝ) ≤ (k : ℝ) + ρ * G.n :=
  ⟨extractedCover c ρ G k p, extractedCover_isCover c ρ G k hk p hb,
    extractedCover_card_le c ρ hρ G k hk p hb⟩

end BinPackingGap

end

namespace BinPackingGap

theorem completeFourGraph_reduction_no_packing (c : ℕ) :
    ¬ HasPacking (reductionInstance c (1 / 8) completeFourGraph 2)
      (reductionBinBound c (1 / 8) completeFourGraph 2 + c) := by
  rintro ⟨p⟩
  exact completeFourGraph_no_small_cover
    (packing_extracts_cover c (1 / 8) (by norm_num) completeFourGraph 2
      (by decide) p le_rfl)

theorem completeFourGraph_reduction_opt_gap (c : ℕ) :
    reductionBinBound c (1 / 8) completeFourGraph 2 + c <
      opt (reductionInstance c (1 / 8) completeFourGraph 2) :=
  (not_hasPacking_iff_lt_opt _ _).mp (completeFourGraph_reduction_no_packing c)

end BinPackingGap

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/LocalJobCounts.lean =====
namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem card_jobCopy_edge_of_endpoint (v : D.Vertex) (e : D.Edge) (s : Fin 2)
    (hs : D.graph.endpoint e s = v) :
    (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card =
      D.d * D.R := by
  classical
  let f : Fin D.R × Fin D.d → D.JobCopy v :=
    fun rc => ((⟨(e, s), hs⟩, rc.1), rc.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Prod.ext
    · exact congrArg (fun j : D.JobCopy v => j.1.2) hab
    · exact congrArg (fun j : D.JobCopy v => j.2) hab
  have hfilter :
      Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e) =
        Finset.univ.image f := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      apply Finset.mem_image.mpr
      refine ⟨(j.1.2, j.2), Finset.mem_univ _, ?_⟩
      rcases j with ⟨⟨⟨⟨e', s'⟩, hv⟩, r⟩, c⟩
      change e' = e at hj
      subst e'
      have hslot : s = s' := D.graph.endpoint_injective e (hs.trans hv.symm)
      subst s'
      rfl
    · intro hj
      obtain ⟨rc, _, rfl⟩ := Finset.mem_image.mp hj
      rfl
  rw [hfilter, Finset.card_image_of_injective _ hf, Finset.card_univ]
  simp [Nat.mul_comm]

theorem card_jobCopy_edge (v : D.Vertex) (e : D.Edge) :
    (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card =
      if D.graph.left e = v ∨ D.graph.right e = v then D.d * D.R else 0 := by
  classical
  by_cases hv : D.graph.left e = v ∨ D.graph.right e = v
  · rw [ite_eq_left hv]
    rcases hv with hl | hr
    · exact D.card_jobCopy_edge_of_endpoint v e 0 (by simpa using hl)
    · exact D.card_jobCopy_edge_of_endpoint v e 1 (by simpa using hr)
  · rw [ite_eq_right hv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    apply hv
    have he : j.1.1.val.1 = e := (Finset.mem_filter.mp hj).2
    have hep : D.graph.endpoint e j.1.1.val.2 = v := by
      rw [← he]
      exact j.1.1.property
    have hslot : j.1.1.val.2 = 0 ∨ j.1.1.val.2 = 1 := by omega
    rcases hslot with hzero | hone
    · left
      simpa only [hzero, GraphInput.endpoint_zero] using hep
    · right
      simpa only [hone, GraphInput.endpoint_one] using hep

theorem sum_card_jobCopy_edge (e : D.Edge) :
    (∑ v : D.Vertex,
      (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card) =
      2 * D.d * D.R := by
  classical
  calc
    _ =
        (Finset.univ.filter (fun j : D.JobCopy (D.graph.left e) =>
          (D.jobPosition j).1 = e)).card +
        (Finset.univ.filter (fun j : D.JobCopy (D.graph.right e) =>
          (D.jobPosition j).1 = e)).card := by
      refine Finset.sum_eq_add_of_mem (D.graph.left e) (D.graph.right e)
        (Finset.mem_univ _) (Finset.mem_univ _) (D.graph.left_ne_right e) ?_
      intro v _ hv
      rw [D.card_jobCopy_edge]
      simp [Ne.symm hv.1, Ne.symm hv.2]
    _ = D.d * D.R + D.d * D.R := by simp [D.card_jobCopy_edge]
    _ = 2 * D.d * D.R := by simp [two_mul, Nat.add_mul]

end BinPackingGap.InventoryData

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/IntegralSpeciesCounts.lean =====
namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

private theorem up_indicator_add (g : GlobalSpecies D.graph) :
    (if g = .up true then 1 else 0) + (if g = .up false then 1 else 0) =
      match g with | .up _ => 1 | _ => 0 := by
  cases g with
  | up b => cases b <;> rfl
  | um b => rfl
  | edge e b => rfl

private theorem um_indicator_add (g : GlobalSpecies D.graph) :
    (if g = .um true then 1 else 0) + (if g = .um false then 1 else 0) =
      match g with | .um _ => 1 | _ => 0 := by
  cases g with
  | up b => rfl
  | um b => cases b <;> rfl
  | edge e b => rfl

private theorem root_copy_indicator_sum (T : UniformTree) (d : ℕ) :
    (∑ node : T.Node, ∑ _j : Fin d, if node = T.root then (1 : ℕ) else 0) = d := by
  classical
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Nat.cast_id]

theorem stateGlobalSpecies_up_true_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up true)).card =
        if selected then D.d else 0 := by
  classical
  cases selected <;>
    simp [-Finset.sum_boole, Finset.card_filter, LocalBin, MBase, TreeRow,
      Fintype.sum_sum_type, Fintype.sum_prod_type, stateGlobalSpecies,
      stateMainGlobalSpecies]
  exact root_copy_indicator_sum D.plus D.d

theorem stateGlobalSpecies_um_true_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um true)).card =
        if selected then 0 else D.d := by
  classical
  cases selected <;>
    simp [-Finset.sum_boole, Finset.card_filter, LocalBin, MBase, TreeRow,
      Fintype.sum_sum_type, Fintype.sum_prod_type, stateGlobalSpecies,
      stateMainGlobalSpecies]
  exact root_copy_indicator_sum D.minus D.d

theorem stateGlobalSpecies_up_total (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up true)).card +
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies selected b = .up false)).card = D.tPlus + D.J v := by
  classical
  simp only [Finset.card_filter, ← Finset.sum_add_distrib, D.up_indicator_add]
  simp [LocalBin, MBase, TreeRow, Fintype.sum_sum_type,
    stateGlobalSpecies, stateMainGlobalSpecies, D.card_jobCopy, tPlus,
    Nat.mul_comm, Nat.add_assoc]

theorem stateGlobalSpecies_um_total (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um true)).card +
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies selected b = .um false)).card = D.tMinus := by
  classical
  simp only [Finset.card_filter, ← Finset.sum_add_distrib, D.um_indicator_add]
  simp [LocalBin, MBase, TreeRow, Fintype.sum_sum_type,
    stateGlobalSpecies, stateMainGlobalSpecies, tMinus, Nat.mul_comm]

theorem stateGlobalSpecies_up_false_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .up false)).card =
        D.tPlus + D.J v - (if selected then D.d else 0) := by
  have h := D.stateGlobalSpecies_up_total v selected
  rw [D.stateGlobalSpecies_up_true_count] at h
  omega

theorem stateGlobalSpecies_um_false_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um false)).card =
        D.tMinus - (if selected then 0 else D.d) := by
  have h := D.stateGlobalSpecies_um_total v selected
  rw [D.stateGlobalSpecies_um_true_count] at h
  omega

theorem stateGlobalSpecies_edge_count (v : D.Vertex) (selected : Bool)
    (e : D.Edge) (permit : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .edge e permit)).card =
        if permit = !selected ∧ (D.graph.left e = v ∨ D.graph.right e = v)
        then D.d * D.R else 0 := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  by_cases hp : permit = !selected
  · subst permit
    simpa [-Finset.sum_boole, Finset.card_filter, stateGlobalSpecies, stateMainGlobalSpecies,
      Fintype.sum_prod_type] using D.card_jobCopy_edge v e
  · have hp' : (!selected) ≠ permit := Ne.symm hp
    simp [-Finset.sum_boole, stateGlobalSpecies, stateMainGlobalSpecies, hp, hp']

theorem stateGlobalSpecies_count (v : D.Vertex) (selected : Bool)
    (g : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateGlobalSpecies selected b = g)).card =
      match g with
      | .up true => if selected then D.d else 0
      | .up false => D.tPlus + D.J v - (if selected then D.d else 0)
      | .um true => if selected then 0 else D.d
      | .um false => D.tMinus - (if selected then 0 else D.d)
      | .edge e permit =>
          if permit = !selected ∧ (D.graph.left e = v ∨ D.graph.right e = v)
          then D.d * D.R else 0 := by
  cases g with
  | up b =>
      cases b
      · exact D.stateGlobalSpecies_up_false_count v selected
      · exact D.stateGlobalSpecies_up_true_count v selected
  | um b =>
      cases b
      · exact D.stateGlobalSpecies_um_false_count v selected
      · exact D.stateGlobalSpecies_um_true_count v selected
  | edge e permit => exact D.stateGlobalSpecies_edge_count v selected e permit

theorem stateFlagSpecies_count (v : D.Vertex) (f : FlagSpecies) :
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateFlagSpecies b = f)).card =
      match f with | .tree => D.t | .main => D.J v | .edge => D.J v := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  cases f <;> simp [stateFlagSpecies, D.card_jobCopy, t, tPlus, tMinus,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private def allGlobalRequests (g : GlobalSpecies D.graph) : ℕ :=
  ∑ v : D.Vertex, ∑ selected : Bool,
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateGlobalSpecies selected b = g)).card

private theorem allGlobalRequests_up_true : D.allGlobalRequests (.up true) = D.graph.n * D.d := by
  classical
  simp [allGlobalRequests, D.stateGlobalSpecies_up_true_count]

private theorem allGlobalRequests_um_true : D.allGlobalRequests (.um true) = D.graph.n * D.d := by
  classical
  simp [allGlobalRequests, D.stateGlobalSpecies_um_true_count]

private theorem allGlobalRequests_up_total :
    D.allGlobalRequests (.up true) + D.allGlobalRequests (.up false) = 2 * D.plusSlots := by
  classical
  calc
    _ = ∑ v : D.Vertex, ∑ selected : Bool,
        ((Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies selected b = .up true)).card +
          (Finset.univ.filter (fun b : D.LocalBin v =>
            D.stateGlobalSpecies selected b = .up false)).card) := by
        simp only [allGlobalRequests, Finset.sum_add_distrib]
    _ = ∑ v : D.Vertex, ∑ _selected : Bool, (D.tPlus + D.J v) := by
        simp_rw [D.stateGlobalSpecies_up_total]
    _ = _ := by simp [plusSlots, Finset.sum_add_distrib, two_mul]

private theorem allGlobalRequests_um_total :
    D.allGlobalRequests (.um true) + D.allGlobalRequests (.um false) = 2 * D.minusSlots := by
  classical
  calc
    _ = ∑ v : D.Vertex, ∑ selected : Bool,
        ((Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies selected b = .um true)).card +
          (Finset.univ.filter (fun b : D.LocalBin v =>
            D.stateGlobalSpecies selected b = .um false)).card) := by
        simp only [allGlobalRequests, Finset.sum_add_distrib]
    _ = ∑ v : D.Vertex, ∑ _selected : Bool, D.tMinus := by
        simp_rw [D.stateGlobalSpecies_um_total]
    _ = _ := by simp [minusSlots, two_mul, Nat.mul_add]

private theorem allGlobalRequests_edge (e : D.Edge) (permit : Bool) :
    D.allGlobalRequests (.edge e permit) = 2 * D.d * D.R := by
  classical
  have hpair (v : D.Vertex) :
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies true b = .edge e permit)).card +
        (Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateGlobalSpecies false b = .edge e permit)).card =
        (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card := by
    cases permit <;> simp [D.stateGlobalSpecies_edge_count, D.card_jobCopy_edge]
  unfold allGlobalRequests
  simp only [Fintype.sum_bool, hpair]
  exact D.sum_card_jobCopy_edge e

private theorem allGlobalRequests_eq_twice_stock (hn : D.graph.n = 2 * D.k)
    (g : GlobalSpecies D.graph) : D.allGlobalRequests g = 2 * D.globalStock g := by
  have hk : D.k ≤ D.graph.n := by omega
  have hdiff : D.graph.n - D.k = D.k := by omega
  have hup : D.allGlobalRequests (.up true) = 2 * (D.d * D.k) := by
    rw [D.allGlobalRequests_up_true, hn]
    ring
  have hum : D.allGlobalRequests (.um true) = 2 * (D.d * (D.graph.n - D.k)) := by
    rw [D.allGlobalRequests_um_true, hdiff, hn]
    ring
  cases g with
  | up b =>
      cases b
      · have ht := D.allGlobalRequests_up_total
        have hs := D.unitPlus_le_stock hk
        rw [hup] at ht
        dsimp [globalStock]
        omega
      · exact hup
  | um b =>
      cases b
      · have ht := D.allGlobalRequests_um_total
        have hs := D.unitMinus_le_stock
        rw [hum] at ht
        dsimp [globalStock]
        omega
      · exact hum
  | edge e permit =>
      simpa [globalStock, Nat.mul_assoc] using D.allGlobalRequests_edge e permit

theorem doubled_stateGlobalSpecies_count (hn : D.graph.n = 2 * D.k)
    (g : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
      D.stateGlobalSpecies q.2.1 q.2.2 = g)).card = 2 * D.globalStock g := by
  classical
  have hsum :
      (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
        D.stateGlobalSpecies q.2.1 q.2.2 = g)).card = D.allGlobalRequests g := by
    simp only [Finset.card_filter, Fintype.sum_sigma, Fintype.sum_prod_type,
      allGlobalRequests]
  rw [hsum]
  exact D.allGlobalRequests_eq_twice_stock hn g

theorem doubled_stateFlagSpecies_count (f : FlagSpecies) :
    (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
      D.stateFlagSpecies q.2.2 = f)).card = 2 * D.flagStock f := by
  classical
  have hsum :
      (Finset.univ.filter (fun q : (Σ v : D.Vertex, Bool × D.LocalBin v) =>
        D.stateFlagSpecies q.2.2 = f)).card =
        ∑ v : D.Vertex, ∑ _selected : Bool,
          (Finset.univ.filter (fun b : D.LocalBin v => D.stateFlagSpecies b = f)).card := by
    simp only [Finset.card_filter, Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [hsum]
  cases f <;>
    simp [D.stateFlagSpecies_count, flagStock, treeFlags,
      jobFlags, Finset.sum_add_distrib, two_mul, Nat.mul_add]

end BinPackingGap.InventoryData

namespace BinPackingGap

namespace GraphInput

theorem IsCover.mono {G : GraphInput} {C C' : Finset G.Vertex}
    (h : G.IsCover C) (hsub : C ⊆ C') : G.IsCover C' := by
  intro e he
  exact (h e he).imp (fun hx => hsub hx) (fun hx => hsub hx)

theorem CoverAtMost.exists_exact {G : GraphInput} {k : ℕ}
    (hk : k ≤ G.n) (h : G.CoverAtMost k) :
    ∃ C : Finset G.Vertex, G.IsCover C ∧ C.card = k := by
  classical
  obtain ⟨C, hC, hcard⟩ := h
  obtain ⟨C', hsub, _, heq⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ C) hcard (by simpa using hk)
  exact ⟨C', hC.mono hsub, heq⟩

theorem IsCover.endpoints {G : GraphInput} {C : Finset G.Vertex}
    (h : G.IsCover C) (e : G.Edge) : G.left e ∈ C ∨ G.right e ∈ C :=
  h _ (List.getElem_mem e.isLt)

end GraphInput

namespace InventoryData

variable (D : InventoryData)

def coverSelected (C : Finset D.Vertex) (v : D.Vertex) : Bool := decide (v ∈ C)

def permitLeft (C : Finset D.Vertex) (e : D.Edge) : Bool :=
  !D.coverSelected C (D.graph.left e) || D.coverSelected C (D.graph.right e)

def integralPermit (C : Finset D.Vertex) (e : D.Edge) (slot : Fin 2) : Bool :=
  if slot = 0 then D.permitLeft C e else !D.permitLeft C e

@[simp] theorem integralPermit_zero (C : Finset D.Vertex) (e : D.Edge) :
    D.integralPermit C e 0 = D.permitLeft C e := by simp [integralPermit]

@[simp] theorem integralPermit_one (C : Finset D.Vertex) (e : D.Edge) :
    D.integralPermit C e 1 = !D.permitLeft C e := by simp [integralPermit]

theorem integralPermit_of_unselected (C : Finset D.Vertex)
    (hC : D.graph.IsCover C) (e : D.Edge) (slot : Fin 2)
    (hnot : D.coverSelected C (D.graph.endpoint e slot) = false) :
    D.integralPermit C e slot = true := by
  have hends := hC.endpoints e
  have hs : slot = 0 ∨ slot = 1 := by omega
  rcases hs with rfl | rfl <;>
    by_cases hl : D.graph.left e ∈ C <;>
    by_cases hr : D.graph.right e ∈ C <;>
    simp_all [integralPermit, permitLeft, coverSelected, GraphInput.endpoint]

def integralGlobalSpecies (C : Finset D.Vertex) : D.PhysicalBins → GlobalSpecies D.graph
  | ⟨v, .inl b⟩ => D.stateMainGlobalSpecies (D.coverSelected C v) b
  | ⟨_, .inr j⟩ => .edge j.1.1.val.1 (D.integralPermit C j.1.1.val.1 j.1.1.val.2)

def integralFlagSpecies : D.PhysicalBins → FlagSpecies :=
  fun b => D.stateFlagSpecies b.2

theorem integral_edge_permit_of_unselected (C : Finset D.Vertex)
    (hC : D.graph.IsCover C) {v : D.Vertex} (j : D.JobCopy v)
    (hv : D.coverSelected C v = false) :
    D.integralPermit C j.1.1.val.1 j.1.1.val.2 = true := by
  apply D.integralPermit_of_unselected C hC
  simpa only [j.1.1.property] using hv

end InventoryData

end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

private theorem integral_up_count_eq_sum (C : Finset D.Vertex) (one : Bool) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up one)).card =
      ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies (D.coverSelected C v) b = .up one)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  rcases b with b | j
  · rfl
  · simp [integralGlobalSpecies, stateGlobalSpecies]

private theorem integral_um_count_eq_sum (C : Finset D.Vertex) (one : Bool) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um one)).card =
      ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies (D.coverSelected C v) b = .um one)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  rcases b with b | j
  · rfl
  · simp [integralGlobalSpecies, stateGlobalSpecies]

private theorem sum_coverSelected (C : Finset D.Vertex) :
    (∑ v : D.Vertex, if D.coverSelected C v then D.d else 0) = D.d * C.card := by
  classical
  simp [coverSelected, Nat.mul_comm]

private theorem sum_coverUnselected (C : Finset D.Vertex) :
    (∑ v : D.Vertex, if D.coverSelected C v then 0 else D.d) =
      D.d * (D.graph.n - C.card) := by
  classical
  calc
    _ = ∑ v : D.Vertex, if v ∈ Cᶜ then D.d else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ C <;> simp [coverSelected, hv]
    _ = D.d * (Cᶜ).card := by
      rw [Fintype.sum_ite_mem]
      simp [Nat.mul_comm]
    _ = _ := by simp [Finset.card_compl]

private theorem integral_up_true_count (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up true)).card = D.d * C.card := by
  rw [D.integral_up_count_eq_sum]
  simp_rw [D.stateGlobalSpecies_up_true_count]
  exact D.sum_coverSelected C

private theorem integral_um_true_count (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um true)).card =
      D.d * (D.graph.n - C.card) := by
  rw [D.integral_um_count_eq_sum]
  simp_rw [D.stateGlobalSpecies_um_true_count]
  exact D.sum_coverUnselected C

private theorem integral_up_total (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .up true)).card +
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralGlobalSpecies C b = .up false)).card = D.plusSlots := by
  rw [D.integral_up_count_eq_sum, D.integral_up_count_eq_sum,
    ← Finset.sum_add_distrib]
  simp_rw [D.stateGlobalSpecies_up_total]
  rfl

private theorem integral_um_total (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um true)).card +
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralGlobalSpecies C b = .um false)).card = D.minusSlots := by
  rw [D.integral_um_count_eq_sum, D.integral_um_count_eq_sum,
    ← Finset.sum_add_distrib]
  simp_rw [D.stateGlobalSpecies_um_total]
  simp [minusSlots]

theorem card_integralEdgeJobs (C : Finset D.Vertex) (e : D.Edge) (permit : Bool) :
    (Finset.univ.filter (fun j : Σ v : D.Vertex, D.JobCopy v =>
      GlobalSpecies.edge (G := D.graph) j.2.1.1.val.1
        (D.integralPermit C j.2.1.1.val.1 j.2.1.1.val.2) =
      GlobalSpecies.edge e permit)).card = D.d * D.R := by
  classical
  let chosen : Fin 2 := if permit = D.permitLeft C e then 0 else 1
  have hslot (slot : Fin 2) :
      D.integralPermit C e slot = permit ↔ slot = chosen := by
    have hs : slot = 0 ∨ slot = 1 := by omega
    rcases hs with rfl | rfl <;>
      cases hp : D.permitLeft C e <;> cases permit <;>
      simp [chosen, hp]
  have hedge (e' : D.Edge) (slot : Fin 2) :
      GlobalSpecies.edge (G := D.graph) e' (D.integralPermit C e' slot) =
        GlobalSpecies.edge e permit ↔ (e', slot) = (e, chosen) := by
    rw [GlobalSpecies.edge.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨he, hp⟩
      subst e'
      exact ⟨rfl, (hslot slot).mp hp⟩
    · rintro ⟨he, hs⟩
      subst e'
      exact ⟨rfl, (hslot slot).mpr hs⟩
  calc
    _ = ((({(e, chosen)} : Finset (D.Edge × Fin 2)) ×ˢ
          (Finset.univ : Finset (Fin D.R))) ×ˢ
          (Finset.univ : Finset (Fin D.d))).card := by
      apply Finset.card_equiv D.allJobEquiv
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, and_true]
      exact hedge j.2.1.1.val.1 j.2.1.1.val.2
    _ = D.d * D.R := by simp [Nat.mul_comm]

theorem card_integralGlobalSpecies (C : Finset D.Vertex) (hC : C.card = D.k)
    (s : GlobalSpecies D.graph) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = s)).card = D.globalStock s := by
  classical
  cases s with
  | up one =>
      cases one
      · have ht := D.integral_up_total C
        have hu := D.integral_up_true_count C
        rw [hC] at hu
        dsimp [globalStock]
        omega
      · simpa [globalStock, hC] using D.integral_up_true_count C
  | um one =>
      cases one
      · have ht := D.integral_um_total C
        have hu := D.integral_um_true_count C
        rw [hC] at hu
        dsimp [globalStock]
        omega
      · simpa [globalStock, hC] using D.integral_um_true_count C
  | edge e permit =>
      rw [Finset.card_filter, Fintype.sum_sigma]
      have hj := D.card_integralEdgeJobs C e permit
      rw [Finset.card_filter, Fintype.sum_sigma] at hj
      refine Eq.trans ?_ hj
      apply Finset.sum_congr rfl
      intro vertex _
      have hmain (base : D.MBase vertex) :
          D.stateMainGlobalSpecies (D.coverSelected C vertex) base ≠ .edge e permit := by
        rcases base with (⟨node, copy⟩ | (⟨node, copy⟩ | zero)) | job <;>
          simp [stateMainGlobalSpecies]
      rw [Fintype.sum_sum_type]
      simp only [integralGlobalSpecies, hmain, ite_false, Finset.sum_const_zero, zero_add]
      rfl

theorem card_integralFlagSpecies (f : FlagSpecies) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralFlagSpecies b = f)).card = D.flagStock f := by
  classical
  have hsum :
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralFlagSpecies b = f)).card =
        ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateFlagSpecies b = f)).card := by
    rw [Finset.card_filter]
    simp only [Finset.card_filter, Fintype.sum_sigma, integralFlagSpecies]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro b _
    rfl
  rw [hsum]
  cases f <;> simp [D.stateFlagSpecies_count, flagStock, treeFlags, jobFlags]

end BinPackingGap.InventoryData

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Configurations/ConfigurationLP.lean =====
namespace OAI

noncomputable section

section

open scoped BigOperators
open Set

namespace BinPackingGap.FractionalCover

variable {I C : Type*} [Fintype C]

theorem objective_nonneg {w : C → ℝ} (hw : ∀ c, 0 ≤ w c) :
    0 ≤ objective w :=
  Finset.sum_nonneg fun c _ => hw c

theorem coordinate_le_objective {w : C → ℝ} (hw : ∀ c, 0 ≤ w c) (c : C) :
    w c ≤ objective w :=
  Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ c)

theorem objectiveSet_nonempty {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) : (objectiveSet a d).Nonempty := by
  obtain ⟨w, hw⟩ := hfeas
  exact ⟨objective w, w, hw, rfl⟩

theorem objectiveSet_bddBelow (a : C → I → ℝ) (d : I → ℝ) :
    BddBelow (objectiveSet a d) := by
  refine ⟨0, ?_⟩
  rintro v ⟨w, hw, rfl⟩
  exact objective_nonneg hw.1

theorem value_le_of_feasible {a : C → I → ℝ} {d : I → ℝ} {w : C → ℝ}
    (hw : Feasible a d w) : value a d ≤ objective w :=
  csInf_le (objectiveSet_bddBelow a d) ⟨w, hw, rfl⟩

theorem le_value_of_lower_bound {a : C → I → ℝ} {d : I → ℝ} {b : ℝ}
    (hfeas : ∃ w, Feasible a d w)
    (hb : ∀ w, Feasible a d w → b ≤ objective w) : b ≤ value a d := by
  apply le_csInf (objectiveSet_nonempty hfeas)
  rintro v ⟨w, hw, rfl⟩
  exact hb w hw

theorem value_nonneg {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) : 0 ≤ value a d :=
  le_value_of_lower_bound hfeas fun _ hw => objective_nonneg hw.1

theorem continuous_objective : Continuous (objective (C := C)) := by
  unfold objective
  exact continuous_finsetSum _ fun c _ => continuous_apply c

theorem continuous_coverage (a : C → I → ℝ) (i : I) :
    Continuous (fun w : C → ℝ => ∑ c, a c i * w c) :=
  continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_apply c)

theorem isClosed_feasible (a : C → I → ℝ) (d : I → ℝ) :
    IsClosed {w | Feasible a d w} := by
  have hn : IsClosed {w : C → ℝ | ∀ c, 0 ≤ w c} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_le continuous_const (continuous_apply c)
  have hd : IsClosed {w : C → ℝ | ∀ i, d i ≤ ∑ c, a c i * w c} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_coverage a i)
  exact hn.inter hd

theorem isCompact_sublevel (a : C → I → ℝ) (d : I → ℝ) (b : ℝ) :
    IsCompact {w | Feasible a d w ∧ objective w ≤ b} := by
  have hc : IsClosed {w | Feasible a d w ∧ objective w ≤ b} :=
    (isClosed_feasible a d).inter (isClosed_le continuous_objective continuous_const)
  apply (isCompact_Icc (a := (0 : C → ℝ)) (b := fun _ => b)).of_isClosed_subset hc
  intro w hw
  exact ⟨hw.1.1, fun c => (coordinate_le_objective hw.1.1 c).trans hw.2⟩

theorem exists_minimum {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) :
    ∃ w, Feasible a d w ∧ ∀ v, Feasible a d v → objective w ≤ objective v := by
  obtain ⟨w₀, hw₀⟩ := hfeas
  obtain ⟨w, hw, hmin⟩ :=
    (isCompact_sublevel a d (objective w₀)).exists_isMinOn
      ⟨w₀, hw₀, le_rfl⟩ continuous_objective.continuousOn
  refine ⟨w, hw.1, fun v hv => ?_⟩
  rcases le_total (objective v) (objective w₀) with h | h
  · exact hmin ⟨hv, h⟩
  · exact hw.2.trans h

theorem exists_minimizer {a : C → I → ℝ} {d : I → ℝ}
    (hfeas : ∃ w, Feasible a d w) :
    ∃ w, Feasible a d w ∧ objective w = value a d := by
  obtain ⟨w, hw, hmin⟩ := exists_minimum hfeas
  exact ⟨w, hw, le_antisymm (le_value_of_lower_bound ⟨w, hw⟩ hmin)
    (value_le_of_feasible hw)⟩

theorem value_eq_of_feasible_of_lower_bound {a : C → I → ℝ} {d : I → ℝ}
    {w : C → ℝ} {b : ℝ} (hw : Feasible a d w) (hwobj : objective w = b)
    (hb : ∀ v, Feasible a d v → b ≤ objective v) : value a d = b := by
  apply le_antisymm
  · exact hwobj ▸ value_le_of_feasible hw
  · exact le_value_of_lower_bound ⟨w, hw⟩ hb

theorem sum_demand_le_mul_objective [Fintype I] {a : C → I → ℝ} {d : I → ℝ}
    {w : C → ℝ} {K : ℝ} (hw : Feasible a d w)
    (hcol : ∀ c, (∑ i, a c i) ≤ K) : (∑ i, d i) ≤ K * objective w := by
  calc
    (∑ i, d i) ≤ ∑ i, ∑ c, a c i * w c :=
      Finset.sum_le_sum fun i _ => hw.2 i
    _ = ∑ c, (∑ i, a c i) * w c := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ c, K * w c :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hcol c) (hw.1 c)
    _ = K * objective w := (Finset.mul_sum _ _ _).symm

theorem sum_demand_le_mul_value [Fintype I] {a : C → I → ℝ} {d : I → ℝ} {K : ℝ}
    (hfeas : ∃ w, Feasible a d w) (hcol : ∀ c, (∑ i, a c i) ≤ K) :
    (∑ i, d i) ≤ K * value a d := by
  obtain ⟨w, hw, hwobj⟩ := exists_minimizer hfeas
  rw [← hwobj]
  exact sum_demand_le_mul_objective hw hcol

variable {J : Type*} [Fintype J]

def pushforward (f : J → C) (mass : J → ℝ) : C → ℝ := by
  classical
  exact fun c => ∑ j, if f j = c then mass j else 0

omit [Fintype C] in
theorem pushforward_nonneg (f : J → C) {mass : J → ℝ}
    (hmass : ∀ j, 0 ≤ mass j) : ∀ c, 0 ≤ pushforward f mass c := by
  classical
  intro c
  exact Finset.sum_nonneg fun j _ => by
    by_cases h : f j = c
    · simpa [h] using hmass j
    · simp [h]

theorem objective_pushforward (f : J → C) (mass : J → ℝ) :
    objective (pushforward f mass) = objective mass := by
  classical
  unfold objective pushforward
  rw [Finset.sum_comm]
  simp

theorem coverage_pushforward (a : C → I → ℝ) (f : J → C) (mass : J → ℝ) (i : I) :
    (∑ c, a c i * pushforward f mass c) = ∑ j, a (f j) i * mass j := by
  classical
  simp only [pushforward, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem feasible_pushforward {a : C → I → ℝ} {d : I → ℝ}
    (f : J → C) {mass : J → ℝ}
    (hmass : Feasible (fun j i => a (f j) i) d mass) :
    Feasible a d (pushforward f mass) := by
  refine ⟨pushforward_nonneg f hmass.1, fun i => ?_⟩
  rw [coverage_pushforward]
  exact hmass.2 i

end BinPackingGap.FractionalCover

end

namespace BinPackingGap

open scoped BigOperators

namespace NumericalSize

variable {I : Instance}

theorem le_one (s : NumericalSize I) : s.val ≤ 1 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp s.property
  rw [← hi]
  exact I.size_le_one i

def ofItem (i : I.Item) : NumericalSize I :=
  ⟨I.size i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem ofItem_val (i : I.Item) : (ofItem i).val = I.size i := rfl

end NumericalSize

namespace TypeConfiguration

variable {I : Instance}

def empty (I : Instance) : TypeConfiguration I := ⟨fun _ => 0, by simp⟩

instance : Nonempty (TypeConfiguration I) := ⟨empty I⟩

def ofIndividual (H : IndividualConfiguration I) : TypeConfiguration I where
  val s := (H.val.filter fun i => I.size i = s.val).card
  property := by
    classical
    have hsum : (∑ s : NumericalSize I,
        s.val * ((H.val.filter fun i => I.size i = s.val).card : ℚ)) =
        ∑ i ∈ H.val, I.size i := by
      calc
        _ = ∑ s : NumericalSize I, ∑ i ∈ H.val,
            if I.size i = s.val then I.size i else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          rw [← Finset.sum_filter]
          rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
          simp [mul_comm]
        _ = ∑ i ∈ H.val, ∑ s : NumericalSize I,
            if I.size i = s.val then I.size i else 0 := by rw [Finset.sum_comm]
        _ = ∑ i ∈ H.val, I.size i := by
          apply Finset.sum_congr rfl
          intro i _
          have heq : ∀ s : NumericalSize I, I.size i = s.val ↔ NumericalSize.ofItem i = s := by
            intro s
            constructor
            · intro h
              exact Subtype.ext h
            · intro h
              exact congrArg Subtype.val h
          simp [heq]
    rw [hsum]
    exact H.property

@[simp] theorem ofIndividual_count (H : IndividualConfiguration I) (s : NumericalSize I) :
    (ofIndividual H).val s = (H.val.filter fun i => I.size i = s.val).card := rfl

theorem card_le_five (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (c : TypeConfiguration I) : (∑ s, c.val s) ≤ 5 := by
  classical
  by_contra h
  have hc : 6 ≤ ∑ s, c.val s := by omega
  have hcq : (6 : ℚ) ≤ ∑ s, (c.val s : ℚ) := by exact_mod_cast hc
  have hsize : ∀ s : NumericalSize I, (1 / 6 : ℚ) < s.val := by
    intro s
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp s.property
    simpa [hi] using hlarge i
  have hnz : ∃ s : NumericalSize I, 0 < c.val s := by
    by_contra hn
    push Not at hn
    have hz : ∀ s, c.val s = 0 := fun s => Nat.eq_zero_of_le_zero (hn s)
    simp [hz] at hc
  obtain ⟨s, hs⟩ := hnz
  have hstrict : (∑ t : NumericalSize I, (1 / 6 : ℚ) * (c.val t : ℚ)) <
      ∑ t : NumericalSize I, t.val * (c.val t : ℚ) := by
    apply Finset.sum_lt_sum
    · intro t _
      exact mul_le_mul_of_nonneg_right (le_of_lt (hsize t)) (Nat.cast_nonneg _)
    · refine ⟨s, Finset.mem_univ _, ?_⟩
      exact mul_lt_mul_of_pos_right (hsize s) (by exact_mod_cast hs)
  rw [← Finset.mul_sum] at hstrict
  have hcap := c.property
  linarith

end TypeConfiguration

theorem sum_type_multiplicity (I : Instance) :
    ∑ s : NumericalSize I, s.multiplicity = I.n := by
  classical
  simp only [NumericalSize.multiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ i : I.Item, ∑ s : NumericalSize I, if I.size i = s.val then 1 else 0) =
        ∑ _i : I.Item, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      have heq : ∀ s : NumericalSize I, I.size i = s.val ↔ NumericalSize.ofItem i = s := by
        intro s
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      simp [heq]
    _ = I.n := by simp [Instance.Item]

def IndividualFeasible (I : Instance) (w : IndividualConfiguration I → ℝ) : Prop :=
  FractionalCover.Feasible (individualMatrix I) (fun _ => 1) w

def TypeFeasible (I : Instance) (w : TypeConfiguration I → ℝ) : Prop :=
  FractionalCover.Feasible (typeMatrix I) (fun s => (s.multiplicity : ℝ)) w

theorem individualMatrix_sum (I : Instance) (H : IndividualConfiguration I) :
    ∑ i, individualMatrix I H i = (H.val.card : ℝ) := by
  classical
  simp [individualMatrix]

theorem typeMatrix_sum (I : Instance) (c : TypeConfiguration I) :
    ∑ s, typeMatrix I c s = ((∑ s, c.val s : ℕ) : ℝ) := by
  simp [typeMatrix]

def singletonWeights (I : Instance) : IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward IndividualConfiguration.singleton (fun _ : I.Item => 1)

theorem singletonWeights_feasible (I : Instance) : IndividualFeasible I (singletonWeights I) := by
  classical
  apply FractionalCover.feasible_pushforward
  constructor
  · intro i
    norm_num
  · intro i
    simp [individualMatrix, IndividualConfiguration.singleton]

theorem singletonWeights_objective (I : Instance) :
    FractionalCover.objective (singletonWeights I) = (I.n : ℝ) := by
  rw [singletonWeights, FractionalCover.objective_pushforward]
  simp [FractionalCover.objective, Instance.Item]

theorem individualLP_attained (I : Instance) :
    ∃ w, IndividualFeasible I w ∧ FractionalCover.objective w = individualLP I :=
  FractionalCover.exists_minimizer ⟨singletonWeights I, singletonWeights_feasible I⟩

theorem individualLP_nonneg (I : Instance) : 0 ≤ individualLP I :=
  FractionalCover.value_nonneg ⟨singletonWeights I, singletonWeights_feasible I⟩

theorem individualLP_le_n (I : Instance) : individualLP I ≤ I.n := by
  rw [← singletonWeights_objective I]
  exact FractionalCover.value_le_of_feasible (singletonWeights_feasible I)

theorem typeMatrix_ofIndividual (I : Instance) (H : IndividualConfiguration I)
    (s : NumericalSize I) :
    typeMatrix I (TypeConfiguration.ofIndividual H) s =
      ∑ i : I.Item, if I.size i = s.val then individualMatrix I H i else 0 := by
  classical
  change ((H.val.filter fun i => I.size i = s.val).card : ℝ) = _
  calc
    _ = ∑ i ∈ H.val, if I.size i = s.val then (1 : ℝ) else 0 := by
      simp
    _ = ∑ i ∈ H.val, if I.size i = s.val then individualMatrix I H i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [individualMatrix, hi]
    _ = ∑ i : I.Item, if I.size i = s.val then individualMatrix I H i else 0 := by
      apply Finset.sum_subset (Finset.subset_univ H.val)
      intro i _ hi
      simp [individualMatrix, hi]

def projectWeights (I : Instance) (w : IndividualConfiguration I → ℝ) :
    TypeConfiguration I → ℝ :=
  FractionalCover.pushforward TypeConfiguration.ofIndividual w

theorem projectWeights_objective (I : Instance) (w : IndividualConfiguration I → ℝ) :
    FractionalCover.objective (projectWeights I w) = FractionalCover.objective w :=
  FractionalCover.objective_pushforward _ _

theorem projectWeights_feasible (I : Instance) {w : IndividualConfiguration I → ℝ}
    (hw : IndividualFeasible I w) : TypeFeasible I (projectWeights I w) := by
  classical
  apply FractionalCover.feasible_pushforward
  refine ⟨hw.1, fun s => ?_⟩
  have hcoverage := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show (if I.size i = s.val then (1 : ℝ) else 0) ≤
      if I.size i = s.val then ∑ H, individualMatrix I H i * w H else 0 by
        split_ifs
        · exact hw.2 i
        · rfl)
  have hleft : (∑ i : I.Item, if I.size i = s.val then (1 : ℝ) else 0) =
      s.multiplicity := by
    simp [NumericalSize.multiplicity]
  have hright :
      (∑ i : I.Item, if I.size i = s.val then ∑ H, individualMatrix I H i * w H else 0) =
      ∑ H, typeMatrix I (TypeConfiguration.ofIndividual H) s * w H := by
    simp_rw [typeMatrix_ofIndividual, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · simp
    · simp
  simpa only [hleft, hright] using hcoverage

theorem typeLP_attained (I : Instance) :
    ∃ w, TypeFeasible I w ∧ FractionalCover.objective w = typeLP I :=
  FractionalCover.exists_minimizer
    ⟨projectWeights I (singletonWeights I), projectWeights_feasible I (singletonWeights_feasible I)⟩

theorem typeLP_nonneg (I : Instance) : 0 ≤ typeLP I :=
  FractionalCover.value_nonneg
    ⟨projectWeights I (singletonWeights I), projectWeights_feasible I (singletonWeights_feasible I)⟩

theorem typeLP_le_individualLP (I : Instance) : typeLP I ≤ individualLP I := by
  obtain ⟨w, hw, hobj⟩ := individualLP_attained I
  calc
    typeLP I ≤ FractionalCover.objective (projectWeights I w) :=
      FractionalCover.value_le_of_feasible (projectWeights_feasible I hw)
    _ = individualLP I := (projectWeights_objective I w).trans hobj

theorem individualLP_eq_zero_of_n_eq_zero (I : Instance) (h : I.n = 0) :
    individualLP I = 0 := by
  have hle := individualLP_le_n I
  rw [h, Nat.cast_zero] at hle
  exact le_antisymm hle (individualLP_nonneg I)

theorem typeLP_eq_zero_of_n_eq_zero (I : Instance) (h : I.n = 0) : typeLP I = 0 := by
  apply le_antisymm
  · simpa [individualLP_eq_zero_of_n_eq_zero I h] using typeLP_le_individualLP I
  · exact typeLP_nonneg I

namespace Packing

def fractionalWeights {I : Instance} {b : ℕ} (p : Packing I b) :
    IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward p.configuration (fun _ : Fin b => 1)

theorem fractionalWeights_feasible {I : Instance} {b : ℕ} (p : Packing I b) :
    IndividualFeasible I p.fractionalWeights := by
  classical
  apply FractionalCover.feasible_pushforward
  constructor
  · intro j
    norm_num
  · intro i
    simp [individualMatrix, configuration]

theorem fractionalWeights_objective {I : Instance} {b : ℕ} (p : Packing I b) :
    FractionalCover.objective p.fractionalWeights = (b : ℝ) := by
  rw [fractionalWeights, FractionalCover.objective_pushforward]
  simp [FractionalCover.objective]

end Packing

theorem individualLP_le_opt (I : Instance) : individualLP I ≤ (opt I : ℝ) := by
  obtain ⟨p⟩ := opt_attained I
  rw [← p.fractionalWeights_objective]
  exact FractionalCover.value_le_of_feasible p.fractionalWeights_feasible

theorem typeLP_le_opt (I : Instance) : typeLP I ≤ (opt I : ℝ) :=
  (typeLP_le_individualLP I).trans (individualLP_le_opt I)

theorem n_le_five_mul_individual_objective (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    {w : IndividualConfiguration I → ℝ} (hw : IndividualFeasible I w) :
    (I.n : ℝ) ≤ 5 * FractionalCover.objective w := by
  have hcol : ∀ H : IndividualConfiguration I, (∑ i, individualMatrix I H i) ≤ 5 := by
    intro H
    rw [individualMatrix_sum]
    exact_mod_cast H.card_le_five hlarge
  simpa [Instance.Item] using FractionalCover.sum_demand_le_mul_objective hw hcol

theorem n_le_five_mul_type_objective (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    {w : TypeConfiguration I → ℝ} (hw : TypeFeasible I w) :
    (I.n : ℝ) ≤ 5 * FractionalCover.objective w := by
  have hcol : ∀ c : TypeConfiguration I, (∑ s, typeMatrix I c s) ≤ 5 := by
    intro c
    rw [typeMatrix_sum]
    exact_mod_cast c.card_le_five hlarge
  have h := FractionalCover.sum_demand_le_mul_objective hw hcol
  have hdem : (∑ s : NumericalSize I, (s.multiplicity : ℝ)) = I.n := by
    rw [← Nat.cast_sum, sum_type_multiplicity]
  simpa only [hdem] using h

theorem n_le_five_mul_individualLP (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) : (I.n : ℝ) ≤ 5 * individualLP I := by
  obtain ⟨w, hw, hobj⟩ := individualLP_attained I
  rw [← hobj]
  exact n_le_five_mul_individual_objective I hlarge hw

theorem n_le_five_mul_typeLP (I : Instance)
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) : (I.n : ℝ) ≤ 5 * typeLP I := by
  obtain ⟨w, hw, hobj⟩ := typeLP_attained I
  rw [← hobj]
  exact n_le_five_mul_type_objective I hlarge hw

theorem bothLP_eq_of_physical_witness (I : Instance) (B : ℕ)
    (hcount : I.n = 5 * B) (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (w : IndividualConfiguration I → ℝ) (hw : IndividualFeasible I w)
    (hobj : FractionalCover.objective w = (B : ℝ)) :
    individualLP I = (B : ℝ) ∧ typeLP I = (B : ℝ) := by
  have hcountR : (I.n : ℝ) = 5 * (B : ℝ) := by exact_mod_cast hcount
  have hilow := n_le_five_mul_individualLP I hlarge
  have htlow := n_le_five_mul_typeLP I hlarge
  have hiup : individualLP I ≤ (B : ℝ) := by
    rw [← hobj]
    exact FractionalCover.value_le_of_feasible hw
  have htup : typeLP I ≤ (B : ℝ) := (typeLP_le_individualLP I).trans hiup
  constructor <;> linarith

end BinPackingGap

end

end OAI


