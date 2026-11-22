-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part08
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part08
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T14:15:18.823195+00:00
-- url     : https://prove2.me/theorems/f54374fd-9bba-415f-a7cd-993a943cdd6c
-- title:
--   Rural postman algorithm — Blossom partitions, dual progress, and immediate-child ownership
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for blossom partitions, dual progress, and immediate-child ownership in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Abel
import Mathlib.Data.Finset.Basic
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part05
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part07

/-! matching/BlossomPartitionMerge.lean -/
section RppSource_BlossomPartitionMerge
namespace VehicleRoutingSurvey.Routing

/-- Contract the chosen top-level children to their union and register the new odd cut. -/
def TopLevelMatchingBlocks.contract {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (children : Finset (Finset (Fin n)))
    (top : children ⊆ O.image blocks.block) :
    TopLevelMatchingBlocks O (insert (children.biUnion id) cuts) where
  block v := if blocks.block v ∈ children then children.biUnion id else blocks.block v
  self_mem v hv := by
    by_cases merged : blocks.block v ∈ children
    · exact (if_pos merged).symm ▸ Finset.mem_biUnion.mpr ⟨blocks.block v, merged, blocks.self_mem v hv⟩
    · exact (if_neg merged).symm ▸ blocks.self_mem v hv
  same_of_mem {v w} hv hw := by
    by_cases merged : blocks.block v ∈ children
    · rw [if_pos merged] at hw ⊢
      obtain ⟨child, member, inChild⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨u, hu, blockEq⟩ := Finset.mem_image.mp (top member)
      have wasChild : blocks.block w = child :=
        (blocks.same_of_mem hu (blockEq.symm ▸ inChild)).trans blockEq
      rw [wasChild, if_pos member]
    · rw [if_neg merged] at hw ⊢
      rw [blocks.same_of_mem hv hw, if_neg merged]
  cut_mem {v} hv nontrivial := by
    by_cases merged : blocks.block v ∈ children
    · rw [if_pos merged]
      exact Finset.mem_insert_self _ _
    · rw [if_neg merged] at nontrivial ⊢
      exact Finset.mem_insert_of_mem (blocks.cut_mem hv nontrivial)

theorem contractedBlossom_eligible {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) {children : Finset (Finset (Fin n))}
    (top : children ⊆ O.image blocks.block) (contained : ∀ v ∈ O, blocks.block v ⊆ O)
    (oddChildren : ∀ S ∈ children, Odd S.card) (oddCycle : Odd children.card) :
    children.biUnion id ⊆ O ∧ Odd (children.biUnion id).card := by
  constructor
  · intro v hv
    obtain ⟨child, member, inChild⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, shape⟩ := Finset.mem_image.mp (top member)
    exact contained u hu (shape.symm ▸ inChild)
  · have disjoint : (children : Set (Finset (Fin n))).PairwiseDisjoint id := by
      intro S sIn T tIn different
      apply Finset.disjoint_left.mpr
      intro v inS inT
      obtain ⟨x, hx, shapeS⟩ := Finset.mem_image.mp (top sIn)
      obtain ⟨y, hy, shapeT⟩ := Finset.mem_image.mp (top tIn)
      have intoS := (blocks.same_of_mem hx (shapeS.symm ▸ inS)).trans shapeS
      have intoT := (blocks.same_of_mem hy (shapeT.symm ▸ inT)).trans shapeT
      exact different (intoS.symm.trans intoT)
    rw [Nat.odd_iff, Finset.card_biUnion disjoint]
    have counts := Nat.ModEq.sum (n := 2) (s := children) (f := fun S => S.card) (g := fun _ => 1)
      (fun S hS => by simpa only [Nat.ModEq] using Nat.odd_iff.mp (oddChildren S hS))
    simp only [Nat.ModEq, Finset.sum_const, nsmul_eq_mul, mul_one] at counts
    simpa only [id_eq] using counts.trans (Nat.odd_iff.mp oddCycle)

/-- Assign zero only to newly represented cuts. Existing dual values are unchanged. -/
noncomputable def extendBlossomCutDual {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (dual : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  if S ∈ cuts then dual S else 0

/-- Registering a contracted cut at zero preserves every edge's dual value and slack. -/
theorem oddCutDualEdgeValue_register_cut {n : ℕ} (cuts : Finset (Finset (Fin n))) (S : Finset (Fin n))
    (potential : Fin n → ℝ) (dual : Finset (Fin n) → ℝ) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue (insert S cuts) potential (extendBlossomCutDual cuts dual) e =
      oddCutDualEdgeValue cuts potential dual e := by
  simp only [oddCutDualEdgeValue, Finset.sum_filter]
  congr 1
  have preserves : (∑ B ∈ cuts, if MatchingCrossesCut B e then extendBlossomCutDual cuts dual B else 0) =
      ∑ B ∈ cuts, if MatchingCrossesCut B e then dual B else 0 :=
    Finset.sum_congr rfl fun B hB => by simp only [extendBlossomCutDual, if_pos hB]
  by_cases already : S ∈ cuts
  · rwa [Finset.insert_eq_of_mem already]
  · rw [Finset.sum_insert already, preserves]
    simp [extendBlossomCutDual, already]

end VehicleRoutingSurvey.Routing
end RppSource_BlossomPartitionMerge

/-! matching/BlossomPartitionExpand.lean -/
section RppSource_BlossomPartitionExpand
namespace VehicleRoutingSurvey.Routing

/-- Expand a top-level blossom into its stored children and remove the blossom cut. -/
def TopLevelMatchingBlocks.expand {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (blossom : Finset (Fin n))
    (top : blossom ∈ O.image blocks.block) (child : Fin n → Finset (Fin n))
    (childSelf : ∀ v ∈ blossom, v ∈ child v) (childSubset : ∀ v ∈ blossom, child v ⊆ blossom)
    (childSame : ∀ v ∈ blossom, ∀ w ∈ child v, child w = child v)
    (childCut : ∀ v ∈ blossom, (child v).card ≠ 1 → child v ∈ cuts.erase blossom) :
    TopLevelMatchingBlocks O (cuts.erase blossom) where
  block v := if blocks.block v = blossom then child v else blocks.block v
  self_mem v hv := by
    by_cases inside : blocks.block v = blossom
    · rw [if_pos inside]
      exact childSelf v (inside ▸ blocks.self_mem v hv)
    · rw [if_neg inside]
      exact blocks.self_mem v hv
  same_of_mem {v w} hv hw := by
    by_cases inside : blocks.block v = blossom
    · rw [if_pos inside] at hw ⊢
      have vIn : v ∈ blossom := inside ▸ blocks.self_mem v hv
      have wIn : w ∈ blossom := childSubset v vIn hw
      obtain ⟨u, hu, identifies⟩ := Finset.mem_image.mp top
      have wBlock : blocks.block w = blossom :=
        (blocks.same_of_mem hu (identifies.symm ▸ wIn)).trans identifies
      rw [if_pos wBlock, childSame v vIn w hw]
    · rw [if_neg inside] at hw ⊢
      rw [blocks.same_of_mem hv hw, if_neg inside]
  cut_mem {v} hv nonsingleton := by
    by_cases inside : blocks.block v = blossom
    · rw [if_pos inside] at nonsingleton ⊢
      exact childCut v (inside ▸ blocks.self_mem v hv) nonsingleton
    · rw [if_neg inside] at nonsingleton ⊢
      exact Finset.mem_erase.mpr ⟨inside, blocks.cut_mem hv nonsingleton⟩

/-- Removing a zero-dual blossom at expansion preserves every edge's slack and tightness. -/
theorem oddCutDualEdgeValue_erase_zero {n : ℕ} (cuts : Finset (Finset (Fin n)))
    {blossom : Finset (Fin n)} (member : blossom ∈ cuts)
    (potential : Fin n → ℝ) (dual : Finset (Fin n) → ℝ) (zero : dual blossom = 0) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue (cuts.erase blossom) potential dual e = oddCutDualEdgeValue cuts potential dual e := by
  simp only [oddCutDualEdgeValue, Finset.sum_filter]
  congr 1
  simpa [zero] using Finset.sum_erase_add cuts (fun S => if MatchingCrossesCut S e then dual S else 0) member

end VehicleRoutingSurvey.Routing
end RppSource_BlossomPartitionExpand

/-! matching/WeightedEffectivePotential.lean -/
section RppSource_WeightedEffectivePotential
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- For edges leaving a top-level blossom, all containing cut variables act as part of the
vertex's effective potential. Storing this value makes external edge slack a constant-time read. -/
noncomputable def effectiveVertexPotential {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  potential v + ∑ S ∈ cuts.filter (v ∈ ·), cutDual S

theorem external_edge_dual_eq_effectivePotential {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    (nested : ∀ S ∈ cuts, ∀ u ∈ S, ∀ v ∈ S, blocks.block u = blocks.block v)
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) {u v : Fin n}
    (separate : blocks.block u ≠ blocks.block v) :
    oddCutDualEdgeValue cuts potential cutDual s(u, v) =
      effectiveVertexPotential cuts potential cutDual u + effectiveVertexPotential cuts potential cutDual v := by
  have different : u ≠ v := fun equal => separate (congrArg blocks.block equal)
  rw [oddCutDualEdgeValue_mk cuts potential cutDual different]
  have cutSum : (∑ S ∈ cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)), cutDual S) =
      (∑ S ∈ cuts.filter (u ∈ ·), cutDual S) + ∑ S ∈ cuts.filter (v ∈ ·), cutDual S := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S inCuts
    by_cases insideU : u ∈ S <;> by_cases insideV : v ∈ S
    · exact (separate (nested S inCuts u insideU v insideV)).elim
    all_goals simp [insideU, insideV]
  rw [cutSum]
  unfold effectiveVertexPotential
  abel

private theorem effectiveForestDirection {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ) {v : Fin n} (hv : v ∈ O) :
    effectiveVertexPotential cuts (forestVertexDirection blocks label) (forestCutDirection blocks label) v =
      label (blocks.block v) := by
  have support : (cuts.filter (v ∈ ·)).filter (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1) =
      if (blocks.block v).card = 1 then ∅ else {blocks.block v} := by
    by_cases singleton : (blocks.block v).card = 1
    · rw [if_pos singleton]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S present
      obtain ⟨inCut, top, nontrivial⟩ := Finset.mem_filter.mp present
      have inside := (Finset.mem_filter.mp inCut).2
      obtain ⟨w, hw, shape⟩ := Finset.mem_image.mp top
      have same : blocks.block v = S := (blocks.same_of_mem hw (shape.symm ▸ inside)).trans shape
      exact nontrivial (same ▸ singleton)
    · rw [if_neg singleton]
      ext S
      constructor
      · intro present
        obtain ⟨inCut, top, _⟩ := Finset.mem_filter.mp present
        have inside := (Finset.mem_filter.mp inCut).2
        obtain ⟨w, hw, shape⟩ := Finset.mem_image.mp top
        exact Finset.mem_singleton.mpr ((blocks.same_of_mem hw (shape.symm ▸ inside)).trans shape).symm
      · intro equal
        obtain rfl := Finset.mem_singleton.mp equal
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨blocks.cut_mem hv singleton, blocks.self_mem v hv⟩,
          Finset.mem_image_of_mem _ hv, singleton⟩
  have cutSum : (∑ S ∈ cuts.filter (v ∈ ·), forestCutDirection blocks label S) =
      ∑ S ∈ (if (blocks.block v).card = 1 then ∅ else {blocks.block v}), label S := by
    rw [← support]
    exact (Finset.sum_filter _ _).symm
  by_cases one : (blocks.block v).card = 1 <;>
    simp [effectiveVertexPotential, forestVertexDirection, cutSum, one]

/-- The effective-potential table is updated by the label of each vertex's current
top-level blossom. This is one linear pass over the vertices. -/
theorem effectiveVertexPotential_shift {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ)
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) (δ : ℝ) {v : Fin n} (hv : v ∈ O) :
    effectiveVertexPotential cuts (fun x => potential x + δ * forestVertexDirection blocks label x)
      (fun S => cutDual S + δ * forestCutDirection blocks label S) v =
    effectiveVertexPotential cuts potential cutDual v + δ * label (blocks.block v) := by
  rw [← effectiveForestDirection blocks label hv]
  simp only [effectiveVertexPotential, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  abel

/-- The outer-to-outer bucket key stays unchanged while both endpoint potentials gain
delta. This avoids touching the quadratic bucket table during a dual step. -/
theorem normalizedOuterSlack_advance (cost left right accumulated delta : ℝ) :
    cost - (left + delta) - (right + delta) + 2 * (accumulated + delta) =
      cost - left - right + 2 * accumulated := by
  ring

end VehicleRoutingSurvey.Routing
end RppSource_WeightedEffectivePotential

/-! matching/MatchingSearchTopology.lean -/
section RppSource_MatchingSearchTopology
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem effectiveVertexPotential_register_cut {k : ℕ} (cuts : Finset (Finset (Fin k)))
    (B : Finset (Fin k)) (potential : Fin k → ℝ) (cutDual : Finset (Fin k) → ℝ) (v : Fin k) :
    effectiveVertexPotential (insert B cuts) potential (extendBlossomCutDual cuts cutDual) v =
      effectiveVertexPotential cuts potential cutDual v := by
  simp only [effectiveVertexPotential, Finset.sum_filter]
  congr 1
  have same : (∑ S ∈ cuts, if v ∈ S then extendBlossomCutDual cuts cutDual S else 0) =
      ∑ S ∈ cuts, if v ∈ S then cutDual S else 0 := by
    apply Finset.sum_congr rfl
    intro S present
    rw [extendBlossomCutDual, if_pos present]
  by_cases old : B ∈ cuts
  · rwa [Finset.insert_eq_of_mem old]
  · rw [Finset.sum_insert old, same]
    simp [extendBlossomCutDual, old]

theorem effectiveVertexPotential_erase_zero {k : ℕ} (cuts : Finset (Finset (Fin k)))
    {B : Finset (Fin k)} (present : B ∈ cuts) (potential : Fin k → ℝ)
    (cutDual : Finset (Fin k) → ℝ) (zero : cutDual B = 0) (v : Fin k) :
    effectiveVertexPotential (cuts.erase B) potential cutDual v = effectiveVertexPotential cuts potential cutDual v := by
  simp only [effectiveVertexPotential, Finset.sum_filter]
  congr 1
  simpa [zero] using Finset.sum_erase_add cuts (fun S => if v ∈ S then cutDual S else 0) present

/-- Contraction registers an odd cut with dual zero. It leaves the original
matching and every edge's dual value intact. -/
noncomputable def CompactMatchingPrimalDual.registerCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (B : Finset (Fin k)) (odd : Odd B.card) :
    CompactMatchingPrimalDual k cost where
  covered := state.covered
  edges := state.edges
  perfect := state.perfect
  cuts := insert B state.cuts
  potential := state.potential
  cutDual := extendBlossomCutDual state.cuts state.cutDual
  cutValid S present := by
    by_cases old : S ∈ state.cuts
    · simpa only [extendBlossomCutDual, if_pos old] using state.cutValid S old
    · have eq : S = B := (Finset.mem_insert.mp present).resolve_right old
      exact ⟨eq.symm ▸ odd, by simp [extendBlossomCutDual, old]⟩
  feasible e legal := by rw [oddCutDualEdgeValue_register_cut]; exact state.feasible e legal
  tight e member := by rw [oddCutDualEdgeValue_register_cut]; exact state.tight e member
  internal S _ positive := by
    have old : S ∈ state.cuts := by
      by_contra absent
      simp [extendBlossomCutDual, absent] at positive
    exact state.internal S old (by simpa only [extendBlossomCutDual, if_pos old] using positive)

/-- Expansion removes the exhausted cut. Its children's registry and dual
values stay available for the next forest and matching operations. -/
def CompactMatchingPrimalDual.eraseZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {B : Finset (Fin k)}
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0) : CompactMatchingPrimalDual k cost where
  covered := state.covered
  edges := state.edges
  perfect := state.perfect
  cuts := state.cuts.erase B
  potential := state.potential
  cutDual := state.cutDual
  cutValid S member := state.cutValid S (Finset.mem_of_mem_erase member)
  feasible e legal := by rw [oddCutDualEdgeValue_erase_zero _ present _ _ zero]; exact state.feasible e legal
  tight e member := by rw [oddCutDualEdgeValue_erase_zero _ present _ _ zero]; exact state.tight e member
  internal S member := state.internal S (Finset.mem_of_mem_erase member)

theorem CompactMatchingPrimalDual.InternalCuts.registerCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (internal : state.InternalCuts)
    {B : Finset (Fin k)} (odd : Odd B.card)
    (new : ∃ base ∈ B, ∀ v ∈ B, v ≠ base → ∃ e ∈ state.edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B) :
    (state.registerCut B odd).InternalCuts := by
  intro S present
  rcases Finset.mem_insert.mp present with rfl | old
  · exact new
  · exact internal S old

theorem CompactMatchingPrimalDual.InternalCuts.eraseZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (internal : state.InternalCuts)
    {B : Finset (Fin k)} (present : B ∈ state.cuts) (zero : state.cutDual B = 0) :
    (state.eraseZeroCut present zero).InternalCuts :=
  fun S member => internal S (Finset.mem_of_mem_erase member)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchTopology

/-! matching/MatchingCacheWriteRAM.lean -/
section RppSource_MatchingCacheWriteRAM
namespace VehicleRoutingSurvey.Routing

/-- Register 18 is the cache slot, registers 15–16 its original endpoints, real register 0
the slack, and real register 4 the rate. Slot `r` uses event identifier `r+1`. -/
def storeMatchingCandidateCell : List ArithmeticInstruction :=
  [.natAdd 6 18 9, .natAdd 10 58 18, .natStore 10 6, .natAdd 10 18 18,
    .natAdd 10 54 10, .natStore 10 15, .natAdd 10 10 9, .natStore 10 16,
    .natAdd 10 59 18, .realStore 10 0, .natAdd 10 60 18, .realStore 10 4]

def installedMatchingCandidateNat (s : ArithmeticState) : ℕ → ℕ :=
  let slot := s.nr 18
  let position := s.nr 54 + (slot + slot)
  let identifier := Function.update s.nm (s.nr 58 + slot) (slot + 1)
  Function.update (Function.update identifier position (s.nr 15)) (position + 1) (s.nr 16)

def installedMatchingCandidateReal (s : ArithmeticState) : ℕ → ℝ :=
  let slot := s.nr 18
  Function.update (Function.update s.rm (s.nr 59 + slot) (s.rr 0)) (s.nr 60 + slot) (s.rr 4)

theorem storeMatchingCandidateCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    let t := (arithmeticStep storeMatchingCandidateCell)^[12] s
    BlockRuns storeMatchingCandidateCell 12 s t ∧ t.halted = false ∧
      t.nm = installedMatchingCandidateNat s ∧ t.rm = installedMatchingCandidateReal s := by
  let t := (arithmeticStep storeMatchingCandidateCell)^[12] s
  have effect : t.pc = storeMatchingCandidateCell.length ∧ t.halted = false ∧
      t.nm = installedMatchingCandidateNat s ∧ t.rm = installedMatchingCandidateReal s := by
    simp [t, arithmeticStep, storeMatchingCandidateCell, Function.iterate_succ_apply', entry, running, one,
      installedMatchingCandidateNat, installedMatchingCandidateReal]
  exact ⟨BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2⟩

private def compareMatchingCacheCandidate : List ArithmeticInstruction :=
  [.natAdd 6 58 18, .natLoad 10 6, .natConst 11 0, .natBranch 10 11 7 4,
    .natAdd 6 59 18, .realLoad 2 6, .realBranch 2 0 19 7]

def improveMatchingCandidateBlock : List ArithmeticInstruction :=
  appendBlock compareMatchingCacheCandidate storeMatchingCandidateCell

theorem improveMatchingCandidate_no_write {r : ℕ} (other : r ∉ [0, 6, 10, 11]) :
    ∀ i ∈ improveMatchingCandidateBlock, naturalDestination i ≠ r := by
  intro i member same
  rw [improveMatchingCandidateBlock, appendBlock, List.mem_append] at member
  rcases member with prefixMember | suffixMember
  · have destination := List.mem_map_of_mem (f := naturalDestination) prefixMember
    rw [same] at destination
    simp [compareMatchingCacheCandidate, naturalDestination] at destination
    simp at other
    omega
  · obtain ⟨ins, belongs, rfl⟩ := List.mem_map.mp suffixMember
    rw [naturalDestination_relocate] at same
    have destination := List.mem_map_of_mem (f := naturalDestination) belongs
    rw [same] at destination
    simp [storeMatchingCandidateCell, naturalDestination] at destination
    simp at other
    omega

def matchingCandidateImproves (s : ArithmeticState) : Prop :=
  s.nm (s.nr 58 + s.nr 18) = 0 ∨ s.rr 0 < s.rm (s.nr 59 + s.nr 18)

private theorem improveMatchingCandidate_write {s ready : ArithmeticState} {steps : ℕ}
    (prefixRun : (arithmeticStep improveMatchingCandidateBlock)^[steps] s = relocateState 7 ready)
    (entry : ready.pc = 0) (running : ready.halted = false) (one : ready.nr 9 = 1) :
    ∃ t, BlockRuns improveMatchingCandidateBlock (steps + 12) s t ∧ t.halted = false ∧
      t.nm = installedMatchingCandidateNat ready ∧ t.rm = installedMatchingCandidateReal ready := by
  let last := (arithmeticStep storeMatchingCandidateCell)^[12] ready
  obtain ⟨run, live, natEffect, realEffect⟩ := storeMatchingCandidateCell_spec ready entry running one
  have wrote : (arithmeticStep improveMatchingCandidateBlock)^[12] (relocateState 7 ready) = relocateState 7 last := by
    have shifted := arithmeticIterate_relocate compareMatchingCacheCandidate storeMatchingCandidateCell [] ready 12 run.inside
    rw [List.append_nil] at shifted
    exact shifted
  have complete : (arithmeticStep improveMatchingCandidateBlock)^[steps + 12] s = relocateState 7 last := by
    rw [Nat.add_comm steps 12, Function.iterate_add_apply, prefixRun, wrote]
  have exitLast : last.pc = storeMatchingCandidateCell.length := run.exit
  have exits : (relocateState 7 last).pc = improveMatchingCandidateBlock.length := by
    simp [relocateState, exitLast, improveMatchingCandidateBlock, compareMatchingCacheCandidate]
  exact ⟨_, BlockRuns.of_running_exit complete live exits, live, natEffect, realEffect⟩

/-- Replace an empty cache entry or one with larger slack, preserving the earlier entry on
ties. The comparison and all necessary stores take at most nineteen instructions. -/
theorem improveMatchingCandidateBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ result steps, steps ≤ 19 ∧ BlockRuns improveMatchingCandidateBlock steps s result ∧ result.halted = false ∧
      (matchingCandidateImproves s → result.nm = installedMatchingCandidateNat s ∧ result.rm = installedMatchingCandidateReal s) ∧
      (¬matchingCandidateImproves s → result.nm = s.nm ∧ result.rm = s.rm) ∧
      ∀ r ≥ 15, result.nr r = s.nr r := by
  let read := {s with
    pc := 0
    nr := Function.update (Function.update (Function.update s.nr 6 (s.nr 58 + s.nr 18))
      10 (s.nm (s.nr 58 + s.nr 18))) 11 0}
  let compared := {read with
    nr := Function.update read.nr 6 (s.nr 59 + s.nr 18)
    rr := Function.update read.rr 2 (s.rm (s.nr 59 + s.nr 18))}
  have fixed {t : ArithmeticState} {steps : ℕ} (ran : BlockRuns improveMatchingCandidateBlock steps s t) :
      ∀ r ≥ 15, t.nr r = s.nr r := by
    intro r high
    have writes : ∀ ins ∈ improveMatchingCandidateBlock, naturalDestination ins < r := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate,
        storeMatchingCandidateCell, relocateInstruction, naturalDestination] <;> omega
    exact ran.run ▸ arithmeticRun_keeps_high_register writes s steps
  classical
  by_cases absent : s.nm (s.nr 58 + s.nr 18) = 0
  · have first : (arithmeticStep improveMatchingCandidateBlock)^[4] s = relocateState 7 read := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate, arithmeticStep,
        Function.iterate_succ_apply', read, relocateState, entry, running, absent]
    obtain ⟨out, ran, live, natEffect, realEffect⟩ := improveMatchingCandidate_write first rfl running (by simpa [read] using one)
    refine ⟨out, 16, by decide, ran, live, ?_, ?_, fixed ran⟩
    · intro _
      exact ⟨by simpa [installedMatchingCandidateNat, read] using natEffect,
        by simpa [installedMatchingCandidateReal, read] using realEffect⟩
    · intro refused
      exact (refused (Or.inl absent)).elim
  by_cases better : s.rr 0 < s.rm (s.nr 59 + s.nr 18)
  · have first : (arithmeticStep improveMatchingCandidateBlock)^[7] s = relocateState 7 compared := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate, arithmeticStep,
        Function.iterate_succ_apply', read, compared, relocateState, entry, running, absent, not_le.mpr better]
    obtain ⟨out, ran, live, natEffect, realEffect⟩ := improveMatchingCandidate_write first rfl running
      (by simpa [read, compared] using one)
    refine ⟨out, 19, le_rfl, ran, live, ?_, ?_, fixed ran⟩
    · intro _
      exact ⟨by simpa [installedMatchingCandidateNat, read, compared] using natEffect,
        by simpa [installedMatchingCandidateReal, read, compared] using realEffect⟩
    · intro refused
      exact (refused (Or.inr better)).elim
  · let out := {compared with pc := 19}
    have trace : (arithmeticStep improveMatchingCandidateBlock)^[7] s = out := by
      simp [improveMatchingCandidateBlock, appendBlock, compareMatchingCacheCandidate, arithmeticStep,
        Function.iterate_succ_apply', out, read, compared, entry, running, absent, le_of_not_gt better]
    have ran : BlockRuns improveMatchingCandidateBlock 7 s out :=
      BlockRuns.of_running_exit trace running (by simp [out, improveMatchingCandidateBlock,
        compareMatchingCacheCandidate, storeMatchingCandidateCell])
    exact ⟨out, 7, by decide, ran, running, fun choose => (choose.elim absent better).elim,
      fun _ => ⟨rfl, rfl⟩, fixed ran⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheWriteRAM

/-! matching/MatchingEdgeSlackRAM.lean -/
section RppSource_MatchingEdgeSlackRAM
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- On registers 15 and 16, load a pair's metric entry and its two effective potentials.
The resulting external edge slack is stored in real register 0. -/
def readExternalSlackBlock : List ArithmeticInstruction :=
  [.natAdd 6 21 15, .natLoad 10 6, .natAdd 6 20 10, .natAdd 6 6 16, .realLoad 0 6,
    .natAdd 6 62 15, .realLoad 2 6, .natAdd 6 62 16, .realLoad 3 6,
    .realSub 0 0 2, .realSub 0 0 3]

theorem readExternalSlackBlock_spec (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false) :
    let t := (arithmeticStep readExternalSlackBlock)^[11] s
    BlockRuns readExternalSlackBlock 11 s t ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      t.rr 1 = s.rr 1 ∧
      t.rr 0 = s.rm (s.nr 20 + s.nm (s.nr 21 + s.nr 15) + s.nr 16) -
        s.rm (s.nr 62 + s.nr 15) - s.rm (s.nr 62 + s.nr 16) ∧
      ∀ r, r ≠ 6 → r ≠ 10 → t.nr r = s.nr r := by
  let t := (arithmeticStep readExternalSlackBlock)^[11] s
  have live : t.halted = false := by
    simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  have exit : t.pc = readExternalSlackBlock.length := by
    simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  refine ⟨BlockRuns.of_running_exit rfl live exit, live, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running]
  · intro r not6 not10
    simp [t, arithmeticStep, readExternalSlackBlock, Function.iterate_succ_apply', entry, running, not6, not10]

theorem readExternalSlackBlock_valid {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    (nested : ∀ S ∈ cuts, ∀ u ∈ S, ∀ v ∈ S, blocks.block u = blocks.block v)
    (c : Fin n → Fin n → ℝ) (symmetric : ∀ u v, c u v = c v u)
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) {u v : Fin n}
    (separate : blocks.block u ≠ blocks.block v)
    (s : ArithmeticState) (entry : s.pc = 0) (running : s.halted = false)
    (first : s.nr 15 = u.val) (second : s.nr 16 = v.val)
    (metric : s.rm (s.nr 20 + s.nm (s.nr 21 + u.val) + v.val) = c u v)
    (firstPot : s.rm (s.nr 62 + u.val) = effectiveVertexPotential cuts potential cutDual u)
    (secondPot : s.rm (s.nr 62 + v.val) = effectiveVertexPotential cuts potential cutDual v) :
    let t := (arithmeticStep readExternalSlackBlock)^[11] s
    BlockRuns readExternalSlackBlock 11 s t ∧
      t.rr 0 = edgeCost c s(u, v) - oddCutDualEdgeValue cuts potential cutDual s(u, v) := by
  obtain ⟨run, _, _, _, _, value, _⟩ := readExternalSlackBlock_spec s entry running
  refine ⟨run, ?_⟩
  rw [value, first, second, metric, firstPot, secondPot, edgeCost_eq_of_symmetric c symmetric,
    external_edge_dual_eq_effectivePotential blocks nested potential cutDual separate, sub_add_eq_sub_sub]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingEdgeSlackRAM

/-! matching/MatchingEventDispatchRAM.lean -/
section RppSource_MatchingEventDispatchRAM
namespace VehicleRoutingSurvey.Routing

/-- Execute exactly one of two blocks, selected by a natural register comparison. -/
def branchOnAtMost (x y : ℕ) (left right : List ArithmeticInstruction) : List ArithmeticInstruction :=
  [.natBranch x y 1 (2 + left.length)] ++ left.map (relocateInstruction 1) ++
    [.jump (2 + left.length + right.length)] ++ right.map (relocateInstruction (2 + left.length))

@[simp] theorem branchOnAtMost_length (x y : ℕ) (left right : List ArithmeticInstruction) :
    (branchOnAtMost x y left right).length = 2 + left.length + right.length := by
  simp [branchOnAtMost] <;> omega

theorem forall_naturalDestination_branch (p : ℕ → Prop) (x y : ℕ) (left right : List ArithmeticInstruction) :
    (∀ ins ∈ branchOnAtMost x y left right, p (naturalDestination ins)) ↔
      p 0 ∧ (∀ ins ∈ left, p (naturalDestination ins)) ∧ ∀ ins ∈ right, p (naturalDestination ins) := by
  simp only [branchOnAtMost, List.forall_mem_append, List.forall_mem_map, naturalDestination_relocate]
  simp [naturalDestination, and_assoc, and_left_comm, and_comm]

theorem branchOnAtMost_left (x y : ℕ) (left right : List ArithmeticInstruction)
    {s t : ArithmeticState} {ticks : ℕ} (entry : s.pc = 0) (running : s.halted = false)
    (atMost : s.nr x ≤ s.nr y) (ran : BlockRuns left ticks s t) (live : t.halted = false) :
    BlockRuns (branchOnAtMost x y left right) (1 + ticks + 1) s
      {t with pc := (branchOnAtMost x y left right).length} := by
  let program := branchOnAtMost x y left right
  have enter : arithmeticStep program s = relocateState 1 s := by
    simp [program, branchOnAtMost, arithmeticStep, entry, running, atMost, relocateState]
  have body : (arithmeticStep program)^[ticks] (relocateState 1 s) = relocateState 1 t := by
    have executed := arithmeticIterate_relocate [.natBranch x y 1 (2 + left.length)] left
      ([.jump (2 + left.length + right.length)] ++ right.map (relocateInstruction (2 + left.length)))
      s ticks ran.inside
    simpa [program, branchOnAtMost, List.append_assoc, ran.run] using executed
  have afterLeft : (relocateState 1 t).pc = 1 + left.length := by simp [relocateState, ran.exit]
  have fetched : program[(relocateState 1 t).pc]? = some (.jump program.length) := by
    rw [afterLeft]
    let front : List ArithmeticInstruction := [.natBranch x y 1 (2 + left.length)] ++ left.map (relocateInstruction 1)
    let back : List ArithmeticInstruction :=
      [.jump (2 + left.length + right.length)] ++ right.map (relocateInstruction (2 + left.length))
    have frontLength : front.length = 1 + left.length := by simp [front, Nat.add_comm]
    have layout : program = front ++ back := by simp only [program, branchOnAtMost, front, back, List.append_assoc]
    have lengthAt : program.length = 2 + left.length + right.length := branchOnAtMost_length x y left right
    rw [lengthAt, layout, List.getElem?_append_right (by rw [frontLength])]
    simp [frontLength, back]
  have leave : arithmeticStep program (relocateState 1 t) = {t with pc := program.length} := by
    have stillRunning : (relocateState 1 t).halted = false := live
    unfold arithmeticStep
    simp only [stillRunning, Bool.false_eq_true, if_false, fetched]
    simp [relocateState, live]
  apply BlockRuns.of_running_exit
  · change (arithmeticStep program)^[1 + ticks + 1] s = {t with pc := program.length}
    rw [Function.iterate_succ_apply', Nat.add_comm 1 ticks, Function.iterate_add_apply, Function.iterate_one,
      enter, body, leave]
  · exact live
  · rfl

theorem branchOnAtMost_right (x y : ℕ) (left right : List ArithmeticInstruction)
    {s t : ArithmeticState} {ticks : ℕ} (entry : s.pc = 0) (running : s.halted = false)
    (larger : s.nr y < s.nr x) (ran : BlockRuns right ticks s t) (live : t.halted = false) :
    BlockRuns (branchOnAtMost x y left right) (1 + ticks) s
      {t with pc := (branchOnAtMost x y left right).length} := by
  let program := branchOnAtMost x y left right
  let front : List ArithmeticInstruction :=
    [.natBranch x y 1 (2 + left.length)] ++ left.map (relocateInstruction 1) ++ [.jump (2 + left.length + right.length)]
  have frontLength : front.length = 2 + left.length := by simp [front] <;> omega
  have enter : arithmeticStep program s = relocateState front.length s := by
    simp [program, branchOnAtMost, arithmeticStep, entry, running, not_le.mpr larger, relocateState, frontLength]
  have body : (arithmeticStep program)^[ticks] (relocateState front.length s) = relocateState front.length t := by
    have layout : program = front ++ right.map (relocateInstruction front.length) ++ [] := by
      rw [frontLength]
      simp [program, branchOnAtMost, front, List.append_assoc]
    rw [layout]
    simpa only [ran.run] using
      arithmeticIterate_relocate front right [] s ticks ran.inside
  apply BlockRuns.of_running_exit
  · rw [Nat.add_comm 1 ticks, Function.iterate_add_apply, Function.iterate_one, enter, body]
    simp [relocateState, frontLength, ran.exit]
  · exact live
  · rfl

/-- After the action tag is stored in register 35, dispatch to its grow, contract, expand,
or augment code. Registers 36–38 hold 0, 1, and 2. -/
def dispatchMatchingActionBlock (grow contract expand augment : List ArithmeticInstruction) : List ArithmeticInstruction :=
  branchOnAtMost 35 37 (branchOnAtMost 35 36 grow contract) (branchOnAtMost 35 38 expand augment)

theorem dispatchMatchingActionBlock_spec
    {grow contract expand augment : List ArithmeticInstruction} {s t : ArithmeticState} {ticks : ℕ}
    (entry : s.pc = 0) (running : s.halted = false) (live : t.halted = false)
    (zero : s.nr 36 = 0) (one : s.nr 37 = 1) (two : s.nr 38 = 2)
    (action : s.nr 35 ≤ 3)
    (ran : BlockRuns (match s.nr 35 with
      | 0 => grow | 1 => contract | 2 => expand | _ => augment) ticks s t) :
    ∃ steps ≤ ticks + 4, BlockRuns (dispatchMatchingActionBlock grow contract expand augment) steps s
      {t with pc := (dispatchMatchingActionBlock grow contract expand augment).length} := by
  have cases : s.nr 35 = 0 ∨ s.nr 35 = 1 ∨ s.nr 35 = 2 ∨ s.nr 35 = 3 := by omega
  rcases cases with tag | tag | tag | tag
  · rw [tag] at ran
    have first := branchOnAtMost_left 35 36 grow contract entry running (by omega) ran live
    have routed := branchOnAtMost_left 35 37 _ (branchOnAtMost 35 38 expand augment) entry running (by omega) first (by exact live)
    exact ⟨1 + (1 + ticks + 1) + 1, by omega, routed⟩
  · rw [tag] at ran
    have second := branchOnAtMost_right 35 36 grow contract entry running (by omega) ran live
    have routed := branchOnAtMost_left 35 37 _ (branchOnAtMost 35 38 expand augment) entry running (by omega) second (by exact live)
    exact ⟨1 + (1 + ticks) + 1, by omega, routed⟩
  · rw [tag] at ran
    have third := branchOnAtMost_left 35 38 expand augment entry running (by omega) ran live
    have routed := branchOnAtMost_right 35 37 (branchOnAtMost 35 36 grow contract) _ entry running (by omega) third (by exact live)
    exact ⟨1 + (1 + ticks + 1), by omega, routed⟩
  · rw [tag] at ran
    have last := branchOnAtMost_right 35 38 expand augment entry running (by omega) ran live
    have routed := branchOnAtMost_right 35 37 (branchOnAtMost 35 36 grow contract) _ entry running (by omega) last (by exact live)
    exact ⟨1 + (1 + ticks), by omega, routed⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingEventDispatchRAM

/-! matching/MatchingPairBucketRAM.lean -/
section RppSource_MatchingPairBucketRAM
namespace VehicleRoutingSurvey.Routing

/-- Update one outer-to-outer bucket. Register 18 is its flat index, 15 and 16 are
the original endpoints, and real register 5 is the normalized slack. -/
def improveMatchingPairBucketCell : List ArithmeticInstruction :=
  [.natAdd 6 18 18, .natAdd 6 65 6, .natLoad 10 6, .natBranch 55 10 7 4,
    .natAdd 11 66 18, .realLoad 2 11, .realBranch 2 5 12 7,
    .natStore 6 15, .natAdd 6 6 9, .natStore 6 16, .natAdd 11 66 18, .realStore 11 5]

def matchingPairBucketAddress (s : ArithmeticState) : ℕ := s.nr 65 + (s.nr 18 + s.nr 18)

def matchingPairBucketImproves (s : ArithmeticState) : Prop :=
  s.nr 55 ≤ s.nm (matchingPairBucketAddress s) ∨ s.rr 5 < s.rm (s.nr 66 + s.nr 18)

def installedMatchingPairBucketNat (s : ArithmeticState) : ℕ → ℕ :=
  Function.update (Function.update s.nm (matchingPairBucketAddress s) (s.nr 15))
    (matchingPairBucketAddress s + 1) (s.nr 16)

def installedMatchingPairBucketReal (s : ArithmeticState) : ℕ → ℝ :=
  Function.update s.rm (s.nr 66 + s.nr 18) (s.rr 5)

/-- Keep the least normalized slack in the selected outer-block pair bucket. The first
endpoint equal to the compact vertex count is the empty sentinel. -/
theorem improveMatchingPairBucketCell_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) :
    ∃ result steps, steps ≤ 12 ∧ BlockRuns improveMatchingPairBucketCell steps s result ∧
      result.halted = false ∧
      (matchingPairBucketImproves s → result.nm = installedMatchingPairBucketNat s ∧ result.rm = installedMatchingPairBucketReal s) ∧
      (¬matchingPairBucketImproves s → result.nm = s.nm ∧ result.rm = s.rm) ∧
      ∀ r ≥ 15, result.nr r = s.nr r := by
  have fixed {steps : ℕ} (r : ℕ) (high : 15 ≤ r) :
      ((arithmeticStep improveMatchingPairBucketCell)^[steps] s).nr r = s.nr r :=
    arithmeticRun_keeps_high_register (by
      simp [improveMatchingPairBucketCell, naturalDestination] <;> omega) s steps
  classical
  by_cases absent : s.nr 55 ≤ s.nm (s.nr 65 + (s.nr 18 + s.nr 18))
  · let t := (arithmeticStep improveMatchingPairBucketCell)^[9] s
    have effect : t.pc = improveMatchingPairBucketCell.length ∧ t.halted = false ∧
        t.nm = installedMatchingPairBucketNat s ∧ t.rm = installedMatchingPairBucketReal s := by
      simp [t, arithmeticStep, improveMatchingPairBucketCell, Function.iterate_succ_apply', entry, running,
        one, absent, installedMatchingPairBucketNat, installedMatchingPairBucketReal, matchingPairBucketAddress]
    refine ⟨t, 9, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, fun _ => effect.2.2,
      ?_, fixed⟩
    intro refuses
    exact (refuses (Or.inl absent)).elim
  by_cases better : s.rr 5 < s.rm (s.nr 66 + s.nr 18)
  · let t := (arithmeticStep improveMatchingPairBucketCell)^[12] s
    have effect : t.pc = improveMatchingPairBucketCell.length ∧ t.halted = false ∧
        t.nm = installedMatchingPairBucketNat s ∧ t.rm = installedMatchingPairBucketReal s := by
      simp [t, arithmeticStep, improveMatchingPairBucketCell, Function.iterate_succ_apply', entry, running,
        one, absent, not_le.mpr better, installedMatchingPairBucketNat, installedMatchingPairBucketReal,
        matchingPairBucketAddress]
    refine ⟨t, 12, le_rfl, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, fun _ => effect.2.2,
      ?_, fixed⟩
    intro refuses
    exact (refuses (Or.inr better)).elim
  · let t := (arithmeticStep improveMatchingPairBucketCell)^[7] s
    have effect : t.pc = improveMatchingPairBucketCell.length ∧ t.halted = false ∧ t.nm = s.nm ∧ t.rm = s.rm := by
      simp [t, arithmeticStep, improveMatchingPairBucketCell, Function.iterate_succ_apply', entry, running,
        absent, le_of_not_gt better]
    refine ⟨t, 7, by decide, BlockRuns.of_running_exit rfl effect.2.1 effect.1, effect.2.1, ?_,
      fun _ => effect.2.2, fixed⟩
    intro chooses
    exact (chooses.elim absent better).elim

end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairBucketRAM

/-! matching/MatchingGrowCacheRAM.lean -/
section RppSource_MatchingGrowCacheRAM
namespace VehicleRoutingSurvey.Routing

attribute [local simp] List.forall_mem_append List.forall_mem_map
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def readGrowthCacheNeighbor : List ArithmeticInstruction :=
  [.natAdd 16 25 14, .natAdd 6 57 16, .natLoad 17 6, .natAdd 6 51 17, .natLoad 19 6]

def growIncomingArgs (rate : ℚ) : List ArithmeticInstruction :=
  [.natAdd 18 55 16, .realConst 4 rate]

def growIncomingCache (rate : ℚ) : List ArithmeticInstruction :=
  appendBlock (growIncomingArgs rate) improveMatchingCandidateBlock

def normalizeGrowthSlack : List ArithmeticInstruction :=
  [.realAdd 5 15 15, .realAdd 5 5 0, .realConst 4 2]

def growBucketArgs (source target : ℕ) : List ArithmeticInstruction :=
  [.natAdd 6 21 source, .natLoad 10 6, .natAdd 18 10 target]

def growOuterRowArgs (source : ℕ) : List ArithmeticInstruction :=
  [.natAdd 18 source 14]

def growOuterCacheSide (source target : ℕ) : List ArithmeticInstruction :=
  appendBlock (appendBlock (growBucketArgs source target) improveMatchingPairBucketCell)
    (appendBlock (growOuterRowArgs source) improveMatchingCandidateBlock)

/-- Registers 26 and 17 name distinct outer blocks, 15 and 16 name the original
endpoints, and real register 0 contains the raw edge slack. Insert the edge into
both outer pair buckets and both incident candidate rows. -/
def insertMatchingOuterEdgeBlock : List ArithmeticInstruction :=
  appendBlock normalizeGrowthSlack
    (appendBlock (growOuterCacheSide 26 17) (growOuterCacheSide 17 26))

def chooseGrowthCache : List ArithmeticInstruction :=
  branchOnAtMost 19 14 (growIncomingCache 1)
    (branchOnAtMost 19 9 insertMatchingOuterEdgeBlock (growIncomingCache 0))

/-- An original vertex in the newly outer block is in register 15. Visit the original
neighbor indexed by register 25. Register 26 contains the newly outer representative
and register 14 is zero. Internal edges are skipped. For external edges, update the
incoming cache for a nonouter target or both directed buckets and row caches for an
outer target. -/
def refreshGrowthNeighborBlock : List ArithmeticInstruction :=
  appendBlock readGrowthCacheNeighbor
    (branchOnUnequal 26 17 (appendBlock readExternalSlackBlock chooseGrowthCache))

structure CacheMemoryFrame (s t : ArithmeticState) : Prop where
  natural : ∀ a < s.nr 58, t.nm a = s.nm a
  real : ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a

private def CacheBlockBounded (code : List ArithmeticInstruction) (cap : ℕ) : Prop :=
  ∀ s : ArithmeticState, s.pc = 0 → s.halted = false → s.nr 9 = 1 →
    s.nr 58 ≤ s.nr 54 → s.nr 58 ≤ s.nr 65 →
    ∃ t steps, steps ≤ cap ∧ BlockRuns code steps s t ∧ t.halted = false ∧ CacheMemoryFrame s t

private theorem CacheBlockBounded.append {a b : List ArithmeticInstruction} {m n : ℕ}
    (left : CacheBlockBounded a m) (right : CacheBlockBounded b n)
    (fixed : a.all (fun i => decide (naturalDestination i ∉ [9, 54, 58, 59, 60, 65, 66])) = true) :
    CacheBlockBounded (appendBlock a b) (m + n) := by
  intro s entry running one dict bucket
  obtain ⟨u, steps, small, first, live, prior⟩ := left s entry running one dict bucket
  have kept (r : ℕ) (base : r ∈ [9, 54, 58, 59, 60, 65, 66]) : u.nr r = s.nr r := by
    rw [← first.run]
    apply arithmeticRun_keeps_register _ s steps
    intro i hi same
    have cannot : naturalDestination i ∉ [9, 54, 58, 59, 60, 65, 66] :=
      of_decide_eq_true (List.all_eq_true.mp fixed i hi)
    exact cannot (same.symm ▸ base)
  have oneAgain : u.nr 9 = 1 := (kept 9 (by decide)).trans one
  have floor : u.nr 58 = s.nr 58 := kept 58 (by decide)
  have dictAgain : u.nr 58 ≤ u.nr 54 := by simpa [floor, kept 54 (by decide)] using dict
  have bucketAgain : u.nr 58 ≤ u.nr 65 := by simpa [floor, kept 65 (by decide)] using bucket
  obtain ⟨t, ticks, bounded, second, stillLive, following⟩ :=
    right {u with pc := 0} rfl live oneAgain dictAgain bucketAgain
  refine ⟨_, steps + ticks, Nat.add_le_add small bounded, first.append second, stillLive, ?_, ?_⟩
  · intro i before
    exact (following.natural i (floor.symm ▸ before)).trans (prior.natural i before)
  · intro i before rate pairScore
    have scoreFloor : u.nr 59 = s.nr 59 := kept 59 (by decide)
    have rateAgain : u.nr 59 ≤ u.nr 60 := by simpa [scoreFloor, kept 60 (by decide)] using rate
    have pairAgain : u.nr 59 ≤ u.nr 66 := by simpa [scoreFloor, kept 66 (by decide)] using pairScore
    exact (following.real i (scoreFloor.symm ▸ before) rateAgain pairAgain).trans (prior.real i before rate pairScore)

private theorem CacheBlockBounded.branch {left right : List ArithmeticInstruction} {l r : ℕ}
    (x y : ℕ) (leftBound : CacheBlockBounded left l) (rightBound : CacheBlockBounded right r) :
    CacheBlockBounded (branchOnAtMost x y left right) (max l r + 2) := by
  intro s entry running one dict bucket
  by_cases pickLeft : s.nr x ≤ s.nr y
  · obtain ⟨t, steps, short, run, live, prior⟩ := leftBound s entry running one dict bucket
    have bound := le_max_left l r
    exact ⟨_, 1 + steps + 1, by omega, branchOnAtMost_left x y left right entry running pickLeft run live,
      live, prior.natural, prior.real⟩
  · obtain ⟨t, steps, short, run, live, prior⟩ := rightBound s entry running one dict bucket
    have bound := le_max_right l r
    exact ⟨_, 1 + steps, by omega, branchOnAtMost_right x y left right entry running
      (Nat.lt_of_not_ge pickLeft) run live, live, prior.natural, prior.real⟩

private theorem CacheBlockBounded.unlessEqual {body : List ArithmeticInstruction} {n : ℕ}
    (x y : ℕ) (bound : CacheBlockBounded body n) :
    CacheBlockBounded (branchOnUnequal x y body) (2 + n) := by
  intro s entry running one dict bucket
  by_cases same : s.nr x = s.nr y
  · exact ⟨_, 2, by omega, branchOnUnequal_skip x y body s entry running same, running,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  · obtain ⟨t, steps, short, run, live, prior⟩ := bound s entry running one dict bucket
    exact ⟨_, 2 + steps, by omega, branchOnUnequal_take x y body entry running same run,
      live, prior.natural, prior.real⟩

private theorem readGrowthCacheNeighbor_bound : CacheBlockBounded readGrowthCacheNeighbor 5 := by
  intro s entry running _ _ _
  let t := (arithmeticStep readGrowthCacheNeighbor)^[5] s
  have exit : t.pc = readGrowthCacheNeighbor.length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', readGrowthCacheNeighbor, entry, running]
  refine ⟨t, 5, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', readGrowthCacheNeighbor, entry, running])

private theorem growIncomingArgs_bound (rate : ℚ) : CacheBlockBounded (growIncomingArgs rate) 2 := by
  intro s entry running _ _ _
  let t := (arithmeticStep (growIncomingArgs rate))^[2] s
  have exit : t.pc = (growIncomingArgs rate).length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', growIncomingArgs, entry, running]
  refine ⟨t, 2, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', growIncomingArgs, entry, running])

private theorem improveMatchingCandidate_bound : CacheBlockBounded improveMatchingCandidateBlock 19 := by
  intro s entry running one dict _
  obtain ⟨t, steps, bound, run, live, write, ignore, _⟩ := improveMatchingCandidateBlock_spec s entry running one
  refine ⟨t, steps, bound, run, live, ?_, ?_⟩
  · intro a before
    by_cases better : matchingCandidateImproves s
    · rw [(write better).1]
      simp (disch := omega) [installedMatchingCandidateNat, Function.update_of_ne]
    · rw [(ignore better).1]
  · intro a before rates _
    by_cases better : matchingCandidateImproves s
    · rw [(write better).2]
      simp (disch := omega) [installedMatchingCandidateReal, Function.update_of_ne]
    · rw [(ignore better).2]

private theorem improveMatchingPairBucket_bound : CacheBlockBounded improveMatchingPairBucketCell 12 := by
  intro s entry running one _ bucket
  obtain ⟨t, steps, bound, run, live, write, ignore, _⟩ := improveMatchingPairBucketCell_spec s entry running one
  refine ⟨t, steps, bound, run, live, ?_, ?_⟩
  · intro a before
    by_cases better : matchingPairBucketImproves s
    · rw [(write better).1]
      simp (disch := omega) [installedMatchingPairBucketNat, matchingPairBucketAddress, Function.update_of_ne]
    · rw [(ignore better).1]
  · intro a before _ pairScore
    by_cases better : matchingPairBucketImproves s
    · rw [(write better).2]
      simp (disch := omega) [installedMatchingPairBucketReal, Function.update_of_ne]
    · rw [(ignore better).2]

private theorem growIncomingCache_bound (rate : ℚ) : CacheBlockBounded (growIncomingCache rate) 21 :=
  CacheBlockBounded.append (growIncomingArgs_bound rate) improveMatchingCandidate_bound rfl

private theorem normalizeGrowthSlack_bound : CacheBlockBounded normalizeGrowthSlack 3 := by
  intro s entry running _ _ _
  let t := (arithmeticStep normalizeGrowthSlack)^[3] s
  have exit : t.pc = normalizeGrowthSlack.length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', normalizeGrowthSlack, entry, running]
  refine ⟨t, 3, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', normalizeGrowthSlack, entry, running])

private theorem growBucketArgs_bound (source target : ℕ) : CacheBlockBounded (growBucketArgs source target) 3 := by
  intro s entry running _ _ _
  let t := (arithmeticStep (growBucketArgs source target))^[3] s
  have exit : t.pc = (growBucketArgs source target).length ∧ t.halted = false := by
    simp [t, arithmeticStep, Function.iterate_succ_apply', growBucketArgs, entry, running]
  refine ⟨t, 3, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, Function.iterate_succ_apply', growBucketArgs, entry, running])

private theorem growOuterRowArgs_bound (source : ℕ) : CacheBlockBounded (growOuterRowArgs source) 1 := by
  intro s entry running _ _ _
  let t := arithmeticStep (growOuterRowArgs source) s
  have exit : t.pc = (growOuterRowArgs source).length ∧ t.halted = false := by
    simp [t, arithmeticStep, growOuterRowArgs, entry, running]
  refine ⟨t, 1, le_rfl, BlockRuns.of_running_exit rfl exit.2 exit.1, exit.2, ?_, ?_⟩ <;>
    (intros; simp [t, arithmeticStep, growOuterRowArgs, entry, running])

private theorem growOuterCacheSide_bound (source target : ℕ) :
    CacheBlockBounded (growOuterCacheSide source target) 35 :=
  CacheBlockBounded.append
    (CacheBlockBounded.append (growBucketArgs_bound source target) improveMatchingPairBucket_bound rfl)
    (CacheBlockBounded.append (growOuterRowArgs_bound source) improveMatchingCandidate_bound rfl)
    rfl

theorem growOuterCacheSide_frames (source target : ℕ) (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t ticks, ticks ≤ 35 ∧ BlockRuns (growOuterCacheSide source target) ticks s t ∧
      t.halted = false ∧ CacheMemoryFrame s t :=
  growOuterCacheSide_bound source target s entry running one dict bucket

private theorem growOuterCache_bound : CacheBlockBounded insertMatchingOuterEdgeBlock 73 := by
  exact CacheBlockBounded.append (m := 3) (n := 70) normalizeGrowthSlack_bound
    (CacheBlockBounded.append (growOuterCacheSide_bound 26 17) (growOuterCacheSide_bound 17 26) rfl) rfl

theorem insertMatchingOuterEdgeBlock_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ 73 ∧ BlockRuns insertMatchingOuterEdgeBlock steps s t ∧ t.halted = false ∧
      ∀ a < s.nr 58, t.nm a = s.nm a := by
  obtain ⟨t, steps, cost, run, live, frames⟩ := growOuterCache_bound s entry running one dict bucket
  exact ⟨t, steps, cost, run, live, frames.natural⟩

theorem insertMatchingOuterEdgeBlock_frames (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ 73 ∧ BlockRuns insertMatchingOuterEdgeBlock steps s t ∧ t.halted = false ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧
      ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a := by
  obtain ⟨t, steps, cost, run, live, frames⟩ := growOuterCache_bound s entry running one dict bucket
  exact ⟨t, steps, cost, run, live, frames.natural, frames.real⟩

private theorem readExternalSlack_bound : CacheBlockBounded readExternalSlackBlock 11 := by
  intro s entry running _ _ _
  obtain ⟨run, live, natural, real, _⟩ := readExternalSlackBlock_spec s entry running
  exact ⟨_, 11, le_rfl, run, live, fun a _ => congrFun natural a, fun a _ _ _ => congrFun real a⟩

private theorem refreshGrowthNeighborBlock_frames : CacheBlockBounded refreshGrowthNeighborBlock 95 := by
  have chosen : CacheBlockBounded chooseGrowthCache 77 :=
    CacheBlockBounded.branch 19 14 (growIncomingCache_bound 1)
      (CacheBlockBounded.branch 19 9 growOuterCache_bound (growIncomingCache_bound 0))
  have external : CacheBlockBounded (appendBlock readExternalSlackBlock chooseGrowthCache) 88 :=
    CacheBlockBounded.append readExternalSlack_bound chosen rfl
  exact CacheBlockBounded.append readGrowthCacheNeighbor_bound (external.unlessEqual 26 17) rfl

theorem refreshGrowthNeighborBlock_memory (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps s t ∧ t.halted = false ∧ CacheMemoryFrame s t :=
  refreshGrowthNeighborBlock_frames s entry running one dict bucket

/-- A single neighbor refresh performs at most ninety-five arithmetic instructions. -/
theorem refreshGrowthNeighborBlock_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps s t ∧ t.halted = false ∧
      ∀ a < s.nr 58, t.nm a = s.nm a := by
  obtain ⟨t, steps, cost, run, live, frames⟩ := refreshGrowthNeighborBlock_frames s entry running one dict bucket
  exact ⟨t, steps, cost, run, live, frames.natural⟩

private theorem refreshGrowthNeighbor_no_write {r : ℕ}
    (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19]) :
    ∀ i ∈ refreshGrowthNeighborBlock, naturalDestination i ≠ r :=
  naturalDestination_ne_of_list [0, 6, 10, 11, 16, 17, 18, 19] (by decide) away

def refreshSelectedOuterVertex : List ArithmeticInstruction :=
  countedLoopFromZero 9 25 55 refreshGrowthNeighborBlock

/-- Scan one selected outer original while preserving the earlier natural and real tables. -/
theorem refreshSelectedOuterVertex_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ s.nr 55 * 98 + 2 ∧ BlockRuns refreshSelectedOuterVertex steps s t ∧
      t.halted = false ∧ (∀ a < s.nr 58, t.nm a = s.nm a) ∧
      ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → t.rm a = s.rm a := by
  let inv (i : ℕ) (m : ArithmeticState) : Prop :=
    m.pc = 0 ∧ m.halted = false ∧ m.nr 25 = i ∧ m.nr 55 = s.nr 55 ∧ m.nr 9 = 1 ∧
    (∀ r ∈ [54, 58, 59, 60, 65, 66], m.nr r = s.nr r) ∧
    (∀ a < s.nr 58, m.nm a = s.nm a) ∧
    ∀ a < s.nr 59, s.nr 59 ≤ s.nr 60 → s.nr 59 ≤ s.nr 66 → m.rm a = s.rm a
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 25 0} := by
    refine ⟨rfl, running, by simp, by simp, by simpa using one, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro r hi
    have other : r ≠ 25 := by simp at hi; omega
    exact Function.update_of_ne other 0 s.nr
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 25 = i ∧ m.nr 55 = s.nr 55 :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have iteration (i : ℕ) (_ : i < s.nr 55) (m : ArithmeticState) (h : inv i m) :
      ∃ t steps, steps ≤ 95 ∧ BlockRuns refreshGrowthNeighborBlock steps m t ∧ t.halted = false ∧
        inv (i+1) {t with pc := 0, nr := Function.update t.nr 25 (t.nr 25 + t.nr 9)} := by
    obtain ⟨atStart, ready, index, size, unit, keptBases, prior, priorReal⟩ := h
    have mFloor : m.nr 58 = s.nr 58 := keptBases 58 (by decide)
    have mDict : m.nr 58 ≤ m.nr 54 := by simpa [mFloor, keptBases 54 (by decide)] using dict
    have mBucket : m.nr 58 ≤ m.nr 65 := by simpa [mFloor, keptBases 65 (by decide)] using bucket
    obtain ⟨t, steps, short, ran, live, frames⟩ := refreshGrowthNeighborBlock_frames m atStart ready unit mDict mBucket
    have fixed {r : ℕ} (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19]) :
        t.nr r = m.nr r := by
      rw [← ran.run, arithmeticRun_keeps_register (refreshGrowthNeighbor_no_write away)]
    refine ⟨t, steps, short, ran, live, rfl, live, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [fixed (r := 25) (by decide), fixed (r := 9) (by decide), index, unit]
    · simpa using (fixed (r := 55) (by decide)).trans size
    · simpa using (fixed (r := 9) (by decide)).trans unit
    · intro r base
      have no : r ≠ 25 := by simp at base; omega
      have away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19] := by simp at base ⊢; omega
      exact (Function.update_of_ne no _ _).trans ((fixed away).trans (keptBases r base))
    · intro a before
      exact (frames.natural a (mFloor.symm ▸ before)).trans (prior a before)
    · intro a before rate score
      have mReal : m.nr 59 = s.nr 59 := keptBases 59 (by decide)
      have mRate : m.nr 59 ≤ m.nr 60 := by simpa [mReal, keptBases 60 (by decide)] using rate
      have mScore : m.nr 59 ≤ m.nr 66 := by simpa [mReal, keptBases 66 (by decide)] using score
      exact (frames.real a (mReal.symm ▸ before) mRate mScore).trans (priorReal a before rate score)
  obtain ⟨t, steps, valid, short, ran⟩ := countedLoopFromZero_bounded 9 25 55 (s.nr 55)
    95 refreshGrowthNeighborBlock inv entry running initial control iteration
  obtain ⟨_, ready, _, _, _, _, natural, real⟩ := valid
  exact ⟨_, steps, by omega, ran, ready, natural, real⟩

theorem refreshSelectedOuterVertex_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ s.nr 55 * 98 + 2 ∧ BlockRuns refreshSelectedOuterVertex steps s t ∧
      t.halted = false ∧ ∀ a < s.nr 58, t.nm a = s.nm a := by
  obtain ⟨t, steps, cost, run, live, natural, _⟩ := refreshSelectedOuterVertex_spec s entry running one dict bucket
  exact ⟨t, steps, cost, run, live, natural⟩

theorem refreshSelectedOuterVertex_no_write {r : ℕ}
    (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25]) :
    ∀ i ∈ refreshSelectedOuterVertex, naturalDestination i ≠ r :=
  naturalDestination_ne_of_list [0, 6, 10, 11, 16, 17, 18, 19, 25] (by decide) away

def readGrowthCacheSource : List ArithmeticInstruction :=
  [.natAdd 15 24 14, .natAdd 6 57 15, .natLoad 17 6]

def selectedGrowthCacheSource : List ArithmeticInstruction :=
  appendBlock [.natAdd 27 27 9] refreshSelectedOuterVertex

def refreshGrowthCacheSourceBlock : List ArithmeticInstruction :=
  appendBlock readGrowthCacheSource
    (branchOnAtMost 17 26 (branchOnAtMost 26 17 selectedGrowthCacheSource []) [])

def initGrowthCacheScan : List ArithmeticInstruction :=
  [.natConst 24 0, .natConst 27 0]

/-- Visit each compact vertex once. Only vertices whose representative is the newly
outer block in register 26 initiate a neighbor scan. Register 27 counts those scans. -/
def refreshMatchingNewOuterBlock : List ArithmeticInstruction :=
  appendBlock initGrowthCacheScan (countedLoop 9 24 55 refreshGrowthCacheSourceBlock)

theorem readGrowthCacheSource_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let next := { s with
      pc := 3
      nr := Function.update (Function.update (Function.update s.nr 15 (s.nr 24 + s.nr 14))
        6 (s.nr 57 + (s.nr 24 + s.nr 14))) 17 (s.nm (s.nr 57 + (s.nr 24 + s.nr 14))) }
    BlockRuns readGrowthCacheSource 3 s next := by
  dsimp only
  apply BlockRuns.of_running_exit
  · simp [readGrowthCacheSource, arithmeticStep, Function.iterate_succ_apply', entry, running]
  · exact running
  · rfl

private theorem nilBlockRuns (s : ArithmeticState) (entry : s.pc = 0) :
    BlockRuns [] 0 s s := by
  exact ⟨fun i early => (Nat.not_lt_zero i early).elim, by simp, entry⟩

private theorem selectedGrowthCacheSource_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ t steps, steps ≤ s.nr 55 * 98 + 3 ∧ BlockRuns selectedGrowthCacheSource steps s t ∧
      t.halted = false ∧ t.nr 27 = s.nr 27 + 1 ∧
      t.nr 9 = s.nr 9 ∧ t.nr 24 = s.nr 24 ∧ t.nr 55 = s.nr 55 ∧
      ∀ a < s.nr 58, t.nm a = s.nm a := by
  let bumped := {s with pc := 1, nr := Function.update s.nr 27 (s.nr 27 + 1)}
  have bump : BlockRuns [.natAdd 27 27 9] 1 s bumped := by
    apply BlockRuns.of_running_exit
    · simp [bumped, arithmeticStep, entry, running, one]
    · exact running
    · rfl
  let loaded := {bumped with pc := 0}
  have oneAt : loaded.nr 9 = 1 := by simp [loaded, bumped, one]
  have dimension : loaded.nr 55 = s.nr 55 := by simp [loaded, bumped]
  have dictAt : loaded.nr 58 ≤ loaded.nr 54 := by simpa [loaded, bumped] using dict
  have bucketAt : loaded.nr 58 ≤ loaded.nr 65 := by simpa [loaded, bumped] using bucket
  obtain ⟨t, steps, short, run, live, earlier⟩ := refreshSelectedOuterVertex_bound loaded rfl running oneAt dictAt bucketAt
  have fixed {r : ℕ} (away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25]) :
      t.nr r = loaded.nr r := by
    rw [← run.run, arithmeticRun_keeps_register (refreshSelectedOuterVertex_no_write away)]
  refine ⟨_, 1 + steps, by omega, bump.append run, live, ?_, ?_, ?_, ?_, ?_⟩
  · change t.nr 27 = s.nr 27 + 1
    rw [fixed (by decide)]
    simp [loaded, bumped]
  · change t.nr 9 = s.nr 9
    rw [fixed (by decide), oneAt, one]
  · change t.nr 24 = s.nr 24
    rw [fixed (by decide)]
    simp [loaded, bumped]
  · exact (fixed (by decide)).trans dimension
  · intro a before
    exact earlier a (by simpa [loaded, bumped] using before)

private theorem refreshGrowthCacheSourceBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65) :
    ∃ (t : ArithmeticState) (steps : ℕ) (selected : Bool), BlockRuns refreshGrowthCacheSourceBlock steps s t ∧
      t.halted = false ∧ t.nr 9 = s.nr 9 ∧ t.nr 24 = s.nr 24 ∧ t.nr 55 = s.nr 55 ∧
      t.nr 27 = s.nr 27 + selected.toNat ∧ steps ≤ 8 + (s.nr 55 * 98 + 2) * selected.toNat ∧
      selected = decide (s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) = s.nr 26) ∧
      ∀ a < s.nr 58, t.nm a = s.nm a := by
  let fetched := { s with
    pc := 3
    nr := Function.update (Function.update (Function.update s.nr 15 (s.nr 24 + s.nr 14)) 6
      (s.nr 57 + (s.nr 24 + s.nr 14))) 17 (s.nm (s.nr 57 + (s.nr 24 + s.nr 14))) }
  have reads : BlockRuns readGrowthCacheSource 3 s fetched := readGrowthCacheSource_spec s entry running
  let p := {fetched with pc := 0}
  have pOne : p.nr 9 = 1 := by simp [p, fetched, one]
  have fixed9 : p.nr 9 = s.nr 9 := by simp [p, fetched]
  have fixed24 : p.nr 24 = s.nr 24 := by simp [p, fetched]
  have fixed55 : p.nr 55 = s.nr 55 := by simp [p, fetched]
  have fixed27 : p.nr 27 = s.nr 27 := by simp [p, fetched]
  have number : p.nr 17 = s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) := by simp [p, fetched]
  have peer : p.nr 26 = s.nr 26 := by simp [p, fetched]
  have pDict : p.nr 58 ≤ p.nr 54 := by simpa [p, fetched] using dict
  have pBucket : p.nr 58 ≤ p.nr 65 := by simpa [p, fetched] using bucket
  by_cases upper : p.nr 17 ≤ p.nr 26
  · by_cases lower : p.nr 26 ≤ p.nr 17
    · obtain ⟨t, steps, short, scanned, live, count, oneAgain, index, dimension, earlier⟩ :=
        selectedGrowthCacheSource_spec p rfl running pOne pDict pBucket
      have inner := branchOnAtMost_left 26 17 selectedGrowthCacheSource [] (s := p) rfl running lower scanned live
      have outer := branchOnAtMost_left 17 26 _ [] (s := p) rfl running upper inner live
      have accepted : s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) = s.nr 26 :=
        number.symm.trans ((Nat.le_antisymm upper lower).trans peer)
      rw [fixed55] at short
      refine ⟨_, 3 + (1 + (1 + steps + 1) + 1), true, reads.append outer, live, oneAgain.trans fixed9,
        index.trans fixed24, dimension.trans fixed55, by
          change t.nr 27 = s.nr 27 + 1
          rw [count, fixed27], by
          change 3 + (1 + (1 + steps + 1) + 1) ≤ 8 + (s.nr 55 * 98 + 2) * 1
          omega, by simp [accepted], ?_⟩
      intro a before
      exact earlier a (by simpa [p, fetched] using before)
    · have inner := branchOnAtMost_right 26 17 selectedGrowthCacheSource [] (s := p) rfl running
        (Nat.lt_of_not_ge lower) (nilBlockRuns p rfl) running
      have outer := branchOnAtMost_left 17 26 _ [] (s := p) rfl running upper inner running
      have rejected : s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) ≠ s.nr 26 := by
        rw [← number, ← peer]
        exact fun eq => lower eq.ge
      exact ⟨_, 3 + (1 + (1 + 0) + 1), false, reads.append outer, running, fixed9, fixed24, fixed55,
        by change p.nr 27 = s.nr 27; exact fixed27, by simp, by simp [rejected], fun _ _ => rfl⟩
  · have outer := branchOnAtMost_right 17 26 (branchOnAtMost 26 17 selectedGrowthCacheSource []) []
      (s := p) rfl running (Nat.lt_of_not_ge upper) (nilBlockRuns p rfl) running
    have rejected : s.nm (s.nr 57 + (s.nr 24 + s.nr 14)) ≠ s.nr 26 := by
      rw [← number, ← peer]
      exact fun eq => upper eq.le
    exact ⟨_, 3 + (1 + 0), false, reads.append outer, running, fixed9, fixed24, fixed55,
      by change p.nr 27 = s.nr 27; exact fixed27, by simp, by simp [rejected], fun _ _ => rfl⟩

theorem growthCacheSourceBlock_no_write {r : ℕ}
    (away : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 27]) :
    ∀ ins ∈ refreshGrowthCacheSourceBlock, naturalDestination ins ≠ r :=
  naturalDestination_ne_of_list [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 27] (by decide) away

private theorem growthCacheSourceBlock_keeps {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns refreshGrowthCacheSourceBlock steps s t) {r : ℕ}
    (base : r ∈ [14, 26, 54, 57, 58, 65]) : t.nr r = s.nr r := by
  have away : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 27] := by simp at base ⊢; omega
  exact run.run ▸ arithmeticRun_keeps_register (growthCacheSourceBlock_no_write away) s steps

theorem refreshMatchingNewOuterBlock_keeps {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns refreshMatchingNewOuterBlock steps s t)
    (away : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 27]) : t.nr r = s.nr r := by
  rw [← run.run]
  exact arithmeticRun_keeps_from_destination_list [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 27]
    (by decide) away s steps

def matchingGrowthMembers (s : ArithmeticState) (i : ℕ) : ℕ :=
  ((List.range i).filter fun j => decide (s.nm (s.nr 57 + j) = s.nr 26)).length

private theorem matchingGrowthMembers_succ (s : ArithmeticState) (i : ℕ) :
    matchingGrowthMembers s (i + 1) = matchingGrowthMembers s i +
      (decide (s.nm (s.nr 57 + i) = s.nr 26)).toNat := by
  by_cases accepts : s.nm (s.nr 57 + i) = s.nr 26 <;>
    simp [matchingGrowthMembers, List.range_succ, List.filter_append, accepts]

private structure GrowthCacheScan (initial : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  live : s.halted = false
  index : s.nr 24 = i
  dimension : s.nr 55 = initial.nr 55
  one : s.nr 9 = 1
  count : s.nr 27 ≤ i
  countExact : s.nr 27 = matchingGrowthMembers initial i
  registers : ∀ r ∈ [14, 26, 54, 57, 58, 65], s.nr r = initial.nr r
  natural : ∀ a < initial.nr 58, s.nm a = initial.nm a

/-- The filtered scan pays a linear overhead, then a linear cost for each selected
source. The measured count in register 27 is exactly the number of originals in the
new outer block. Memory preceding the cache tables stays intact. -/
theorem refreshMatchingNewOuterBlock_bound (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) (one : s.nr 9 = 1) (zero : s.nr 14 = 0)
    (dict : s.nr 58 ≤ s.nr 54) (bucket : s.nr 58 ≤ s.nr 65)
    (repBefore : s.nr 57 + s.nr 55 ≤ s.nr 58) :
    ∃ t steps, BlockRuns refreshMatchingNewOuterBlock steps s t ∧ t.halted = false ∧
      t.nr 27 = matchingGrowthMembers s (s.nr 55) ∧ steps ≤ 11 * s.nr 55 + (s.nr 55 * 98 + 2) * t.nr 27 + 3 ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧ (∀ r ∈ [14, 26, 54, 57, 58, 65], t.nr r = s.nr r) := by
  let k := s.nr 55
  let seeded := {s with pc := 2, nr := Function.update (Function.update s.nr 24 0) 27 0}
  have seeds : BlockRuns initGrowthCacheScan 2 s seeded := by
    apply BlockRuns.of_running_exit
    · simp [seeded, arithmeticStep, initGrowthCacheScan, Function.iterate_succ_apply', entry, running]
    · exact running
    · rfl
  let start := {seeded with pc := 0}
  let charge := k * 98 + 2
  let potential := fun t : ArithmeticState => charge * (k - t.nr 27)
  have ready : GrowthCacheScan s 0 start := by
    refine ⟨rfl, running, by simp [start, seeded], by simp [start, seeded], by simpa [start, seeded] using one,
      by simp [start, seeded], by simp [start, seeded, matchingGrowthMembers], ?_, fun _ _ => rfl⟩
    intro r hr
    have a : r ≠ 24 := by simp at hr; omega
    have b : r ≠ 27 := by simp at hr; omega
    simp [start, seeded, Function.update_of_ne a, Function.update_of_ne b]
  have control (i : ℕ) (m : ArithmeticState) (valid : GrowthCacheScan s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 24 = i ∧ m.nr 55 = k :=
    ⟨valid.entry, valid.live, valid.index, valid.dimension⟩
  have iteration (i : ℕ) (less : i < k) (m : ArithmeticState) (valid : GrowthCacheScan s i m) :
      ∃ t steps,
      let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
      BlockRuns refreshGrowthCacheSourceBlock steps m t ∧ t.halted = false ∧
        GrowthCacheScan s (i + 1) next ∧ steps + potential next ≤ 8 + potential m := by
    have floor : m.nr 58 = s.nr 58 := valid.registers 58 (by decide)
    have mDict : m.nr 58 ≤ m.nr 54 := by simpa [floor, valid.registers 54 (by decide)] using dict
    have mBucket : m.nr 58 ≤ m.nr 65 := by simpa [floor, valid.registers 65 (by decide)] using bucket
    obtain ⟨t, steps, selected, ran, live, tOne, index, dimension, visits, short, picked, prior⟩ :=
      refreshGrowthCacheSourceBlock_spec m valid.entry valid.live valid.one mDict mBucket
    let next := {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)}
    have nextCount : next.nr 27 = m.nr 27 + selected.toNat := by simpa [next] using visits
    have selBound : selected.toNat ≤ 1 := by cases selected <;> decide
    have newCount : next.nr 27 ≤ i + 1 := by have old := valid.count; omega
    have balance : (k - next.nr 27) + selected.toNat = k - m.nr 27 := by omega
    have short' : steps ≤ 8 + charge * selected.toNat := by simpa [charge, valid.dimension] using short
    have read : m.nm (s.nr 57 + i) = s.nm (s.nr 57 + i) := valid.natural _ (by dsimp [k] at less; omega)
    have zeroAt : m.nr 14 = 0 := (valid.registers 14 (by decide)).trans zero
    have selection : selected = decide (s.nm (s.nr 57 + i) = s.nr 26) := by
      simpa only [valid.registers 57 (by decide), valid.registers 26 (by decide), valid.index, zeroAt, Nat.add_zero, read]
        using picked
    have exactCount : next.nr 27 = matchingGrowthMembers s (i + 1) := by
      rw [nextCount, matchingGrowthMembers_succ, selection, valid.countExact]
    refine ⟨t, steps, ran, live, ?_, ?_⟩
    · change GrowthCacheScan s (i + 1) next
      exact ⟨rfl, live, by simp [next, index, valid.index, tOne, valid.one],
        by simp [next, dimension, valid.dimension], by simp [next, tOne, valid.one], newCount, exactCount,
        fun r hr => by
          have away : r ≠ 24 := by simp at hr; omega
          simpa [next, Function.update_of_ne away] using (growthCacheSourceBlock_keeps ran hr).trans (valid.registers r hr),
        fun a ha => (prior a (floor.symm ▸ ha)).trans (valid.natural a ha)⟩
    · change steps + charge * (k - next.nr 27) ≤ 8 + charge * (k - m.nr 27)
      rw [← balance, Nat.mul_add]
      omega
  obtain ⟨last, steps, done, cost, complete⟩ := countedLoop_amortized 9 24 55 k 8
    refreshGrowthCacheSourceBlock (GrowthCacheScan s) potential ready control iteration
  have used := done.count
  have credits : charge * (k - last.nr 27) + charge * last.nr 27 = charge * k := by
    rw [← Nat.mul_add, Nat.sub_add_cancel used]
  have seededCount : start.nr 27 = 0 := by simp [start, seeded]
  change steps + charge * (k - last.nr 27) ≤ k * (8 + 3) + charge * (k - start.nr 27) + 1 at cost
  simp only [seededCount, Nat.sub_zero] at cost
  refine ⟨_, 2 + steps, seeds.append complete, done.live, done.countExact, ?_, done.natural, done.registers⟩
  change 2 + steps ≤ 11 * k + charge * last.nr 27 + 3
  rw [Nat.mul_comm 11 k]
  omega

end VehicleRoutingSurvey.Routing
end RppSource_MatchingGrowCacheRAM

/-! matching/AlternatingForestGrowRAM.lean -/
section RppSource_AlternatingForestGrowRAM
namespace VehicleRoutingSurvey.Routing

/-- Registers 0, 1, and 2 hold the predecessor, inner vertex, and outer vertex. Registers
3, 4, and 5 hold the role, parent, and depth table bases. Outer is stored as 1 and inner as 2. -/
def alternatingForestGrowBlock : List ArithmeticInstruction :=
  [.natAdd 6 5 0, .natLoad 8 6,
    .natAdd 6 3 1, .natConst 7 2, .natStore 6 7,
    .natAdd 6 3 2, .natConst 7 1, .natStore 6 7,
    .natAdd 6 4 1, .natStore 6 0,
    .natAdd 6 4 2, .natStore 6 1,
    .natAdd 8 8 7, .natAdd 6 5 1, .natStore 6 8,
    .natAdd 8 8 7, .natAdd 6 5 2, .natStore 6 8]

def alternatingForestGrownMemory (s : ArithmeticState) : ℕ → ℕ :=
  let withInnerRole := Function.update s.nm (s.nr 3 + s.nr 1) 2
  let withOuterRole := Function.update withInnerRole (s.nr 3 + s.nr 2) 1
  let withInnerParent := Function.update withOuterRole (s.nr 4 + s.nr 1) (s.nr 0)
  let withOuterParent := Function.update withInnerParent (s.nr 4 + s.nr 2) (s.nr 1)
  let predecessorDepth := s.nm (s.nr 5 + s.nr 0)
  let withInnerDepth := Function.update withOuterParent (s.nr 5 + s.nr 1) (predecessorDepth + 1)
  Function.update withInnerDepth (s.nr 5 + s.nr 2) (predecessorDepth + 2)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem alternatingForestGrowBlock_spec (s : ArithmeticState) (entry : s.pc = 0)
    (running : s.halted = false) :
    let result := (arithmeticStep alternatingForestGrowBlock)^[18] s
    BlockRuns alternatingForestGrowBlock 18 s result ∧
      result.nm = alternatingForestGrownMemory s ∧ result.rm = s.rm ∧ result.rr = s.rr ∧
      ∀ reg < 6, result.nr reg = s.nr reg := by
  let result := (arithmeticStep alternatingForestGrowBlock)^[18] s
  have computed : result.pc = alternatingForestGrowBlock.length ∧ result.halted = false ∧
      result.nm = alternatingForestGrownMemory s ∧ result.rm = s.rm ∧ result.rr = s.rr := by
    simp [result, alternatingForestGrowBlock, arithmeticStep, Function.iterate_succ_apply',
      alternatingForestGrownMemory, entry, running, Nat.add_assoc]
  refine ⟨BlockRuns.of_running_exit rfl computed.2.1 computed.1,
    computed.2.2.1, computed.2.2.2.1, computed.2.2.2.2, ?_⟩
  intro reg argument
  have notAddress : reg ≠ 6 := by omega
  have notValue : reg ≠ 7 := by omega
  have notDepth : reg ≠ 8 := by omega
  simp [result, alternatingForestGrowBlock, arithmeticStep, Function.iterate_succ_apply',
    entry, running, notAddress, notValue, notDepth]

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrowRAM

/-! matching/AlternatingForestMemory.lean -/
section RppSource_AlternatingForestMemory
namespace VehicleRoutingSurvey.Routing

def alternatingRoleCode {n : ℕ} : AlternatingForestRole (Fin n) → ℕ
  | .unlabelled => 0
  | .outer _ => 1
  | .inner _ => 2

def alternatingParentCode {n : ℕ} : AlternatingForestRole (Fin n) → ℕ
  | .unlabelled => n
  | .outer none => n
  | .outer (some p) => p.val
  | .inner p => p.val

/-- A forest is stored in three consecutive tables. The vertex count is the empty parent code. -/
def AlternatingForestMemory {n : ℕ} (forest : AlternatingForestState (Fin n)) (base : ℕ)
    (memory : ℕ → ℕ) : Prop :=
  ∀ v : Fin n,
    memory (base + v.val) = alternatingRoleCode (forest.role v) ∧
    memory (base + n + v.val) = alternatingParentCode (forest.role v) ∧
    memory (base + n + n + v.val) = forest.depth v

theorem alternatingForestGrownMemory_encodes {n : ℕ}
    {forest : AlternatingForestState (Fin n)} {base : ℕ} {s : ArithmeticState}
    (before : AlternatingForestMemory forest base s.nm) {source inner outer : Fin n}
    (sourceArg : s.nr 0 = source.val) (innerArg : s.nr 1 = inner.val) (outerArg : s.nr 2 = outer.val)
    (roleBase : s.nr 3 = base) (parentBase : s.nr 4 = base + n) (depthBase : s.nr 5 = base + n + n)
    (distinct : inner ≠ outer) :
    AlternatingForestMemory (forest.grow source inner outer) base (alternatingForestGrownMemory s) := by
  intro v
  have sourceDepth := (before source).2.2
  have oldRole := (before v).1
  have oldParent := (before v).2.1
  have oldDepth := (before v).2.2
  have innerLt := inner.isLt
  have outerLt := outer.isLt
  have vLt := v.isLt
  have different : inner.val ≠ outer.val := fun equal => distinct (Fin.ext equal)
  by_cases isInner : v = inner
  · subst v
    simp (disch := omega) [alternatingForestGrownMemory, sourceArg, innerArg, outerArg,
      roleBase, parentBase, depthBase, Function.update_apply, AlternatingForestState.grow,
      alternatingRoleCode, alternatingParentCode, sourceDepth]
  by_cases isOuter : v = outer
  · subst v
    simp (disch := omega) [alternatingForestGrownMemory, sourceArg, innerArg, outerArg,
      roleBase, parentBase, depthBase, Function.update_apply, AlternatingForestState.grow,
      alternatingRoleCode, alternatingParentCode, sourceDepth, distinct.symm]
  have notInner : v.val ≠ inner.val := fun equal => isInner (Fin.ext equal)
  have notOuter : v.val ≠ outer.val := fun equal => isOuter (Fin.ext equal)
  simp (disch := omega) [alternatingForestGrownMemory, sourceArg, innerArg, outerArg,
    roleBase, parentBase, depthBase, Function.update_apply, AlternatingForestState.grow,
    isInner, isOuter, oldRole, oldParent, oldDepth]

/-- Executing the growth block produces an encoding of the next valid alternating forest. -/
theorem alternatingForestGrowBlock_valid {n : ℕ} {forest : AlternatingForestState (Fin n)}
    {base : ℕ} {s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (before : AlternatingForestMemory forest base s.nm)
    {mate : Fin n → Option (Fin n)} {tight : Fin n → Fin n → Prop} (valid : forest.valid mate tight)
    {source inner outer : Fin n} {parent : Option (Fin n)}
    (sourceArg : s.nr 0 = source.val) (innerArg : s.nr 1 = inner.val) (outerArg : s.nr 2 = outer.val)
    (roleBase : s.nr 3 = base) (parentBase : s.nr 4 = base + n) (depthBase : s.nr 5 = base + n + n)
    (sourceRole : forest.role source = .outer parent)
    (innerRole : forest.role inner = .unlabelled) (outerRole : forest.role outer = .unlabelled)
    (distinct : inner ≠ outer) (mateInner : mate inner = some outer) (mateOuter : mate outer = some inner)
    (tightIncoming : tight source inner) (tightMatched : tight inner outer) :
    let next := forest.grow source inner outer
    let result := (arithmeticStep alternatingForestGrowBlock)^[18] s
    BlockRuns alternatingForestGrowBlock 18 s result ∧
      AlternatingForestMemory next base result.nm ∧ next.valid mate tight := by
  obtain ⟨block, memory, _, _, _⟩ := alternatingForestGrowBlock_spec s entry running
  exact ⟨block, memory.symm ▸ alternatingForestGrownMemory_encodes before sourceArg innerArg outerArg
      roleBase parentBase depthBase distinct,
    AlternatingForestState.grow_valid valid sourceRole innerRole outerRole distinct mateInner mateOuter
      tightIncoming tightMatched⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestMemory

/-! matching/AlternatingStageRoots.lean -/
section RppSource_AlternatingStageRoots
namespace VehicleRoutingSurvey.Routing

/-- All exposed active nodes are roots. Active mates are distinct, reciprocal and tight. -/
structure AlternatingStageRoots {α : Type*} (state : AlternatingForestState α)
    (active : Finset α) (mate : α → Option α) (tight : α → α → Prop) : Prop where
  forest : state.valid mate tight
  exposedRoots : ∀ v ∈ active, mate v = none → state.role v = .outer none
  partners : ∀ v ∈ active, ∀ w, mate v = some w → w ∈ active ∧ v ≠ w ∧ mate w = some v ∧ tight v w

/-- Start the next augmenting search with exactly the exposed active nodes as roots. -/
def resetAlternatingForest {α : Type*} [DecidableEq α] (active : Finset α) (mate : α → Option α) :
    AlternatingForestState α where
  role v := if v ∈ active ∧ mate v = none then .outer none else .unlabelled
  depth _ := 0

theorem resetAlternatingForest_valid {α : Type*} [DecidableEq α]
    (active : Finset α) (mate : α → Option α) (tight : α → α → Prop)
    (partners : ∀ v ∈ active, ∀ w, mate v = some w → w ∈ active ∧ v ≠ w ∧ mate w = some v ∧ tight v w) :
    AlternatingStageRoots (resetAlternatingForest active mate) active mate tight where
  forest := by
    intro v
    by_cases root : v ∈ active ∧ mate v = none
    · simp [resetAlternatingForest, root]
    · simp [resetAlternatingForest, root]
  exposedRoots v hv free := by simp [resetAlternatingForest, hv, free]
  partners := partners

/-- If the edge target is matched, grow to its mate. -/
def AlternatingForestState.growMatchedTarget {α : Type*} [DecidableEq α]
    (state : AlternatingForestState α) (mate : α → Option α) (source target : α) : Option (AlternatingForestState α) :=
  (mate target).map (state.grow source target)

/-- An active unlabelled target reached from an outer node always has an unlabelled mate,
so the growth transition can be taken. -/
theorem AlternatingForestState.growMatchedTarget_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {active : Finset α} {mate : α → Option α} {tight : α → α → Prop}
    (stage : AlternatingStageRoots state active mate tight) {source target : α} {parent : Option α}
    (sourceOuter : state.role source = .outer parent) (targetIn : target ∈ active)
    (targetDormant : state.role target = .unlabelled) (incoming : tight source target) :
    ∃ next, state.growMatchedTarget mate source target = some next ∧ AlternatingStageRoots next active mate tight := by
  cases found : mate target with
  | none =>
    have wrong := targetDormant.symm.trans (stage.exposedRoots target targetIn found)
    cases wrong
  | some peer =>
    obtain ⟨peerIn, distinct, reciprocal, matched⟩ := stage.partners target targetIn peer found
    have dormant : state.role peer = .unlabelled := by
      have old := stage.forest peer
      cases kind : state.role peer with
      | unlabelled => rfl
      | outer previous =>
        try rw [kind] at old
        cases previous with
        | none =>
          have impossible : some target = none := reciprocal.symm.trans old
          cases impossible
        | some p =>
          have equal : p = target := Option.some.inj (old.2.1.symm.trans reciprocal)
          obtain ⟨q, inner⟩ := old.1
          have wrong := targetDormant.symm.trans (equal ▸ inner)
          cases wrong
      | inner p =>
        try rw [kind] at old
        obtain ⟨child, childMate, childOuter⟩ := old.2.2.1
        have equal : child = target := Option.some.inj (childMate.symm.trans reciprocal)
        have wrong := targetDormant.symm.trans (equal ▸ childOuter)
        cases wrong
    let next := state.grow source target peer
    refine ⟨next, by simp [growMatchedTarget, found, next],
      grow_valid stage.forest sourceOuter targetDormant dormant distinct found reciprocal incoming matched,
      ?_, stage.partners⟩
    intro v hv free
    have notTarget : v ≠ target := by
      intro equal
      have impossible : some peer = none := found.symm.trans (equal ▸ free)
      cases impossible
    have notPeer : v ≠ peer := by
      intro equal
      have impossible : some target = none := reciprocal.symm.trans (equal ▸ free)
      cases impossible
    simpa [next, grow, notTarget, notPeer] using stage.exposedRoots v hv free

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingStageRoots

/-! matching/MatchingForestReset.lean -/
section RppSource_MatchingForestReset
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Reset one vertex's forest entry. The top-level representatives are exactly the vertices
that represent themselves. An exposed representative has the compact dimension as its mate. -/
private def resetMatchingForestCell : List ArithmeticInstruction :=
  [.natAdd 12 57 71, .natLoad 13 12, .natAdd 12 50 71, .natLoad 14 12,
   .natConst 15 0, .natBranch 13 71 6 9, .natBranch 71 13 7 9, .natBranch 55 14 8 9,
   .natConst 15 1, .natAdd 12 51 71, .natStore 12 15, .natAdd 12 52 71, .natStore 12 55,
   .natAdd 12 53 71, .natConst 17 0, .natStore 12 17]

def resetMatchingForestBlock : List ArithmeticInstruction :=
  countedLoopFromZero 34 71 55 resetMatchingForestCell

private def forestResetRoleCode (s : ArithmeticState) : ℕ :=
  let v := s.nr 71
  if s.nm (s.nr 57 + v) = v ∧ s.nr 55 ≤ s.nm (s.nr 50 + v) then 1 else 0

private def matchingForestResetMemory (s : ArithmeticState) : ℕ → ℕ :=
  let v := s.nr 71
  Function.update (Function.update (Function.update s.nm (s.nr 51 + v) (forestResetRoleCode s))
    (s.nr 52 + v) (s.nr 55)) (s.nr 53 + v) 0

private theorem resetMatchingForestCell_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t steps, steps ≤ 16 ∧ BlockRuns resetMatchingForestCell steps s t ∧ t.halted = false ∧
      t.nm = matchingForestResetMemory s ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0, 12, 13, 14, 15, 17] → t.nr r = s.nr r := by
  let v := s.nr 71
  let rep := s.nm (s.nr 57 + v)
  let mate := s.nm (s.nr 50 + v)
  have build (steps : ℕ) (bound : steps ≤ 16)
      (ready : ((arithmeticStep resetMatchingForestCell)^[steps] s).halted = false)
      (exit : ((arithmeticStep resetMatchingForestCell)^[steps] s).pc = resetMatchingForestCell.length)
      (natural : ((arithmeticStep resetMatchingForestCell)^[steps] s).nm = matchingForestResetMemory s)
      (real : ((arithmeticStep resetMatchingForestCell)^[steps] s).rm = s.rm) :
      ∃ t ticks, ticks ≤ 16 ∧ BlockRuns resetMatchingForestCell ticks s t ∧ t.halted = false ∧
        t.nm = matchingForestResetMemory s ∧ t.rm = s.rm ∧
        ∀ r, r ∉ [0, 12, 13, 14, 15, 17] → t.nr r = s.nr r := by
    refine ⟨_, steps, bound, BlockRuns.of_running_exit rfl ready exit, ready, natural, real, ?_⟩
    intro r safe
    apply arithmeticRun_keeps_register _ s steps
    simp [resetMatchingForestCell, naturalDestination] at safe ⊢
    omega
  rcases lt_trichotomy rep v with below | equal | above
  · apply build 14 (by decide)
    all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
      matchingForestResetMemory, forestResetRoleCode, v, rep, below.le, (not_le.mpr below), below.ne]
  · by_cases free : s.nr 55 ≤ mate
    · apply build 16 le_rfl
      all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
        matchingForestResetMemory, forestResetRoleCode, v, rep, mate, equal, free]
    · apply build 15 (by decide)
      all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
        matchingForestResetMemory, forestResetRoleCode, v, rep, mate, equal, free]
  · apply build 13 (by decide)
    all_goals simp [resetMatchingForestCell, arithmeticStep, entry, running, Function.iterate_succ_apply',
      matchingForestResetMemory, forestResetRoleCode, v, rep, (not_le.mpr above), above.ne']

private structure MatchingForestResetProgress {k : ℕ} (active : Finset (Fin k))
    (mate : Fin k → Option (Fin k)) (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 71 = i
  regs : ∀ r, r ∉ [0, 12, 13, 14, 15, 17, 71] → s.nr r = original.nr r
  roles : ∀ v : Fin k, v.val < i → s.nm (original.nr 51 + v.val) =
    if v ∈ active ∧ mate v = none then 1 else 0
  parents : ∀ j < i, s.nm (original.nr 51 + k + j) = k
  depths : ∀ j < i, s.nm (original.nr 51 + k + k + j) = 0
  natural : ∀ a, a < original.nr 51 ∨ original.nr 51 + 3 * k ≤ a → s.nm a = original.nm a
  real : s.rm = original.rm

set_option maxHeartbeats 650000 in
/-- Erase the old forest and give each unmatched top-level representative its own root.
The matching, representatives, metric, and routing memory remain available. -/
theorem resetMatchingForestBlock_correct {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) (dimension : s.nr 55 = k)
    (parentBase : s.nr 52 = s.nr 51 + k) (depthBase : s.nr 53 = s.nr 51 + k + k)
    (mateBefore : s.nr 50 + k ≤ s.nr 51) (repAfter : s.nr 51 + 3 * k ≤ s.nr 57)
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {representative : Fin k → Fin k}
    (activeAt : ∀ v, v ∈ active ↔ representative v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).elim k Fin.val)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representative v).val) :
    ∃ t steps, steps ≤ 19 * k + 2 ∧ BlockRuns resetMatchingForestBlock steps s t ∧ t.halted = false ∧
      AlternatingForestMemory (resetAlternatingForest active mate) (s.nr 51) t.nm ∧
      (∀ r, r ∉ [0, 12, 13, 14, 15, 17, 71] → t.nr r = s.nr r) ∧
      (∀ a, a < s.nr 51 ∨ s.nr 51 + 3 * k ≤ a → t.nm a = s.nm a) ∧ t.rm = s.rm := by
  let inv := MatchingForestResetProgress active mate s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 71 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp, by simp, by simp, fun _ _ => rfl, rfl⟩
    intro r safe
    have different : r ≠ 71 := fun equal => safe (by simp [equal])
    simp [different]
  have iterate (i : ℕ) (hi : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 16 ∧ BlockRuns resetMatchingForestCell steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 71 (t.nr 71 + t.nr 34)} := by
    have fixed (r : ℕ) (safe : r ∉ [0, 12, 13, 14, 15, 17, 71] := by decide) := hm.regs r safe
    let v : Fin k := ⟨i, hi⟩
    have atMate : m.nm (m.nr 50 + i) = (mate v).elim k Fin.val := by
      rw [fixed 50, hm.natural _ (Or.inl (by omega))]
      exact mates v
    have atRep : m.nm (m.nr 57 + i) = (representative v).val := by
      rw [fixed 57, hm.natural _ (Or.inr (by omega))]
      exact reps v
    have root : (representative v).val = i ↔ v ∈ active :=
      ⟨fun equal => (activeAt v).mpr (Fin.ext equal), fun h => congrArg Fin.val ((activeAt v).mp h)⟩
    have role : forestResetRoleCode m = if v ∈ active ∧ mate v = none then 1 else 0 := by
      cases hmMate : mate v with
      | none => simp [forestResetRoleCode, hm.index, atRep, atMate, root, hmMate, fixed 55, dimension]
      | some peer => simp [forestResetRoleCode, hm.index, atRep, atMate, root, hmMate, fixed 55, dimension,
          Nat.not_le.mpr peer.isLt]
    obtain ⟨t, steps, budget, run, live, memory, real, regs⟩ := resetMatchingForestCell_correct hm.entry hm.running
    have naturalMemory : t.nm = Function.update
        (Function.update (Function.update m.nm (s.nr 51 + i) (if v ∈ active ∧ mate v = none then 1 else 0))
          (s.nr 51 + k + i) k) (s.nr 51 + k + k + i) 0 := by
      simpa [matchingForestResetMemory, role, hm.index, fixed 51, fixed 52, fixed 53, fixed 55,
        parentBase, depthBase, dimension] using memory
    refine ⟨t, steps, budget, run, live, ?_⟩
    constructor
    · rfl
    · exact live
    · simp [regs 71 (by decide), regs 34 (by decide), hm.index, fixed 34, one]
    · intro r safe
      have different : r ≠ 71 := fun equal => safe (by simp [equal])
      have untouched : r ∉ [0, 12, 13, 14, 15, 17] := fun h => safe (List.mem_append_left [71] h)
      simpa [different] using (regs r untouched).trans (fixed r safe)
    · intro w hw
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with earlier | current
      · simp (disch := omega) [naturalMemory, Function.update_apply, hm.roles w earlier]
      · have wEq : w = v := Fin.ext current
        subst w
        simp (disch := omega) [naturalMemory, Function.update_apply, v]
    · intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with earlier | rfl
      · simp (disch := omega) [naturalMemory, Function.update_apply, hm.parents j earlier]
      · simp (disch := omega) [naturalMemory, Function.update_apply]
    · intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with earlier | rfl
      · simp (disch := omega) [naturalMemory, Function.update_apply, hm.depths j earlier]
      · simp [naturalMemory]
    · intro a outside
      simp (disch := omega) [naturalMemory, Function.update_apply, hm.natural a outside]
    · exact real.trans hm.real
  obtain ⟨last, steps, done, cost, run⟩ := countedLoopFromZero_bounded 34 71 55 k 16
    resetMatchingForestCell inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, (h.regs 55 (by decide)).trans dimension⟩) iterate
  refine ⟨_, steps, by omega, run, done.running, ?_, done.regs, done.natural, done.real⟩
  intro v
  have role := done.roles v v.isLt
  have parent := done.parents v.val v.isLt
  have depth := done.depths v.val v.isLt
  change last.nm (s.nr 51 + v.val) = _ ∧ last.nm (s.nr 51 + k + v.val) = _ ∧ _
  by_cases root : v ∈ active ∧ mate v = none <;>
    simp [resetAlternatingForest, root, role, parent, depth, relocateState] <;> exact ⟨rfl, rfl⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingForestReset

/-! matching/MatchingClearCandidates.lean -/
section RppSource_MatchingClearCandidates
namespace VehicleRoutingSurvey.Routing

private def clearMatchingCandidateCell : List ArithmeticInstruction :=
  [.natConst 0 0, .natAdd 2 58 71, .natStore 2 0]

/-- Mark every candidate slot inactive. Its other cells are read only once a new identifier
has been installed. -/
def clearMatchingCandidatesBlock : List ArithmeticInstruction :=
  countedLoopFromZero 34 71 61 clearMatchingCandidateCell

private structure MatchingClearCandidatesInvariant (original : ArithmeticState) (i : ℕ)
    (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 71 = i
  regs : ∀ r, r ≠ 0 → r ≠ 2 → r ≠ 71 → s.nr r = original.nr r
  real : s.rm = original.rm
  slots : ∀ a, s.nm a = if original.nr 58 ≤ a ∧ a < original.nr 58 + i then 0 else original.nm a

theorem clearMatchingCandidatesBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) :
    ∃ t, BlockRuns clearMatchingCandidatesBlock (6 * s.nr 61 + 2) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 71 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ a, t.nm a = if s.nr 58 ≤ a ∧ a < s.nr 58 + s.nr 61 then 0 else s.nm a := by
  let inv := MatchingClearCandidatesInvariant s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 71 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, ?_⟩
    · intro r _ _ avoid
      simp [avoid]
    · intro a
      simp only [Nat.add_zero, if_neg (show ¬ (s.nr 58 ≤ a ∧ a < s.nr 58) by omega)]
  have iterate (i : ℕ) (_ : i < s.nr 61) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns clearMatchingCandidateCell 3 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 71 (t.nr 71 + t.nr 34)} := by
    let address := s.nr 58 + i
    let t := {m with
      pc := 3
      nr := Function.update (Function.update m.nr 0 0) 2 address
      nm := Function.update m.nm address 0}
    have table := hm.regs 58 (by decide) (by decide) (by decide)
    have increment := (hm.regs 34 (by decide) (by decide) (by decide)).trans one
    have run : BlockRuns clearMatchingCandidateCell 3 m t := by
      refine BlockRuns.of_running_exit ?_ (show t.halted = false from hm.running) rfl
      simp [t, address, clearMatchingCandidateCell, arithmeticStep, hm.entry, hm.running,
        hm.index, table, Function.iterate_succ_apply']
    refine ⟨t, run, hm.running, rfl, hm.running, by simp [t, hm.index, increment], ?_, hm.real, ?_⟩
    · intro r notAddr notZero notIndex
      simp [t, notAddr, notZero, notIndex, hm.regs r notAddr notZero notIndex]
    · intro a
      change Function.update m.nm address 0 a =
        if s.nr 58 ≤ a ∧ a < s.nr 58 + (i + 1) then 0 else s.nm a
      by_cases changed : a = address
      · rw [changed, Function.update_self, if_pos (by dsimp [address]; omega)]
      · rw [Function.update_of_ne changed, hm.slots]
        have same : (s.nr 58 ≤ a ∧ a < s.nr 58 + i) ↔
            (s.nr 58 ≤ a ∧ a < s.nr 58 + (i + 1)) := by dsimp [address] at changed; omega
        simp only [same]
  obtain ⟨last, done, run⟩ := countedLoopFromZero_correct 34 71 61 (s.nr 61) 3
    clearMatchingCandidateCell inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.regs 61 (by decide) (by decide) (by decide)⟩) iterate
  have steps : 6 * s.nr 61 + 2 = 1 + (s.nr 61 * (3 + 3) + 1) := by omega
  let final := relocateState 1 {last with pc := (countedLoop 34 71 61 clearMatchingCandidateCell).length}
  refine ⟨final, ?_, done.running, done.regs, done.real, done.slots⟩
  simpa only [clearMatchingCandidatesBlock, steps] using run


end VehicleRoutingSurvey.Routing
end RppSource_MatchingClearCandidates

/-! matching/MatchingPairClear.lean -/
section RppSource_MatchingPairClear
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

private def measureMatchingMatrixBlock : List ArithmeticInstruction :=
  [.natConst 71 0, .natBranch 55 71 7 2, .natSub 73 55 34, .natAdd 73 21 73,
   .natLoad 73 73, .natAdd 73 73 55, .jump 8, .natConst 73 0]

private theorem measureMatchingMatrixBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1)
    (offsets : ∀ u < s.nr 55, s.nm (s.nr 21 + u) = s.nr 55 * u) :
    ∃ t steps, steps ≤ 7 ∧ BlockRuns measureMatchingMatrixBlock steps s t ∧ t.halted = false ∧
      t.nr 73 = s.nr 55 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r, r ∉ [0, 71, 73] → t.nr r = s.nr r := by
  have build (steps : ℕ) (bound : steps ≤ 7)
      (ready : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).halted = false)
      (exit : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).pc = measureMatchingMatrixBlock.length)
      (size : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).nr 73 = s.nr 55 * s.nr 55)
      (natural : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).nm = s.nm)
      (real : ((arithmeticStep measureMatchingMatrixBlock)^[steps] s).rm = s.rm) :
      ∃ t steps, steps ≤ 7 ∧ BlockRuns measureMatchingMatrixBlock steps s t ∧ t.halted = false ∧
        t.nr 73 = s.nr 55 * s.nr 55 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
        ∀ r, r ∉ [0, 71, 73] → t.nr r = s.nr r := by
    refine ⟨_, steps, bound, BlockRuns.of_running_exit rfl ready exit, ready, size, natural, real, ?_⟩
    intro r safe
    apply arithmeticRun_keeps_register _ s steps
    simp [measureMatchingMatrixBlock, naturalDestination] at safe ⊢
    omega
  by_cases empty : s.nr 55 = 0
  · apply build 3 (by decide)
    all_goals simp [measureMatchingMatrixBlock, arithmeticStep, entry, running, empty,
      Function.iterate_succ_apply']
  · have positive := Nat.pos_of_ne_zero empty
    have index : s.nr 55 - 1 < s.nr 55 := by omega
    have last := offsets _ index
    have square : s.nr 55 * (s.nr 55 - 1) + s.nr 55 = s.nr 55 * s.nr 55 := by
      rw [← Nat.mul_succ, show (s.nr 55 - 1).succ = s.nr 55 by omega]
    apply build 7 le_rfl
    all_goals simp [measureMatchingMatrixBlock, arithmeticStep, entry, running, one, last, square,
      not_le.mpr positive, Function.iterate_succ_apply']

private def clearMatchingPairSlot : List ArithmeticInstruction :=
  [.natAdd 71 72 72, .natAdd 71 65 71, .natStore 71 55]

private def clearMatchingPairSlots : List ArithmeticInstruction :=
  countedLoopFromZero 34 72 73 clearMatchingPairSlot

/-- Only the first endpoint word of a pair bucket needs resetting. Both endpoints and its
key are installed together when an edge occupies the bucket. -/
def clearMatchingPairCacheBlock : List ArithmeticInstruction :=
  appendBlock measureMatchingMatrixBlock clearMatchingPairSlots

abbrev matchingPairSentinelAddress (base cells address : ℕ) : Prop :=
  base ≤ address ∧ address < base + 2 * cells ∧ (address - base) % 2 = 0

private structure PairClearProgress (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 72 = i
  fixed : ∀ r, r ≠ 71 → r ≠ 72 → s.nr r = original.nr r
  real : s.rm = original.rm
  slots : ∀ a, s.nm a = if matchingPairSentinelAddress (original.nr 65) i a
    then original.nr 55 else original.nm a

private theorem clearMatchingPairSlots_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1) :
    ∃ t, BlockRuns clearMatchingPairSlots (6 * s.nr 73 + 2) s t ∧ t.halted = false ∧
      (∀ r, r ≠ 71 → r ≠ 72 → t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ a, t.nm a = if matchingPairSentinelAddress (s.nr 65) (s.nr 73) a then s.nr 55 else s.nm a := by
  let inv := PairClearProgress s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 72 0} := by
    refine ⟨rfl, running, by simp, ?_, rfl, ?_⟩
    · intro r _ avoid
      simp [avoid]
    · intro a
      rw [if_neg]
      unfold matchingPairSentinelAddress
      omega
  have iterate (i : ℕ) (_ : i < s.nr 73) (m : ArithmeticState) (hm : inv i m) :
      ∃ t, BlockRuns clearMatchingPairSlot 3 m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 72 (t.nr 72 + t.nr 34)} := by
    let address := s.nr 65 + 2 * i
    let t := {m with
      pc := 3
      nr := Function.update m.nr 71 address
      nm := Function.update m.nm address (s.nr 55)}
    have table := hm.fixed 65 (by decide) (by decide)
    have k := hm.fixed 55 (by decide) (by decide)
    have step := (hm.fixed 34 (by decide) (by decide)).trans one
    have executed : BlockRuns clearMatchingPairSlot 3 m t := by
      refine BlockRuns.of_running_exit ?_ (show t.halted = false from hm.running) rfl
      simp [t, address, clearMatchingPairSlot, arithmeticStep, hm.entry, hm.running, hm.index, table, k,
        Nat.two_mul, Function.iterate_succ_apply', Function.update_idem]
    refine ⟨t, executed, hm.running, rfl, hm.running, by simp [t, hm.index, step], ?_, hm.real, ?_⟩
    · intro r notAddr notIndex
      simp [t, notAddr, notIndex, hm.fixed r notAddr notIndex]
    · intro a
      change Function.update m.nm address (s.nr 55) a =
        if matchingPairSentinelAddress (s.nr 65) (i + 1) a then s.nr 55 else s.nm a
      by_cases target : a = address
      · rw [target, Function.update_self, if_pos]
        unfold matchingPairSentinelAddress
        dsimp [address]
        omega
      · have same : matchingPairSentinelAddress (s.nr 65) i a ↔
            matchingPairSentinelAddress (s.nr 65) (i + 1) a := by
          unfold matchingPairSentinelAddress
          dsimp [address] at target
          omega
        simp only [Function.update_of_ne target, hm.slots, same]
  obtain ⟨last, done, ran⟩ := countedLoopFromZero_correct 34 72 73 (s.nr 73) 3 clearMatchingPairSlot
    inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.fixed 73 (by decide) (by decide)⟩) iterate
  let t := relocateState 1 {last with pc := (countedLoop 34 72 73 clearMatchingPairSlot).length}
  have steps : 6 * s.nr 73 + 2 = 1 + (s.nr 73 * (3 + 3) + 1) := by omega
  exact ⟨t, steps.symm ▸ ran, done.running, done.fixed, done.real, done.slots⟩

/-- Invalidate all pair buckets before rebuilding the cache for a new search. The pass costs
at most six instructions per bucket plus a fixed setup and leaves the prior arrays intact. -/
theorem clearMatchingPairCacheBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 34 = 1)
    (offsets : ∀ u < s.nr 55, s.nm (s.nr 21 + u) = s.nr 55 * u) :
    ∃ t steps, steps ≤ 6 * (s.nr 55 * s.nr 55) + 9 ∧
      BlockRuns clearMatchingPairCacheBlock steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 71, 72, 73] → t.nr r = s.nr r) ∧ t.rm = s.rm ∧
      ∀ a, t.nm a = if matchingPairSentinelAddress (s.nr 65) (s.nr 55 * s.nr 55) a
        then s.nr 55 else s.nm a := by
  obtain ⟨a, front, budget, measured, live, size, natural, real, fixed⟩ :=
    measureMatchingMatrixBlock_correct entry running one offsets
  let ready := {a with pc := 0}
  obtain ⟨b, cleared, done, keeps, bReal, cells⟩ := clearMatchingPairSlots_correct (s := ready) rfl live
    ((fixed 34 (by decide)).trans one)
  refine ⟨_, front + (6 * ready.nr 73 + 2), ?_, measured.append cleared, done, ?_, bReal.trans real, ?_⟩
  · have size' : ready.nr 73 = s.nr 55 * s.nr 55 := size
    rw [size']
    omega
  · intro r safe
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at safe
    obtain ⟨h0, h71, h72, h73⟩ := safe
    exact (keeps r h71 h72).trans (fixed r (by simp [h0, h71, h73]))
  · intro address
    simpa only [relocateState, ready, size, fixed 65 (by decide), fixed 55 (by decide), natural] using cells address


end VehicleRoutingSurvey.Routing
end RppSource_MatchingPairClear

/-! matching/MatchingWarmSeed.lean -/
section RppSource_MatchingWarmSeed
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace VehicleRoutingSurvey.Routing

def readWarmCacheSource : List ArithmeticInstruction :=
  [.natAdd 15 24 14, .natAdd 6 57 15, .natLoad 26 6, .natAdd 6 51 26, .natLoad 19 6]

def refreshWarmCacheSource : List ArithmeticInstruction :=
  appendBlock readWarmCacheSource (branchOnAtMost 19 14 [] refreshSelectedOuterVertex)

def sweepWarmMatchingCache : List ArithmeticInstruction :=
  countedLoopFromZero 9 24 55 refreshWarmCacheSource

/-- Rebuild the reset cache from each original vertex whose top-level representative is
outer. The stage begins with no inner representatives. -/
def rebuildMatchingActiveCacheBlock : List ArithmeticInstruction :=
  appendBlock [.natConst 14 0] sweepWarmMatchingCache

/-- Reinitialize a search following an augmentation. The reset preserves the matched
edges and the remaining blossoms. -/
def warmMatchingPreparationPrefixBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock resetMatchingStageControlBlock resetMatchingForestBlock)
    clearMatchingCandidatesBlock) clearMatchingPairCacheBlock

def warmMatchingPreparationBlock : List ArithmeticInstruction :=
  appendBlock warmMatchingPreparationPrefixBlock rebuildMatchingActiveCacheBlock

theorem refreshWarmCacheSource_fixed {s t : ArithmeticState} {steps : ℕ}
    (run : BlockRuns refreshWarmCacheSource steps s t) (r : ℕ)
    (fixed : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26]) : t.nr r = s.nr r := by
  rw [← run.run]
  apply arithmeticRun_keeps_register _ s steps
  have away : r ∉ [0, 6, 10, 11, 16, 17, 18, 19, 25] := by
    simp at fixed ⊢
    omega
  apply (forall_naturalDestination_append (· ≠ r) _ _).2
  constructor
  · apply naturalDestination_ne_of_list [6, 15, 19, 26] (by decide)
    simp at fixed ⊢
    omega
  · apply (forall_naturalDestination_branch (· ≠ r) _ _ _ _).2
    exact ⟨fun equal => fixed (by simp [← equal]), by simp, refreshSelectedOuterVertex_no_write away⟩

private theorem refreshWarmCacheSource_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (dictAfter : s.nr 58 ≤ s.nr 54) (pairAfter : s.nr 58 ≤ s.nr 65)
    (rateAfter : s.nr 59 ≤ s.nr 60) (keyAfter : s.nr 59 ≤ s.nr 66) :
    ∃ t steps, steps ≤ 98 * s.nr 55 + 8 ∧ BlockRuns refreshWarmCacheSource steps s t ∧
      t.halted = false ∧ (∀ a < s.nr 58, t.nm a = s.nm a) ∧ ∀ a < s.nr 59, t.rm a = s.rm a := by
  let u := s.nr 24 + s.nr 14
  let rep := s.nm (s.nr 57 + u)
  let p := (arithmeticStep readWarmCacheSource)^[5] s
  have live : p.halted = false := by
    simp [p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : p.pc = readWarmCacheSource.length := by
    simp [p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have read : BlockRuns readWarmCacheSource 5 s p := BlockRuns.of_running_exit rfl live exit
  let ready := {p with pc := 0}
  have unchanged : ready.nm = s.nm := by
    simp [ready, p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have real : ready.rm = s.rm := by
    simp [ready, p, readWarmCacheSource, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have fixed (r : ℕ) (safe : r ∉ [0, 6, 15, 19, 26] := by decide) : ready.nr r = s.nr r := by
    change p.nr r = s.nr r
    apply arithmeticRun_keeps_register _ s 5
    simp [readWarmCacheSource, naturalDestination] at safe ⊢
    omega
  by_cases dormant : ready.nr 19 ≤ ready.nr 14
  · have empty : BlockRuns [] 0 ready ready :=
      ⟨fun i h => (Nat.not_lt_zero i h).elim, by simp, rfl⟩
    have finished := branchOnAtMost_left 19 14 [] refreshSelectedOuterVertex
      (s := ready) rfl live dormant empty live
    exact ⟨_, 5 + (1 + 0 + 1), by omega, read.append finished, live,
      fun addr _ => congrFun unchanged addr, fun addr _ => congrFun real addr⟩
  · obtain ⟨q, ticks, budget, scan, qLive, holds, keptReal⟩ := refreshSelectedOuterVertex_spec ready rfl live
      ((fixed 9).trans one) (by rw [fixed 58, fixed 54]; exact dictAfter)
      (by rw [fixed 58, fixed 65]; exact pairAfter)
    have finished := branchOnAtMost_right 19 14 [] refreshSelectedOuterVertex (s := ready) rfl live
      (lt_of_not_ge dormant) scan qLive
    rw [fixed 55] at budget
    have upper : ticks ≤ 98 * s.nr 55 + 2 := by simpa [Nat.mul_comm 98] using budget
    refine ⟨_, 5 + (1 + ticks), by omega, read.append finished, qLive, ?_, ?_⟩
    · intro addr before
      exact (holds addr ((fixed 58).symm ▸ before)).trans (congrFun unchanged addr)
    · intro addr before
      exact (keptReal addr ((fixed 59).symm ▸ before)
        (by rw [fixed 59, fixed 60]; exact rateAfter)
        (by rw [fixed 59, fixed 66]; exact keyAfter)).trans (congrFun real addr)

private structure WarmMatchingCacheProgress (original : ArithmeticState) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  running : s.halted = false
  index : s.nr 24 = i
  regs : ∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → s.nr r = original.nr r
  natural : ∀ addr < original.nr 58, s.nm addr = original.nm addr
  real : ∀ addr < original.nr 59, s.rm addr = original.rm addr

private theorem sweepWarmMatchingCache_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (dictAfter : s.nr 58 ≤ s.nr 54) (pairAfter : s.nr 58 ≤ s.nr 65)
    (rateAfter : s.nr 59 ≤ s.nr 60) (keyAfter : s.nr 59 ≤ s.nr 66) :
    ∃ t steps, steps ≤ s.nr 55 * (98 * s.nr 55 + 11) + 2 ∧
      BlockRuns sweepWarmMatchingCache steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] → t.nr r = s.nr r) ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧ ∀ a < s.nr 59, t.rm a = s.rm a := by
  let k := s.nr 55
  let inv := WarmMatchingCacheProgress s
  have initial : inv 0 {s with pc := 0, nr := Function.update s.nr 24 0} := by
    refine ⟨rfl, running, by simp, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    intro r safe
    have notIndex : r ≠ 24 := fun equal => safe (by simp [equal])
    simp [notIndex]
  have iterate (i : ℕ) (_ : i < k) (m : ArithmeticState) (hm : inv i m) :
      ∃ t steps, steps ≤ 98 * k + 8 ∧ BlockRuns refreshWarmCacheSource steps m t ∧ t.halted = false ∧
        inv (i + 1) {t with pc := 0, nr := Function.update t.nr 24 (t.nr 24 + t.nr 9)} := by
    have preserved (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) :=
      hm.regs r safe
    have oneAt : m.nr 9 = 1 := (preserved 9).trans one
    obtain ⟨t, steps, budget, run, live, natural, real⟩ := refreshWarmCacheSource_correct hm.entry hm.running oneAt
      (by rw [preserved 58, preserved 54]; exact dictAfter)
      (by rw [preserved 58, preserved 65]; exact pairAfter)
      (by rw [preserved 59, preserved 60]; exact rateAfter)
      (by rw [preserved 59, preserved 66]; exact keyAfter)
    have fixed := refreshWarmCacheSource_fixed run
    rw [preserved 55] at budget
    refine ⟨t, steps, budget, run, live, rfl, live, ?_, ?_, ?_, ?_⟩
    · simp [fixed 24 (by decide), hm.index, fixed 9 (by decide), oneAt]
    · intro r safe
      have notIndex : r ≠ 24 := fun equal => safe (by simp [equal])
      have before : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 25, 26] := by simp at safe ⊢; omega
      simpa [notIndex] using (fixed r before).trans (preserved r safe)
    · intro addr before
      exact (natural addr ((preserved 58).symm ▸ before)).trans (hm.natural addr before)
    · intro addr before
      exact (real addr ((preserved 59).symm ▸ before)).trans (hm.real addr before)
  obtain ⟨last, steps, checked, budget, ran⟩ := countedLoopFromZero_bounded 9 24 55 k (98 * k + 8)
    refreshWarmCacheSource inv entry running initial
    (fun _ _ h => ⟨h.entry, h.running, h.index, h.regs 55 (by decide)⟩) iterate
  refine ⟨_, steps, ?_, ran, checked.running, checked.regs, checked.natural, checked.real⟩
  change steps ≤ 1 + (k * (98 * k + 8 + 3) + 1) at budget
  change steps ≤ k * (98 * k + 11) + 2
  rw [show 98 * k + 8 + 3 = 98 * k + 11 by omega] at budget
  omega

theorem rebuildMatchingActiveCacheBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 9 = 1)
    (dictAfter : s.nr 58 ≤ s.nr 54) (pairAfter : s.nr 58 ≤ s.nr 65)
    (rateAfter : s.nr 59 ≤ s.nr 60) (keyAfter : s.nr 59 ≤ s.nr 66) :
    ∃ t steps, steps ≤ s.nr 55 * (98 * s.nr 55 + 11) + 3 ∧
      BlockRuns rebuildMatchingActiveCacheBlock steps s t ∧ t.halted = false ∧
      (∀ r, r ∉ [0, 6, 10, 11, 14, 15, 16, 17, 18, 19, 24, 25, 26] → t.nr r = s.nr r) ∧
      (∀ a < s.nr 58, t.nm a = s.nm a) ∧ ∀ a < s.nr 59, t.rm a = s.rm a := by
  let after := {s with pc := 0, nr := Function.update s.nr 14 0}
  obtain ⟨t, steps, bound, sweep, live, kept, natural, real⟩ := sweepWarmMatchingCache_correct (s := after) rfl running
    (by simpa [after] using one) (by simpa [after] using dictAfter) (by simpa [after] using pairAfter)
    (by simpa [after] using rateAfter) (by simpa [after] using keyAfter)
  refine ⟨_, 1 + steps, ?_, (zeroRegister_runs 14 s entry running).append sweep, live, ?_, ?_, ?_⟩
  · simp [after] at bound
    omega
  · intro r safe
    change t.nr r = s.nr r
    have notZero : r ≠ 14 := fun equal => safe (by simp [equal])
    have unaffected : r ∉ [0, 6, 10, 11, 15, 16, 17, 18, 19, 24, 25, 26] := by simp at safe ⊢; omega
    simpa [after, notZero] using kept r unaffected
  · change ∀ a < s.nr 58, t.nm a = s.nm a
    simpa [after] using natural
  · change ∀ a < s.nr 59, t.rm a = s.rm a
    simpa [after] using real


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmSeed

/-! matching/MatchingCacheRealFrame.lean -/
section RppSource_MatchingCacheRealFrame
namespace VehicleRoutingSurvey.Routing

def updatedRealRegister : ArithmeticInstruction → Option ℕ
  | .realConst dst _ | .realAdd dst _ _ | .realSub dst _ _ | .realMul dst _ _
    | .realDiv dst _ _ | .realLoad dst _ => some dst
  | _ => none

private theorem arithmeticStep_keeps_cache_real {code : List ArithmeticInstruction} {r : ℕ}
    (avoids : ∀ ins ∈ code, updatedRealRegister ins ≠ some r) (s : ArithmeticState) :
    (arithmeticStep code s).rr r = s.rr r := by
  by_cases stopped : s.halted = true
  · simp [arithmeticStep, stopped]
  cases fetched : code[s.pc]? with
  | none => simp [arithmeticStep, stopped, fetched]
  | some ins =>
    have other := avoids ins (List.mem_of_getElem? fetched)
    cases ins <;> simp [updatedRealRegister] at other <;>
      simp (disch := omega) [arithmeticStep, stopped, fetched, Function.update_of_ne]

theorem BlockRuns.keeps_cache_real {code : List ArithmeticInstruction} {s t : ArithmeticState} {steps r : ℕ}
    (run : BlockRuns code steps s t) (avoids : code.all (fun ins => decide (updatedRealRegister ins ≠ some r)) = true) :
    t.rr r = s.rr r := by
  have writes : ∀ ins ∈ code, updatedRealRegister ins ≠ some r := fun ins present =>
    of_decide_eq_true (List.all_eq_true.mp avoids ins present)
  rw [← run.run]
  clear run
  induction steps with
  | zero => rfl
  | succ steps ih => rw [Function.iterate_succ_apply', arithmeticStep_keeps_cache_real writes, ih]

end VehicleRoutingSurvey.Routing
end RppSource_MatchingCacheRealFrame

/-! matching/MatchingWarmPreparation.lean -/
section RppSource_MatchingWarmPreparation
namespace VehicleRoutingSurvey.Routing

/-- The persistent memory layout used when starting another augmenting search. -/
structure MatchingWarmLayout (s : ArithmeticState) (k : ℕ) : Prop where
  size : s.nr 55 = k
  candidates : s.nr 61 = 3 * k
  parents : s.nr 52 = s.nr 51 + k
  depths : s.nr 53 = s.nr 51 + k + k
  matesBefore : s.nr 50 + k ≤ s.nr 51
  representativesAfter : s.nr 51 + 3 * k ≤ s.nr 57
  candidatesAfter : s.nr 57 + k ≤ s.nr 58
  dictionaryAfter : s.nr 58 ≤ s.nr 54
  pairsAfter : s.nr 58 ≤ s.nr 65
  ratesAfter : s.nr 59 ≤ s.nr 60
  keysAfter : s.nr 59 ≤ s.nr 66
  offsetsBefore : s.nr 21 + k ≤ s.nr 50

/-- Exact forest and cleared cache at the start of the warm scan. -/
structure MatchingWarmCleared {k : ℕ} (s t : ArithmeticState) (active : Finset (Fin k))
    (mate : Fin k → Option (Fin k)) : Prop where
  controls : t.nr 31 = 6*k+1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
    t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.nr 8 = 3*k ∧ t.nr 3 = s.nr 58 ∧
    t.nr 4 = s.nr 59 ∧ t.nr 5 = s.nr 60
  fixed : ∀ r, r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] →
    t.nr r = s.nr r
  forest : AlternatingForestMemory (resetAlternatingForest active mate) (s.nr 51) t.nm
  zeroClock : t.rr 15 = 0
  real : t.rm = s.rm
  natural : ∀ a, (a < s.nr 51 ∨ s.nr 51 + 3*k ≤ a) →
    ¬ (s.nr 58 ≤ a ∧ a < s.nr 58 + s.nr 61) →
    ¬ matchingPairSentinelAddress (s.nr 65) (k*k) a → t.nm a = s.nm a
  emptyId : s.nr 58 + s.nr 61 ≤ s.nr 65 → ∀ i < s.nr 61, t.nm (s.nr 58 + i) = 0
  emptyPair : ∀ i < k*k, t.nm (s.nr 65 + (i+i)) = k

set_option maxHeartbeats 700000 in
/-- Run stage controls, reset forest labels, and invalidate all candidate rows and pair buckets. -/
theorem warmMatchingPreparationPrefixBlock_runs {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (layout : MatchingWarmLayout s k)
    (offsets : ∀ i < k, s.nm (s.nr 21 + i) = k * i)
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {representative : Fin k → Fin k}
    (activeAt : ∀ v, v ∈ active ↔ representative v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).elim k Fin.val)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representative v).val) :
    ∃ t steps, steps ≤ 6*(k*k) + 37*k + 28 ∧
      BlockRuns warmMatchingPreparationPrefixBlock steps s t ∧ t.halted = false ∧
      MatchingWarmCleared s t active mate := by
  obtain ⟨a, setup, aLive, aFrame⟩ := resetMatchingStageControlBlock_correct entry running
  let aInput := {a with pc := 0}
  have aReg (r : ℕ) (safe : r ∉ [0, 1, 3, 4, 5, 8, 9, 29, 31, 32, 33, 34] := by decide) :
      aInput.nr r = s.nr r := aFrame.fixed r safe
  obtain ⟨b, resetSteps, resetBudget, reset, bLive, forest, bFixed, bNat, bReal⟩ :=
    resetMatchingForestBlock_correct (s := aInput) rfl aLive aFrame.one ((aReg 55).trans layout.size)
      (by rw [aReg 52, aReg 51]; exact layout.parents)
      (by rw [aReg 53, aReg 51]; exact layout.depths)
      (by rw [aReg 50, aReg 51]; exact layout.matesBefore)
      (by rw [aReg 51, aReg 57]; exact layout.representativesAfter) activeAt
      (fun v => by change a.nm _ = _; rw [aReg 50, aFrame.natural]; exact mates v)
      (fun v => by change a.nm _ = _; rw [aReg 57, aFrame.natural]; exact reps v)
  let preForest := appendBlock resetMatchingStageControlBlock resetMatchingForestBlock
  let bInput := {relocateState resetMatchingStageControlBlock.length b with pc := 0}
  have bReg (r : ℕ) (safe : r ∉ [0, 12, 13, 14, 15, 17, 71] := by decide) : bInput.nr r = aInput.nr r :=
    bFixed r safe
  have keptMates (address : ℕ) (low : address < s.nr 50 + k) : bInput.nm address = s.nm address := by
    have earlier : address < aInput.nr 51 := by rw [aReg 51]; have := layout.matesBefore; omega
    exact (bNat address (Or.inl earlier)).trans (congrFun aFrame.natural address)
  obtain ⟨c, cleared, cLive, cFixed, cReal, cMemory⟩ := clearMatchingCandidatesBlock_correct
    (s := bInput) rfl bLive ((bReg 34).trans aFrame.one)
  let prePair := appendBlock preForest clearMatchingCandidatesBlock
  let cInput := {relocateState preForest.length c with pc := 0}
  have cReg (r : ℕ) (h0 : r ≠ 0 := by decide) (h2 : r ≠ 2 := by decide) (h71 : r ≠ 71 := by decide) :
      cInput.nr r = bInput.nr r := cFixed r h0 h2 h71
  have idsBase : bInput.nr 58 = s.nr 58 := (bReg 58).trans (aReg 58)
  have idsEnd : s.nr 51 + 3 * k ≤ s.nr 58 := layout.representativesAfter.trans
    (Nat.le_trans (Nat.le_add_right _ _) layout.candidatesAfter)
  have cNatural (address : ℕ) (earlier : address < s.nr 58) : cInput.nm address = bInput.nm address := by
    change c.nm address = _
    rw [cMemory, idsBase, if_neg (fun h => (not_le.mpr earlier) h.1)]
  have cSize : cInput.nr 55 = k := (cReg 55).trans ((bReg 55).trans ((aReg 55).trans layout.size))
  have cRows (i : ℕ) (hi : i < cInput.nr 55) : cInput.nm (cInput.nr 21 + i) = cInput.nr 55 * i := by
    rw [cSize] at hi
    rw [cReg 21, bReg 21, aReg 21, cSize, cNatural _ (by
      have := layout.offsetsBefore
      have := layout.matesBefore
      omega), keptMates _ (by have := layout.offsetsBefore; omega)]
    exact offsets i hi
  have cOne : cInput.nr 34 = 1 := (cReg 34).trans ((bReg 34).trans aFrame.one)
  obtain ⟨d, pairSteps, pairBudget, pair, dLive, dFixed, dReal, dMemory⟩ :=
    clearMatchingPairCacheBlock_correct (s := cInput) rfl cLive cOne cRows
  let dInput := {relocateState prePair.length d with pc := 0}
  have dReg (r : ℕ) (safe : r ∉ [0, 71, 72, 73] := by decide) : dInput.nr r = cInput.nr r := dFixed r safe
  have dNatural (address : ℕ) (earlier : address < s.nr 58) : dInput.nm address = cInput.nm address := by
    change d.nm address = _
    have pairBase : cInput.nr 65 = s.nr 65 := (cReg 65).trans ((bReg 65).trans (aReg 65))
    rw [dMemory, if_neg (fun h => (not_le.mpr (earlier.trans_le layout.pairsAfter)) (pairBase ▸ h.1))]
  have dOne : dInput.nr 9 = 1 := (dReg 9).trans ((cReg 9).trans ((bReg 9).trans aFrame.selectorOne))
  have dFromA (r : ℕ) (sd : r ∉ [0, 71, 72, 73] := by decide) (h0 : r ≠ 0 := by decide)
      (h2 : r ≠ 2 := by decide) (h71 : r ≠ 71 := by decide)
      (sb : r ∉ [0, 12, 13, 14, 15, 17, 71] := by decide) : dInput.nr r = aInput.nr r :=
    (dReg r sd).trans ((cReg r h0 h2 h71).trans (bReg r sb))
  have aPair := (cReg 65).trans ((bReg 65).trans (aReg 65))
  have pairs (addr : ℕ) : dInput.nm addr = if matchingPairSentinelAddress (s.nr 65) (k*k) addr
      then k else cInput.nm addr := by
    change d.nm addr = _
    rw [dMemory, aPair, cSize]
  have clearedIds (addr : ℕ) : cInput.nm addr =
      if s.nr 58 ≤ addr ∧ addr < s.nr 58 + s.nr 61 then 0 else bInput.nm addr := by
    change c.nm addr = _
    rw [cMemory, idsBase, bReg 61, aReg 61]
  have prefixRun : BlockRuns warmMatchingPreparationPrefixBlock
      (15 + resetSteps + (6*bInput.nr 61+2) + pairSteps) s (relocateState prePair.length d) :=
    ((setup.append reset).append cleared).append pair
  have rowCount : bInput.nr 61 = 3*k := (bReg 61).trans ((aReg 61).trans layout.candidates)
  rw [cSize] at pairBudget
  refine ⟨_, _, ?_, prefixRun, dLive, ?_⟩
  · rw [rowCount]
    omega
  · constructor
    · exact ⟨(dFromA 31).trans (layout.size ▸ aFrame.limit), (dFromA 32).trans aFrame.tick,
        (dFromA 33).trans aFrame.active, (dFromA 34).trans aFrame.one, (dFromA 1).trans aFrame.winner,
        dOne, (dFromA 8).trans (aFrame.count.trans layout.candidates),
        (dFromA 3).trans aFrame.identifierBase, (dFromA 4).trans aFrame.slackBase,
        (dFromA 5).trans aFrame.rateBase⟩
    · intro r safe
      exact (dFromA r (by simp at safe ⊢; omega) (by simp at safe; omega) (by simp at safe; omega)
        (by simp at safe; omega) (by simp at safe ⊢; omega)).trans (aReg r (by simp at safe ⊢; omega))
    · intro v
      have ordinary (addr : ℕ) (low : addr < s.nr 58) : dInput.nm addr = bInput.nm addr :=
        (dNatural addr low).trans (cNatural addr low)
      obtain ⟨role, parent, depth⟩ := forest v
      rw [aReg 51] at role parent depth
      have inside := v.isLt
      exact ⟨(ordinary _ (by omega)).trans role, (ordinary _ (by omega)).trans parent,
        (ordinary _ (by omega)).trans depth⟩
    · have bTime := reset.keeps_cache_real (r := 15) (by decide)
      have cTime := cleared.keeps_cache_real (r := 15) (by decide)
      have dTime := pair.keeps_cache_real (r := 15) (by decide)
      exact dTime.trans (cTime.trans (bTime.trans aFrame.cumulativeDelta))
    · exact dReal.trans (cReal.trans (bReal.trans aFrame.real))
    · intro addr forestAway idAway pairAway
      change dInput.nm addr = _
      have safe : addr < aInput.nr 51 ∨ aInput.nr 51 + 3*k ≤ addr := by rwa [aReg 51]
      rw [pairs, if_neg pairAway, clearedIds, if_neg idAway]
      exact (bNat addr safe).trans (congrFun aFrame.natural addr)
    · intro separated i hi
      change dInput.nm (s.nr 58 + i) = 0
      have outside : ¬ matchingPairSentinelAddress (s.nr 65) (k*k) (s.nr 58 + i) :=
        fun h => by have lo := h.1; omega
      rw [pairs, if_neg outside, clearedIds, if_pos (by omega)]
    · intro i hi
      change dInput.nm _ = _
      have here : matchingPairSentinelAddress (s.nr 65) (k*k) (s.nr 65 + (i+i)) :=
        ⟨by omega, by omega, by omega⟩
      rw [pairs, if_pos here]

set_option maxHeartbeats 700000 in
/-- Execute the warm start with a quadratic instruction bound and an exact forest reset.
The persistent pointers, mate table, and routing input prefixes remain in place. -/
theorem warmMatchingPreparationBlock_runs {k : ℕ} {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (layout : MatchingWarmLayout s k)
    (offsets : ∀ i < k, s.nm (s.nr 21 + i) = k * i)
    {active : Finset (Fin k)} {mate : Fin k → Option (Fin k)} {representative : Fin k → Fin k}
    (activeAt : ∀ v, v ∈ active ↔ representative v = v)
    (mates : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).elim k Fin.val)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (representative v).val) :
    ∃ t steps, steps ≤ 104 * k * k + 48 * k + 31 ∧
      BlockRuns warmMatchingPreparationBlock steps s t ∧ t.halted = false ∧
      MatchingWarmLayout t k ∧
      t.nr 31 = 6 * k + 1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
      t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.nr 8 = 3 * k ∧
      t.nr 3 = t.nr 58 ∧ t.nr 4 = t.nr 59 ∧ t.nr 5 = t.nr 60 ∧
      AlternatingForestMemory (resetAlternatingForest active mate) (s.nr 51) t.nm ∧
      (∀ a < s.nr 50 + k, t.nm a = s.nm a) ∧
      (∀ a < s.nr 59, t.rm a = s.rm a) ∧
      ∀ r, 50 ≤ r → (r < 71 ∨ 73 < r) → t.nr r = s.nr r := by
  obtain ⟨d, preTicks, preBudget, pre, dLive, ready⟩ :=
    warmMatchingPreparationPrefixBlock_runs entry running layout offsets activeAt mates reps
  let start := {d with pc := 0}
  have before (r : ℕ) (safe : r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] := by decide) :
      start.nr r = s.nr r := ready.fixed r safe
  obtain ⟨l, clock, activePort, unit, winner, one, count, id, slack, rate⟩ := ready.controls
  obtain ⟨e, scanSteps, scanBudget, scan, eLive, eFixed, eNat, eReal⟩ :=
    rebuildMatchingActiveCacheBlock_correct (s := start) rfl dLive one
      (by rw [before 58, before 54]; exact layout.dictionaryAfter)
      (by rw [before 58, before 65]; exact layout.pairsAfter)
      (by rw [before 59, before 60]; exact layout.ratesAfter)
      (by rw [before 59, before 66]; exact layout.keysAfter)
  let t := relocateState warmMatchingPreparationPrefixBlock.length e
  have after (r : ℕ) (safe : r ∉ [0, 6, 10, 11, 14, 15, 16, 17, 18, 19, 24, 25, 26] := by decide) :
      t.nr r = start.nr r := eFixed r safe
  have keep (r : ℕ)
      (sa : r ∉ [0, 6, 10, 11, 14, 15, 16, 17, 18, 19, 24, 25, 26] := by decide)
      (sb : r ∉ [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 15, 17, 29, 31, 32, 33, 34, 71, 72, 73] := by decide) :
      t.nr r = s.nr r := (after r sa).trans (before r sb)
  have natural (addr : ℕ) (low : addr < s.nr 58) : t.nm addr = d.nm addr :=
    eNat addr ((before 58).symm ▸ low)
  have forestEnd : s.nr 51 + 3*k ≤ s.nr 58 := by
    have a := layout.representativesAfter
    have b := layout.candidatesAfter
    omega
  rw [before 55, layout.size] at scanBudget
  refine ⟨t, preTicks + scanSteps, ?_, pre.append scan, eLive, ?_, ?_⟩
  · calc
      _ ≤ (6*(k*k) + 37*k + 28) + (k*(98*k+11)+3) := Nat.add_le_add preBudget scanBudget
      _ = _ := by ring
  · exact ⟨(keep 55).trans layout.size, (keep 61).trans layout.candidates,
      by rw [keep 52, keep 51]; exact layout.parents, by rw [keep 53, keep 51]; exact layout.depths,
      by rw [keep 50, keep 51]; exact layout.matesBefore, by rw [keep 51, keep 57]; exact layout.representativesAfter,
      by rw [keep 57, keep 58]; exact layout.candidatesAfter, by rw [keep 58, keep 54]; exact layout.dictionaryAfter,
      by rw [keep 58, keep 65]; exact layout.pairsAfter, by rw [keep 59, keep 60]; exact layout.ratesAfter,
      by rw [keep 59, keep 66]; exact layout.keysAfter, by rw [keep 21, keep 50]; exact layout.offsetsBefore⟩
  · refine ⟨(after 31).trans l, (after 32).trans clock, (after 33).trans activePort, (after 34).trans unit,
      (after 1).trans winner, (after 9).trans one, (after 8).trans count, (after 3).trans (id.trans (keep 58).symm),
      (after 4).trans (slack.trans (keep 59).symm), (after 5).trans (rate.trans (keep 60).symm), ?_, ?_, ?_, ?_⟩
    · intro v
      have inside := v.isLt
      obtain ⟨role, parent, depth⟩ := ready.forest v
      exact ⟨(natural _ (by omega)).trans role, (natural _ (by omega)).trans parent, (natural _ (by omega)).trans depth⟩
    · intro addr early
      have forestBefore : addr < s.nr 51 := by have h := layout.matesBefore; omega
      have cacheBefore : addr < s.nr 58 := by omega
      exact (natural addr cacheBefore).trans (ready.natural addr (Or.inl forestBefore)
        (fun h => (not_le.mpr cacheBefore) h.1)
        (fun h => (not_le.mpr (cacheBefore.trans_le layout.pairsAfter)) h.1))
    · intro addr early
      exact (eReal addr ((before 59).symm ▸ early)).trans (congrFun ready.real addr)
    · intro r high safe
      exact keep r (by simp; omega) (by simp; omega)


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPreparation

/-! matching/MatchingWarmPrimal.lean -/
section RppSource_MatchingWarmPrimal
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

noncomputable def CompactMatchingPrimalDual.partialMate {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (v : Fin k) : Option (Fin k) :=
  if v ∈ state.covered then some (mateOfMatching state.perfect v) else none

theorem CompactMatchingPrimalDual.partialMate_some_iff {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {v w : Fin k} : state.partialMate v = some w ↔
      s(v, w) ∈ state.edges := by
  by_cases covered : v ∈ state.covered
  · rw [CompactMatchingPrimalDual.partialMate, if_pos covered, Option.some.injEq]
    constructor
    · rintro rfl
      exact mateOfMatching_edge state.perfect covered
    · intro known
      have equal := (state.perfect.2 v covered).unique
        ⟨mateOfMatching_edge state.perfect covered, Sym2.mem_mk_left _ _⟩
        ⟨known, Sym2.mem_mk_left _ _⟩
      rcases Sym2.eq_iff.mp equal with direct | reversal
      · exact direct.2
      · exact reversal.2.trans reversal.1
  · rw [CompactMatchingPrimalDual.partialMate, if_neg covered]
    constructor
    · intro impossible
      cases impossible
    · intro impossible
      exact (covered ((state.perfect.1 _ impossible).2 v (Sym2.mem_mk_left _ _))).elim

theorem CompactMatchingPrimalDualMemory.partialMate_word {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {original s : ArithmeticState}
    (before : CompactMatchingPrimalDualMemory state original s) (v : Fin k) :
    s.nm (s.nr 50 + v.val) = (state.partialMate v).elim k Fin.val := by
  by_cases h : v ∈ state.covered <;> simp [before.mate, CompactMatchingPrimalDual.partialMate, h]

/-- Every nonbase member of a top block is already matched inside it. A matched
base instead has a partner in a different block. -/
structure CompactTopMatching {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) : Prop where
  interior : ∀ v w, w ∈ part.blocks.block v → w ≠ part.representative v →
    ∃ e ∈ state.edges, w ∈ e ∧ ∀ z ∈ e, z ∈ part.blocks.block v
  matchedBase : ∀ {v w}, part.representative v = v → state.partialMate v = some w →
    part.blocks.block v ≠ part.blocks.block w

def CompactMatchingPartition.activeRepresentatives {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) : Finset (Fin k) :=
  Finset.univ.filter fun v => part.representative v = v

theorem CompactMatchingPartition.mem_activeRepresentatives {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (v : Fin k) :
    v ∈ part.activeRepresentatives ↔ part.representative v = v := by
  simp [CompactMatchingPartition.activeRepresentatives]

theorem CompactTopMatching.crossing_endpoints {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) {u v : Fin k} (edge : s(u, v) ∈ state.edges)
    (separate : part.blocks.block u ≠ part.blocks.block v) :
    part.representative u = u ∧ part.representative v = v := by
  have atBase {a b : Fin k} (present : s(a, b) ∈ state.edges)
      (separated : part.blocks.block a ≠ part.blocks.block b) : part.representative a = a := by
    by_contra notBase
    obtain ⟨inner, member, incident, allInside⟩ := top.interior a a
      (part.blocks.self_mem a (Finset.mem_univ a)) (Ne.symm notBase)
    have covered := (state.perfect.1 _ present).2 a (Sym2.mem_mk_left _ _)
    have equal := (state.perfect.2 a covered).unique ⟨present, Sym2.mem_mk_left _ _⟩ ⟨member, incident⟩
    have bIn := allInside b (equal ▸ Sym2.mem_mk_right a b)
    exact separated (part.blocks.same_of_mem (Finset.mem_univ a) bIn).symm
  exact ⟨atBase edge separate, atBase (Sym2.eq_swap ▸ edge) separate.symm⟩

def CompactMatchingPartition.tightBetween {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (u v : Fin k) : Prop :=
  ∃ a b : Fin k, part.representative a = u ∧ part.representative b = v ∧
    oddCutDualEdgeValue state.cuts state.potential state.cutDual s(a, b) = edgeCost cost s(a, b)

theorem CompactTopMatching.resetForest {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (top : CompactTopMatching part) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    AlternatingStageRoots forest part.activeRepresentatives state.partialMate part.tightBetween ∧
      CompactMatchingSearchForest part forest state.partialMate part.tightBetween := by
  intro forest
  have roots := resetAlternatingForest_valid part.activeRepresentatives state.partialMate part.tightBetween
    (fun v active w mate => by
      have edge := (state.partialMate_some_iff).mp mate
      have separated := top.matchedBase ((part.mem_activeRepresentatives v).mp active) mate
      obtain ⟨vBase, wBase⟩ := top.crossing_endpoints edge separated
      exact ⟨(part.mem_activeRepresentatives w).mpr wBase, (fun eq => separated (congrArg part.blocks.block eq)),
        state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge), v, w, vBase, wBase, state.tight _ edge⟩)
  refine ⟨roots, ⟨roots.forest, ?_, ?_⟩⟩
  · intro v w edge separated
    obtain ⟨vBase, wBase⟩ := top.crossing_endpoints edge separated
    rw [vBase, wBase]
    exact ⟨state.partialMate_some_iff.mpr edge, state.partialMate_some_iff.mpr (Sym2.eq_swap ▸ edge)⟩
  · intro v uncovered
    rw [part.exposed_fixed uncovered]
    apply roots.exposedRoots v ((part.mem_activeRepresentatives v).mpr (part.exposed_fixed uncovered))
    simp [CompactMatchingPrimalDual.partialMate, uncovered]

/-- The actual warm preparation starts a new rooted search while preserving the
original matching and routing prefixes. -/
theorem warmMatchingPreparationBlock_primal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {original s : ArithmeticState} (entry : s.pc = 0) (running : s.halted = false)
    (primal : CompactMatchingPrimalDualMemory state original s) (top : CompactTopMatching part)
    (layout : MatchingWarmLayout s k) (realPrefix : original.nr 64 ≤ s.nr 59)
    (offsets : ∀ i < k, s.nm (s.nr 21 + i) = k * i)
    (reps : ∀ v : Fin k, s.nm (s.nr 57 + v.val) = (part.representative v).val) :
    let forest := resetAlternatingForest part.activeRepresentatives state.partialMate
    ∃ t steps, steps ≤ 104 * k * k + 48 * k + 31 ∧
      BlockRuns warmMatchingPreparationBlock steps s t ∧ t.halted = false ∧
      MatchingWarmLayout t k ∧ CompactMatchingPrimalDualMemory state original t ∧
      AlternatingForestMemory forest (t.nr 51) t.nm ∧
      AlternatingStageRoots forest part.activeRepresentatives state.partialMate part.tightBetween ∧
      CompactMatchingSearchForest part forest state.partialMate part.tightBetween ∧
      t.nr 31 = 6 * k + 1 ∧ t.nr 32 = 0 ∧ t.nr 33 = 1 ∧ t.nr 34 = 1 ∧
      t.nr 1 = 0 ∧ t.nr 9 = 1 ∧ t.nr 8 = 3 * k ∧
      t.nr 3 = t.nr 58 ∧ t.nr 4 = t.nr 59 ∧ t.nr 5 = t.nr 60 := by
  intro forest
  obtain ⟨t, steps, budget, run, live, newLayout, limit, zero, active, one, empty, unit,
    count, ids, slacks, rates, forestMemory, natPrefix, rmPrefix, fixed⟩ :=
    warmMatchingPreparationBlock_runs entry running layout offsets part.mem_activeRepresentatives
      primal.partialMate_word reps
  have mateBase := fixed 50 (by decide) (by decide)
  have roleBase := fixed 51 (by decide) (by decide)
  have next : CompactMatchingPrimalDualMemory state original t := by
    refine ⟨newLayout.size, (fixed 56 (by decide) (by decide)).trans primal.oddMap,
      mateBase.symm ▸ primal.mateAbove, ?_, ?_, ?_, ?_⟩
    · intro v
      rw [mateBase, natPrefix _ (Nat.add_lt_add_left v.isLt _)]
      exact primal.mate v
    · intro r high
      exact (fixed r (by omega) (Or.inr (by omega))).trans (primal.saved r high)
    · intro a before
      exact (natPrefix a (by have := primal.mateAbove; omega)).trans (primal.natural a before)
    · intro a before
      exact (rmPrefix a (before.trans_le realPrefix)).trans (primal.real a before)
  obtain ⟨roots, forestSearch⟩ := top.resetForest
  exact ⟨t, steps, budget, run, live, newLayout, next, roleBase.symm ▸ forestMemory, roots, forestSearch,
    limit, zero, active, one, empty, unit, count, ids, slacks, rates⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingWarmPrimal

/-! matching/MatchingExpansionPartition.lean -/
section RppSource_MatchingExpansionPartition
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The child blocks obtained from the live registry agree with their original
members and identify one exposed port for each child. -/
structure MatchingExpansionChildren {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (B : Finset (Fin k)) where
  block : Fin k → Finset (Fin k)
  representative : Fin k → Fin k
  self : ∀ v ∈ B, v ∈ block v
  subset : ∀ v ∈ B, block v ⊆ B
  same : ∀ v ∈ B, ∀ w ∈ block v, block w = block v
  cut : ∀ v ∈ B, (block v).card ≠ 1 → block v ∈ state.cuts.erase B
  inside : ∀ v ∈ B, representative v ∈ block v
  constant : ∀ u ∈ B, ∀ v ∈ B, block u = block v → representative u = representative v
  interior : ∀ v ∈ B, ∀ w ∈ block v, w ≠ representative v →
    ∃ e ∈ state.edges, w ∈ e ∧ ∀ z ∈ e, z ∈ block v
  matchedBase : ∀ v ∈ B, ∀ w, state.partialMate (representative v) = some w → w ∉ block v

theorem CompactMatchingPartition.block_eq_iff_member {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block) (v : Fin k) :
    part.blocks.block v = B ↔ v ∈ B := by
  constructor
  · intro same
    rw [← same]
    exact part.blocks.self_mem v (Finset.mem_univ v)
  · intro member
    obtain ⟨u, hu, identifies⟩ := Finset.mem_image.mp top
    exact (part.blocks.same_of_mem hu (identifies.symm ▸ member)).trans identifies

private theorem selectExpansionBlock {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (v : Fin k) (inside outside : Finset (Fin k)) :
    (if part.blocks.block v = B then inside else outside) = (if v ∈ B then inside else outside) := by
  by_cases h : v ∈ B
  · simp only [if_pos h, if_pos ((part.block_eq_iff_member top v).2 h)]
  · simp only [if_neg h, if_neg (fun e => h ((part.block_eq_iff_member top v).1 e))]

/-- Opening an exhausted blossom refines exactly its own block and retains
its children as top-level blocks. Every outside representative is unchanged. -/
def CompactMatchingPartition.openZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (children : MatchingExpansionChildren state B) :
    CompactMatchingPartition (state.eraseZeroCut present zero) where
  blocks := part.blocks.expand B top children.block children.self children.subset children.same children.cut
  representative v := if v ∈ B then children.representative v else part.representative v
  inside v := by
    change (if v ∈ B then children.representative v else part.representative v) ∈
      (if part.blocks.block v = B then children.block v else part.blocks.block v)
    rw [selectExpansionBlock part top v]
    split
    · exact children.inside v ‹v ∈ B›
    · exact part.inside v
  constant u v same := by
    change (if part.blocks.block u = B then children.block u else part.blocks.block u) =
      (if part.blocks.block v = B then children.block v else part.blocks.block v) at same
    rw [selectExpansionBlock part top u, selectExpansionBlock part top v] at same
    change (if u ∈ B then children.representative u else part.representative u) =
      (if v ∈ B then children.representative v else part.representative v)
    by_cases hu : u ∈ B <;> by_cases hv : v ∈ B
    · rw [if_pos hu, if_pos hv] at same ⊢
      exact children.constant u hu v hv same
    · rw [if_pos hu, if_neg hv] at same
      have member := part.blocks.self_mem v (Finset.mem_univ v)
      rw [← same] at member
      exact (hv (children.subset u hu member)).elim
    · rw [if_neg hu, if_pos hv] at same
      have member := part.blocks.self_mem u (Finset.mem_univ u)
      rw [same] at member
      exact (hu (children.subset v hv member)).elim
    · rw [if_neg hu, if_neg hv] at same ⊢
      exact part.constant u v same
  coveredAway v w member notBase := by
    change w ∈ (if part.blocks.block v = B then children.block v else part.blocks.block v) at member
    rw [selectExpansionBlock part top v] at member
    change w ≠ (if v ∈ B then children.representative v else part.representative v) at notBase
    change w ∈ state.covered
    by_cases hv : v ∈ B
    · rw [if_pos hv] at member notBase
      obtain ⟨e, edge, incident, _⟩ := children.interior v hv w member notBase
      exact (state.perfect.1 e edge).2 w incident
    · rw [if_neg hv] at member notBase
      exact part.coveredAway v w member notBase

theorem CompactMatchingPartition.openZeroCut_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (children : MatchingExpansionChildren state B) (v : Fin k) :
    (part.openZeroCut top present zero children).blocks.block v =
      if v ∈ B then children.block v else part.blocks.block v := by
  change (if part.blocks.block v = B then children.block v else part.blocks.block v) = _
  rw [selectExpansionBlock part top v]

theorem CompactMatchingPrimalDual.partialMate_eraseZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) {B : Finset (Fin k)}
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0) :
    (state.eraseZeroCut present zero).partialMate = state.partialMate := by
  funext v
  rfl

/-- The original matching still has a single exposed port on each new top
block after expansion, including blocks that were outside the selected cut. -/
theorem CompactTopMatching.openZeroCut {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    (matching : CompactTopMatching part)
    {B : Finset (Fin k)} (top : B ∈ Finset.univ.image part.blocks.block)
    (present : B ∈ state.cuts) (zero : state.cutDual B = 0)
    (children : MatchingExpansionChildren state B) :
    CompactTopMatching (part.openZeroCut top present zero children) := by
  have block := part.openZeroCut_block top present zero children
  have representative (v : Fin k) : (part.openZeroCut top present zero children).representative v =
      if v ∈ B then children.representative v else part.representative v := rfl
  constructor
  · intro v w member different
    rw [block] at member
    rw [representative] at different
    by_cases hv : v ∈ B
    · rw [if_pos hv] at member different
      simpa only [block, if_pos hv, show (state.eraseZeroCut present zero).edges = state.edges from rfl] using children.interior v hv w member different
    · rw [if_neg hv] at member different
      simpa only [block, if_neg hv, show (state.eraseZeroCut present zero).edges = state.edges from rfl] using matching.interior v w member different
  · intro v w base mate same
    rw [representative] at base
    rw [state.partialMate_eraseZeroCut present zero] at mate
    rw [block, block] at same
    by_cases hv : v ∈ B <;> by_cases hw : w ∈ B
    · rw [if_pos hv] at base
      rw [if_pos hv, if_pos hw] at same
      have incident := children.self w hw
      rw [← same] at incident
      exact children.matchedBase v hv w (base.symm ▸ mate) incident
    · rw [if_pos hv, if_neg hw] at same
      exact hw (children.subset v hv (same.symm ▸ part.blocks.self_mem w (Finset.mem_univ w)))
    · rw [if_neg hv, if_pos hw] at same
      exact hv (children.subset w hw (same ▸ part.blocks.self_mem v (Finset.mem_univ v)))
    · rw [if_neg hv] at base
      rw [if_neg hv, if_neg hw] at same
      exact matching.matchedBase base mate same

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionPartition

/-! matching/MatchingExpansionChildPorts.lean -/
section RppSource_MatchingExpansionChildPorts
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The child port table is a partition of the opened blossom. Each registered
child owns its original endpoints, and any nontrivial child remains a live cut. -/
structure MatchingExpansionChildPorts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (B : Finset (Fin k)) where
  ports : Finset (Fin k)
  block : Fin k → Finset (Fin k)
  owner : Fin k → Fin k
  containsPort : ∀ p ∈ ports, p ∈ block p
  subset : ∀ p ∈ ports, block p ⊆ B
  covered : ∀ v ∈ B, owner v ∈ ports ∧ v ∈ block (owner v)
  unique : ∀ p ∈ ports, ∀ v ∈ block p, owner v = p
  live : ∀ p ∈ ports, (block p).card ≠ 1 → block p ∈ state.cuts.erase B

/-- An exposed port of an internally matched child must be the base in the
matching certificate. This identifies the certificate with the registered port. -/
theorem CompactMatchingPrimalDual.certifiedChildBase {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)} {p : Fin k}
    (internal : state.InternalCuts) (live : B ∈ state.cuts) (inside : p ∈ B)
    (exposed : ∀ w, state.partialMate p = some w → w ∉ B) :
    ∀ v ∈ B, v ≠ p → ∃ e ∈ state.edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B := by
  obtain ⟨base, _, matched⟩ := internal B live
  have same : p = base := by
    by_contra different
    obtain ⟨e, edge, incident, contained⟩ := matched p inside different
    have covered := (state.perfect.1 e edge).2 p incident
    let w := mateOfMatching state.perfect p
    have mate : state.partialMate p = some w := by simp [CompactMatchingPrimalDual.partialMate, covered, w]
    have exactEdge := (state.partialMate_some_iff).mp mate
    have sameEdge := (state.perfect.2 p covered).unique ⟨exactEdge, Sym2.mem_mk_left _ _⟩ ⟨edge, incident⟩
    exact exposed w mate (contained w (sameEdge ▸ Sym2.mem_mk_right p w))
  rwa [same]

/-- The old matching determines the nonbase interior edges of every child.
Only exposure of each registered port needs to be read from the cycle. -/
def MatchingExpansionChildPorts.toExpansionChildren {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) (internal : state.InternalCuts)
    (external : ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p) :
    MatchingExpansionChildren state B where
  block v := registry.block (registry.owner v)
  representative := registry.owner
  self v member := (registry.covered v member).2
  subset v member := registry.subset _ (registry.covered v member).1
  same v member w inside := by rw [registry.unique _ (registry.covered v member).1 w inside]
  cut v member := registry.live _ (registry.covered v member).1
  inside v member := registry.containsPort _ (registry.covered v member).1
  constant u hu v hv same := by
    have left := (registry.covered u hu).1
    have right := (registry.covered v hv).1
    have inside := registry.containsPort _ left
    rw [same] at inside
    have lhs := registry.unique _ left _ (registry.containsPort _ left)
    exact lhs.symm.trans (registry.unique _ right _ inside)
  interior v member w inside different := by
    have child := (registry.covered v member).1
    have port := registry.containsPort _ child
    by_cases singleton : (registry.block (registry.owner v)).card = 1
    · obtain ⟨p, eq⟩ := Finset.card_eq_one.mp singleton
      rw [eq] at inside port
      exact (different ((Finset.mem_singleton.mp inside).trans (Finset.mem_singleton.mp port).symm)).elim
    · exact CompactMatchingPrimalDual.certifiedChildBase internal
        (Finset.mem_of_mem_erase (registry.live _ child singleton)) port (external _ child) w inside different
  matchedBase v member := external _ (registry.covered v member).1

theorem MatchingExpansionChildPorts.port_external_of_adjacentMate {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    (registry : MatchingExpansionChildPorts state B) {p q : Fin k}
    (pIn : p ∈ registry.ports) (qIn : q ∈ registry.ports) (different : p ≠ q)
    (matched : state.partialMate p = some q) :
    ∀ w, state.partialMate p = some w → w ∉ registry.block p := by
  intro w mate inside
  have same : q = w := Option.some.inj (matched.symm.trans mate)
  subst w
  exact different ((registry.unique p pIn q inside).symm.trans
    (registry.unique q qIn q (registry.containsPort q qIn)))

theorem MatchingExpansionChildPorts.port_external_of_oldBase {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    {part : CompactMatchingPartition state} (matching : CompactTopMatching part)
    (registry : MatchingExpansionChildPorts state B) {p : Fin k} (pIn : p ∈ registry.ports)
    (base : part.representative p = p) (block : part.blocks.block p = B) :
    ∀ w, state.partialMate p = some w → w ∉ registry.block p := by
  intro w mate inside
  have member : w ∈ part.blocks.block p := block.symm ▸ registry.subset p pIn inside
  exact matching.matchedBase base mate (part.blocks.same_of_mem (Finset.mem_univ p) member).symm

/-- The even tail of the current cycle pairs every child except its base.
Those mates are different child ports, so all child bases stay exposed to
their own blocks when the old base is released. -/
theorem MatchingExpansionChildPorts.ports_external_of_cycle {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {B : Finset (Fin k)}
    {part : CompactMatchingPartition state} (matching : CompactTopMatching part)
    (registry : MatchingExpansionChildPorts state B) (base : Fin k) (children : List (Fin k))
    (cyclePorts : registry.ports = (base :: children).toFinset)
    (nodup : children.Nodup) (even : children.length % 2 = 0)
    (baseFixed : part.representative base = base) (baseBlock : part.blocks.block base = B)
    (childMates : ∀ a b, s(a, b) ∈ alternatingEdges children →
      state.partialMate a = some b ∧ state.partialMate b = some a) :
    ∀ p ∈ registry.ports, ∀ w, state.partialMate p = some w → w ∉ registry.block p := by
  intro p pIn
  by_cases isBase : p = base
  · subst p
    exact registry.port_external_of_oldBase matching pIn baseFixed baseBlock
  · have inner : p ∈ children := by
      rw [cyclePorts, List.mem_toFinset, List.mem_cons] at pIn
      exact pIn.resolve_left isBase
    have perfect := (alternatingEdges_perfect children nodup even).2
    obtain ⟨edge, ⟨eIn, incident⟩, _⟩ := perfect.2 p (List.mem_toFinset.mpr inner)
    induction edge using Sym2.inductionOn with
    | _ a b =>
      have aIn : a ∈ registry.ports := by
        rw [cyclePorts, List.mem_toFinset]
        exact List.mem_cons.mpr (.inr (List.mem_toFinset.mp ((perfect.1 _ eIn).2 a (Sym2.mem_mk_left _ _))))
      have bIn : b ∈ registry.ports := by
        rw [cyclePorts, List.mem_toFinset]
        exact List.mem_cons.mpr (.inr (List.mem_toFinset.mp ((perfect.1 _ eIn).2 b (Sym2.mem_mk_right _ _))))
      have mates := childMates a b (List.mem_toFinset.mp eIn)
      have distinct := mt Sym2.mk_isDiag_iff.mpr (perfect.1 _ eIn).1
      rcases Sym2.mem_iff.mp incident with left | right
      · subst p
        exact registry.port_external_of_adjacentMate aIn bIn distinct mates.1
      · subst p
        exact registry.port_external_of_adjacentMate bIn aIn (Ne.symm distinct) mates.2

end VehicleRoutingSurvey.Routing
end RppSource_MatchingExpansionChildPorts


