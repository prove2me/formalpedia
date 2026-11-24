-- Prove2me | Definitions.Def_CSL_Circuit_Framework_Circuit
-- name    : CSL_Circuit_Framework_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:50.780903+00:00
-- url     : https://prove2.me/theorems/d0988146-25ba-4eb5-9703-cea5f2b8a9fa
-- title:
--   Coded sorting library: Circuit / Framework / Circuit
-- statement:
--   Module `CodedSorting.Circuit.Framework.Circuit` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Section 4.1: executable XOR blocks and arbitrary auxiliary initial values
--
--   The payload field is `ZMod 2`.  A side-array is represented as a total array;
--   entries for which `side S T` is false are inert padding, never read or changed.
--   Thus restriction to the actual side-register set is immediate, while no
--   assumption that an auxiliary initial value is zero is used.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.Circuit

import Definitions.Def_CSL_Compat
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Section 4.1: executable XOR blocks and arbitrary auxiliary initial values

The payload field is `ZMod 2`.  A side-array is represented as a total array;
entries for which `side S T` is false are inert padding, never read or changed.
Thus restriction to the actual side-register set is immediate, while no
assumption that an auxiliary initial value is zero is used.
-/

set_option autoImplicit false

namespace CSL.Circuit

open scoped BigOperators

abbrev Bit := ZMod 2
abbrev Triple (d : ℕ) := {s : Finset (Fin d) // s.card = 3}

private theorem bit_add_self (a : Bit) : a + a = 0 := by
  exact (by decide : ∀ b : Bit, b + b = 0) a

variable {d : ℕ}

noncomputable def side (S T : Triple d) : Prop := (S.val ∩ T.val).card = 1

theorem side_symmetric (S T : Triple d) : side S T ↔ side T S := by
  simp only [side, Finset.inter_comm]

abbrev SideIndex (d : ℕ) :=
  {p : Triple d × Triple d // side p.1 p.2}

/-- Embedding of the real side-register set into the convenient total array. -/
noncomputable def extendSide (a : SideIndex d → Bit) : Triple d → Triple d → Bit := by
  classical
  exact fun S T => if h : side S T then a ⟨(S,T),h⟩ else 0

def restrictSide (a : Triple d → Triple d → Bit) (p : SideIndex d) : Bit :=
  a p.val.1 p.val.2

@[simp] theorem restrictSide_extendSide (a : SideIndex d → Bit) :
    restrictSide (extendSide a) = a := by
  classical
  funext p
  rcases p with ⟨⟨S,T⟩,h⟩
  simp [restrictSide, extendSide, h]

noncomputable def centreIncrement (x : Triple d → Bit) (i : Fin d) : Bit :=
  ∑ T, if i ∈ T.val then x T else 0

noncomputable def centreRead (c : Fin d → Bit) (S : Triple d) : Bit :=
  ∑ i ∈ S.val, c i

noncomputable def sideRead (a : Triple d → Triple d → Bit) (S : Triple d) : Bit := by
  classical
  exact ∑ T, if side S T then a S T else 0

noncomputable def correction (x : Triple d → Bit) (S : Triple d) : Bit := by
  classical
  exact ∑ T, if side S T then x T else 0

noncomputable def shared (x : Triple d → Bit) (S : Triple d) : Bit :=
  centreRead (centreIncrement x) S

/-- The paper's intersection-parity coefficient, proved for arbitrary `d`. -/
theorem intersection_coefficient (S T : Triple d) :
    ((S.val ∩ T.val).card : Bit) +
      (if (S.val ∩ T.val).card = 1 then 1 else 0) =
      if S = T then 1 else 0 := by
  classical
  by_cases h : S = T
  · subst T
    norm_num [S.property]
    decide
  · have hle : (S.val ∩ T.val).card ≤ 3 := by
      calc
        (S.val ∩ T.val).card ≤ S.val.card := Finset.card_le_card Finset.inter_subset_left
        _ = 3 := S.property
    have hne : (S.val ∩ T.val).card ≠ 3 := by
      intro hc
      have hs : S.val ∩ T.val = S.val :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [S.property, hc])
      have hst : S.val ⊆ T.val := hs ▸ Finset.inter_subset_right
      have heq : S.val = T.val :=
        Finset.eq_of_subset_of_card_le hst (by rw [S.property, T.property])
      exact h (Subtype.ext heq)
    have hcases : (S.val ∩ T.val).card = 0 ∨
        (S.val ∩ T.val).card = 1 ∨ (S.val ∩ T.val).card = 2 := by omega
    rcases hcases with hc | hc | hc <;> norm_num [hc, h] <;> decide

/-- Interchanging the two finite sums counts each incidence exactly once. -/
theorem shared_as_intersection_sum (x : Triple d → Bit) (S : Triple d) :
    shared x S = ∑ T, ((S.val ∩ T.val).card : Bit) * x T := by
  classical
  unfold shared centreRead centreIncrement
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.sum_filter]
  have hf : S.val.filter (fun i => i ∈ T.val) = S.val ∩ T.val := by
    ext i
    simp
  rw [hf]
  simp [nsmul_eq_mul]

/-- Equation (block-cancellation), with no assumption on the input vector. -/
theorem shared_add_correction (x : Triple d → Bit) (S : Triple d) :
    shared x S + correction x S = x S := by
  classical
  rw [shared_as_intersection_sum]
  unfold correction side
  rw [← Finset.sum_add_distrib]
  trans ∑ T, if S = T then x T else 0
  · apply Finset.sum_congr rfl
    intro T _
    have hc := congrArg (fun b : Bit => b * x T) (intersection_coefficient S T)
    by_cases h1 : (S.val ∩ T.val).card = 1 <;>
      by_cases heq : S = T <;> simpa [h1, heq, add_mul] using hc
  · simp


structure BlockState (d : ℕ) where
  x : Triple d → Bit
  y : Triple d → Bit
  a : Triple d → Triple d → Bit
  c : Fin d → Bit

noncomputable def updateSide (x : Triple d → Bit)
    (a : Triple d → Triple d → Bit) : Triple d → Triple d → Bit := by
  classical
  exact fun S T => if side S T then a S T + x T else a S T

theorem updateSide_inactive (x : Triple d → Bit)
    (a : Triple d → Triple d → Bit) (S T : Triple d) (h : ¬ side S T) :
    updateSide x a S T = a S T := by
  simp [updateSide, h]

theorem sideRead_congr_active (a b : Triple d → Triple d → Bit)
    (h : ∀ S T, side S T → a S T = b S T) (S : Triple d) :
    sideRead a S = sideRead b S := by
  classical
  unfold sideRead
  apply Finset.sum_congr rfl
  intro T _
  by_cases hs : side S T
  · simp [hs, h S T hs]
  · simp [hs]

noncomputable def updateCentre (x : Triple d → Bit)
    (c : Fin d → Bit) : Fin d → Bit := fun i => c i + centreIncrement x i

@[simp] theorem updateSide_twice (x : Triple d → Bit)
    (a : Triple d → Triple d → Bit) : updateSide x (updateSide x a) = a := by
  classical
  funext S T
  unfold updateSide
  split_ifs <;> simp [add_assoc, bit_add_self]

@[simp] theorem updateCentre_twice (x : Triple d → Bit)
    (c : Fin d → Bit) : updateCentre x (updateCentre x c) = c := by
  funext i
  simp [updateCentre, add_assoc, bit_add_self]

theorem sideRead_updateSide (x : Triple d → Bit)
    (a : Triple d → Triple d → Bit) (S : Triple d) :
    sideRead (updateSide x a) S = sideRead a S + correction x S := by
  classical
  unfold sideRead updateSide correction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem centreRead_updateCentre (x : Triple d → Bit)
    (c : Fin d → Bit) (S : Triple d) :
    centreRead (updateCentre x c) S = centreRead c S + shared x S := by
  classical
  unfold centreRead updateCentre shared
  exact Finset.sum_add_distrib

/-- Simultaneous gates at a numbered layer of the first block. -/
noncomputable def g0 (s : BlockState d) : BlockState d :=
  {s with y := fun S => s.y S + sideRead s.a S}
noncomputable def g1 (s : BlockState d) : BlockState d :=
  {s with y := fun S => s.y S + centreRead s.c S}
noncomputable def g2 (s : BlockState d) : BlockState d :=
  {s with a := updateSide s.x s.a}
noncomputable def g3 (s : BlockState d) : BlockState d :=
  {s with c := updateCentre s.x s.c}

theorem g0_involutive (s : BlockState d) : g0 (g0 s) = s := by
  cases s with
  | mk x y a c =>
    unfold g0
    congr 1
    funext S
    simp [add_assoc, bit_add_self]

theorem g1_involutive (s : BlockState d) : g1 (g1 s) = s := by
  cases s with
  | mk x y a c =>
    unfold g1
    congr 1
    funext S
    simp [add_assoc, bit_add_self]

theorem g2_involutive (s : BlockState d) : g2 (g2 s) = s := by
  cases s
  simp [g2]

theorem g3_involutive (s : BlockState d) : g3 (g3 s) = s := by
  cases s
  simp [g3]

/-- Eight layers 0,1,2,3,4,5,6,7: layers 4--7 repeat 1,0,3,2. -/
noncomputable def firstBlock (s : BlockState d) : BlockState d :=
  g2 (g3 (g0 (g1 (g3 (g2 (g1 (g0 s)))))))

/-- The actual eight-layer first block preserves `x`, adds `x` to `y`,
and restores every arbitrary side and centre value. -/
theorem firstBlock_correct (s : BlockState d) :
    firstBlock s = {s with y := fun S => s.y S + s.x S} := by
  cases s with
  | mk x y a c =>
    unfold firstBlock g0 g1 g2 g3
    simp only [updateSide_twice, updateCentre_twice]
    congr 1
    funext S
    rw [centreRead_updateCentre, sideRead_updateSide]
    calc
      y S + sideRead a S + centreRead c S +
          (centreRead c S + shared x S) + (sideRead a S + correction x S) =
        y S + (sideRead a S + sideRead a S) +
          (centreRead c S + centreRead c S) + (shared x S + correction x S) := by ring
      _ = y S + x S := by rw [bit_add_self, bit_add_self, shared_add_correction]; simp

/-- Swap the data interfaces and transpose the side indices; centres unchanged. -/
def swapInterfaces (s : BlockState d) : BlockState d :=
  ⟨s.y, s.x, fun S T => s.a T S, s.c⟩

@[simp] theorem swapInterfaces_twice (s : BlockState d) :
    swapInterfaces (swapInterfaces s) = s := by cases s; rfl

/-- Reverse the eight layers, retaining the register coordinates. -/
noncomputable def reverseBlock (s : BlockState d) : BlockState d :=
  g0 (g1 (g2 (g3 (g1 (g0 (g3 (g2 s)))))))

/-- Direct proof of the reversed eight-layer execution, without assuming
that reversing arrows is a defined operation. -/
theorem reverseBlock_correct (s : BlockState d) :
    reverseBlock s = {s with y := fun S => s.y S + s.x S} := by
  cases s with
  | mk x y a c =>
    unfold reverseBlock g0 g1 g2 g3
    simp only [updateSide_twice, updateCentre_twice]
    congr 1
    funext S
    rw [sideRead_updateSide, centreRead_updateCentre]
    calc
      y S + (sideRead a S + correction x S) +
          (centreRead c S + shared x S) + centreRead c S + sideRead a S =
        y S + (sideRead a S + sideRead a S) +
          (centreRead c S + centreRead c S) + (shared x S + correction x S) := by ring
      _ = y S + x S := by rw [bit_add_self, bit_add_self, shared_add_correction]; simp

/-- The paper's second operation set: reverse, exchange interfaces and S,T. -/
noncomputable def secondBlock (s : BlockState d) : BlockState d :=
  swapInterfaces (reverseBlock (swapInterfaces s))

theorem secondBlock_correct (s : BlockState d) :
    secondBlock s = {s with x := fun T => s.x T + s.y T} := by
  rw [secondBlock, reverseBlock_correct]
  cases s
  rfl

/- The remaining lemmas lift the proved local operations to triple-indexed
arrays.  `slice1/2/3` are explicit coordinate bijections, so every data register
belongs to one and only one group in each round. -/

abbrev DataIndex (d : ℕ) := Triple d × Triple d × Triple d

def slice1 (a : DataIndex d) : (Triple d × Triple d) × Triple d :=
  ((a.2.1, a.2.2), a.1)
def unslice1 (b : (Triple d × Triple d) × Triple d) : DataIndex d :=
  (b.2, b.1.1, b.1.2)
def slice2 (a : DataIndex d) : (Triple d × Triple d) × Triple d :=
  ((a.1, a.2.2), a.2.1)
def unslice2 (b : (Triple d × Triple d) × Triple d) : DataIndex d :=
  (b.1.1, b.2, b.1.2)
def slice3 (a : DataIndex d) : (Triple d × Triple d) × Triple d :=
  ((a.1, a.2.1), a.2.2)
def unslice3 (b : (Triple d × Triple d) × Triple d) : DataIndex d :=
  (b.1.1, b.1.2, b.2)

@[simp] theorem unslice1_slice1 (a : DataIndex d) : unslice1 (slice1 a) = a := rfl
@[simp] theorem slice1_unslice1 (b : (Triple d × Triple d) × Triple d) :
    slice1 (unslice1 b) = b := rfl
@[simp] theorem unslice2_slice2 (a : DataIndex d) : unslice2 (slice2 a) = a := rfl
@[simp] theorem slice2_unslice2 (b : (Triple d × Triple d) × Triple d) :
    slice2 (unslice2 b) = b := rfl
@[simp] theorem unslice3_slice3 (a : DataIndex d) : unslice3 (slice3 a) = a := rfl
@[simp] theorem slice3_unslice3 (b : (Triple d × Triple d) × Triple d) :
    slice3 (unslice3 b) = b := rfl

/-- Exact XOR swap used after assembling the disjoint groups in each round. -/
theorem three_round_xor_swap {ι : Type*} (x y : ι → Bit) :
    (fun i => x i + (y i + x i)) = y ∧
    (fun i => (y i + x i) + (x i + (y i + x i))) = x := by
  constructor <;> funext i
  · calc
      x i + (y i + x i) = y i + (x i + x i) := by ring
      _ = y i := by simp [bit_add_self]
  · calc
      (y i + x i) + (x i + (y i + x i)) =
          x i + (x i + x i) + (y i + y i) := by ring
      _ = x i := by simp [bit_add_self]

abbrev GroupIndex (d : ℕ) := Triple d × Triple d
abbrev AuxState (d : ℕ) :=
  (SideIndex d → Bit) × (Fin d → Bit)

@[ext] structure GlobalState (d : ℕ) where
  x : DataIndex d → Bit
  y : DataIndex d → Bit
  aux : Fin 3 → GroupIndex d → AuxState d

def grouping1 : DataIndex d ≃ GroupIndex d × Triple d :=
  ⟨slice1, unslice1, unslice1_slice1, slice1_unslice1⟩
def grouping2 : DataIndex d ≃ GroupIndex d × Triple d :=
  ⟨slice2, unslice2, unslice2_slice2, slice2_unslice2⟩
def grouping3 : DataIndex d ≃ GroupIndex d × Triple d :=
  ⟨slice3, unslice3, unslice3_slice3, slice3_unslice3⟩

/-- The exact block input associated with one fixed-coordinate group. -/
noncomputable def groupInput (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (s : GlobalState d) (k : GroupIndex d) : BlockState d :=
  ⟨fun T => s.x (e.symm (k,T)), fun T => s.y (e.symm (k,T)),
    extendSide (s.aux j k).1, (s.aux j k).2⟩

/-- Execute one copy of the given block in every disjoint group. -/
noncomputable def executeGrouped (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (block : BlockState d → BlockState d)
    (s : GlobalState d) : GlobalState d :=
  { x := fun a => (block (groupInput e j s (e a).1)).x (e a).2
    y := fun a => (block (groupInput e j s (e a).1)).y (e a).2
    aux := fun j' k => if j' = j then
      (restrictSide (block (groupInput e j s k)).a,
       (block (groupInput e j s k)).c)
      else s.aux j' k }

theorem executeGrouped_first_correct
    (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (s : GlobalState d) :
    executeGrouped e j firstBlock s =
      {s with y := fun a => s.y a + s.x a} := by
  apply GlobalState.ext
  · funext a
    simp [executeGrouped, firstBlock_correct, groupInput]
  · funext a
    simp [executeGrouped, firstBlock_correct, groupInput]
  · funext j' k
    by_cases h : j' = j
    · subst j'
      simp [executeGrouped, firstBlock_correct, groupInput]
    · simp [executeGrouped, firstBlock_correct, groupInput, h]

theorem executeGrouped_second_correct
    (e : DataIndex d ≃ GroupIndex d × Triple d)
    (j : Fin 3) (s : GlobalState d) :
    executeGrouped e j secondBlock s =
      {s with x := fun a => s.x a + s.y a} := by
  apply GlobalState.ext
  · funext a
    simp [executeGrouped, secondBlock_correct, groupInput]
  · funext a
    simp [executeGrouped, secondBlock_correct, groupInput]
  · funext j' k
    by_cases h : j' = j
    · subst j'
      simp [executeGrouped, secondBlock_correct, groupInput]
    · simp [executeGrouped, secondBlock_correct, groupInput, h]

/-- All three concrete rounds, with distinct auxiliary arrays per block. -/
noncomputable def threeRoundCircuit (s : GlobalState d) : GlobalState d :=
  executeGrouped grouping3 2 firstBlock
    (executeGrouped grouping2 1 secondBlock
      (executeGrouped grouping1 0 firstBlock s))

/-- Section 4.1's complete functional claim, for arbitrary d and ALL initial
payloads and auxiliary values. Topology/rank/cost claims are separate. -/
theorem threeRoundCircuit_correct (s : GlobalState d) :
    threeRoundCircuit s = ⟨s.y, s.x, s.aux⟩ := by
  unfold threeRoundCircuit
  simp only [executeGrouped_first_correct, executeGrouped_second_correct]
  apply GlobalState.ext
  · exact (three_round_xor_swap s.x s.y).1
  · exact (three_round_xor_swap s.x s.y).2
  · rfl

end CSL.Circuit


