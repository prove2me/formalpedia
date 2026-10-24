-- Prove2me | Definitions.Def_PricingWithTips3DM_3b6a88d9be5918e3cb96dca9
-- name    : PricingWithTips3DM_3b6a88d9be5918e3cb96dca9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:47:25.032282+00:00
-- url     : https://prove2.me/theorems/02fd9259-dec3-4c93-b45d-bf4fbe302afb
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Sets.Matching3D.FromSat.Adequacy
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_0ce3e5e1c7f27e9a1020a44d
import Definitions.Def_PricingWithTips3DM_e80588e5c6eb8509e1ccd808
import Definitions.Def_PricingWithTips3DM_b27b057a2325e62412e51b11
import Definitions.Def_PricingWithTips3DM_e5bee0ce4f35f592b340b7b1
import Definitions.Def_PricingWithTips3DM_4c74acf7ab61410b0782962b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# SAT → 3-dimensional matching, certified

The bridged correctness of `satToMatching3DCode`. Cost and output-size bounds
are free (`Code.cost_size_le_polyBound`); what is proved here is that the
program's output decodes to a yes-instance exactly when the input formula is
satisfiable.

## The shape of the argument

The mathematical layer states the construction over *tagged* element types —
`Sat3dm.Ext` and `Sat3dm.Slot`, built from `Fin`, `Bool`, sums and products —
and proves it correct there (`Sat3dm.satisfiable_iff_exists_matching`, which is
parametric in the variable list, so the certificate may supply the list its own
deduplication produces). A concrete instance names elements by *positions* of
an element list. The two views are related by the mixed-radix numberings
`extIdx` and `slotIdx`, which this file exhibits as **bijections** onto the
positions of the element lists the program emits; 3DM is invariant under such
renamings (`matching3D_iff_of_equiv`), and that is the whole bridge.

This is the 3DM analogue of the "up to injective relabelling" discipline the
SAT gadget certificates use. The numberings are instances of the block layer
(`Cert/Numbering.lean`) — the external elements one rectangle, the internal
elements three blocks laid end to end — and the bound, the injectivity and the
bijections are read off it.
-/

namespace Hardness
namespace Cert

open Sat3dm

namespace SatToMatching3DCode

/-! ## What the program computes -/

theorem clauseUnits_eval (x : SatTy.denote) : clauseUnits.eval x = x.map fun _ ↦ 0 := rfl

theorem length_clauseUnits (x : SatTy.denote) : (clauseUnits.eval x).length = x.length := by
  rw [clauseUnits_eval, List.length_map]

theorem slotsCode_eval (x : SatTy.denote) : slotsCode.eval x = vsOf x ++ [0] := by
  have h : slotsCode.eval x = varsCode.eval x ++ [0] := rfl
  rw [h, varsCode_eval]

theorem length_slotsCode (x : SatTy.denote) :
    (slotsCode.eval x).length = (vsOf x).length + 1 := by
  rw [slotsCode_eval, List.length_append]
  rfl

theorem envCode_eval (x : SatTy.denote) : envCode.eval x = (vsOf x, x.length) := by
  have h : envCode.eval x = (varsCode.eval x, x.length) := rfl
  rw [h, varsCode_eval]

/-- A `unitsProd` list has the product length — this is how the certificate
builds element lists of the prescribed sizes. -/
theorem length_unitsProd (l₁ l₂ : Code SatTy (.list .nat)) (x : SatTy.denote) :
    ((unitsProd l₁ l₂).eval x).length = (l₁.eval x).length * (l₂.eval x).length := by
  have h : (unitsProd l₁ l₂).eval x =
      (Code.cross.eval (l₁.eval x, l₂.eval x)).map fun _ ↦ (0 : ℕ) := rfl
  rw [h, List.length_map, length_cross_eval]

/-- The external element list has one position per `(slot, clause, polarity)`,
which is `Fintype.card (Ext n m)`. -/
theorem length_extElems (x : SatTy.denote) :
    (extElems.eval x).length = ((vsOf x).length + 1) * (x.length * 2) := by
  rw [extElems, length_unitsProd, length_slotsCode, length_unitsProd, length_clauseUnits]
  rfl

/-- The internal element list has one position per `Slot`, the three components
in turn. -/
theorem length_slotElems (x : SatTy.denote) :
    (slotElems.eval x).length =
      ((vsOf x).length + 1) * x.length + (x.length + x.length * (vsOf x).length) := by
  have h : slotElems.eval x =
      (unitsProd slotsCode clauseUnits).eval x ++
        (clauseUnits.eval x ++ (unitsProd clauseUnits varsCode).eval x) := rfl
  rw [h, List.length_append, List.length_append, length_unitsProd, length_unitsProd,
    length_slotsCode, length_clauseUnits, varsCode_eval]

/-! ## The numberings

The mixed-radix positions the program computes, stated over the mathematical
layer's tagged element types. -/

/-- The bit a polarity contributes to an external element's position. -/
def bitOf (b : Bool) : ℕ := if b then 1 else 0

/-- The position of the external element `(i, j, b)`. -/
def extIdxN (m i j b : ℕ) : ℕ := 2 * (m * i + j) + b

/-- The position of the truth-setting ring element `(i, j)`. -/
def ringIdxN (m i j : ℕ) : ℕ := m * i + j

/-- The position of the clause-testing element of clause `j`. -/
def testIdxN (n m j : ℕ) : ℕ := (n + 1) * m + j

/-- The position of the garbage-collection element `(j, i)`. -/
def junkIdxN (n m j i : ℕ) : ℕ := (n + 1) * m + m + (n * j + i)

/-- The position of an external element. -/
def extIdx {n m : ℕ} (e : Ext n m) : ℕ := extIdxN m e.1.1 e.2.1.1 (bitOf e.2.2)

/-- The position of an internal element: the three components in turn. -/
def slotIdx {n m : ℕ} : Slot n m → ℕ
  | .inl p => ringIdxN m p.1.1 p.2.1
  | .inr (.inl j) => testIdxN n m j.1
  | .inr (.inr q) => junkIdxN n m q.1.1 q.2.1

/-- The positions of a triple. -/
def tripIdx {n m : ℕ} (t : Trip n m) : ℕ × ℕ × ℕ :=
  (extIdx t.1, slotIdx t.2.1, slotIdx t.2.2)

/-! The two numberings are block layouts (`Cert/Numbering.lean`): the external
elements one rectangle, the internal elements three blocks laid end to end.
The definitions above stay arithmetic — the annex matches them against the
program's output *definitionally* — and one bridge lemma per numbering hands
the bound, the injectivity and the bijection to the layer. -/

/-- The block layout behind `extIdx`: a `(slot, bit)` rectangle. -/
def extNumbering (n m : ℕ) : Numbering (Ext n m) :=
  (Numbering.fin (n + 1)).prod ((Numbering.fin m).prod .bool)

/-- The block layout behind `slotIdx`: the ring rectangle, the test row, the
junk rectangle. -/
def slotNumbering (n m : ℕ) : Numbering (Slot n m) :=
  ((Numbering.fin (n + 1)).prod (Numbering.fin m)).sum
    ((Numbering.fin m).sum ((Numbering.fin m).prod (Numbering.fin n)))

/-- The arithmetic is the layout. -/
theorem extIdx_eq_num {n m : ℕ} (e : Ext n m) : extIdx e = (extNumbering n m).num e := by
  obtain ⟨i, j, b⟩ := e
  simp only [extIdx, extIdxN, extNumbering, Numbering.prod_num, Numbering.fin_num,
    Numbering.prod_size, Numbering.fin_size, Numbering.bool_size, Numbering.bool_num]
  cases b <;> simp [bitOf] <;> ring

/-- The arithmetic is the layout. -/
theorem slotIdx_eq_num {n m : ℕ} (s : Slot n m) : slotIdx s = (slotNumbering n m).num s := by
  rcases s with ⟨i, j⟩ | (j | ⟨jq, iq⟩) <;>
    simp only [slotIdx, ringIdxN, testIdxN, junkIdxN, slotNumbering,
      Numbering.sum_num_inl, Numbering.sum_num_inr,
      Numbering.prod_num, Numbering.prod_size, Numbering.fin_num, Numbering.fin_size] <;>
    ring

theorem extIdx_lt {n m : ℕ} (e : Ext n m) : extIdx e < (n + 1) * (m * 2) := by
  rw [extIdx_eq_num]
  exact (extNumbering n m).num_lt e

theorem extIdx_inj {n m : ℕ} : Function.Injective (extIdx (n := n) (m := m)) :=
  fun _ _ h ↦ (extNumbering n m).num_inj
    (by rw [← extIdx_eq_num, ← extIdx_eq_num]; exact h)

theorem slotIdx_lt {n m : ℕ} (s : Slot n m) : slotIdx s < (n + 1) * m + (m + m * n) := by
  rw [slotIdx_eq_num]
  exact (slotNumbering n m).num_lt s

theorem slotIdx_inj {n m : ℕ} : Function.Injective (slotIdx (n := n) (m := m)) :=
  fun _ _ h ↦ (slotNumbering n m).num_inj
    (by rw [← slotIdx_eq_num, ← slotIdx_eq_num]; exact h)

theorem tripIdx_inj {n m : ℕ} : Function.Injective (tripIdx (n := n) (m := m)) := by
  intro t₁ t₂ h
  exact Prod.ext (extIdx_inj (congrArg Prod.fst h))
    (Prod.ext (slotIdx_inj (congrArg (fun r ↦ r.2.1) h))
      (slotIdx_inj (congrArg (fun r ↦ r.2.2) h)))

/-! ## What the four families of triples are

Each family is a map over an explicit source list, so membership is read off
by `mem_cross_eval` and `List.mem_map`. The statements are phrased in terms of
`(decodeCNF x).length`, the clause count the mathematical layer indexes by. -/

theorem ringPositions_eval (x : SatTy.denote) :
    ringPositions.eval x =
      (Code.cross (σ := .nat) (τ := .nat)).eval
        (List.range ((vsOf x).length + 1), List.range x.length) := by
  have h : ringPositions.eval x =
      Code.cross.eval (Code.indices.eval (slotsCode.eval x),
        Code.indices.eval (clauseUnits.eval x)) := rfl
  rw [h, indices_eval, indices_eval, length_slotsCode, length_clauseUnits]

theorem mem_trueList_eval (x : SatTy.denote) (t : ℕ × ℕ × ℕ) :
    t ∈ trueList.eval x ↔ ∃ i j, i < (vsOf x).length + 1 ∧ j < (decodeCNF x).length ∧
      t = (extIdxN (decodeCNF x).length i j 0,
        (ringIdxN (decodeCNF x).length i j, ringIdxN (decodeCNF x).length i j)) := by
  rw [length_decodeCNF]
  have h : trueList.eval x = (ringPositions.eval x).map fun p ↦
      (extIdxN x.length p.1 p.2 0,
        (ringIdxN x.length p.1 p.2, ringIdxN x.length p.1 p.2)) := by
    have h0 : trueList.eval x =
        (ringPositions.eval x).map fun p ↦ trueTripCode.eval (envCode.eval x, p) := rfl
    rw [h0, envCode_eval]
    rfl
  rw [h, ringPositions_eval]
  constructor
  · intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨h1, h2⟩ := (mem_cross_eval _ _ p).mp hp
    exact ⟨p.1, p.2, List.mem_range.mp h1, List.mem_range.mp h2, rfl⟩
  · rintro ⟨i, j, hi, hj, rfl⟩
    refine List.mem_map.mpr ⟨(i, j), ?_, rfl⟩
    exact (mem_cross_eval _ _ _).mpr ⟨List.mem_range.mpr hi, List.mem_range.mpr hj⟩

theorem mem_falseList_eval (x : SatTy.denote) (t : ℕ × ℕ × ℕ) :
    t ∈ falseList.eval x ↔ ∃ i j, i < (vsOf x).length + 1 ∧ j < (decodeCNF x).length ∧
      t = (extIdxN (decodeCNF x).length i j 1,
        (ringIdxN (decodeCNF x).length i j,
          ringIdxN (decodeCNF x).length i
            (if j + 1 = (decodeCNF x).length then 0 else j + 1))) := by
  rw [length_decodeCNF]
  have h : falseList.eval x = (ringPositions.eval x).map fun p ↦
      (extIdxN x.length p.1 p.2 1,
        (ringIdxN x.length p.1 p.2,
          ringIdxN x.length p.1 (if p.2 + 1 = x.length then 0 else p.2 + 1))) := by
    have h0 : falseList.eval x =
        (ringPositions.eval x).map fun p ↦ falseTripCode.eval (envCode.eval x, p) := rfl
    rw [h0, envCode_eval]
    refine List.map_congr_left fun p _ ↦ ?_
    have hp : falseTripCode.eval ((vsOf x, x.length), p) =
        (extIdxN x.length p.1 p.2 1,
          (ringIdxN x.length p.1 p.2,
            ringIdxN x.length p.1
              (if decide (p.2 + 1 = x.length) = true then 0 else p.2 + 1))) := rfl
    rw [hp]
    by_cases hc : p.2 + 1 = x.length
    · rw [if_pos (decide_eq_true hc), if_pos hc]
    · rw [if_neg (by simp [hc]), if_neg hc]
  rw [h, ringPositions_eval]
  constructor
  · intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨h1, h2⟩ := (mem_cross_eval _ _ p).mp hp
    exact ⟨p.1, p.2, List.mem_range.mp h1, List.mem_range.mp h2, rfl⟩
  · rintro ⟨i, j, hi, hj, rfl⟩
    refine List.mem_map.mpr ⟨(i, j), ?_, rfl⟩
    exact (mem_cross_eval _ _ _).mpr ⟨List.mem_range.mpr hi, List.mem_range.mpr hj⟩

theorem mem_testList_eval (x : SatTy.denote) (t : ℕ × ℕ × ℕ) :
    t ∈ testList.eval x ↔ ∃ q ∈ x.zipIdx, ∃ p ∈ q.1,
      t = (extIdxN (decodeCNF x).length (varSlot (vsOf x) (litOf p).var).1 q.2
            (bitOf (litOf p).polarity),
        (testIdxN (vsOf x).length (decodeCNF x).length q.2,
          testIdxN (vsOf x).length (decodeCNF x).length q.2)) := by
  rw [length_decodeCNF]
  have h : testList.eval x = (x.zipIdx.map fun q ↦ q.1.map fun p ↦
      (extIdxN x.length (varSlot (vsOf x) (litOf p).var).1 q.2 (bitOf (litOf p).polarity),
        (testIdxN (vsOf x).length x.length q.2,
          testIdxN (vsOf x).length x.length q.2))).flatten := by
    have h0 : testList.eval x = (x.zipIdx.map fun q ↦ q.1.map fun p ↦
        litTripCode.eval ((envCode.eval x, q.2), p)).flatten := rfl
    rw [h0, envCode_eval]
    refine congrArg List.flatten (List.map_congr_left fun q _ ↦ ?_)
    refine List.map_congr_left fun p _ ↦ ?_
    have hlit : litTripCode.eval (((vsOf x, x.length), q.2), p) =
        (extIdxN x.length (slotOfCode.eval (vsOf x, p.1)) q.2 (bitOf p.2),
          (testIdxN (vsOf x).length x.length q.2,
            testIdxN (vsOf x).length x.length q.2)) := rfl
    rw [hlit, slotOfCode_eval]
    rfl
  rw [h, List.mem_flatten]
  constructor
  · rintro ⟨L, hL, hmem⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hL
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
    exact ⟨q, hq, p, hp, rfl⟩
  · rintro ⟨q, hq, p, hp, rfl⟩
    exact ⟨_, List.mem_map_of_mem hq, List.mem_map_of_mem hp⟩

theorem mem_junkList_eval (x : SatTy.denote) (t : ℕ × ℕ × ℕ) :
    t ∈ junkList.eval x ↔ ∃ j i w, j < (decodeCNF x).length ∧ i < (vsOf x).length ∧
      w < ((vsOf x).length + 1) * ((decodeCNF x).length * 2) ∧
      t = (w, (junkIdxN (vsOf x).length (decodeCNF x).length j i,
        junkIdxN (vsOf x).length (decodeCNF x).length j i)) := by
  rw [length_decodeCNF]
  have hsrc : ((Code.cross (σ := .pair .nat .nat) (τ := .nat)).eval
        ((Code.cross (σ := .nat) (τ := .nat)).eval (Code.indices.eval (clauseUnits.eval x),
            Code.indices.eval (varsCode.eval x)),
          Code.indices.eval (extElems.eval x))) =
      (Code.cross (σ := .pair .nat .nat) (τ := .nat)).eval
        ((Code.cross (σ := .nat) (τ := .nat)).eval
          (List.range x.length, List.range (vsOf x).length),
        List.range (((vsOf x).length + 1) * (x.length * 2))) := by
    rw [indices_eval, indices_eval, indices_eval, length_clauseUnits, length_extElems,
      varsCode_eval]
  have h : junkList.eval x =
      ((Code.cross (σ := .pair .nat .nat) (τ := .nat)).eval
        ((Code.cross (σ := .nat) (τ := .nat)).eval
          (List.range x.length, List.range (vsOf x).length),
        List.range (((vsOf x).length + 1) * (x.length * 2)))).map fun r ↦
          (r.2, (junkIdxN (vsOf x).length x.length r.1.1 r.1.2,
            junkIdxN (vsOf x).length x.length r.1.1 r.1.2)) := by
    have h0 : junkList.eval x = ((Code.cross (σ := .pair .nat .nat) (τ := .nat)).eval
        ((Code.cross (σ := .nat) (τ := .nat)).eval (Code.indices.eval (clauseUnits.eval x),
            Code.indices.eval (varsCode.eval x)),
          Code.indices.eval (extElems.eval x))).map fun r ↦
            junkTripCode.eval (envCode.eval x, r) := rfl
    rw [h0, hsrc, envCode_eval]
    rfl
  rw [h]
  constructor
  · intro hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    obtain ⟨h1, h2⟩ := (mem_cross_eval _ _ r).mp hr
    obtain ⟨h3, h4⟩ := (mem_cross_eval _ _ r.1).mp h1
    exact ⟨r.1.1, r.1.2, r.2, List.mem_range.mp h3, List.mem_range.mp h4,
      List.mem_range.mp h2, rfl⟩
  · rintro ⟨j, i, w, hj, hi, hw, rfl⟩
    refine List.mem_map.mpr ⟨((j, i), w), ?_, rfl⟩
    refine (mem_cross_eval _ _ _).mpr ⟨?_, List.mem_range.mpr hw⟩
    exact (mem_cross_eval _ _ _).mpr ⟨List.mem_range.mpr hj, List.mem_range.mpr hi⟩

/-! ## The coordinate bijections

Read off the block layouts. This is what `matching3D_iff_of_equiv` consumes. -/

/-- The external numbering, as a bijection onto the positions of the external
element list. Noncomputable only because `Numbering.equivFin` is: this is
proof-layer apparatus, not part of the certified program. -/
noncomputable def extEquivFin (n m : ℕ) : Ext n m ≃ Fin ((n + 1) * (m * 2)) :=
  (extNumbering n m).equivFin

theorem extEquivFin_val (n m : ℕ) (e : Ext n m) : ((extEquivFin n m e : Fin _) : ℕ) = extIdx e :=
  (extIdx_eq_num e).symm

/-- The internal numbering, as a bijection onto the positions of the internal
element list. -/
noncomputable def slotEquivFin (n m : ℕ) : Slot n m ≃ Fin ((n + 1) * m + (m + m * n)) :=
  (slotNumbering n m).equivFin

theorem slotEquivFin_val (n m : ℕ) (s : Slot n m) :
    ((slotEquivFin n m s : Fin _) : ℕ) = slotIdx s :=
  (slotIdx_eq_num s).symm

/-! ## The triple list is the triple set, numbered -/

/-- **The construction is faithfully realized**: the program's triple list
holds exactly the numberings of the mathematical layer's available triples. -/
theorem mem_triplesCode_eval (x : SatTy.denote) (t : ℕ × ℕ × ℕ) :
    t ∈ triplesCode.eval x ↔ ∃ T ∈ tripleSet (decodeCNF x) (vsOf x), tripIdx T = t := by
  have hsplit : t ∈ triplesCode.eval x ↔
      t ∈ trueList.eval x ∨ t ∈ falseList.eval x ∨
        t ∈ testList.eval x ∨ t ∈ junkList.eval x := by
    have h : triplesCode.eval x =
        trueList.eval x ++ (falseList.eval x ++ (testList.eval x ++ junkList.eval x)) := rfl
    rw [h, List.mem_append, List.mem_append, List.mem_append]
  rw [hsplit, mem_trueList_eval, mem_falseList_eval, mem_testList_eval, mem_junkList_eval,
    ← exists_occ_decodeCNF_iff (Q := fun l j ↦
      t = (extIdxN (decodeCNF x).length (varSlot (vsOf x) l.var).1 j (bitOf l.polarity),
        (testIdxN (vsOf x).length (decodeCNF x).length j,
          testIdxN (vsOf x).length (decodeCNF x).length j))) (x := x)]
  simp only [mem_tripleSet_iff]
  constructor
  · rintro (⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩ | ⟨o, ho⟩ |
      ⟨j, i, w, hj, hi, hw, rfl⟩)
    · exact ⟨trueTrip ⟨i, hi⟩ ⟨j, hj⟩, Or.inl ⟨_, _, rfl⟩, rfl⟩
    · refine ⟨falseTrip ⟨i, hi⟩ ⟨j, hj⟩, Or.inr (Or.inl ⟨_, _, rfl⟩), ?_⟩
      have hval : tripIdx (falseTrip (⟨i, hi⟩ : Fin ((vsOf x).length + 1))
            (⟨j, hj⟩ : Fin (decodeCNF x).length))
          = (extIdxN (decodeCNF x).length i j 1,
            (ringIdxN (decodeCNF x).length i j,
              ringIdxN (decodeCNF x).length i (next (⟨j, hj⟩ : Fin _)).1)) := rfl
      rw [hval, next_val]
    · exact ⟨testTrip (varSlot (vsOf x) ((decodeCNF x).occLit o).var) o.1
        ((decodeCNF x).occLit o).polarity, Or.inr (Or.inr (Or.inl ⟨o, rfl⟩)), ho.symm⟩
    · refine ⟨junkTrip (⟨j, hj⟩, ⟨i, hi⟩)
        ((extEquivFin (vsOf x).length (decodeCNF x).length).symm ⟨w, hw⟩),
        Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)), ?_⟩
      have hw' : extIdx ((extEquivFin (vsOf x).length (decodeCNF x).length).symm ⟨w, hw⟩) = w := by
        rw [← extEquivFin_val, Equiv.apply_symm_apply]
      have hval : tripIdx (junkTrip ((⟨j, hj⟩, ⟨i, hi⟩) :
            Fin (decodeCNF x).length × Fin (vsOf x).length)
              ((extEquivFin (vsOf x).length (decodeCNF x).length).symm ⟨w, hw⟩))
          = (extIdx ((extEquivFin (vsOf x).length (decodeCNF x).length).symm ⟨w, hw⟩),
            (junkIdxN (vsOf x).length (decodeCNF x).length j i,
              junkIdxN (vsOf x).length (decodeCNF x).length j i)) := rfl
      rw [hval, hw']
  · rintro ⟨T, (⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨o, rfl⟩ | ⟨q, w, rfl⟩), rfl⟩
    · exact Or.inl ⟨i.1, j.1, i.isLt, j.isLt, rfl⟩
    · refine Or.inr (Or.inl ⟨i.1, j.1, i.isLt, j.isLt, ?_⟩)
      have hval : tripIdx (falseTrip i j)
          = (extIdxN (decodeCNF x).length i.1 j.1 1,
            (ringIdxN (decodeCNF x).length i.1 j.1,
              ringIdxN (decodeCNF x).length i.1 (next j).1)) := rfl
      rw [hval, next_val]
    · exact Or.inr (Or.inr (Or.inl ⟨o, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨q.1.1, q.2.1, extIdx w, q.1.isLt, q.2.isLt,
        extIdx_lt w, rfl⟩))

/-! ## Correctness -/

/-- The bundled instance the mathematical layer's correctness theorem speaks
about: the tagged element types, and the triples of the three components. -/
def absInstance (x : SatTy.denote) : Matching3DInstance where
  W := Ext (vsOf x).length (decodeCNF x).length
  X := Slot (vsOf x).length (decodeCNF x).length
  Y := Slot (vsOf x).length (decodeCNF x).length
  triples := tripleSet (decodeCNF x) (vsOf x)

theorem satisfiable_iff_absInstance (x : SatTy.denote) :
    (decodeCNF x).Satisfiable ↔ MATCHING_3D (absInstance x) :=
  satisfiable_iff_exists_matching (decodeCNF x) (vsOf x) (mem_vsOf x)

end SatToMatching3DCode

open SatToMatching3DCode

/-- **The bridged reduction**: `satToMatching3DCode` is a correct
SAT → 3-DIMENSIONAL MATCHING reduction on concrete instances. Polynomial cost
and output size come from the generic theorem; correctness is the mathematical
layer's three-component theorem, transported along the two coordinate
bijections. -/
def satToMatching3DCertified :
    CertifiedReduction Concrete.SAT Concrete.MATCHING_3D where
  code := satToMatching3DCode
  correct x := by
    have hW : ((vsOf x).length + 1) * ((decodeCNF x).length * 2)
        = (satToMatching3DCode.eval x).1.length := by
      rw [length_decodeCNF]
      exact (length_extElems x).symm
    have hS : ((vsOf x).length + 1) * (decodeCNF x).length
          + ((decodeCNF x).length + (decodeCNF x).length * (vsOf x).length)
        = (satToMatching3DCode.eval x).2.1.length := by
      rw [length_decodeCNF]
      exact (length_slotElems x).symm
    refine (Concrete.sat_iff x).trans
      ((satisfiable_iff_absInstance x).trans
        (matching3D_iff_of_equiv
          ((extEquivFin _ _).trans (finCongr hW))
          ((slotEquivFin _ _).trans (finCongr hS))
          ((slotEquivFin _ _).trans (finCongr hS)) fun T ↦ ?_))
    refine Iff.trans ?_ (mem_decodeMatching3D_triples (satToMatching3DCode.eval x) _).symm
    -- the numbered triple in the goal is `tripIdx T` only up to the bridge lemmas,
    -- so the two are lined up propositionally (and by `exact`, not `rw`: the
    -- goal's equivs are typed at the decoded instance's coordinate types)
    refine Iff.trans ?_ (iff_of_eq (congrArg
      (fun u ↦ u ∈ (satToMatching3DCode.eval x).2.2.2) (?_ : tripIdx T = _)))
    · exact Iff.trans
        ⟨fun h ↦ ⟨T, h, rfl⟩, fun ⟨T', hT', heq⟩ ↦ tripIdx_inj heq ▸ hT'⟩
        (mem_triplesCode_eval x (tripIdx T)).symm
    · exact Prod.ext (extIdx_eq_num T.1)
        (Prod.ext (slotIdx_eq_num T.2.1) (slotIdx_eq_num T.2.2))

/-- Sanity check: the certified reduction projects to a plain reduction. -/
example : Concrete.SAT ⟶ᵣ Concrete.MATCHING_3D := satToMatching3DCertified.toReduction

/-- 3SAT → 3-DIMENSIONAL MATCHING, certified: weaken the source to SAT, then
run the construction — `sat3ToMatching3D` at the certificate level. -/
def sat3ToMatching3DCertified :
    CertifiedReduction Concrete.SAT3 Concrete.MATCHING_3D :=
  sat3ToSatCertified.comp satToMatching3DCertified

example : Concrete.SAT3 ⟶ᵣ Concrete.MATCHING_3D := sat3ToMatching3DCertified.toReduction

end Cert
end Hardness


