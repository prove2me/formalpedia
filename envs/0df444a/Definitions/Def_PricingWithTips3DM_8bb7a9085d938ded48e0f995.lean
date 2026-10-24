-- Prove2me | Definitions.Def_PricingWithTips3DM_8bb7a9085d938ded48e0f995
-- name    : PricingWithTips3DM_8bb7a9085d938ded48e0f995
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:33:41.853386+00:00
-- url     : https://prove2.me/theorems/255e1bf2-f33b-46b3-a12f-0bdc0ba1006d
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeCell
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130
import Definitions.Def_PricingWithTips3DM_3b6a88d9be5918e3cb96dca9
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Executable cell predicate for the fixed-shape SAT-to-3DM reduction. -/

namespace PricingWithTips.FixedShapeCell

open Hardness Hardness.Sat3dm Hardness.Cert
open SatToMatching3DCode
open PricingWithTips.FixedShape3DM

abbrev Triple := ℕ × ℕ × ℕ

def trueCell (input : List CLRS.Chapter34.CNFSym) (t : Triple) : Bool :=
  (List.range (input.length + 1)).any fun i =>
    (List.range input.length).any fun j =>
      decide (t = (extIdxN input.length i j 0,
        (ringIdxN input.length i j, ringIdxN input.length i j)))

def falseCell (input : List CLRS.Chapter34.CNFSym) (t : Triple) : Bool :=
  (List.range (input.length + 1)).any fun i =>
    (List.range input.length).any fun j =>
      decide (t = (extIdxN input.length i j 1,
        (ringIdxN input.length i j,
          ringIdxN input.length i
            (if j + 1 = input.length then 0 else j + 1))))

def testCell (input : List CLRS.Chapter34.CNFSym) (t : Triple) : Bool :=
  (paddedCNF input).zipIdx.any fun q => q.1.any fun l =>
    decide (t = (extIdxN input.length l.var q.2 (bitOf l.polarity),
      (testIdxN input.length input.length q.2,
        testIdxN input.length input.length q.2)))

def junkCell (input : List CLRS.Chapter34.CNFSym) (t : Triple) : Bool :=
  (List.range input.length).any fun j =>
    (List.range input.length).any fun i =>
      (List.range (dimension input)).any fun w =>
        decide (t = (w,
          (junkIdxN input.length input.length j i,
            junkIdxN input.length input.length j i)))

def cell (input : List CLRS.Chapter34.CNFSym) (t : Triple) : Bool :=
  trueCell input t ||
    (falseCell input t || (testCell input t || junkCell input t))

theorem varSlot_range_val {L v : ℕ} (hv : v < L) :
    (varSlot (List.range L) v).1 = v := by
  have hmem : v ∈ List.range L := List.mem_range.mpr hv
  rw [varSlot_val_of_mem hmem]
  have hi : (List.range L).idxOf v < (List.range L).length :=
    List.idxOf_lt_length_of_mem hmem
  have hget := List.getElem_idxOf hi
  have hrange := List.getElem_range (j := (List.range L).idxOf v)
    (n := L) hi
  omega

theorem trueCell_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    trueCell input t = true ↔
      ∃ i j, i < input.length + 1 ∧ j < input.length ∧
        t = (extIdxN input.length i j 0,
          (ringIdxN input.length i j, ringIdxN input.length i j)) := by
  simp [trueCell, List.any_eq_true]

theorem falseCell_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    falseCell input t = true ↔
      ∃ i j, i < input.length + 1 ∧ j < input.length ∧
        t = (extIdxN input.length i j 1,
          (ringIdxN input.length i j,
            ringIdxN input.length i
              (if j + 1 = input.length then 0 else j + 1))) := by
  simp [falseCell, List.any_eq_true]

theorem testCell_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    testCell input t = true ↔
      ∃ q ∈ (paddedCNF input).zipIdx, ∃ l ∈ q.1,
        t = (extIdxN input.length l.var q.2 (bitOf l.polarity),
          (testIdxN input.length input.length q.2,
            testIdxN input.length input.length q.2)) := by
  simp [testCell, List.any_eq_true]

theorem junkCell_iff (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    junkCell input t = true ↔
      ∃ j i w, j < input.length ∧ i < input.length ∧
        w < dimension input ∧
        t = (w, (junkIdxN input.length input.length j i,
          junkIdxN input.length input.length j i)) := by
  simp [junkCell, List.any_eq_true]

def numericTriples (input : List CLRS.Chapter34.CNFSym) : Finset Triple :=
  (triples input).image SatToMatching3DCode.tripIdx

def valTriple {n : ℕ} (t : ThreeDMTriple n) : Triple :=
  (t.1.1, t.2.1.1, t.2.2.1)

theorem normalized_mem_iff_numeric
    (input : List CLRS.Chapter34.CNFSym)
    (t : ThreeDMTriple (dimension input)) :
    t ∈ normalizedTriples input ↔ valTriple t ∈ numericTriples input := by
  constructor
  · intro ht
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp ht
    refine Finset.mem_image.mpr ⟨u, hu, ?_⟩
    subst t
    rfl
  · intro ht
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp ht
    refine Finset.mem_image.mpr ⟨u, hu, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hut
    · apply Prod.ext <;> apply Fin.ext
      · exact congrArg (fun z => z.2.1) hut
      · exact congrArg (fun z => z.2.2) hut

theorem cell_iff_numeric (input : List CLRS.Chapter34.CNFSym) (t : Triple) :
    cell input t = true ↔ t ∈ numericTriples input := by
  simp only [cell, Bool.or_eq_true]
  constructor
  · intro hc
    rcases hc with ht | hf | hs | hj
    · obtain ⟨i, j, hi, hj, rfl⟩ := (trueCell_iff input t).mp ht
      let ii : Fin ((variableList input).length + 1) :=
        ⟨i, by simpa [variableList] using hi⟩
      let jj : Fin (paddedCNF input).length :=
        ⟨j, by simpa [paddedCNF_length] using hj⟩
      refine Finset.mem_image.mpr
        ⟨Sat3dm.trueTrip ii jj, Sat3dm.trueTrip_mem_tripleSet ii jj, ?_⟩
      simp [SatToMatching3DCode.tripIdx, SatToMatching3DCode.extIdx,
        SatToMatching3DCode.slotIdx, Sat3dm.trueTrip, ii, jj,
        SatToMatching3DCode.bitOf, variableList, paddedCNF_length]
    · obtain ⟨i, j, hi, hj, rfl⟩ := (falseCell_iff input t).mp hf
      let ii : Fin ((variableList input).length + 1) :=
        ⟨i, by simpa [variableList] using hi⟩
      let jj : Fin (paddedCNF input).length :=
        ⟨j, by simpa [paddedCNF_length] using hj⟩
      refine Finset.mem_image.mpr
        ⟨Sat3dm.falseTrip ii jj, Sat3dm.falseTrip_mem_tripleSet ii jj, ?_⟩
      simp [SatToMatching3DCode.tripIdx, SatToMatching3DCode.extIdx,
        SatToMatching3DCode.slotIdx, Sat3dm.falseTrip, ii, jj,
        SatToMatching3DCode.bitOf, variableList, paddedCNF_length,
        Sat3dm.next_val]
    · obtain ⟨q, hq, l, hl, rfl⟩ := (testCell_iff input t).mp hs
      rw [List.mem_zipIdx_iff_getElem?] at hq
      obtain ⟨hjq, hqe⟩ := List.getElem?_eq_some_iff.mp hq
      have hj : q.2 < (paddedCNF input).length := by
        simpa [paddedCNF_length] using hjq
      have hl' : l ∈ (paddedCNF input)[q.2] := by simpa [hqe] using hl
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl'
      let o : (paddedCNF input).Occ := ⟨⟨q.2, hj⟩, ⟨k, hk⟩⟩
      have hvar : ((paddedCNF input).occLit o).var < input.length := by
        simpa [variableList] using
          variable_coverage input _ (List.getElem_mem hj) _
            ((paddedCNF input).occLit_mem o)
      have hvar' : (paddedCNF input)[q.2][k].var < input.length := by
        simpa [o, Hardness.CNF.occLit] using hvar
      refine Finset.mem_image.mpr
        ⟨Sat3dm.testTrip
            (varSlot (variableList input) ((paddedCNF input).occLit o).var)
            o.1 ((paddedCNF input).occLit o).polarity,
          Sat3dm.testTrip_mem_tripleSet o, ?_⟩
      simp [SatToMatching3DCode.tripIdx, SatToMatching3DCode.extIdx,
        SatToMatching3DCode.slotIdx, Sat3dm.testTrip, o,
        SatToMatching3DCode.bitOf, variableList, paddedCNF_length,
        Hardness.CNF.occLit]
      rw [varSlot_range_val hvar']
      rfl
    · obtain ⟨j, i, w, hjlt, hi, hw, rfl⟩ := (junkCell_iff input t).mp hj
      let jj : Fin (paddedCNF input).length :=
        ⟨j, by simpa [paddedCNF_length] using hjlt⟩
      let ii : Fin (variableList input).length :=
        ⟨i, by simpa [variableList] using hi⟩
      have hw' : w < ((variableList input).length + 1) *
          ((paddedCNF input).length * 2) := by
        simpa [dimension, variableList, paddedCNF_length] using hw
      let ww := (SatToMatching3DCode.extEquivFin _ _).symm ⟨w, hw'⟩
      refine Finset.mem_image.mpr
        ⟨Sat3dm.junkTrip (jj, ii) ww,
          Sat3dm.junkTrip_mem_tripleSet (jj, ii) ww, ?_⟩
      have hww : SatToMatching3DCode.extIdx ww = w := by
        rw [← SatToMatching3DCode.extEquivFin_val,
          Equiv.apply_symm_apply]
      simp [SatToMatching3DCode.tripIdx, SatToMatching3DCode.slotIdx,
        Sat3dm.junkTrip, jj, ii, variableList, paddedCNF_length]
      exact hww
  · intro hm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
    rcases (Sat3dm.mem_tripleSet_iff u).mp hu with
      ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨o, rfl⟩ | ⟨p, w, rfl⟩
    · exact Or.inl ((trueCell_iff input _).mpr ⟨i.1, j.1,
        by simpa [variableList] using i.isLt,
        by simpa [paddedCNF_length] using j.isLt, by
          simp [SatToMatching3DCode.tripIdx, SatToMatching3DCode.extIdx,
            SatToMatching3DCode.slotIdx, Sat3dm.trueTrip,
            SatToMatching3DCode.bitOf, variableList, paddedCNF_length]⟩)
    · exact Or.inr (Or.inl ((falseCell_iff input _).mpr ⟨i.1, j.1,
        by simpa [variableList] using i.isLt,
        by simpa [paddedCNF_length] using j.isLt, by
          simp [SatToMatching3DCode.tripIdx, SatToMatching3DCode.extIdx,
            SatToMatching3DCode.slotIdx, Sat3dm.falseTrip,
            SatToMatching3DCode.bitOf, variableList, paddedCNF_length,
            Sat3dm.next_val]⟩))
    · have hj : o.1.1 < input.length := by
        simpa [paddedCNF_length] using o.1.isLt
      have hvar : ((paddedCNF input).occLit o).var < input.length :=
        by simpa [variableList] using
          variable_coverage input _ (List.getElem_mem o.1.isLt) _
            ((paddedCNF input).occLit_mem o)
      let q := ((paddedCNF input)[o.1.1], o.1.1)
      have hq : q ∈ (paddedCNF input).zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?]
        exact List.getElem?_eq_getElem o.1.isLt
      exact Or.inr (Or.inr (Or.inl ((testCell_iff input _).mpr
        ⟨q, hq, (paddedCNF input).occLit o,
          (paddedCNF input).occLit_mem o, by
            simp [q, SatToMatching3DCode.tripIdx,
              SatToMatching3DCode.extIdx, SatToMatching3DCode.slotIdx,
              Sat3dm.testTrip, SatToMatching3DCode.bitOf,
              variableList, paddedCNF_length, varSlot_range_val hvar]
            rfl⟩)))
    · have hj : p.1.1 < input.length := by
        simpa [paddedCNF_length] using p.1.isLt
      have hi : p.2.1 < input.length := by
        simpa [variableList] using p.2.isLt
      have hw : SatToMatching3DCode.extIdx w < dimension input := by
        simpa [dimension, variableList, paddedCNF_length] using
          SatToMatching3DCode.extIdx_lt w
      exact Or.inr (Or.inr (Or.inr ((junkCell_iff input _).mpr
        ⟨p.1.1, p.2.1, SatToMatching3DCode.extIdx w, hj, hi, hw, by
          simp [SatToMatching3DCode.tripIdx, SatToMatching3DCode.slotIdx,
            Sat3dm.junkTrip, variableList, paddedCNF_length]⟩)))

theorem cell_eq_decide_normalized
    (input : List CLRS.Chapter34.CNFSym)
    (t : ThreeDMTriple (dimension input)) :
    cell input (valTriple t) = decide (t ∈ normalizedTriples input) := by
  apply Bool.eq_iff_iff.mpr
  rw [cell_iff_numeric, ← normalized_mem_iff_numeric]
  simp

end PricingWithTips.FixedShapeCell


