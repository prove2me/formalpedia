-- Prove2me | Definitions.Def_PricingWithTips3DM_a93140320b2ce04366c96818
-- name    : PricingWithTips3DM_a93140320b2ce04366c96818
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:08:15.871988+00:00
-- url     : https://prove2.me/theorems/299762f6-c265-4b77-bcdc-5b70dfbf72f0
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeJunkEdgesTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_cab083267a7384abeae850b3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Native sparse-edge generator for the junk-triple family. -/

noncomputable section

namespace PricingWithTips.FixedShapeJunkEdgesTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing.PolyBuilder
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeQueryStream
open PricingWithTips.FixedShapeFalseEdgesTM2

def junkDimension : Polynomial Nat := 2 * Polynomial.X * (Polynomial.X + 1)
def junkSlotBase : Polynomial Nat :=
  Polynomial.X * (Polynomial.X + 1) + Polynomial.X
def junkOrdinalBase : Polynomial Nat :=
  junkSlotBase * (junkDimension + 1)
def junkOuterStep : Polynomial Nat := junkDimension + 1
def junkInnerStep : Polynomial Nat := junkDimension ^ 2
def junkInnerCount : Polynomial Nat := junkDimension
def junkOuterCount : Polynomial Nat := Polynomial.X ^ 2

@[simp] theorem junkDimension_eval (L : Nat) :
    junkDimension.eval L = 2 * L * (L + 1) := by simp [junkDimension]

@[simp] theorem junkSlotBase_eval (L : Nat) :
    junkSlotBase.eval L = L * (L + 1) + L := by simp [junkSlotBase]

@[simp] theorem junkOrdinalBase_eval (L : Nat) :
    junkOrdinalBase.eval L =
      (L * (L + 1) + L) * (2 * L * (L + 1) + 1) := by
  simp [junkOrdinalBase]

@[simp] theorem junkOuterStep_eval (L : Nat) :
    junkOuterStep.eval L = 2 * L * (L + 1) + 1 := by
  simp [junkOuterStep]

@[simp] theorem junkInnerStep_eval (L : Nat) :
    junkInnerStep.eval L = (2 * L * (L + 1)) ^ 2 := by
  simp [junkInnerStep]

@[simp] theorem junkInnerCount_eval (L : Nat) :
    junkInnerCount.eval L = 2 * L * (L + 1) := by
  simp [junkInnerCount]

@[simp] theorem junkOuterCount_eval (L : Nat) :
    junkOuterCount.eval L = L ^ 2 := by simp [junkOuterCount]

def junkSeedFrames (input : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    junkOrdinalBase junkInnerStep junkInnerCount junkOuterStep 0 0
      junkOuterCount input

def junkSeeds (input : List CLRS.Chapter34.CNFSym) :
    List AffineUnaryTripleSeed :=
  (affineUnaryTripleProgressionRows
    (exactPolynomialAffineUnaryTripleProgression
      junkOrdinalBase junkInnerStep junkInnerCount junkOuterStep 0 0
        junkOuterCount input)).map rowToSeed

private theorem map_finRange_val (n : Nat) :
    (List.finRange n).map (fun index => index.val) = List.range n := by
  rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
  simp

theorem junkSeeds_eq_range (input : List CLRS.Chapter34.CNFSym) :
    junkSeeds input =
      (List.range (input.length ^ 2)).map fun k =>
        (⟨(input.length * (input.length + 1) + input.length) *
              (2 * input.length * (input.length + 1) + 1) +
            k * (2 * input.length * (input.length + 1) + 1),
          (2 * input.length * (input.length + 1)) ^ 2,
          2 * input.length * (input.length + 1)⟩ : AffineUnaryTripleSeed) := by
  unfold junkSeeds
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  simp only [exactPolynomialAffineUnaryTripleProgression,
    Polynomial.eval_zero, Nat.mul_zero, Nat.add_zero]
  change (List.ofFn fun k : Fin (junkOuterCount.eval input.length) =>
      (junkOrdinalBase.eval input.length + k.val * junkOuterStep.eval input.length,
        junkInnerStep.eval input.length,
        junkInnerCount.eval input.length)).map rowToSeed = _
  rw [List.map_ofFn, List.ofFn_eq_map]
  have h := map_finRange_val (junkOuterCount.eval input.length)
  have hmap := congrArg
    (List.map fun k : Nat =>
      (⟨junkOrdinalBase.eval input.length + k * junkOuterStep.eval input.length,
        junkInnerStep.eval input.length,
        junkInnerCount.eval input.length⟩ : AffineUnaryTripleSeed)) h
  rw [List.map_map] at hmap
  change List.map
      ((fun k : Nat =>
        (⟨junkOrdinalBase.eval input.length + k * junkOuterStep.eval input.length,
          junkInnerStep.eval input.length,
          junkInnerCount.eval input.length⟩ : AffineUnaryTripleSeed)) ∘
        fun index : Fin (junkOuterCount.eval input.length) => index.val)
      (List.finRange (junkOuterCount.eval input.length)) = _
  simpa only [junkOrdinalBase_eval, junkOuterStep_eval,
    junkInnerStep_eval, junkInnerCount_eval, junkOuterCount_eval] using hmap

theorem junkSeedFrames_eq (input : List CLRS.Chapter34.CNFSym) :
    junkSeedFrames input = encodeAffineUnaryTripleSeedFamily (junkSeeds input) := by
  simp [junkSeedFrames, junkSeeds,
    exactPolynomialAffineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionFrameStream, encode_seed_family_map]

def junkProgressions (input : List CLRS.Chapter34.CNFSym) :
    List AffineUnaryTripleProgression := (junkSeeds input).map seedToProgression

noncomputable def junkSeeds_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id encodeAffineUnaryTripleSeedFamily
      junkSeeds := by
  let machine :=
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (Γ := CLRS.Chapter34.CNFSym)
      junkOrdinalBase junkInnerStep junkInnerCount junkOuterStep 0 0
        junkOuterCount
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have h := machine.outputsFun input
        change Turing.TM2OutputsInTime machine.tm
          (List.map machine.inputAlphabet.symm input)
          (some (List.map machine.outputAlphabet.symm (junkSeedFrames input)))
          (machine.time.eval input.length) at h
        rw [junkSeedFrames_eq] at h
        exact h }

noncomputable def junkDescriptors_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily junkProgressions := by
  let mapped := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    junkSeeds_computableInPolyTime
    (affineUnaryTripleMapFamily_computableInPolyTime descriptorForms)
  let machine := Classical.choice mapped
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have h := machine.outputsFun input
        simpa [Function.comp_def, junkProgressions,
          encode_progressions_eq_map] using h }

def junkOrdinalFrames (input : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream (junkProgressions input)

noncomputable def junkOrdinalFrames_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id junkOrdinalFrames := by
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    junkDescriptors_computableInPolyTime
    affineUnaryTripleProgressionFamilyFrameStream_computableInPolyTime
  change Turing.TM2ComputableInPolyTime id id
    (fun input => affineUnaryTripleProgressionFamilyFrameStream
      (junkProgressions input))
  exact Classical.choice composed

def junkOrdinals (input : List CLRS.Chapter34.CNFSym) : List Nat :=
  (junkSeeds input).flatMap fun seed =>
    (List.range seed.third).map fun w => seed.first + w * seed.second

theorem junkOrdinalFrames_eq (input : List CLRS.Chapter34.CNFSym) :
    junkOrdinalFrames input =
      (junkOrdinals input).flatMap fun n => encodeUnaryFrame [0, 0, n] := by
  unfold junkOrdinalFrames junkProgressions junkOrdinals
  induction junkSeeds input with
  | nil => rfl
  | cons seed seeds ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream,
        progression_seed_frames, ih, List.flatMap_map]

def junkEdges (input : List CLRS.Chapter34.CNFSym) : List (Nat × Nat) :=
  (junkOrdinals input).map (0, ·)

def junkEdgeStream (input : List CLRS.Chapter34.CNFSym) : List CliqueSym :=
  rewriteStatefulFlatMap formatSpec (junkOrdinalFrames input)

theorem junkEdgeStream_eq (input : List CLRS.Chapter34.CNFSym) :
    junkEdgeStream input = (junkEdges input).flatMap encodeCliqueEdge := by
  rw [junkEdgeStream, junkOrdinalFrames_eq, format_rows]
  simp [junkEdges, List.flatMap_map]

noncomputable def junkEdgeStream_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id junkEdgeStream := by
  let formatter := statefulFlatMap_computableInPolyTime formatSpec
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    junkOrdinalFrames_computableInPolyTime formatter
  change Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteStatefulFlatMap formatSpec (junkOrdinalFrames input))
  exact Classical.choice composed

theorem mem_junkEdges_iff (input : List CLRS.Chapter34.CNFSym)
    (edge : Nat × Nat) :
    edge ∈ junkEdges input ↔
      edge ∈ (PricingWithTips.FixedShapeSparseCells.junkTriples input).map
        (fun t => (0, PricingWithTips.FixedShapeSparseCells.ordinal
          (dimension input) t)) := by
  simp [junkEdges, junkOrdinals, junkSeeds_eq_range,
    PricingWithTips.FixedShapeSparseCells.junkTriples,
    PricingWithTips.FixedShapeSparseCells.ordinal,
    Hardness.Cert.SatToMatching3DCode.junkIdxN, dimension]
  constructor
  · rintro ⟨k, hk, w, hw, hedge⟩
    have hL : 0 < input.length := by nlinarith
    let j := k / input.length
    let i := k % input.length
    have hj : j < input.length := by
      rw [Nat.div_lt_iff_lt_mul hL]
      simpa [pow_two] using hk
    have hi : i < input.length := Nat.mod_lt _ hL
    have hw' : w < dimension input := by
      unfold dimension
      convert hw using 1 <;> ring
    refine ⟨w, j, i, ⟨hj, hi, hw'⟩, ?_⟩
    have hki : input.length * j + i = k := by
      simpa [j, i] using (Nat.div_add_mod k input.length)
    rw [← hedge]
    simp [hki]
    ring
  · rintro ⟨w, j, i, ⟨hj, hi, hw⟩, hedge⟩
    have hw' : w < 2 * input.length * (input.length + 1) := by
      convert hw using 1 <;> ring
    refine ⟨input.length * j + i, ?_, w, hw', ?_⟩
    · nlinarith
    · rw [← hedge]
      ring

theorem query_mem_junkEdges_iff
    (input : List CLRS.Chapter34.CNFSym)
    (t : PricingWithTips.FixedShapeCell.Triple)
    (hb : t.1 < dimension input) (hs : t.2.1 < dimension input)
    (hd : t.2.2 < dimension input) :
    (0, PricingWithTips.FixedShapeSparseCells.ordinal (dimension input) t) ∈
        junkEdges input ↔
      PricingWithTips.FixedShapeCell.junkCell input t = true := by
  rw [mem_junkEdges_iff]
  constructor
  · intro he
    obtain ⟨u, hu, hedge⟩ := List.mem_map.mp he
    have hju := (PricingWithTips.FixedShapeSparseCells.mem_junkTriples_iff
      input u).mp hu
    have hcu : PricingWithTips.FixedShapeCell.cell input u = true := by
      simp [PricingWithTips.FixedShapeCell.cell, hju]
    rcases PricingWithTips.FixedShapeOrdinal.cell_true_bounds input u hcu with
      ⟨hub, hus, hud⟩
    have hord : PricingWithTips.FixedShapeSparseCells.ordinal
          (dimension input) u =
        PricingWithTips.FixedShapeSparseCells.ordinal (dimension input) t := by
      exact congrArg Prod.snd hedge
    have hut := PricingWithTips.FixedShapeOrdinal.ordinal_injective_of_lt
      (dimension input) u t hus hud hs hd hord
    simpa [hut] using hju
  · intro hjt
    apply List.mem_map.mpr
    exact ⟨t, (PricingWithTips.FixedShapeSparseCells.mem_junkTriples_iff
      input t).mpr hjt, rfl⟩

end PricingWithTips.FixedShapeJunkEdgesTM2


