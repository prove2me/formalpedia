-- Prove2me | Definitions.Def_PricingWithTips3DM_cab083267a7384abeae850b3
-- name    : PricingWithTips3DM_cab083267a7384abeae850b3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:04:59.764041+00:00
-- url     : https://prove2.me/theorems/a4d99525-49af-48af-94b4-b6525d1a3b6d
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeFalseEdgesTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_4e826b46f3c1a426fe602561
import Definitions.Def_PricingWithTips3DM_db4e278a2acaaf8b3ea05b7b
import Definitions.Def_PricingWithTips3DM_afa391945f44504e78ade3cb
import Definitions.Def_PricingWithTips3DM_1a1974f54f1a1e0128c37c0a
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Native sparse-edge generator for the false-ring family. -/

noncomputable section

namespace PricingWithTips.FixedShapeFalseEdgesTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing.PolyBuilder
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeBaselineTM2
open PricingWithTips.FixedShapeQueryStream

/-- Delete the first source symbol, so the runtime length is `L - 1`. -/
def dropFirstSpec : StatefulFlatMapSpec Bool CLRS.Chapter34.CNFSym
    CLRS.Chapter34.CNFSym where
  initial := false
  action
    | false, _ => ([], true)
    | true, symbol => ([symbol], true)
  finish _ := []

def dropFirst (input : List CLRS.Chapter34.CNFSym) :
    List CLRS.Chapter34.CNFSym :=
  rewriteStatefulFlatMap dropFirstSpec input

private theorem dropFirst_started (input : List CLRS.Chapter34.CNFSym) :
    rewriteStatefulFlatMapFrom dropFirstSpec true input = input := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      change symbol :: rewriteStatefulFlatMapFrom dropFirstSpec true input =
        symbol :: input
      rw [ih]

theorem dropFirst_eq_tail (input : List CLRS.Chapter34.CNFSym) :
    dropFirst input = input.tail := by
  cases input with
  | nil => rfl
  | cons symbol input =>
      change rewriteStatefulFlatMapFrom dropFirstSpec true input = input
      exact dropFirst_started input

noncomputable def dropFirst_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id dropFirst :=
  statefulFlatMap_computableInPolyTime dropFirstSpec

/-- Polynomials below are evaluated at `M = L - 1`; hence `sourceLength`
represents the original raw length `L` on every nonempty input. -/
def sourceLength : Polynomial Nat := Polynomial.X + 1
def sourceDimension : Polynomial Nat :=
  2 * sourceLength * (sourceLength + 1)
def falseStride : Polynomial Nat :=
  2 * sourceDimension ^ 2 + sourceDimension + 1
def outerStride : Polynomial Nat := sourceLength * falseStride
def outerCount : Polynomial Nat := Polynomial.X + 2

def nonwrapBase : Polynomial Nat := sourceDimension ^ 2 + 1
def nonwrapCount : Polynomial Nat := Polynomial.X

@[simp] theorem sourceLength_eval (m : Nat) :
    sourceLength.eval m = m + 1 := by simp [sourceLength]

@[simp] theorem sourceDimension_eval (m : Nat) :
    sourceDimension.eval m = 2 * (m + 1) * (m + 2) := by
  simp [sourceDimension]

@[simp] theorem falseStride_eval (m : Nat) :
    falseStride.eval m =
      2 * (2 * (m + 1) * (m + 2)) ^ 2 +
        2 * (m + 1) * (m + 2) + 1 := by
  simp [falseStride]

@[simp] theorem outerStride_eval (m : Nat) :
    outerStride.eval m =
      (m + 1) * (2 * (2 * (m + 1) * (m + 2)) ^ 2 +
        2 * (m + 1) * (m + 2) + 1) := by
  simp [outerStride]

@[simp] theorem outerCount_eval (m : Nat) :
    outerCount.eval m = m + 2 := by simp [outerCount]

@[simp] theorem nonwrapBase_eval (m : Nat) :
    nonwrapBase.eval m = (2 * (m + 1) * (m + 2)) ^ 2 + 1 := by
  simp [nonwrapBase]

@[simp] theorem nonwrapCount_eval (m : Nat) :
    nonwrapCount.eval m = m := by simp [nonwrapCount]

/-- For each variable index `i`, emit the runtime seed
`(firstOrdinal i, cellStride, numberOfNonwrapCells)`. -/
def nonwrapSeedFrames (tail : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    nonwrapBase falseStride nonwrapCount outerStride 0 0 outerCount tail

def descriptorForms : List AffineUnaryTripleForm :=
  [⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩,
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩,
    ⟨0, 0, 0, 1⟩]

def rowToSeed (row : Nat × Nat × Nat) : AffineUnaryTripleSeed :=
  ⟨row.1, row.2.1, row.2.2⟩

def nonwrapSeeds (tail : List CLRS.Chapter34.CNFSym) :
    List AffineUnaryTripleSeed :=
  (affineUnaryTripleProgressionRows
    (exactPolynomialAffineUnaryTripleProgression
      nonwrapBase falseStride nonwrapCount outerStride 0 0 outerCount tail)).map
      rowToSeed

theorem encode_seed_family_map
    (rows : List (Nat × Nat × Nat)) :
    encodeAffineUnaryTripleSeedFamily (rows.map rowToSeed) =
      rows.flatMap fun row =>
        encodeUnaryFrame (affineUnaryTripleRowValues row) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [encodeAffineUnaryTripleSeedFamily, rowToSeed,
        encodeAffineUnaryTripleSeed, affineUnaryTripleRowValues, ih]

theorem nonwrapSeedFrames_eq (tail : List CLRS.Chapter34.CNFSym) :
    nonwrapSeedFrames tail = encodeAffineUnaryTripleSeedFamily
      (nonwrapSeeds tail) := by
  simp [nonwrapSeedFrames, nonwrapSeeds,
    exactPolynomialAffineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionFrameStream, encode_seed_family_map]

def nonwrapSeedFunction (input : List CLRS.Chapter34.CNFSym) :
    List AffineUnaryTripleSeed := nonwrapSeeds (dropFirst input)

theorem nonwrapSeedFunction_cons (symbol : CLRS.Chapter34.CNFSym)
    (rest : List CLRS.Chapter34.CNFSym) :
    nonwrapSeedFunction (symbol :: rest) =
      List.ofFn fun i : Fin (outerCount.eval rest.length) =>
        (⟨nonwrapBase.eval rest.length + i.val * outerStride.eval rest.length,
          falseStride.eval rest.length,
          nonwrapCount.eval rest.length⟩ : AffineUnaryTripleSeed) := by
  unfold nonwrapSeedFunction nonwrapSeeds
  rw [dropFirst_eq_tail]
  simp only [List.tail_cons]
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  simp only [exactPolynomialAffineUnaryTripleProgression,
    Polynomial.eval_zero, Nat.mul_zero, Nat.add_zero]
  change (List.ofFn fun i : Fin (outerCount.eval rest.length) =>
      (nonwrapBase.eval rest.length + i.val * outerStride.eval rest.length,
        falseStride.eval rest.length,
        nonwrapCount.eval rest.length)).map rowToSeed = _
  rw [List.map_ofFn]
  rfl

theorem nonwrapSeedFunction_cons_range (symbol : CLRS.Chapter34.CNFSym)
    (rest : List CLRS.Chapter34.CNFSym) :
    nonwrapSeedFunction (symbol :: rest) =
      (List.range (outerCount.eval rest.length)).map fun i =>
        (⟨nonwrapBase.eval rest.length + i * outerStride.eval rest.length,
          falseStride.eval rest.length,
          nonwrapCount.eval rest.length⟩ : AffineUnaryTripleSeed) := by
  rw [nonwrapSeedFunction_cons, List.ofFn_eq_map]
  have h : (List.finRange (outerCount.eval rest.length)).map
      (fun index => index.val) =
      List.range (outerCount.eval rest.length) := by
    rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
    simp
  have hmap := congrArg
    (List.map fun i : Nat =>
      (⟨nonwrapBase.eval rest.length + i * outerStride.eval rest.length,
        falseStride.eval rest.length,
        nonwrapCount.eval rest.length⟩ : AffineUnaryTripleSeed)) h
  rw [List.map_map] at hmap
  change List.map
      ((fun i : Nat =>
        (⟨nonwrapBase.eval rest.length + i * outerStride.eval rest.length,
          falseStride.eval rest.length,
          nonwrapCount.eval rest.length⟩ : AffineUnaryTripleSeed)) ∘
        fun index : Fin (outerCount.eval rest.length) => index.val)
      (List.finRange (outerCount.eval rest.length)) = _
  exact hmap

def seedToProgression (seed : AffineUnaryTripleSeed) :
    AffineUnaryTripleProgression where
  base₁ := 0
  base₂ := 0
  base₃ := seed.first
  step₁ := 0
  step₂ := 0
  step₃ := seed.second
  count := seed.third

def nonwrapProgressions (input : List CLRS.Chapter34.CNFSym) :
    List AffineUnaryTripleProgression :=
  (nonwrapSeedFunction input).map seedToProgression

private theorem affine_map_descriptor (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap descriptorForms seed =
      [0, 0, seed.first, 0, 0, seed.second, seed.third] := by
  simp [affineUnaryTripleMap, descriptorForms,
    affineUnaryTripleFormValue]

theorem encode_progressions_eq_map (seeds : List AffineUnaryTripleSeed) :
    encodeAffineUnaryTripleProgressionFamily (seeds.map seedToProgression) =
      encodeUnaryFrame (affineUnaryTripleMapFamily descriptorForms seeds) := by
  induction seeds with
  | nil => rfl
  | cons seed seeds ih =>
      simp [encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, seedToProgression,
        affineUnaryTripleMapFamily, affine_map_descriptor, ih,
        encodeUnaryFrame]

noncomputable def nonwrapSeeds_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id encodeAffineUnaryTripleSeedFamily
      nonwrapSeedFunction := by
  let progression :=
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (Γ := CLRS.Chapter34.CNFSym)
      nonwrapBase falseStride nonwrapCount outerStride 0 0 outerCount
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    dropFirst_computableInPolyTime progression
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have h := machine.outputsFun input
        change Turing.TM2OutputsInTime machine.tm
          (List.map machine.inputAlphabet.symm input)
          (some (List.map machine.outputAlphabet.symm
            (nonwrapSeedFrames (dropFirst input))))
          (machine.time.eval input.length) at h
        rw [nonwrapSeedFrames_eq] at h
        exact h }

noncomputable def nonwrapDescriptors_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily nonwrapProgressions := by
  let mapped := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    nonwrapSeeds_computableInPolyTime
    (affineUnaryTripleMapFamily_computableInPolyTime descriptorForms)
  let machine := Classical.choice mapped
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have h := machine.outputsFun input
        simpa [Function.comp_def, nonwrapProgressions,
          encode_progressions_eq_map] using h }

def nonwrapOrdinalFrames (input : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream (nonwrapProgressions input)

def nonwrapOrdinals (input : List CLRS.Chapter34.CNFSym) : List Nat :=
  (nonwrapSeedFunction input).flatMap fun seed =>
    (List.range seed.third).map fun j => seed.first + j * seed.second

private theorem map_finRange_val (n : Nat) :
    (List.finRange n).map (fun index => index.val) = List.range n := by
  rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
  simp

theorem progression_seed_frames (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleProgressionFrameStream (seedToProgression seed) =
      (List.range seed.third).flatMap fun j =>
        encodeUnaryFrame [0, 0, seed.first + j * seed.second] := by
  simp [affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionRows_eq_ofFn, seedToProgression,
    affineUnaryTripleRowValues, List.ofFn_eq_map]
  have h := congrArg
    (List.flatMap fun j : Nat =>
      encodeUnaryFrame [0, 0, seed.first + j * seed.second])
    (map_finRange_val seed.third)
  simpa only [List.flatMap_map, Function.comp_apply] using h

theorem nonwrapOrdinalFrames_eq (input : List CLRS.Chapter34.CNFSym) :
    nonwrapOrdinalFrames input =
      (nonwrapOrdinals input).flatMap fun n => encodeUnaryFrame [0, 0, n] := by
  unfold nonwrapOrdinalFrames nonwrapProgressions nonwrapOrdinals
  induction nonwrapSeedFunction input with
  | nil => rfl
  | cons seed seeds ih =>
      simp [affineUnaryTripleProgressionFamilyFrameStream,
        progression_seed_frames, ih, List.flatMap_map]

noncomputable def nonwrapOrdinalFrames_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id nonwrapOrdinalFrames := by
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    nonwrapDescriptors_computableInPolyTime
    affineUnaryTripleProgressionFamilyFrameStream_computableInPolyTime
  change Turing.TM2ComputableInPolyTime id id
    (fun input => affineUnaryTripleProgressionFamilyFrameStream
      (nonwrapProgressions input))
  exact Classical.choice composed

def nonwrapEdgeStream (input : List CLRS.Chapter34.CNFSym) : List CliqueSym :=
  rewriteStatefulFlatMap formatSpec (nonwrapOrdinalFrames input)

def nonwrapEdges (input : List CLRS.Chapter34.CNFSym) : List (Nat × Nat) :=
  (nonwrapOrdinals input).map (0, ·)

theorem nonwrapEdgeStream_eq (input : List CLRS.Chapter34.CNFSym) :
    nonwrapEdgeStream input = (nonwrapEdges input).flatMap encodeCliqueEdge := by
  rw [nonwrapEdgeStream, nonwrapOrdinalFrames_eq, format_rows]
  simp [nonwrapEdges, List.flatMap_map]

noncomputable def nonwrapEdgeStream_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id nonwrapEdgeStream := by
  let formatter := statefulFlatMap_computableInPolyTime formatSpec
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    nonwrapOrdinalFrames_computableInPolyTime formatter
  change Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteStatefulFlatMap formatSpec
      (nonwrapOrdinalFrames input))
  exact Classical.choice composed

/-- At the unique wrap position of each ring, the ordinal base simplifies to
`(L-1) * (falseStride-1) + D^2`, which is subtraction-free when evaluated at
`M = L-1`. -/
def wrapBase : Polynomial Nat :=
  Polynomial.X * (2 * sourceDimension ^ 2 + sourceDimension) +
    sourceDimension ^ 2

@[simp] theorem wrapBase_eval (m : Nat) :
    wrapBase.eval m =
      m * (2 * (2 * (m + 1) * (m + 2)) ^ 2 +
        2 * (m + 1) * (m + 2)) +
      (2 * (m + 1) * (m + 2)) ^ 2 := by
  simp [wrapBase]

def wrapOrdinalFramesFromTail (tail : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    0 0 wrapBase 0 0 outerStride outerCount tail

def wrapSeed (tail : List CLRS.Chapter34.CNFSym) : AffineUnaryTripleSeed :=
  ⟨wrapBase.eval tail.length, outerStride.eval tail.length,
    outerCount.eval tail.length⟩

def wrapOrdinalFrames (input : List CLRS.Chapter34.CNFSym) :
    List UnaryFrameSym := wrapOrdinalFramesFromTail (dropFirst input)

def wrapOrdinals (input : List CLRS.Chapter34.CNFSym) : List Nat :=
  let seed := wrapSeed (dropFirst input)
  (List.range seed.third).map fun i => seed.first + i * seed.second

theorem wrapOrdinalFrames_eq (input : List CLRS.Chapter34.CNFSym) :
    wrapOrdinalFrames input =
      (wrapOrdinals input).flatMap fun n => encodeUnaryFrame [0, 0, n] := by
  have h := progression_seed_frames (wrapSeed (dropFirst input))
  simpa [wrapOrdinalFrames, wrapOrdinalFramesFromTail, wrapOrdinals,
    wrapSeed, seedToProgression,
    exactPolynomialAffineUnaryTripleProgressionFrameStream,
    exactPolynomialAffineUnaryTripleProgression, List.flatMap_map] using h

noncomputable def wrapOrdinalFrames_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id wrapOrdinalFrames := by
  let progression :=
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (Γ := CLRS.Chapter34.CNFSym)
      0 0 wrapBase 0 0 outerStride outerCount
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    dropFirst_computableInPolyTime progression
  change Turing.TM2ComputableInPolyTime id id
    (fun input => wrapOrdinalFramesFromTail (dropFirst input))
  exact Classical.choice composed

def wrapEdgeStream (input : List CLRS.Chapter34.CNFSym) : List CliqueSym :=
  rewriteStatefulFlatMap formatSpec (wrapOrdinalFrames input)

def wrapEdges (input : List CLRS.Chapter34.CNFSym) : List (Nat × Nat) :=
  (wrapOrdinals input).map (0, ·)

theorem wrapEdgeStream_eq (input : List CLRS.Chapter34.CNFSym) :
    wrapEdgeStream input = (wrapEdges input).flatMap encodeCliqueEdge := by
  rw [wrapEdgeStream, wrapOrdinalFrames_eq, format_rows]
  simp [wrapEdges, List.flatMap_map]

noncomputable def wrapEdgeStream_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id wrapEdgeStream := by
  let formatter := statefulFlatMap_computableInPolyTime formatSpec
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    wrapOrdinalFrames_computableInPolyTime formatter
  change Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteStatefulFlatMap formatSpec (wrapOrdinalFrames input))
  exact Classical.choice composed

def falseEdgeStream (input : List CLRS.Chapter34.CNFSym) : List CliqueSym :=
  nonwrapEdgeStream input ++ wrapEdgeStream input

def falseEdges (input : List CLRS.Chapter34.CNFSym) : List (Nat × Nat) :=
  nonwrapEdges input ++ wrapEdges input

theorem falseEdgeStream_eq (input : List CLRS.Chapter34.CNFSym) :
    falseEdgeStream input = (falseEdges input).flatMap encodeCliqueEdge := by
  rw [falseEdgeStream, nonwrapEdgeStream_eq, wrapEdgeStream_eq]
  simp [falseEdges]

theorem mem_falseEdges_cons_iff (symbol : CLRS.Chapter34.CNFSym)
    (rest : List CLRS.Chapter34.CNFSym) (edge : Nat × Nat) :
    edge ∈ falseEdges (symbol :: rest) ↔
      edge ∈ (PricingWithTips.FixedShapeSparseCells.falseTriples
        (symbol :: rest)).map (fun t =>
          (0, PricingWithTips.FixedShapeSparseCells.ordinal
            (dimension (symbol :: rest)) t)) := by
  rw [falseEdges]
  simp [nonwrapEdges, wrapEdges, nonwrapOrdinals,
    wrapOrdinals, nonwrapSeedFunction_cons_range, wrapSeed,
    dropFirst_eq_tail,
    PricingWithTips.FixedShapeSparseCells.falseTriples,
    PricingWithTips.FixedShapeSparseCells.ordinal,
    Hardness.Cert.SatToMatching3DCode.extIdxN,
    Hardness.Cert.SatToMatching3DCode.ringIdxN, dimension]
  constructor
  · intro h
    rcases h with hnonwrap | hwrap
    · rcases hnonwrap with ⟨i, hi, j, hj, hedge⟩
      refine ⟨i, by omega, j, by omega, ?_⟩
      rw [← hedge]
      simp [show j ≠ rest.length by omega]
      ring
    · rcases hwrap with ⟨i, hi, hedge⟩
      refine ⟨i, by omega, rest.length, by omega, ?_⟩
      rw [← hedge]
      simp
      ring
  · rintro ⟨i, hi, j, hj, hedge⟩
    by_cases hnonwrap : j < rest.length
    · left
      refine ⟨i, by omega, j, hnonwrap, ?_⟩
      rw [← hedge]
      simp [show j ≠ rest.length by omega]
      ring
    · right
      have hj_eq : j = rest.length := by omega
      subst j
      refine ⟨i, by omega, ?_⟩
      rw [← hedge]
      simp
      ring

theorem query_mem_falseEdges_iff
    (input : List CLRS.Chapter34.CNFSym)
    (t : PricingWithTips.FixedShapeCell.Triple)
    (hb : t.1 < dimension input) (hs : t.2.1 < dimension input)
    (hd : t.2.2 < dimension input) :
    (0, PricingWithTips.FixedShapeSparseCells.ordinal (dimension input) t) ∈
        falseEdges input ↔
      PricingWithTips.FixedShapeCell.falseCell input t = true := by
  cases input with
  | nil => simp [dimension] at hb
  | cons symbol rest =>
      rw [mem_falseEdges_cons_iff]
      constructor
      · intro he
        obtain ⟨u, hu, hedge⟩ := List.mem_map.mp he
        have hfu :=
          (PricingWithTips.FixedShapeSparseCells.mem_falseTriples_iff
            (symbol :: rest) u).mp hu
        have hcu : PricingWithTips.FixedShapeCell.cell (symbol :: rest) u = true := by
          simp [PricingWithTips.FixedShapeCell.cell, hfu]
        rcases PricingWithTips.FixedShapeOrdinal.cell_true_bounds
            (symbol :: rest) u hcu with ⟨hub, hus, hud⟩
        have hord : PricingWithTips.FixedShapeSparseCells.ordinal
              (dimension (symbol :: rest)) u =
            PricingWithTips.FixedShapeSparseCells.ordinal
              (dimension (symbol :: rest)) t := by
          exact congrArg Prod.snd hedge
        have hut := PricingWithTips.FixedShapeOrdinal.ordinal_injective_of_lt
          (dimension (symbol :: rest)) u t hus hud hs hd hord
        simpa [hut] using hfu
      · intro hft
        apply List.mem_map.mpr
        exact ⟨t,
          (PricingWithTips.FixedShapeSparseCells.mem_falseTriples_iff
            (symbol :: rest) t).mpr hft, rfl⟩
def cliquePairEncode : CliqueSym → UnaryFrameSym × UnaryFrameSym
  | .instanceMark => (.tick, .tick)
  | .certificateMark => (.tick, .separator)
  | .tick => (.tick, .frameEnd)
  | .fieldSep => (.separator, .tick)
  | .edgeMark => (.separator, .separator)
  | .vertexMark => (.separator, .frameEnd)
  | .pairSep => (.frameEnd, .tick)
  | .recordEnd => (.frameEnd, .separator)

def cliquePairDecode : UnaryFrameSym → UnaryFrameSym → CliqueSym
  | .tick, .tick => .instanceMark
  | .tick, .separator => .certificateMark
  | .tick, .frameEnd => .tick
  | .separator, .tick => .fieldSep
  | .separator, .separator => .edgeMark
  | .separator, .frameEnd => .vertexMark
  | .frameEnd, .tick => .pairSep
  | .frameEnd, .separator => .recordEnd
  | .frameEnd, .frameEnd => .recordEnd

@[simp] theorem cliquePair_leftInverse (symbol : CliqueSym) :
    cliquePairDecode (cliquePairEncode symbol).1
      (cliquePairEncode symbol).2 = symbol := by
  cases symbol <;> rfl

noncomputable def falseEdgeStream_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id falseEdgeStream := by
  exact fixedPairSameInputConcat_computableInPolyTime
    cliquePairEncode cliquePairDecode cliquePair_leftInverse
    nonwrapEdgeStream_computableInPolyTime wrapEdgeStream_computableInPolyTime

end PricingWithTips.FixedShapeFalseEdgesTM2


