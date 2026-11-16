-- Prove2me | Definitions.Def_PolyhedralPacking1261_Packing_Supplement_Containers
-- name    : PolyhedralPacking1261_Packing_Supplement_Containers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:37:05.209959+00:00
-- url     : https://prove2.me/theorems/ffbc8fbb-0494-45d0-be13-a710933daa3f
-- title:
--   Bin and strip packing objectives and executions, and the metadata of a box repacking
-- statement:
--   This definition layer adds the two further objectives of §5 and the input of Lemma 15 to the base mission's computational model.
--
--   1. $\mathrm{Box}(\ell,u)=\{x:\ell_r\le x_r\le u_r\}$ is a closed axis-parallel box, $[0,1]^3$ the unit cube and $[0,1]^2\times[0,H]$ the closed strip container. An input has **coordinate widths at most $w$** when, in every piece, any two vertices differ by at most $w$ in every coordinate.
--   2. **Bin packing.** An output gives a bin count $N$, a bin index and a translation for every input position. It is feasible when every bin index is below $N$, every translated piece lies in $[0,1]^3$, and distinct pieces with the same bin index have disjoint interiors. $\mathrm{OPT}_{\mathrm{bin}}$ is the least feasible bin count.
--   3. **Strip packing.** An output gives a height $H\ge0$ and translations; it is feasible when every translated piece lies in $[0,1]^2\times[0,H]$ and distinct pieces have disjoint interiors. $\mathrm{OPT}_{\mathrm{strip}}$ is the infimum of feasible heights.
--   4. Bin and strip **executions** run finite scalar code of the base machine on the base vertex encoding and decode the final memory at fixed cells, charging one read per output cell.
--   5. **Repacking metadata.** Parameters $s,h$, finitely many host boxes, and for every object a host index, a coordinate bounding box and a translation. It is valid when $0<s\le1$, $h>0$, every bounding box has x- and y-widths at most $1-s$ and z-width at most $h$, and every translated bounding box lies in its host box. $V$ is the total volume of the host boxes. A repacking execution runs scalar code on the encoded metadata and decodes one translation per object.
--
--   Interiors are ambient (in $\mathbb R^3$), so boundary contact is allowed, exactly as in the base mission.
--
--   **Formalization Note** $\mathrm{OPT}_{\mathrm{bin}}$ is `sInf` over $\mathbb N$ and $\mathrm{OPT}_{\mathrm{strip}}$ is `sInf` over $\mathbb R$; on inputs with widths at most $1-\delta<1$ both feasible sets are nonempty (one piece per bin; pieces stacked in the strip) and the height set is bounded below by $0$, so neither infimum takes a default value.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, §5 bin and strip packing, PDF p.21 (printed p.20); Lemma 15, PDF p.19 (printed p.18)

import Definitions.Def_PolyhedralPacking1261_Packing_Execution
import Definitions.Def_PolyhedralPacking1261_Packing_Parallelepipeds

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- The closed axis-parallel box with lower corner `lo` and upper corner `hi`. -/
def closedBox (lo hi : Point3) : Set Point3 :=
  {x | ∀ r, lo r ≤ x r ∧ x r ≤ hi r}

/-- The closed unit cube `[0,1]³`. -/
def unitCube : Set Point3 :=
  {x | ∀ r, 0 ≤ x r ∧ x r ≤ 1}

/-- The closed strip container `[0,1]² × [0,H]`. -/
def stripContainer (H : ℝ) : Set Point3 :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ H}

/-- Every piece has every coordinate width at most `w`: the width of the convex hull
in coordinate `r` is the largest difference of two vertex coordinates. -/
def WidthsAtMost (w : ℝ) (K : PackingInput) : Prop :=
  ∀ vertices ∈ K, ∀ x ∈ vertices, ∀ y ∈ vertices, ∀ r : Fin 3, x r - y r ≤ w

/-! ### Translational bin packing -/

/-- A bin packing: a number of unit-cube bins, a bin index for every input position
and a translation for every input position. -/
structure BinOutput (n : ℕ) where
  count : ℕ
  bin : Fin n → ℕ
  translation : Fin n → Point3

/-- Each translated piece lies in `[0,1]³` (its own bin), every bin index is below the
bin count, and two distinct pieces in the same bin have disjoint ambient interiors. -/
def BinFeasible (K : PackingInput) (out : BinOutput K.length) : Prop :=
  (∀ i, out.bin i < out.count ∧
    shiftSet (out.translation i) (inputBody K i) ⊆ unitCube) ∧
  ∀ i j, i ≠ j → out.bin i = out.bin j →
    Disjoint (interior (shiftSet (out.translation i) (inputBody K i)))
      (interior (shiftSet (out.translation j) (inputBody K j)))

def feasibleBinCounts (K : PackingInput) : Set ℕ :=
  {N | ∃ out : BinOutput K.length, BinFeasible K out ∧ out.count = N}

/-- The least feasible number of bins (`OPT_bin`). On inputs whose widths are at most
one the set is nonempty (one piece per bin), so this is its minimum. -/
noncomputable def optimumBins (K : PackingInput) : ℕ :=
  sInf (feasibleBinCounts K)

/-! ### Translational strip packing -/

structure StripOutput (n : ℕ) where
  height : ℝ
  translation : Fin n → Point3

/-- A strip packing of height `H ≥ 0`: every translated piece lies in `[0,1]²×[0,H]`
and distinct pieces have disjoint ambient interiors. -/
def StripFeasible (K : PackingInput) (out : StripOutput K.length) : Prop :=
  0 ≤ out.height ∧
  (∀ i, shiftSet (out.translation i) (inputBody K i) ⊆ stripContainer out.height) ∧
  ∀ i j, i ≠ j →
    Disjoint (interior (shiftSet (out.translation i) (inputBody K i)))
      (interior (shiftSet (out.translation j) (inputBody K j)))

def feasibleHeights (K : PackingInput) : Set ℝ :=
  {H | ∃ out : StripOutput K.length, StripFeasible K out ∧ out.height = H}

/-- The infimum of feasible strip heights (`OPT_strip`). The set is bounded below by
`0` and, on inputs whose x- and y-widths are at most one, nonempty (stack the pieces). -/
noncomputable def optimumHeight (K : PackingInput) : ℝ :=
  sInf (feasibleHeights K)

/-- Execution of finite scalar code on the vertex input of the base mission, decoding a
bin packing: cell `0` is the bin count, cell `1+4i` the bin of piece `i`, cells
`2+4i, 3+4i, 4+4i` its translation. One scalar read is charged per output cell. -/
def BinExecution (program : ScalarProgram) (K : PackingInput) (time : ℕ)
    (out : BinOutput K.length) : Prop :=
  ∃ scalarTime finalState,
    ScalarExecution program (packingWords K) scalarTime finalState ∧
    finalState.memory 0 = (out.count : ℝ) ∧
    (∀ i : Fin K.length, finalState.memory (1 + 4 * i.val) = (out.bin i : ℝ)) ∧
    (∀ (i : Fin K.length) (r : Fin 3),
      finalState.memory (2 + 4 * i.val + r.val) = out.translation i r) ∧
    time = scalarTime + (1 + 4 * K.length)

/-- Execution decoding a strip packing: cell `0` is the height, cells
`1+3i, 2+3i, 3+3i` the translation of piece `i`. -/
def StripExecution (program : ScalarProgram) (K : PackingInput) (time : ℕ)
    (out : StripOutput K.length) : Prop :=
  ∃ scalarTime finalState,
    ScalarExecution program (packingWords K) scalarTime finalState ∧
    finalState.memory 0 = out.height ∧
    (∀ (i : Fin K.length) (r : Fin 3),
      finalState.memory (1 + 3 * i.val + r.val) = out.translation i r) ∧
    time = scalarTime + (1 + 3 * K.length)

/-! ### Repacking data (Lemma 15) -/

/-- Finite real metadata of a packing of objects into finitely many axis-parallel host
boxes: parameters `s, h`, the host boxes, and for every object its host box, a
coordinate bounding box (in the object's own coordinates) and its translation. -/
structure RepackInstance where
  s : ℝ
  h : ℝ
  boxCount : ℕ
  boxLower : Fin boxCount → Point3
  boxUpper : Fin boxCount → Point3
  objectCount : ℕ
  host : Fin objectCount → Fin boxCount
  bboxLower : Fin objectCount → Point3
  bboxUpper : Fin objectCount → Point3
  translation : Fin objectCount → Point3

/-- The scalar input: `s, h`, the box count, the box corners, the object count, and per
object its host index, bounding-box corners and translation. -/
def repackWords (I : RepackInstance) : List ℝ :=
  [I.s, I.h, (I.boxCount : ℝ)] ++
  (List.ofFn fun b => pointWords (I.boxLower b) ++ pointWords (I.boxUpper b)).flatten ++
  [(I.objectCount : ℝ)] ++
  (List.ofFn fun i => ((I.host i : ℕ) : ℝ) ::
    (pointWords (I.bboxLower i) ++ pointWords (I.bboxUpper i) ++
      pointWords (I.translation i))).flatten

/-- The hypotheses of Lemma 15 on the metadata: `0 < s ≤ 1`, `h > 0`, boxes with lower
corner below upper corner, bounding boxes with x- and y-widths at most `1 - s` and
z-width at most `h`, and every translated bounding box inside its host box. -/
def RepackInstance.Valid (I : RepackInstance) : Prop :=
  0 < I.s ∧ I.s ≤ 1 ∧ 0 < I.h ∧
  (∀ b r, I.boxLower b r ≤ I.boxUpper b r) ∧
  (∀ i r, I.bboxLower i r ≤ I.bboxUpper i r) ∧
  (∀ i, I.bboxUpper i 0 - I.bboxLower i 0 ≤ 1 - I.s ∧
    I.bboxUpper i 1 - I.bboxLower i 1 ≤ 1 - I.s ∧
    I.bboxUpper i 2 - I.bboxLower i 2 ≤ I.h) ∧
  (∀ i r, I.boxLower (I.host i) r ≤ I.bboxLower i r + I.translation i r ∧
    I.bboxUpper i r + I.translation i r ≤ I.boxUpper (I.host i) r)

/-- Total volume `V` of the host boxes. -/
def RepackInstance.totalVolume (I : RepackInstance) : ℝ :=
  ∑ b, ∏ r : Fin 3, (I.boxUpper b r - I.boxLower b r)

/-- Execution on the metadata; cells `3i, 3i+1, 3i+2` of the final memory are the new
translation of object `i`, one charged read per output cell. -/
def RepackExecution (program : ScalarProgram) (I : RepackInstance) (time : ℕ)
    (out : Fin I.objectCount → Point3) : Prop :=
  ∃ scalarTime finalState,
    ScalarExecution program (repackWords I) scalarTime finalState ∧
    (∀ (i : Fin I.objectCount) (r : Fin 3),
      finalState.memory (3 * i.val + r.val) = out i r) ∧
    time = scalarTime + 3 * I.objectCount

end PolyhedralPacking1261.Packing.Supplement


