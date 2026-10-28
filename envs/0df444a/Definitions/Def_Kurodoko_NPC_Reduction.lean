-- Prove2me | Definitions.Def_Kurodoko_NPC_Reduction
-- name    : Kurodoko_NPC_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:59.813183+00:00
-- url     : https://prove2.me/theorems/a6d9661c-85c4-4a25-9dbf-9666dd0c18b8
-- title:
--   §4, Appendix A.1, pp. 695–701 — the gadgets, the board built from a formula, the ? values, the reduction, ports and gadget relations
-- statement:
--   This file transcribes the reduction of Kölker (2012) from one-in-three SAT to Kurodoko, following the Python program of Appendix A.1.
--
--   **Gadgets.** Nine $17\times17$ gadgets (Wire, Negation, Variable, Zero, Xor, Choice, Split, Sidesplit, Bend) are given by the strings of A.1. A cell is blank, a ray end `!` (never a clue), a clue `?` whose value is fixed later, or a digit clue. A gadget can be rotated a quarter turn counter-clockwise, $(r,c)\mapsto(16-c,r)$, and mirrored, $(r,c)\mapsto(r,16-c)$; the oriented gadgets of A.1 are built from these two operations.
--
--   **The board.** From a formula $F$ with $n$ literal occurrences and largest variable multiplicity $k$, the program computes
--   1. the sorted list of variables and, for each, its variable component (a Variable gadget, Sidesplits, Wires and a Bend fanning its value out once per occurrence);
--   2. an odd-even transposition sorting network that routes the outputs to the clause slots, with one layer of Xor/Sidesplit/Split swaps and Wires per round, stopping once sorted;
--   3. one clause component per clause: Bend, Wire, Choice, Wire, Bend on top, and a Wire or a Negation below each literal.
--
--   With $L$ layers, the board has $16(2n-1)+1$ columns and $16(k+2L+2)+1$ rows; the gadget at gadget row $R$ and column $C$ covers the board rows $16R,\dots,16R+16$ and columns $16C,\dots,16C+16$, so neighbours share one row or column.
--
--   **The ? values.** A `?` square gets the value $1$ plus the number of squares passed over in the four directions before the first `!`.
--
--   **The reduction.** The instance $K(F)=(w,h,\text{clues})$ lists every digit clue and every `?` square, with its value, in row-major order. On words, the code of a formula whose clauses all have three literals is mapped to the code of $K(F)$, and every other word to the code of an unsolvable instance.
--
--   **Ports and gadget relations.** The eight marked squares $n_i,n_o,w_i,w_o,e_i,e_o,s_i,s_o$ of a gadget (Fig. 1) lie at $(1,8),(2,8),(8,1),(8,2),(8,15),(8,14),(15,8),(14,8)$ and move with the gadget. With black read as $1$, the relations of §4.1 are: Wire $n_o=s_i$; Negation $n_o=1-s_i$; Variable no constraint; Zero $n_o=0$; Choice $w_i+s_i+e_i=1$; Split $w_o=e_o=s_i$; Bend $e_o=s_i$; the Xor string draws $X^2$, with $s_o=w_i\oplus e_i$; the Sidesplit string draws $S^+$, with $e_o=s_o=w_i$.
--
--   These objects are the subject of Lemma 1, the gadget claim of §4.1, and Theorems 4 and 5.
--
--   **Formalization Note** Two slips of the printed program are corrected: occurrences are keyed by the variable rather than the signed literal (the printed program raises an error on every negated literal), and `tee_l` is `rotate ltee` rather than `rotate (flip ltee)` (with the printed orientation the formula $(x\lor x\lor x)$, which has no one-in-three assignment, produces a solvable board). The empty formula, on which the program fails, is sent to the solvable instance $(1,1,[])$. Where gadgets overlap the last one written wins; the program asserts that overlapping cells agree. The `?` walks carry fuel $w+h$ and stop at the board edge. A digit pair `44` in the strings is two clues 4, 4, as the program reads it.
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), pp. 695–699 (PDF 2–6), §4.1–4.4 (gadgets, Fig. 1, components, ? values); pp. 700–702 (PDF 7–9), Appendix A.1, the program (lines 11–287)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-! # The reduction from one-in-three SAT to Kurodoko (Kölker 2012, §4 and Appendix A.1)

A transcription of the Python program of Appendix A.1 (pp. 700–702), with two corrections:
occurrences are keyed by the variable, not by the signed literal (`count_vars`,
`make_sorting_network`), and `tee_l` is `rotate ltee` (not `rotate (flip ltee)`). The empty
formula, on which the program fails, is sent to a fixed solvable instance. -/

/-- The content of a square of a gadget: blank, `!` (the end of a ray, never a clue), `?` (a
clue whose value is fixed after the board is assembled), or a clue with the value `n`. -/
inductive GCell where
  | blank
  | bang
  | qmark
  | clue (n : ℕ)
  deriving DecidableEq, Repr

/-- The cells produced by one character of a gadget string (`unpack`, A.1 lines 11–27): a lower
case letter skips `1 + (its distance from 'a')` blank cells, `!` and `?` are one cell each, and a
digit is one clue cell with that value. -/
def decodeChar (ch : Char) : List GCell :=
  if ch.isLower then List.replicate (1 + (ch.toNat - 'a'.toNat)) GCell.blank
  else if ch = '!' then [GCell.bang]
  else if ch = '?' then [GCell.qmark]
  else if ch.isDigit then [GCell.clue (ch.toNat - '0'.toNat)]
  else []

/-- A gadget: a 17 × 17 square of cells, indexed by (row, column). -/
abbrev Gadget : Type := Fin 17 → Fin 17 → GCell

/-- `unpack`: the gadget given by a stream (the part of an A.1 gadget string after `17x17:`,
spaces removed), read in row-major order. -/
def unpack (s : String) : Gadget :=
  fun r c => (s.toList.flatMap decodeChar).getD (17 * r.val + c.val) GCell.blank

/-- `rotate` (A.1 lines 29–35): `new[16 − c][r] = old[r][c]`, a counter-clockwise quarter turn. -/
def rotate (g : Gadget) : Gadget := fun r c => g c (Fin.rev r)

/-- `flip` (A.1 lines 37–43): `new[r][16 − c] = old[r][c]`, a mirror image left to right. -/
def flip (g : Gadget) : Gadget := fun r c => g r (Fin.rev c)

/-- The nine gadget strings of A.1 (lines 47–84). -/
inductive BaseGadget where
  | wire
  | neg
  | var
  | zero
  | xor
  | choice
  | tee
  | ltee
  | bend
  deriving DecidableEq, Repr

/-- The streams of the nine gadget strings of A.1 (lines 52–83), after `17x17:` and with the
spaces removed (A.1 line 85). -/
def BaseGadget.stream : BaseGadget → String
  | .wire => "e!?!2!?!eqqe!?!2!?!eqqe!?!2!?!eqqqd!2?!3!?2!dqqe!?!2!?!eqqe!?!2!?!e"
  | .neg => "e!?!2!?!eqqe!?!2!?!eqqe!?!2!?!eqqqe!?!2!?!eqqe!?!2!?!eqqe!?!2!?!e"
  | .var => "e!?!2!?!eqqd3!?!2!?!3dd3a!c!a3dqqqqqqqqqqqq"
  | .zero => "e!?!2!?!eqqd3!?!2!?!3dd3a!c!a3dh7hqqqqqqqqqqq"
  | .xor =>
    "qqqqc!d!d!c!b2d2d2b!?b?d?d?b?!b!d!d!b!2b4d3d4b2!b!i!b!?b?!g!?b?!b44a!c!a44b!c!i!cd!2?!3!?2!dqqe!?!2!?!e"
  | .choice =>
    "qqqqc!i!c!b2d!d2b!?b?d?d?b?!b!d!d!b!2b4d2d4b2!b!i!b!?b?!g!?b?!b44a!c!a44b!c!i!cd!2?!4!?2!dqqe!?!2!?!e"
  | .tee =>
    "qqqqq!b!b!c!b!b!?b?b?c?b?b?!b!b!c!b!b!2b2b2c2b2b2!b!d4d!b!?b?!g!?b?!b44a!c!a44b!c!i!cd!2?!3!?2!dqqe!?!2!?!e"
  | .ltee =>
    "qqqqc!f!f!b2b4c3b!b!?b?a!2!b?b?b?!b!b!c!b!b!2b2b3c2b2b2!b!d4d!b!?b?!g!?b?!b44a!c!a44b!c!i!cd!2?!2!?2!dqqe!?!2!?!e"
  | .bend =>
    "qqqqj!fj2b!b!e2!c?b?b?j!b!b!j2b2b2e4b4a!b!b!l!?b?d3a!c!a44b!m!cd!2?!3!?2!dqqe!?!2!?!e"

/-- The gadget drawn by a gadget string. -/
def BaseGadget.cells (b : BaseGadget) : Gadget := unpack b.stream

/-- The two operations used to orient a gadget. -/
inductive Op where
  | rotate
  | flip
  deriving DecidableEq, Repr

/-- Apply an operation to a gadget. -/
def Op.apply : Op → Gadget → Gadget
  | .rotate => Kurodoko.NPC.rotate
  | .flip => Kurodoko.NPC.flip

/-- Where an operation moves the square `(r, c)` of a gadget: `rotate` sends it to `(16 − c, r)`,
`flip` to `(r, 16 − c)`. -/
def Op.move : Op → Fin 17 × Fin 17 → Fin 17 × Fin 17
  | .rotate => fun p => (Fin.rev p.2, p.1)
  | .flip => fun p => (p.1, Fin.rev p.2)

/-- An oriented gadget: a gadget string and the operations applied to it, first to last. -/
structure OGadget where
  base : BaseGadget
  ops : List Op
  deriving DecidableEq, Repr

/-- The cells of an oriented gadget. -/
def OGadget.cells (g : OGadget) : Gadget :=
  g.ops.foldl (fun acc op => op.apply acc) g.base.cells

/-- Where the square `p` of the gadget string ends up in the oriented gadget. -/
def OGadget.pos (g : OGadget) (p : Fin 17 × Fin 17) : Fin 17 × Fin 17 :=
  g.ops.foldl (fun q op => op.move q) p

/-- The cell at position `(i, j)` of an oriented gadget, blank outside the 17 × 17 square. -/
def OGadget.cellAt (g : OGadget) (i j : ℕ) : GCell :=
  if h : i < 17 ∧ j < 17 then g.cells ⟨i, h.1⟩ ⟨j, h.2⟩ else GCell.blank

/-! The oriented gadgets of A.1 lines 88–107 (with `tee_l = rotate ltee`). -/

/-- `bend_dr = bend`. -/
def bendDR : OGadget := ⟨.bend, []⟩
/-- `bend_dl = flip bend_dr`. -/
def bendDL : OGadget := ⟨.bend, [.flip]⟩
/-- `bend_lu = rotate (rotate bend_dr)`. -/
def bendLU : OGadget := ⟨.bend, [.rotate, .rotate]⟩
/-- `tee_d = tee`. -/
def teeD : OGadget := ⟨.tee, []⟩
/-- `tee_l = rotate ltee` (corrected; the printed program has `rotate (flip ltee)`). -/
def teeL : OGadget := ⟨.ltee, [.rotate]⟩
/-- `tee_r = flip tee_l`. -/
def teeR : OGadget := ⟨.ltee, [.rotate, .flip]⟩
/-- `xor_r = rotate xor`. -/
def xorR : OGadget := ⟨.xor, [.rotate]⟩
/-- `xor_d = rotate xor_r`. -/
def xorD : OGadget := ⟨.xor, [.rotate, .rotate]⟩
/-- `xor_l = rotate xor_d`. -/
def xorL : OGadget := ⟨.xor, [.rotate, .rotate, .rotate]⟩
/-- `wire_up = wire`. -/
def wireUp : OGadget := ⟨.wire, []⟩
/-- `wire_right = rotate wire_up`. -/
def wireRight : OGadget := ⟨.wire, [.rotate]⟩
/-- `wire_left = flip wire_right`. -/
def wireLeft : OGadget := ⟨.wire, [.rotate, .flip]⟩
/-- `gchoice = choice`. -/
def gChoice : OGadget := ⟨.choice, []⟩
/-- `gwnot = neg`. -/
def gWNot : OGadget := ⟨.neg, []⟩
/-- `gzero = zero`. -/
def gZero : OGadget := ⟨.zero, []⟩
/-- `variable = var`. -/
def gVariable : OGadget := ⟨.var, []⟩

/-- A placement `(R, C, g)`: the oriented gadget `g` soldered at gadget row `R` and gadget column
`C`, covering board rows `16R, …, 16R + 16` and columns `16C, …, 16C + 16`. -/
abbrev Placement : Type := ℕ × ℕ × OGadget

/-! ## The data of the formula -/

/-- The variables occurring in `F`, in increasing order (`sorted(counts.keys())`). -/
def vars (F : CNF) : List ℕ :=
  ((F.flatten.map Prod.snd).dedup).mergeSort (fun a b => decide (a ≤ b))

/-- The number of occurrences of the variable `x` in `F`, of either sign (`count_vars`, keyed by
the variable). -/
def counts (F : CNF) (x : ℕ) : ℕ := (F.flatten.filter fun ℓ => decide (ℓ.2 = x)).length

/-- The largest number of occurrences of a variable (`k = max(counts.values())`, 0 if none). -/
def maxCount (F : CNF) : ℕ := (vars F).foldr (fun x m => max (counts F x) m) 0

/-- The terminals: the variable of every literal occurrence, clause by clause. Terminal `i`
belongs to clause `i / 3`, slot `i % 3`, when all clauses have three literals. -/
def terminals (F : CNF) : List ℕ := F.flatten.map Prod.snd

/-- `goals x`: the indices of the terminals with the variable `x`, in increasing order. -/
def goals (F : CNF) (x : ℕ) : List ℕ :=
  (List.range (terminals F).length).filter fun i => decide ((terminals F).getD i 0 = x)

/-- `wires`: for each variable in increasing order, its goal indices (the outputs of the variable
components, left to right, labelled by their target terminal). -/
def wires (F : CNF) : List ℕ := (vars F).flatMap fun x => ((goals F x).take (counts F x))

/-! ## The odd-even transposition network (`make_sorting_network`, A.1 lines 257–279) -/

/-- One pass over consecutive pairs: a pair `a, b` with `a > b` is swapped and marked `1, 0`,
otherwise marked `0, 0`; a final single element is marked `0`. Returns the row and the new wires. -/
def pairPass : List ℕ → List ℕ × List ℕ
  | a :: b :: rest =>
    let p := pairPass rest
    if b < a then (1 :: 0 :: p.1, b :: a :: p.2) else (0 :: 0 :: p.1, a :: b :: p.2)
  | [a] => ([0], [a])
  | [] => ([], [])

/-- Layer `i` of the network: pairs start at position `i % 2`; at odd `i` the first wire is passed
through and marked `0`. -/
def transpositionStep (i : ℕ) (ws : List ℕ) : List ℕ × List ℕ :=
  if i % 2 = 0 then pairPass ws
  else
    match ws with
    | [] => ([], [])
    | a :: rest => let p := pairPass rest; (0 :: p.1, a :: p.2)

/-- Layers `i, i + 1, …` (at most `fuel` of them), stopping as soon as the wires are sorted. -/
def sortingNetworkAux : ℕ → ℕ → List ℕ → List (List ℕ)
  | 0, _, _ => []
  | fuel + 1, i, ws =>
    if ws.Pairwise (· ≤ ·) then []
    else
      let p := transpositionStep i ws
      p.1 :: sortingNetworkAux fuel (i + 1) p.2

/-- The sorting network: one row per layer; entry `j` of a row is `1` iff wires `j` and `j + 1`
are swapped in that layer. -/
def sortingNetwork (F : CNF) : List (List ℕ) :=
  sortingNetworkAux (wires F).length 0 (wires F)

/-! ## The board size (`compute_gadget_count`, A.1 lines 281–287) -/

/-- The number of gadget columns, `2n − 1`, with `n` the number of literal occurrences. -/
def gadgetCols (F : CNF) : ℕ := 2 * F.flatten.length - 1

/-- The number of gadget rows, `k + 2·(number of layers) + 2`. -/
def gadgetRows (F : CNF) : ℕ := maxCount F + 2 * (sortingNetwork F).length + 2

/-- The board width (number of columns), `16·(gadget columns) + 1`. -/
def boardW (F : CNF) : ℕ := 16 * gadgetCols F + 1

/-- The board height (number of rows), `16·(gadget rows) + 1`. -/
def boardH (F : CNF) : ℕ := 16 * gadgetRows F + 1

/-! ## The placements -/

/-- The variable component of a variable with `nv` occurrences, its left column at `c`
(`add_variables`, A.1 lines 158–171), with `r = (gadget rows) − k`. -/
def variableComponent (r c nv : ℕ) : List Placement :=
  ((List.range (nv - 1)).flatMap fun i =>
      [(r + i, c, teeL), (r + i, c + 1, wireRight)] ++
      ((List.range i).flatMap fun j' =>
        [(r + i, c + 2 * (j' + 1), wireRight), (r + i, c + 2 * (j' + 1) + 1, wireRight)]) ++
      [(r + i, c + 2 * i + 2, bendLU)] ++
      ((List.range (nv - (i + 2))).map fun j' => (r + i, c + 2 * (i + 2 + j'), wireUp))) ++
    [(r + (nv - 1), c, gVariable)]

/-- The variable components, left to right, the next one `2·(occurrences)` columns further. -/
def addVariablesAux (r : ℕ) (cnt : ℕ → ℕ) : List ℕ → ℕ → List Placement
  | [], _ => []
  | x :: xs, c => variableComponent r c (cnt x) ++ addVariablesAux r cnt xs (c + 2 * cnt x)

/-- `add_variables` (A.1 lines 154–174). -/
def addVariables (F : CNF) : List Placement :=
  addVariablesAux (gadgetRows F - maxCount F) (counts F) (vars F) 0

/-- `swap(r, c)` (A.1 lines 178–185), with `br = base − 2r`, `bc = 2c`. -/
def swapPlacements (base r c : ℕ) : List Placement :=
  let br := base - 2 * r
  let bc := 2 * c
  [(br, bc, teeL), (br, bc + 1, xorD), (br, bc + 2, teeR),
    (br - 1, bc, xorR), (br - 1, bc + 1, teeD), (br - 1, bc + 2, xorL)]

/-- `mkwire(r, c)` (A.1 lines 187–190). -/
def wirePlacements (base r c : ℕ) : List Placement :=
  [(base - 2 * r, 2 * c, wireUp), (base - (2 * r + 1), 2 * c, wireUp)]

/-- `add_sorting_network` (A.1 lines 176–196), with `base = (gadget rows) − 1 − k`: a swap where
the row has `1`, a wire at position `j` when `j = 0` or position `j − 1` has `0`. -/
def addSortingNetwork (F : CNF) : List Placement :=
  let base := gadgetRows F - 1 - maxCount F
  let net := sortingNetwork F
  (List.range net.length).flatMap fun i =>
    let row := net.getD i []
    (List.range row.length).flatMap fun j =>
      if row.getD j 0 ≠ 0 then swapPlacements base i j
      else if j = 0 ∨ row.getD (j - 1) 0 = 0 then wirePlacements base i j
      else []

/-- `add_clauses` (A.1 lines 198–215): for clause `i`, the top row
`bend_dr, wire_right, gchoice, wire_left, bend_dl` at columns `6i, …, 6i + 4`, and below it, at
column `6i + 2j`, `gwnot` for a negated `j`-th literal and `wire_up` otherwise, then `gzero` in
the remaining slots `j < 3`. -/
def addClauses (F : CNF) : List Placement :=
  (List.range F.length).flatMap fun i =>
    let cl := F.getD i []
    [(0, 6 * i, bendDR), (0, 6 * i + 1, wireRight), (0, 6 * i + 2, gChoice),
        (0, 6 * i + 3, wireLeft), (0, 6 * i + 4, bendDL)] ++
      ((List.range cl.length).map fun j =>
        (1, 6 * i + 2 * j, if (cl.getD j (true, 0)).1 then wireUp else gWNot)) ++
      ((List.range (3 - cl.length)).map fun j' => (1, 6 * i + 2 * (cl.length + j'), gZero))

/-- All placements, in the order the program solders them. -/
def placements (F : CNF) : List Placement :=
  addVariables F ++ addSortingNetwork F ++ addClauses F

/-- The assembled board before the `?` values are fixed: the square `(r, c)` (for `r < boardH F`,
`c < boardW F`) carries the cell written last by a placement covering it (`solder`, A.1 lines
237–246); squares off the board, and squares no placement covers, are blank. -/
def preBoard (F : CNF) (v : Cell) : GCell :=
  if v.1 < boardH F ∧ v.2 < boardW F then
    (placements F).foldl
      (fun acc p =>
        if 16 * p.1 ≤ v.1 ∧ v.1 ≤ 16 * p.1 + 16 ∧ 16 * p.2.1 ≤ v.2 ∧ v.2 ≤ 16 * p.2.1 + 16 then
          p.2.2.cellAt (v.1 - 16 * p.1) (v.2 - 16 * p.2.1)
        else acc)
      GCell.blank
  else GCell.blank

/-! ## The `?` values (`fix_deferred_work`, A.1 lines 217–233) -/

/-- The number of squares stepped over from `v` in the direction `step` before the first `!`
(at most `fuel` steps; the walk also stops where `step` leaves the board). -/
def walkCount (F : CNF) (step : Cell → Option Cell) : ℕ → Cell → ℕ
  | 0, _ => 0
  | fuel + 1, v =>
    match step v with
    | none => 0
    | some u => if preBoard F u = GCell.bang then 0 else 1 + walkCount F step fuel u

/-- One step left, right, up and down, within the board. -/
def stepLeft (_F : CNF) (v : Cell) : Option Cell := if 0 < v.2 then some (v.1, v.2 - 1) else none
def stepRight (F : CNF) (v : Cell) : Option Cell :=
  if v.2 + 1 < boardW F then some (v.1, v.2 + 1) else none
def stepUp (_F : CNF) (v : Cell) : Option Cell := if 0 < v.1 then some (v.1 - 1, v.2) else none
def stepDown (F : CNF) (v : Cell) : Option Cell :=
  if v.1 + 1 < boardH F then some (v.1 + 1, v.2) else none

/-- The value given to a `?` square `v`: `1` plus the number of squares walked over in each of
the four directions before the first `!`. -/
def qValue (F : CNF) (v : Cell) : ℕ :=
  let fuel := boardW F + boardH F
  1 + walkCount F (stepLeft F) fuel v + walkCount F (stepRight F) fuel v +
    walkCount F (stepUp F) fuel v + walkCount F (stepDown F) fuel v

/-- The clue of the final board at `v`, if any: a digit keeps its value, a `?` gets `qValue`. -/
def clueAt (F : CNF) (v : Cell) : Option ℕ :=
  match preBoard F v with
  | GCell.clue n => some n
  | GCell.qmark => some (qValue F v)
  | _ => none

/-- The Kurodoko instance `(w, h, clues)` produced from the formula `F`: the board is
`boardW F` columns by `boardH F` rows and the clues are listed in row-major order. The empty
formula is sent to the solvable instance `(1, 1, [])`. -/
def reduceCNF (F : CNF) : ℕ × ℕ × List (ℕ × ℕ × ℕ) :=
  if F = [] then (1, 1, [])
  else
    (boardW F, boardH F,
      (List.range (boardH F)).flatMap fun r =>
        (List.range (boardW F)).filterMap fun c => (clueAt F (r, c)).map fun n => (r, c, n))

open Classical in
/-- The reduction on words: the code of a formula `F` whose clauses all have three literals is
sent to the code of `reduceCNF F`; every other word is sent to the code of the unsolvable
instance `w = 2`, `h = 1`, clues `(0, 0, 1)` and `(0, 1, 1)`. -/
noncomputable def reduceWord (s : List SatSym) : List BSym :=
  if h : ∃ F : CNF, (∀ C ∈ F, C.length = 3) ∧ s = encodeCNF F then
    code (reduceCNF h.choose).1 (reduceCNF h.choose).2.1 (reduceCNF h.choose).2.2
  else code 2 1 [(0, 0, 1), (0, 1, 1)]

/-! ## Ports (§4.1, Fig. 1, p. 695) and the gadget relations -/

/-- The eight marked squares of a gadget: `n, w, e, s` (north, west, east, south) inputs `i`
and outputs `o`. -/
inductive Port where
  | ni | no | wi | wo | ei | eo | si | so
  deriving DecidableEq, Repr

/-- The position of a port in a gadget string's own frame: `ni (1,8)`, `no (2,8)`, `so (14,8)`,
`si (15,8)`, `wi (8,1)`, `wo (8,2)`, `eo (8,14)`, `ei (8,15)`. -/
def Port.basePos : Port → Fin 17 × Fin 17
  | .ni => (1, 8)
  | .no => (2, 8)
  | .so => (14, 8)
  | .si => (15, 8)
  | .wi => (8, 1)
  | .wo => (8, 2)
  | .eo => (8, 14)
  | .ei => (8, 15)

/-- The board square of the port `q` of a placement `(R, C, g)`: its position in the gadget
string, moved by the operations of `g`, then shifted by `(16R, 16C)`. -/
def portCell (p : Placement) (q : Port) : Cell :=
  (16 * p.1 + (p.2.2.pos q.basePos).1.val, 16 * p.2.1 + (p.2.2.pos q.basePos).2.val)

/-- The behaviour of each gadget (§4.1, p. 696), in the frame of its A.1 string; `x q` means the
port `q` is black (= 1). The `xor` and `ltee` strings draw the rotated gadgets X² (Xor turned by
180°) and S+ (Sidesplit turned clockwise), so their relations are transported. -/
def GadgetRel : BaseGadget → (Port → Prop) → Prop
  | .wire, x => (x .no ↔ x .si)
  | .neg, x => (x .no ↔ ¬ x .si)
  | .var, _ => True
  | .zero, x => ¬ x .no
  | .xor, x => (x .so ↔ ¬ (x .wi ↔ x .ei))
  | .choice, x =>
      (x .wi ∧ ¬ x .si ∧ ¬ x .ei) ∨ (¬ x .wi ∧ x .si ∧ ¬ x .ei) ∨ (¬ x .wi ∧ ¬ x .si ∧ x .ei)
  | .tee, x => (x .wo ↔ x .si) ∧ (x .eo ↔ x .si)
  | .ltee, x => (x .eo ↔ x .so) ∧ (x .so ↔ x .wi)
  | .bend, x => (x .eo ↔ x .si)

end Kurodoko.NPC


