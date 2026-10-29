-- Prove2me | Definitions.Def_ClickomaniaNPC_ThreeColor_Languages
-- name    : ClickomaniaNPC_ThreeColor_Languages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T03:49:42.980705+00:00
-- url     : https://prove2.me/theorems/aca0a59c-e146-46ea-8b1d-e8af5903fe5a
-- title:
--   Explicit rectangular puzzle inputs and the two solvability languages
-- statement:
--   A raw puzzle input records width w, height h, palette size k and a finite list of cell labels, in column-major bottom-to-top order. It is valid exactly when the list has w times h entries and every label is less than k. This is a full rectangle, with unused palette entries allowed. Its board is obtained by slicing the list into w columns of length h. Height zero is normalized to the empty board; the original width is retained in the input record. Invalid raw records are excluded by the decoder before any language tests solvability.
--
--   The input word consists of the canonical natural-number codes of w, h and k, followed by one canonical code for every cell. The decoder parses these headers, rejects a cell count exceeding the remaining bit count, reads precisely w times h labels, and rejects any suffix or invalid label. It returns a valid input or fails. No runs of cells are compressed, so every block contributes its own symbols. Declared unused palette entries can be binary-coded.
--
--   The unrestricted language contains exactly words that decode to valid, solvable initial rectangles. The restricted language imposes the additional initial conditions w = 5 and k = 3, with arbitrary finite height. It does not require all three colors to occur, nor five columns to remain during play. Malformed words belong to neither language. Zero-area rectangles, including height-zero inputs with width five, are accepted as already cleared. A zero palette is compatible only with zero area.
--
--   Both languages are sets of Boolean words in the published CookPvsNP framework. No verifier, hardness result, reduction, or assignment is assumed in their definitions.
-- source:
--   Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro, The Complexity of Clickomania, arXiv:cs/0107031v1 (21 July 2001), section 1, p. 1; section 4, Theorem 15, p. 11. https://arxiv.org/abs/cs/0107031v1

import Definitions.Def_ClickomaniaNPC_ThreeColor_Play
import Definitions.Def_ClickomaniaNPC_ThreeColor_Code
import Definitions.Def_CookPvsNP_defs

namespace ClickomaniaNPC.ThreeColor

/-- Raw rectangle data. Cells are stored column by column, bottom to top. -/
structure PuzzleInput where
  width : ℕ
  height : ℕ
  palette : ℕ
  cells : List ℕ
  deriving DecidableEq, Repr

/-- Exactly one in-range color per cell of a full rectangle. Unused colors are allowed. -/
def PuzzleInput.Valid (I : PuzzleInput) : Prop :=
  I.cells.length = I.width * I.height ∧ ∀ c ∈ I.cells, c < I.palette

instance (I : PuzzleInput) : Decidable I.Valid := by
  unfold PuzzleInput.Valid
  infer_instance

/-- Build a board from explicit cells. Zero height is normalized to the empty
board, while width remains available in the input record. Invalid raw records
are never accepted by decodeInput. -/
def PuzzleInput.board (I : PuzzleInput) : Board :=
  if I.height = 0 then [] else
    (List.range I.width).map fun x => (I.cells.drop (x * I.height)).take I.height

/-- Dimensions, palette, then every individual cell; no run-length compression. -/
def encodeInput (I : PuzzleInput) : List Bool :=
  encodeNat I.width ++ encodeNat I.height ++ encodeNat I.palette ++
    I.cells.flatMap encodeNat

/-- Concrete decoder. The preliminary cell-count check avoids expanding a
positive-area board larger than its explicit input. Malformed inputs are rejected. -/
def decodeInput (s : List Bool) : Option PuzzleInput := do
  let (w, s₁) ← readNat s
  let (h, s₂) ← readNat s₁
  let (k, s₃) ← readNat s₂
  if s₃.length < w * h then none else
    let (cells, tail) ← readNats (w * h) s₃
    let I : PuzzleInput := ⟨w, h, k, cells⟩
    if tail = [] ∧ I.Valid then some I else none

/-- The unrestricted decision language of the source's initially full puzzles. -/
def clickomaniaLanguage : CookPvsNP.Lang Bool :=
  {s | ∃ I, decodeInput s = some I ∧ Solvable I.board}

/-- Exactly five initial columns and three available colors. Height is arbitrary,
and later positions may have fewer columns. -/
def fiveThreeLanguage : CookPvsNP.Lang Bool :=
  {s | ∃ I, decodeInput s = some I ∧ I.width = 5 ∧ I.palette = 3 ∧
    Solvable I.board}

end ClickomaniaNPC.ThreeColor


