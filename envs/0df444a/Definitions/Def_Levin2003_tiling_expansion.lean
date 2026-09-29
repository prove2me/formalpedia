-- Prove2me | Definitions.Def_Levin2003_tiling_expansion
-- name    : Levin2003_tiling_expansion
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T21:53:31.014343+00:00
-- url     : https://prove2.me/theorems/792061eb-0352-4d54-9e5c-b1baeeefc58c
-- title:
--   Tiling Expansion (Levin 2003, Definition 5)
-- statement:
--   **Tiling Expansion** (Definition 5 of the paper): *expand a given top line of tiles to a square using a given set of permitted tiles; output the bottom line and the permitted tiles.* Tiles are unit squares with a letter at each corner and may be joined if the letters match; expansion is the maximal tile-by-tile unique extension of a partial tiling of a square.
--
--   A square of $N \times N$ cells is labelled at its $(N+1) \times (N+1)$ corner points. A cell is *forced* when exactly one permitted tile is compatible with the letters already present at its four corners; forcing fills in that cell's corners. The process is iterated $(N+1)^2$ times, which reaches a fixed point because every round that changes anything labels at least one of the $(N+1)^2$ corners.
--
--   At the bit level an instance consists of the letter width $\ell$ written in unary, the characteristic vector of the permitted tiles among all $2^{4\ell}$ conceivable tiles, and the top line, holding $N+1$ letters of $\ell$ bits each. The output repeats the width and the characteristic vector and replaces the top line by the bottom line of the expanded square, an undetermined corner being written as the all-zero letter; inputs that do not parse are returned unchanged. The file also defines the hashing $g(a,x) = (a, f(x) + ax)$ over the field with $2^{n}$ elements that appears in the Remark closing Section 4.3.
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Section 4.3 (p. 101, Definition 5; p. 102, Remark)

import Definitions.Def_Levin2003_owf_model

/-!
# Levin 2003, Definition 5: Tiling Expansion

Tiles are unit squares carrying a letter at each corner; two tiles may be
joined when the letters they share match.  A square of `N × N` cells is tiled
by labelling its `(N+1) × (N+1)` corner points.  Starting from a partial
labelling (here: the top line of corner letters), the *expansion* repeatedly
fills in a cell whenever exactly one permitted tile is consistent with the
letters already present at that cell's corners, and stops when no further cell
is forced.  Tiling Expansion outputs the permitted tiles together with the
bottom line of the expanded square.
-/

namespace Levin2003

/-- A tile: a unit square with a letter at each of its four corners,
listed as top-left, top-right, bottom-left, bottom-right. -/
structure Tile (α : Type) where
  tl : α
  tr : α
  bl : α
  br : α
  deriving DecidableEq

/-- A partial labelling of the corner points of the grid. -/
abbrev Lab (α : Type) := ℕ × ℕ → Option α

variable {α : Type} [DecidableEq α]

/-- An already-placed letter is compatible with a proposed one when they agree;
an unlabelled corner is compatible with everything. -/
def compat (o : Option α) (a : α) : Bool :=
  match o with
  | none => true
  | some b => decide (b = a)

/-- The tile `t` fits the cell whose top-left corner is `(i, j)`
under the partial labelling `lab`. -/
def fits (lab : Lab α) (i j : ℕ) (t : Tile α) : Bool :=
  compat (lab (i, j)) t.tl && compat (lab (i, j + 1)) t.tr &&
    compat (lab (i + 1, j)) t.bl && compat (lab (i + 1, j + 1)) t.br

/-- The unique permitted tile fitting the cell with top-left corner `(i, j)`,
when there is exactly one such tile; `none` when the cell is not forced. -/
def forcedTile (T : List (Tile α)) (lab : Lab α) (i j : ℕ) : Option (Tile α) :=
  match T.filter (fun t => fits lab i j t) with
  | [t] => some t
  | _ => none

/-- One round of the expansion process on a square of `N × N` cells: every
corner that is still unlabelled and belongs to a cell forced by a unique
permitted tile receives the letter that tile carries at that corner. -/
def stepLab (N : ℕ) (T : List (Tile α)) (lab : Lab α) : Lab α := fun p =>
  match lab p with
  | some a => some a
  | none =>
      let i := p.1
      let j := p.2
      let cell : ℕ → ℕ → Option (Tile α) := fun a b =>
        if a < N ∧ b < N then forcedTile T lab a b else none
      let fromTL : Option α := (cell i j).map Tile.tl
      let fromTR : Option α := if 0 < j then (cell i (j - 1)).map Tile.tr else none
      let fromBL : Option α := if 0 < i then (cell (i - 1) j).map Tile.bl else none
      let fromBR : Option α :=
        if 0 < i ∧ 0 < j then (cell (i - 1) (j - 1)).map Tile.br else none
      fromTL.orElse fun _ => fromTR.orElse fun _ => fromBL.orElse fun _ => fromBR

/-- `k` rounds of the expansion process. -/
def iterLab (N : ℕ) (T : List (Tile α)) (lab : Lab α) : ℕ → Lab α
  | 0 => lab
  | k + 1 => stepLab N T (iterLab N T lab k)

/-- The maximal expansion of a partial labelling: enough rounds are performed
that no further corner can be filled (each nontrivial round fills at least one
of the `(N+1)^2` corners). -/
def expansion (N : ℕ) (T : List (Tile α)) (lab : Lab α) : Lab α :=
  iterLab N T lab ((N + 1) * (N + 1))

/-! ### The bit-string level function

An instance is a bit string of the form

* `l` ones followed by a zero — the width `l` of a letter, so letters are the
  bit strings of length `l`;
* the characteristic vector of the set of permitted tiles, of length `2 ^ (4 l)`,
  indexed by the number whose binary expansion is the concatenation of the four
  corner letters of a tile;
* the top line of the square, a nonempty block of `(N+1) * l` bits holding the
  `N + 1` corner letters of the top line.

The output repeats the first two blocks and replaces the top line by the bottom
line of the expanded square, an undetermined corner being written as the
all-zero letter.  Bit strings that do not parse are left unchanged. -/

/-- The value of a bit string read as a binary numeral, most significant bit first. -/
def bitsToNat (x : Bits) : ℕ :=
  x.foldl (fun n b => 2 * n + (if b then 1 else 0)) 0

/-- All bit strings of length `l`. -/
def allBits : ℕ → List Bits
  | 0 => [[]]
  | l + 1 => (allBits l).flatMap fun x => [x ++ [false], x ++ [true]]

/-- The index of a tile in the characteristic vector of a tile set. -/
def tileIndex (t : Tile Bits) : ℕ :=
  bitsToNat (t.tl ++ t.tr ++ t.bl ++ t.br)

/-- All tiles whose corner letters have width `l`. -/
def allTiles (l : ℕ) : List (Tile Bits) :=
  (allBits l).flatMap fun a =>
    (allBits l).flatMap fun b =>
      (allBits l).flatMap fun c =>
        (allBits l).map fun d => ⟨a, b, c, d⟩

/-- The set of permitted tiles described by the characteristic vector `mask`. -/
def tileSet (l : ℕ) (mask : Bits) : List (Tile Bits) :=
  (allTiles l).filter fun t => mask.getD (tileIndex t) false

/-- Cut `x` into `k` consecutive blocks of `l` bits. -/
def chunks (l : ℕ) : ℕ → Bits → List Bits
  | 0, _ => []
  | k + 1, x => x.take l :: chunks l k (x.drop l)

/-- The number of leading ones of a bit string. -/
def leadingOnes : Bits → ℕ
  | [] => 0
  | true :: x => leadingOnes x + 1
  | false :: _ => 0

/-- Parse an instance into the letter width, the characteristic vector of the
permitted tiles, and the bits holding the top line. -/
def parse (x : Bits) : Option (ℕ × Bits × Bits) :=
  let l := leadingOnes x
  if 0 < l ∧ l + 1 + 2 ^ (4 * l) ≤ x.length then
    let rest := x.drop (l + 1)
    let mask := rest.take (2 ^ (4 * l))
    let body := rest.drop (2 ^ (4 * l))
    if 0 < body.length ∧ body.length % l = 0 then some (l, mask, body) else none
  else none

/-- **Tiling Expansion** (Levin 2003, Definition 5): expand the given top line
of tiles to a square using the given set of permitted tiles, and output the
bottom line together with the permitted tiles. -/
def tilingExpansion (x : Bits) : Bits :=
  match parse x with
  | none => x
  | some (l, mask, body) =>
      let m := body.length / l
      let N := m - 1
      let top := chunks l m body
      let blank : Bits := List.replicate l false
      let lab0 : Lab Bits := fun p =>
        if p.1 = 0 ∧ p.2 ≤ N then some (top.getD p.2 blank) else none
      let final := expansion N (tileSet l mask) lab0
      let bottom : List Bits :=
        (List.range m).map fun j => (final (N, j)).getD blank
      List.replicate l true ++ false :: (mask ++ bottom.flatten)

/-- The hashing of Levin's closing Remark: `g (a, x) = (a, f x + a * x)`
over the field with `2 ^ n` elements. -/
noncomputable def hashPair {n : ℕ} (f : GaloisField 2 n → GaloisField 2 n) :
    GaloisField 2 n × GaloisField 2 n → GaloisField 2 n × GaloisField 2 n :=
  fun p => (p.1, f p.2 + p.1 * p.2)

end Levin2003


