-- Prove2me | Definitions.Def_Tatamibari_NPC_Geometry
-- name    : Tatamibari_NPC_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:33:38.145036+00:00
-- url     : https://prove2.me/theorems/f9cd45ea-948c-4c97-8943-2652f6e7d646
-- title:
--   Parameterized wire, terminator, variable, and clause geometry
-- statement:
--   The wire family has four columns, n square clues for every positive integer n, alternating vertical inner-sheathing clues, and four-cell interfaces at each end. The fixed six-column terminator is Figure 4. Variable gadgets have arbitrary positive branch count, six columns per branch and the nine square clues of Figures 5–7 in each branch. Between successive wires the coupler has one square clue and eight surrounding vertical clues; separate optional interfaces are retained for every branch and direction.
--
--   The clause is the 25-by-22 bounding-grid diagram in Figure 8, including exterior cells, barriers, enforcement lines, and its three four-cell interfaces. Two independent nonnegative parameters insert arbitrary numbers of columns in the repeatable strips of Figure 9. Vertical reflection produces the negative clause. The concrete table consists of the seven non-all-false masks of the optional areas, not an abstract Boolean replacement for the gadget. The local rectangle predicate and candidate-covering search remain geometric.
--
--   Safety means that in every full solution no rectangle associated with a vertical clue reaches the cells immediately to the right of the first or last square clue. It does not assert square size or wire parity. The coordinate predicates describe upper-left and lower-left square placements and the staggered inner sheathing. Coordinates increase rightwards and downwards; figures are transcribed with +, -, and | for the three graphic clue symbols.
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 6, Sections 1–3 (definitions and figures)

import Definitions.Def_Tatamibari_NPC_Gadget

set_option autoImplicit false

namespace Tatamibari.NPC

def characterClue (c : Char) : Clue :=
  if c = '+' then .square else if c = '-' then .horizontal
  else if c = '|' then .vertical else .empty

/-- Spaces are exterior; letters a,b,c,... label optional areas; all other
characters denote mandatory cells. The strings transcribe the printed diagrams. -/
def diagram (rows : List String) (ports : List Char) : Gadget :=
  let cells := rows.zipIdx.flatMap fun (row, y) =>
    row.toList.zipIdx.map fun (c, x) => ((x, y), c)
  { width := (rows.map String.length).foldl max 0
    height := rows.length
    mandatory := (cells.filter fun (_, c) => c != ' ' && !ports.contains c).map Prod.fst
    optional := ports.map fun label => (cells.filter fun (_, c) => c == label).map Prod.fst
    clues := cells.filterMap fun (p, c) =>
      if characterClue c != .empty then some (p, characterClue c) else none }

/-- n square clues, with four-cell top and bottom interfaces, Figure 3. -/
def wire (n : Nat) : Gadget :=
  let w := 4
  let h := 2 * n + 2
  let all := (Rectangle.mk 0 0 w h).cells
  let upper := [(0, 0), (3, 0), (1, 1), (2, 1)]
  let lower := [(0, 2*n), (3, 2*n), (1, 2*n+1), (2, 2*n+1)]
  { width := w, height := h
    mandatory := all.filter fun p =>
      (1 ≤ p.2 && p.2 < 2*n && !upper.contains p) ||
      (p.2 == 2*n && (p.1 == 1 || p.1 == 2))
    optional := [upper, lower]
    clues := (List.range n).flatMap fun i =>
      [((0, 2*i+1), .vertical), ((3, 2*i+1), .vertical), ((1, 2*i+2), .square)] }

def wireProfile (n : Nat) (down : Bool) : List Cell := (wire n).profile [!down, down]

def terminator : Gadget := diagram
  ["......", "..||..", ".|..|.", "..+...", ".|..|.", "..+...",
   ".|..|.", "..+...", ".|..|.", "|a+.a|", "  aa  "] ['a']

/-- An arbitrary nonempty chain is obtained by taking n ≥ 1; no fixed bound on n. -/
def variableGadget (n : Nat) : Gadget :=
  let upper := (List.range n).map fun i =>
    [(6*i+1, 0), (6*i+4, 0), (6*i+2, 1), (6*i+3, 1)]
  let lower := (List.range n).map fun i =>
    [(6*i+1, 20), (6*i+4, 20), (6*i+2, 19), (6*i+3, 19)]
  { width := 6*n, height := 21
    mandatory := (Rectangle.mk 0 2 (6*n) 19).cells ++
      (List.range n).flatMap (fun i => [(6*i+1,1), (6*i+4,1), (6*i+1,19), (6*i+4,19)])
    optional := upper ++ lower
    clues := ((List.range n).flatMap fun i =>
      ((List.range 9).map fun j => ((6*i+2, 2*j+2), Clue.square)) ++
      ((List.range 10).flatMap fun j =>
        [((6*i+1, 2*j+1), Clue.vertical), ((6*i+4, 2*j+1), Clue.vertical)])) ++
      ((List.range n).flatMap fun i =>
        [((6*i,2), .vertical), ((6*i+5,2), .vertical),
         ((6*i,18), .vertical), ((6*i+5,18), .vertical)]) ++
      ((List.range (n-1)).flatMap fun i =>
        [((6*i+5,8), .vertical), ((6*i+6,8), .vertical),
         ((6*i+5,12), .vertical), ((6*i+6,12), .vertical),
         ((6*i+5,10), .square)]) }

def variableProfile (n : Nat) (upper lower : List Bool) : List Cell :=
  (variableGadget n).profile (upper ++ lower)

/-- The three independent branch-orientation conditions of Lemma 3.9. -/
def consistentOrientations (upper lower : List Bool) : Prop :=
  (∀ a ∈ upper, ∀ b ∈ upper, a = b) ∧
  (∀ a ∈ lower, ∀ b ∈ lower, a = b) ∧
  (∀ a ∈ upper, ∀ b ∈ lower, a = !b)

def clauseRows : List String :=
  ["-........................", "|+|++++++++++++++++++++++", ".+.-.....................",
   ".+.....................+|", ".+...+|||||||||||||||||+.", ".+.|.................-.+.",
   ".+...+............+..|.+.", ".+.|..|..........|..|..+.", ".+...+.||||||||||.+....+.",
   ".+.|...........-.|..|..+.", ".+...+-...|.+..|..+....+.", ".+.|.......|..|..|..|..+.",
   ".+...+-.....+.....+....+.", ".+.|.....-.|..|..|..|..+.", ".+....+..|..+.....+....+.",
   ".+..||..|..|..|..|..|..+.", "-.....+.....+.....+.....-", "+++..|..|..|..|..|..|.+++",
   "-.....+.....+.....+.....-", "    ||..||||..||||..||   ",
   "    .a+.a..b+.b..c+.c.   ", "      aa    bb    cc     "]

/-- Insert columns in the two repeatable strips of Figure 9. Rows below the
rectangular body are exterior in these extra columns. -/
def extensionChar (first : Bool) (y : Nat) : Char :=
  if y ≥ 19 then ' ' else if y = 1 then '+'
  else if y = 4 || y = 8 || (first && y = 10) then '|' else '.'

def clauseGadget (a b : Nat) (negative : Bool) : Gadget :=
  let rows := clauseRows.zipIdx.map fun (s, y) =>
    let cs := s.toList
    String.ofList (cs.take 10 ++ List.replicate a (extensionChar true y) ++
      (cs.drop 10).take 6 ++ List.replicate b (extensionChar false y) ++ cs.drop 16)
  let g := diagram rows ['a', 'b', 'c']
  if negative then g.reflect else g

def clauseProfile (a b : Nat) (negative : Bool) (values : List Bool) : List Cell :=
  (clauseGadget a b negative).profile values

def satisfyingPatterns : List (List Bool) :=
  [[false,false,true], [false,true,false], [false,true,true],
   [true,false,false], [true,false,true], [true,true,false], [true,true,true]]

def clauseProfiles (a b : Nat) (negative : Bool) : List (List Cell) :=
  satisfyingPatterns.map (clauseProfile a b negative)

/-- Profile entries carry an executable search for their actual rectangle covering;
failure is explicit, never silently treated as a proof of solvability. -/
def wireTable (n : Nat) : List (List Cell × Option (List Rectangle)) :=
  [false,true].map fun v =>
    let p := wireProfile n v
    (p, (wire n).tableCovering p)

def terminatorTable : List (List Cell × Option (List Rectangle)) :=
  [false,true].map fun v =>
    let p := terminator.profile [v]
    (p, terminator.tableCovering p)

def variableTable (n : Nat) : List (List Cell × Option (List Rectangle)) :=
  [false,true].map fun v =>
    let p := variableProfile n (List.replicate n (!v)) (List.replicate n v)
    (p, (variableGadget n).tableCovering p)

def clauseTable (a b : Nat) (negative : Bool) : List (List Cell × Option (List Rectangle)) :=
  (clauseProfiles a b negative).map fun p => (p, (clauseGadget a b negative).tableCovering p)

/-- Safety restricts intrusion from vertical clues, never the sizes of square rectangles. -/
def safelyPlaced (b : Board) (offset : Cell) (n : Nat) : Prop :=
  ∀ rs, b.isSolution rs = true → ∀ r ∈ rs, ∀ p ∈ b.cluesIn r,
    b.at p = .vertical →
    r.contains (translateCell offset (2, 2)) = false ∧
    r.contains (translateCell offset (2, 2*n)) = false

/-- down=true puts a clue in the upper-left cell; false in the lower-left cell. -/
def squarePosition (p : Cell) (down : Bool) : Rectangle :=
  ⟨p.1, if down then p.2 else p.2-1, p.1+2, if down then p.2+2 else p.2+1⟩
def sheathPosition (p : Cell) (down : Bool) : Rectangle :=
  ⟨p.1, if down then p.2 else p.2-1, p.1+1, if down then p.2+2 else p.2+1⟩

def wireHasParity (offset : Cell) (n : Nat) (rs : List Rectangle) (down : Bool) : Prop :=
  ∀ i < n, squarePosition (translateCell offset (1, 2*i+2)) down ∈ rs

end Tatamibari.NPC


