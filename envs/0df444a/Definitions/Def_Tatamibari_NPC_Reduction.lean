-- Prove2me | Definitions.Def_Tatamibari_NPC_Reduction
-- name    : Tatamibari_NPC_Reduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:34:04.78636+00:00
-- url     : https://prove2.me/theorems/9140b226-2367-4960-bce5-7434505c015e
-- title:
--   Normalized monotone drawings and the concrete Tatamibari reduction
-- statement:
--   A reduction input is a monotone formula with exactly three occurrences per clause, together with the left-to-right order of its distinct occurrence edges in a planar rectilinear drawing. Variable labels follow their horizontal order; repeated variable occurrences are allowed. Validity checks the occurrence permutation, contiguous variable ordering, ordered clause ports, laminar same-side clause intervals, and absence of edges crossing inner clauses. Satisfaction has its ordinary Boolean meaning.
--
--   The construction uses that order and clause nesting, not the magnitudes of original coordinates. Each occurrence receives a branch slot, with spare branches capped in both directions. Variable gadgets lie on a central band; positive clauses lie above and negative clauses below, with mirrored wires and clause geometry. Heights are separated by 64 rows, branch slots by six columns, with four slots per occurrence and explicit margins. These are fixed layout choices, not constants claimed in the source theorem. Outer-sheathing columns are reserved before free strips are computed. Consecutive strips are joined only when their entire horizontal intervals agree; each filler rectangle gets an aspect-appropriate clue at its upper-right cell. Meeting points of outer-sheathing rectangles remain unfixed solution data.
--
--   All operations are concrete finite-list computations. Invalid drawing codes map to the one-cell board with no clue. A drawing with no variables or clauses is allowed; the same filler construction handles it. The encoded drawing uses unary counts and occurrence indices, so its length is polynomial in n+m. There is no satisfiability oracle, assumed reduction correctness, or machine-time assertion hidden in a definition. Compatible local profiles must partition the common gadget region. Extension may move outer-sheathing boundaries and retains profile coverage within each gadget.
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 16, Sections 1–3 (definitions and figures)

import Definitions.Def_Tatamibari_NPC_Geometry
import Definitions.Def_Tatamibari_NPC_Encoding

set_option autoImplicit false

namespace Tatamibari.NPC

/-- A monotone clause has three occurrences, with repetitions permitted. -/
structure Clause where
  negative : Bool
  vars : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- The order is the left-to-right permutation of occurrence indices 3*j+k.
Variable labels are in left-to-right segment order. Original coordinate magnitudes
are discarded; the embedding is represented by its combinatorial order. -/
structure Drawing where
  vars : Nat
  clauses : List Clause
  order : List Nat
  deriving DecidableEq, Repr, Inhabited

def Drawing.variableOf (d : Drawing) (e : Nat) : Nat :=
  (d.clauses.getD (e / 3) default).vars.getD (e % 3) 0
def Drawing.rank (d : Drawing) (e : Nat) : Nat := d.order.idxOf e
def Drawing.lo (d : Drawing) (j : Nat) : Nat := d.rank (3*j)
def Drawing.hi (d : Drawing) (j : Nat) : Nat := d.rank (3*j+2)
def Drawing.sameSide (d : Drawing) (i j : Nat) : Bool :=
  (d.clauses.getD i default).negative == (d.clauses.getD j default).negative

def Drawing.valid (d : Drawing) : Bool :=
  d.clauses.all (fun c => c.vars.length == 3 && c.vars.all (· < d.vars)) &&
  d.order.length == 3*d.clauses.length && d.order.all (· < 3*d.clauses.length) &&
  decide d.order.Nodup &&
  d.order.zipIdx.all (fun (e, i) => d.order.zipIdx.all fun (f, j) =>
    i ≥ j || d.variableOf e ≤ d.variableOf f) &&
  (List.range d.clauses.length).all (fun j =>
    d.rank (3*j) < d.rank (3*j+1) && d.rank (3*j+1) < d.rank (3*j+2)) &&
  (List.range d.clauses.length).all (fun i =>
    (List.range d.clauses.length).all fun j =>
      i == j || !d.sameSide i j || d.hi i < d.lo j || d.hi j < d.lo i ||
      (d.lo i < d.lo j && d.hi j < d.hi i &&
        (List.range 3).all (fun k => d.rank (3*i+k) < d.lo j || d.hi j < d.rank (3*i+k))) ||
      (d.lo j < d.lo i && d.hi i < d.hi j &&
        (List.range 3).all (fun k => d.rank (3*j+k) < d.lo i || d.hi i < d.rank (3*j+k))))

def Drawing.satisfies (d : Drawing) (assignment : Nat → Bool) : Prop :=
  ∀ c ∈ d.clauses, ∃ v ∈ c.vars, assignment v = !c.negative
def Drawing.satisfiable (d : Drawing) : Prop := ∃ assignment, d.satisfies assignment

def Drawing.occurrences (d : Drawing) (v : Nat) : List Nat :=
  d.order.filter fun e => d.variableOf e == v
def Drawing.branches (d : Drawing) (v : Nat) : Nat := max 1 (4*(d.occurrences v).length)
def Drawing.base (d : Drawing) (v : Nat) : Nat :=
  ((List.range v).map d.branches).sum
def Drawing.slot (d : Drawing) (e : Nat) : Nat :=
  d.base (d.variableOf e) + 4 * (d.occurrences (d.variableOf e)).idxOf e
def Drawing.portX (d : Drawing) (e : Nat) : Nat := 22 + 6*d.slot e
def Drawing.layer (d : Drawing) (j : Nat) : Nat :=
  1 + ((List.range d.clauses.length).filter fun i =>
    d.sameSide i j && d.lo j < d.lo i && d.hi i < d.hi j).length
def Drawing.center (d : Drawing) : Nat := 64*(d.clauses.length+2)
def Drawing.boardWidth (d : Drawing) : Nat := 40 + 6*d.base d.vars
def Drawing.boardHeight (d : Drawing) : Nat := 2*d.center + 21

def Drawing.clauseOffset (d : Drawing) (j : Nat) : Cell :=
  (d.portX (3*j)-6,
   if (d.clauses.getD j default).negative then d.center + 64*d.layer j - 1
   else d.center - 64*d.layer j)
def Drawing.clauseA (d : Drawing) (j : Nat) : Nat := d.portX (3*j+1)-d.portX (3*j)-6
def Drawing.clauseB (d : Drawing) (j : Nat) : Nat := d.portX (3*j+2)-d.portX (3*j+1)-6
def Drawing.placedClause (d : Drawing) (j : Nat) : Gadget :=
  (clauseGadget (d.clauseA j) (d.clauseB j)
    (d.clauses.getD j default).negative).translate (d.clauseOffset j)
def Drawing.placedVariable (d : Drawing) (v : Nat) : Gadget :=
  (variableGadget (d.branches v)).translate (20+6*d.base v, d.center)
def Drawing.wireLength (d : Drawing) (e : Nat) : Nat := 32*d.layer (e/3)-10
def Drawing.wireOffset (d : Drawing) (e : Nat) : Cell :=
  (d.portX e-1, if (d.clauses.getD (e/3) default).negative
    then d.center+19 else d.center-64*d.layer (e/3)+20)
def Drawing.placedWire (d : Drawing) (e : Nat) : Gadget :=
  let g := wire (d.wireLength e)
  (if (d.clauses.getD (e/3) default).negative then g.reflect else g).translate (d.wireOffset e)

/-- Every unused branch in each direction receives a concrete cap. -/
def Drawing.terminators (d : Drawing) : List Gadget :=
  (List.range d.vars).flatMap fun v =>
    (List.range (d.branches v)).flatMap fun k =>
      [false, true].filterMap fun negative =>
        let slot := d.base v + k
        let used := d.order.any fun e => d.slot e == slot &&
          (d.clauses.getD (e/3) default).negative == negative
        if used then none else
          some ((if negative then terminator.reflect else terminator).translate
            (20+6*slot, if negative then d.center+19 else d.center-9))

def Drawing.gadgets (d : Drawing) : List Gadget :=
  (List.range d.vars).map d.placedVariable ++
  (List.range d.clauses.length).map d.placedClause ++
  (List.range (3*d.clauses.length)).map d.placedWire ++ d.terminators

/-- Reserve the two outer-sheathing columns; their eventual meeting points are
solution data and are not fixed by this reservation. -/
def Drawing.outerCells (d : Drawing) : List Cell :=
  d.order.flatMap fun e =>
    let j := e/3
    let neg := (d.clauses.getD j default).negative
    let top := if neg then d.center+18 else d.center-64*d.layer j+19
    let bottom := if neg then d.center+64*d.layer j+2 else d.center+3
    (Rectangle.mk (d.portX e-2) top (d.portX e-1) bottom).cells ++
      (Rectangle.mk (d.portX e+3) top (d.portX e+4) bottom).cells

def Drawing.reserved (d : Drawing) : List Cell :=
  d.gadgets.flatMap Gadget.area ++ d.outerCells

/-- Maximal free horizontal strips, using exactly the same horizontal interval
when extending into later rows. -/
def freeStrips (w h : Nat) (occupied : List Cell) : List Rectangle :=
  (List.range h).flatMap fun y =>
    (List.range w).filterMap fun l =>
      if !occupied.contains (l,y) && (l == 0 || occupied.contains (l-1,y)) then
        let r := ((List.range (w-l)).find? fun k => occupied.contains (l+k,y)).getD (w-l) + l
        some ⟨l,y,r,y+1⟩
      else none

def joinStrips (h : Nat) (strips : List Rectangle) : List Rectangle :=
  strips.filterMap fun r =>
    let prev : Rectangle := ⟨r.left, r.top-1, r.right, r.top⟩
    if r.top != 0 && strips.contains prev then none else
      let k := ((List.range (h-r.top)).find? fun k =>
        !strips.contains ⟨r.left, r.top+k, r.right, r.top+k+1⟩).getD (h-r.top)
      some ⟨r.left,r.top,r.right,r.top+k⟩

def Drawing.fillerRectangles (d : Drawing) : List Rectangle :=
  joinStrips d.boardHeight (freeStrips d.boardWidth d.boardHeight d.reserved)
def aspectClue (r : Rectangle) : Clue :=
  if r.width = r.height then .square else if r.width > r.height then .horizontal else .vertical
def Drawing.allClues (d : Drawing) : List (Cell × Clue) :=
  d.gadgets.flatMap Gadget.clues ++
  d.fillerRectangles.map (fun r => ((r.right-1,r.top), aspectClue r))

def yesBoard : Board := ⟨1,1,[.square]⟩
def noBoard : Board := ⟨1,1,[.empty]⟩

/-- The concrete normalized construction. No truth assignment, SAT oracle,
correctness certificate, or satisfying rectangle assignment is an input. -/
def reduction (d : Drawing) : Board :=
  if !d.valid then noBoard else
    let clues := d.allClues
    ⟨d.boardWidth, d.boardHeight,
      (Rectangle.mk 0 0 d.boardWidth d.boardHeight).cells.map fun p =>
        ((clues.find? fun c => c.1 == p).map Prod.snd).getD .empty⟩

def encodeDrawing (d : Drawing) : List Bool :=
  unary d.vars ++ unary d.clauses.length ++
  d.clauses.flatMap (fun c => [c.negative] ++ c.vars.flatMap unary) ++ d.order.flatMap unary
def readNats : Nat → List Bool → Option (List Nat × List Bool)
  | 0, xs => some ([],xs)
  | n+1, xs => do
    let (v,xs) ← readUnary xs
    let (vs,xs) ← readNats n xs
    return (v::vs,xs)
def readClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, xs => some ([],xs)
  | _+1, [] => none
  | n+1, neg::xs => do
    let (vs,xs) ← readNats 3 xs
    let (cs,xs) ← readClauses n xs
    return (⟨neg,vs⟩::cs,xs)
def decodeDrawing (xs : List Bool) : Option Drawing := do
  let (n,xs) ← readUnary xs
  let (m,xs) ← readUnary xs
  let (cs,xs) ← readClauses m xs
  let (order,xs) ← readNats (3*m) xs
  let d : Drawing := ⟨n,cs,order⟩
  if xs.isEmpty && d.valid then some d else none
def reductionBits (xs : List Bool) : List Bool :=
  encodeBoard false (match decodeDrawing xs with | some d => reduction d | none => noBoard)

/-- The containing-puzzle class for clause isolation is the constructed layouts,
with the same clause and wire restrictions used throughout the reduction. -/
def admissibleAmbient (b : Board) : Prop := ∃ d, d.valid = true ∧ b = reduction d

def profilesCompatible (gs : List Gadget) (ps : List (List Cell)) : Prop :=
  ps.length = gs.length ∧
  (∀ i, ∀ j, i < ps.length → j < ps.length → i ≠ j →
    ∀ p ∈ ps.getD i [], p ∉ ps.getD j []) ∧
  sameCells ps.flatten (gs.flatMap Gadget.area) = true ∧
  ∀ i < gs.length, (gs.getD i default).locallySolvable (ps.getD i [])

/-- Outer-sheathing rectangles may change at assembly time; gadget clue profiles
are preserved on their gadget areas, and all filler rectangles are retained. -/
def extendsProfiles (d : Drawing) (ps : List (List Cell)) (rs : List Rectangle) : Prop :=
  ∀ i < d.gadgets.length,
    sameCells (((d.gadgets.getD i default).induced rs).filter
      (d.gadgets.getD i default).area.contains) (ps.getD i []) = true

end Tatamibari.NPC


