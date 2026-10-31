-- Prove2me | Definitions.Def_Tatamibari_NPC_Gadget
-- name    : Tatamibari_NPC_Gadget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:33:04.524894+00:00
-- url     : https://prove2.me/theorems/7573003f-70d5-478d-a007-047a8b66b630
-- title:
--   Gadget regions, profiles, local solutions, and completeness
-- statement:
--   A gadget records its mandatory cells, separately identified optional interface regions, and clues. A proper profile contains every mandatory cell and either all or none of each optional region. A local solution partitions the chosen profile into clue-compatible nonempty rectangles inside the gadget area and satisfies the four-corner constraint among those rectangles. The profile is locally solvable if such rectangles exist. Translation and vertical reflection act on the geometric data.
--
--   A profile is any subset of the gadget area, as on page 3, and need not be proper. For a class of admissible ambient puzzles, a profile table is complete when no unlisted profile can equal the union of the full rectangles assigned to the gadget clues in a full solution. Equivalently, whenever that union is contained in the gadget area, it equals a listed profile. Entire rectangles are used without clipping; a union extending outside the area is not a profile in the source definition. This quantifies over global solutions, not merely local coverings. An executable exhaustive rectangle search supplies a candidate local covering for a specified profile, returning none if absent; it is never the reduction algorithm.
--
--   Formalization Note: the local assignment partitions its selected profile, following Section 3.1, rather than covering unselected optional cells. This resolves the Section 2 wording ambiguity without changing global coverage. Membership and profile equality ignore list order and repetition.
-- source:
--   Adler et al., Tatamibari Is NP-Complete, DOI:10.4230/LIPIcs.FUN.2021.1; supplied PDF identified as arXiv:2003.08331v2 (7 May 2020), p. 3, Sections 1–3 (definitions and figures)

import Definitions.Def_Tatamibari_NPC_Puzzle

set_option autoImplicit false

namespace Tatamibari.NPC

/-- A finite marked region, with a mandatory part and separately named interfaces. -/
structure Gadget where
  width : Nat
  height : Nat
  mandatory : List Cell
  optional : List (List Cell)
  clues : List (Cell × Clue)
  deriving Repr, Inhabited

def Gadget.area (g : Gadget) : List Cell := g.mandatory ++ g.optional.flatten
def Gadget.at (g : Gadget) (p : Cell) : Clue :=
  ((g.clues.find? fun q => q.1 == p).map Prod.snd).getD .empty
def sameCells (a b : List Cell) : Bool :=
  a.all b.contains && b.all a.contains
def Gadget.profile (g : Gadget) (mask : List Bool) : List Cell :=
  g.mandatory ++ ((g.optional.zip mask).filterMap fun (a, b) => if b then some a else none).flatten
def Gadget.proper (g : Gadget) (p : List Cell) : Bool :=
  p.all g.area.contains && g.mandatory.all p.contains &&
  g.optional.all (fun a => a.all p.contains || a.all (fun c => !p.contains c))
def Gadget.legal (g : Gadget) (r : Rectangle) : Bool :=
  r.nonempty && r.cells.all g.area.contains &&
  match g.clues.filter (fun c => r.contains c.1) with
  | [(p, c)] => r.contains p && c.fits r
  | _ => false
def Gadget.localSolution (g : Gadget) (p : List Cell) (rs : List Rectangle) : Bool :=
  rs.length == g.clues.length && rs.all g.legal && pairwiseDisjoint rs &&
  sameCells (rs.flatMap Rectangle.cells) p && g.proper p && noFourCorners rs
def Gadget.locallySolvable (g : Gadget) (p : List Cell) : Prop :=
  ∃ rs, g.localSolution p rs = true

def translateCell (offset p : Cell) : Cell := (offset.1 + p.1, offset.2 + p.2)
def translateRectangle (offset : Cell) (r : Rectangle) : Rectangle :=
  ⟨offset.1 + r.left, offset.2 + r.top, offset.1 + r.right, offset.2 + r.bottom⟩
def Gadget.translate (offset : Cell) (g : Gadget) : Gadget :=
  { width := offset.1 + g.width, height := offset.2 + g.height
    mandatory := g.mandatory.map (translateCell offset)
    optional := g.optional.map (List.map (translateCell offset))
    clues := g.clues.map fun (p, c) => (translateCell offset p, c) }
def Gadget.reflect (g : Gadget) : Gadget :=
  let f : Cell → Cell := fun p => (p.1, g.height - 1 - p.2)
  { g with mandatory := g.mandatory.map f
           optional := g.optional.map (List.map f)
           clues := g.clues.map fun (p, c) => (f p, c) }
def Gadget.embedded (g : Gadget) (b : Board) : Prop :=
  g.area.all (fun p => b.area.contains p && b.at p == g.at p) = true
def Gadget.induced (g : Gadget) (rs : List Rectangle) : List Cell :=
  (rs.filter fun r => g.clues.any fun c => r.contains c.1).flatMap Rectangle.cells

/-- A profile is a subset of the gadget area (Section 2). Completeness excludes
every unlisted such subset, including improper ones, as the untrimmed union
assigned to gadget clues in a full solution. It makes no claim about unions
that are not profiles because they extend outside the gadget area. -/
def Gadget.complete (g : Gadget) (profiles : List (List Cell))
    (ambient : Board → Prop) : Prop :=
  ∀ b, ambient b → g.embedded b → ∀ rs, b.isSolution rs = true →
    (g.induced rs).all g.area.contains = true →
    ∃ p ∈ profiles, sameCells (g.induced rs) p = true

/-- Exhaustive finite candidate rectangles, used only to exhibit profile-table coverings;
this search is not the reduction algorithm or the NP verifier. -/
def Gadget.rectangles (g : Gadget) : List Rectangle :=
  (List.range (g.width + 1)).flatMap fun l =>
  (List.range (g.height + 1)).flatMap fun t =>
  (List.range (g.width + 1)).flatMap fun r =>
  (List.range (g.height + 1)).filterMap fun b =>
    let q : Rectangle := ⟨l, t, r, b⟩
    if g.legal q then some q else none
def selections {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | a :: rest => a.flatMap fun x => (selections rest).map (x :: ·)
def Gadget.tableCovering (g : Gadget) (p : List Cell) : Option (List Rectangle) :=
  let choices := g.clues.map fun c => g.rectangles.filter fun r => r.contains c.1
  (selections choices).find? (g.localSolution p)

end Tatamibari.NPC


