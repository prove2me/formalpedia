-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_nfdh
-- name    : BeyondConvexity_APTAS_nfdh
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:10:51.711809+00:00
-- url     : https://prove2.me/theorems/42807057-b554-4ec2-be64-3c5097dee027
-- title:
--   Next-Fit Decreasing Height for labeled squares
-- statement:
--   Next-Fit Decreasing Height sorts labeled square side lengths in nonincreasing order, breaking ties by occurrence index. It maintains the current bin, horizontal position, shelf bottom, and shelf height. A square joins the current shelf when it fits horizontally; otherwise it starts a shelf above the current shelf if it fits vertically; otherwise it opens a new unit bin. Shelf height is the first square's side. The returned placements are restored to the input occurrence order.
--
--   All fit comparisons allow equality, so boundary contact is permitted. Empty input returns zero bins and no placements. The square-packing predicate checks containment and pairwise disjoint interiors for every labeled square. Real sides are permitted, as in Lemma 11. This transparent geometric algorithm definition asserts no performance theorem and no bit-runtime theorem; the latter for rational inputs remains separate proof work.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Lemma 11 and Appendix B.2, printed p.20 / PDF p.21; Appendix D.1, printed pp.27–28 / PDF pp.28–29.

import Definitions.Def_BeyondConvexity_APTAS_Packing

noncomputable section

namespace BeyondConvexity.APTAS

/-- Shelf state after a prefix of the height-sorted labeled square list. -/
structure ShelfState where
  bins : ℕ
  x : ℝ
  y : ℝ
  height : ℝ
  placed : List (ℕ × (ℕ × Point))

def emptyShelf : ShelfState := ⟨0, 0, 0, 0, []⟩

/-- Next-fit: try the current shelf, then a new shelf, then a new unit bin.
All comparisons are non-strict, so boundary contact is permitted. -/
def shelfStep (s : ShelfState) (item : ℕ × ℝ) : ShelfState :=
  let i := item.1
  let a := item.2
  if s.bins = 0 then
    ⟨1, a, 0, a, s.placed ++ [(i, (0, (0, 0)))]⟩
  else if s.x + a ≤ 1 then
    ⟨s.bins, s.x + a, s.y, s.height,
      s.placed ++ [(i, (s.bins - 1, (s.x, s.y))) ]⟩
  else if s.y + s.height + a ≤ 1 then
    ⟨s.bins, a, s.y + s.height, a,
      s.placed ++ [(i, (s.bins - 1, (0, s.y + s.height))) ]⟩
  else
    ⟨s.bins + 1, a, 0, a, s.placed ++ [(i, (s.bins, (0, 0)))]⟩

def nfdhState (sides : List ℝ) : ShelfState :=
  let labeled := sides.zipIdx |>.map (fun p => (p.2, p.1))
  let sorted := labeled.mergeSort (fun a b =>
    decide (b.2 < a.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)))
  sorted.foldl shelfStep emptyShelf

/-- Output is put back in occurrence order after sorting; equal sides retain labels. -/
def nfdh (sides : List ℝ) : Packing ℝ :=
  let s := nfdhState sides
  ⟨s.bins, (List.range sides.length).map (fun i =>
    ((s.placed.find? (fun p => p.1 = i)).getD (0, (0, (0, 0)))).2)⟩

def SquarePacking (sides : List ℝ) (p : Packing ℝ) : Prop :=
  p.placements.length = sides.length ∧
  (∀ i : Fin sides.length, (p.entry i).1 < p.bins ∧
    translate (p.entry i).2 (square (sides.get i)) ⊆ square 1) ∧
  ∀ i j : Fin sides.length, i ≠ j → (p.entry i).1 = (p.entry j).1 →
    Disjoint (interior (translate (p.entry i).2 (square (sides.get i))))
      (interior (translate (p.entry j).2 (square (sides.get j))))

end BeyondConvexity.APTAS


