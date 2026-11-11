-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_RectangularPartitions
-- name    : FixedPolyominoSquare_SquareCounting_RectangularPartitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:39.955573+00:00
-- url     : https://prove2.me/theorems/fb9d5164-28dd-468f-b0b2-efa6dde83aae
-- title:
--   Unordered rectangular partitions and their seam graphs
-- statement:
--   A nonempty discrete rectangle is an integer translate of $\mathrm{Rect}_{w,h}$ with positive integer width and height. A rectangular partition is an unordered finite set of such rectangles, pairwise disjoint, with union the square. The one-block partition is included. A seam pair is an adjacent pair of cells in different blocks, counted once by ordering its endpoints lexicographically. Its seam segment is the common physical unit side.
--
--   $$I(D)=|\operatorname{SeamPairs}(D)|,\qquad \mathrm{Part}_n=\{D:D\text{ is a rectangular partition of }\mathrm{Square}_n\}.$$
--
--   The seam graph joins distinct segments sharing either endpoint, including crossings and T-junctions. Its components use finite-path reachability. Width and height are the corresponding coordinate spans plus one on a nonempty region, and zero on the empty region. Partitions and their counts are enumerated as subsets of the square's powerset; no ordering factor is introduced.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), pp. 14–15, Theorem 6.1 and its proof; p. 18, Section 7

import Mathlib
import Definitions.Def_FixedPolyominoSquare_SquareCounting_PolyominoModel

namespace FixedPolyominoSquare.SquareCounting

noncomputable section
attribute [local instance] Classical.propDecidable

def IsDiscreteRectangle (B : Region) : Prop :=
  ∃ (v : Cell) (w h : ℕ), 1 ≤ w ∧ 1 ≤ h ∧ B = translate (rect w h) v

def IsRectangularPartition (Ω : Region) (D : Finset Region) : Prop :=
  (∀ B ∈ D, IsDiscreteRectangle B) ∧
  (∀ A ∈ D, ∀ B ∈ D, A ≠ B → Disjoint A B) ∧
  D.biUnion id = Ω

/-- Unordered partitions; there is no ordering factor for blocks. -/
def Part (n : ℕ) : Finset (Finset Region) :=
  (square n).powerset.powerset.filter (IsRectangularPartition (square n))

def cellBefore (a b : Cell) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

def gridEdges (n : ℕ) : Finset (Cell × Cell) :=
  ((square n).product (square n)).filter fun e =>
    cellBefore e.1 e.2 ∧ gridAdjacent e.1 e.2

def seamPairs (n : ℕ) (D : Finset Region) : Finset (Cell × Cell) :=
  (gridEdges n).filter fun e => ∃ B ∈ D, e.1 ∈ B ∧ e.2 ∉ B

def I (n : ℕ) (D : Finset Region) : ℕ := (seamPairs n D).card

abbrev Segment := Cell × Cell

/-- The common physical unit side, with endpoints in increasing order. -/
def commonSide (e : Cell × Cell) : Segment :=
  if e.1.2 = e.2.2 then
    ((e.2.1, e.1.2), (e.2.1, e.1.2 + 1))
  else ((e.1.1, e.2.2), (e.1.1 + 1, e.2.2))

def seams (n : ℕ) (D : Finset Region) : Finset Segment :=
  (seamPairs n D).image commonSide

def shareEndpoint (e f : Segment) : Prop :=
  e ≠ f ∧ (e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2)

def seamComponent (n : ℕ) (D : Finset Region) (e : Segment) : Finset Segment :=
  (seams n D).filter fun f => Relation.ReflTransGen
    (fun u v => u ∈ seams n D ∧ v ∈ seams n D ∧ shareEndpoint u v) e f

def width (s : Region) : ℕ :=
  if s.Nonempty then 1 + (s.product s).sup (fun p => (p.1.1 - p.2.1).natAbs) else 0

def height (s : Region) : ℕ :=
  if s.Nonempty then 1 + (s.product s).sup (fun p => (p.1.2 - p.2.2).natAbs) else 0

end
end FixedPolyominoSquare.SquareCounting


