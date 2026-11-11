-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_Macrogrid
-- name    : FixedPolyominoSquare_SquareCounting_Macrogrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:22.207495+00:00
-- url     : https://prove2.me/theorems/e4f10ae8-b143-4516-a6c4-6cd390ab5007
-- title:
--   Saturated index graphs and physical macrocell windows
-- statement:
--   For integer parameters $P\geq1$, $c\geq0$ and $n\geq1$, put
--
--   $$L_{\rm mac}(n)=Pn+2c,\qquad x_0=0,\quad x_n=L_{\rm mac}(n),\quad x_i=c+Pi\ (0<i<n),\qquad \mathrm{Mac}_{p,q}=[x_p,x_{p+1})\times[x_q,x_{q+1})\cap\mathbb Z^2.$$
--
--   An index graph is a spanning subgraph of the square's unit-adjacency graph. It is saturated if any two consecutive open edges of a unit two-by-two window force all four. A tiling opens a macro-edge when a single placement contains adjacent physical cells on its two sides. Filled components must contain all internal grid adjacencies of their rectangular vertex set.
--
--   The maximum prototile diameter $d_T$ is computed from all pairs of cells of each finite prototile using the maximum of the two absolute coordinate differences. The neighbourhood of a finite window is its closed $\ell_\infty$ neighbourhood of radius $d_T$. Physical components are unions of the macrocells of index components, and the restricted placement set consists of precisely those placements meeting the window. All these objects are computed from the actual supports and placements, rather than supplied with correctness fields.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), pp. 15–16, Theorem 6.2 and its proof

import Mathlib
import Definitions.Def_FixedPolyominoSquare_SquareCounting_RectangularPartitions

namespace FixedPolyominoSquare.SquareCounting

noncomputable section
attribute [local instance] Classical.propDecidable

def edgePresent (E : Finset (Cell × Cell)) (u v : Cell) : Prop :=
  (u, v) ∈ E ∨ (v, u) ∈ E

def indexComponent (n : ℕ) (E : Finset (Cell × Cell)) (p : Cell) : Region :=
  (square n).filter fun q => Relation.ReflTransGen (edgePresent E) p q

def windowEdge (p : Cell) (i : Fin 4) : Cell × Cell :=
  if i = 0 then (p, p + (1, 0)) else
  if i = 1 then (p + (1, 0), p + (1, 1)) else
  if i = 2 then (p + (0, 1), p + (1, 1)) else
    (p, p + (0, 1))

def windowOpen (E : Finset (Cell × Cell)) (p : Cell) (i : Fin 4) : Prop :=
  edgePresent E (windowEdge p i).1 (windowEdge p i).2

def Saturated (n : ℕ) (E : Finset (Cell × Cell)) : Prop :=
  ∀ p ∈ square (n - 1), ∀ i : Fin 4,
    windowOpen E p i → windowOpen E p (i + 1) → ∀ j, windowOpen E p j

def FilledRectangle (n : ℕ) (E : Finset (Cell × Cell)) (B : Region) : Prop :=
  IsDiscreteRectangle B ∧ ∀ e ∈ gridEdges n,
    e.1 ∈ B → e.2 ∈ B → edgePresent E e.1 e.2

def Lmac (P c n : ℕ) : ℕ := P * n + 2 * c

def macroCoord (P c n i : ℕ) : ℤ :=
  if i = 0 then 0 else if i = n then (Lmac P c n : ℤ) else (c + P * i : ℕ)

def macrocell (P c n : ℕ) (p : Cell) : Region :=
  (Finset.Ico (macroCoord P c n p.1.toNat) (macroCoord P c n (p.1.toNat + 1))).product
    (Finset.Ico (macroCoord P c n p.2.toNat) (macroCoord P c n (p.2.toNat + 1)))

def macroGraph (P c n : ℕ) (T : TileFamily) (pi : Finset (Placement T)) : Finset (Cell × Cell) :=
  (gridEdges n).filter fun e => ∃ t ∈ pi, ∃ a ∈ support T t, ∃ b ∈ support T t,
    a ∈ macrocell P c n e.1 ∧ b ∈ macrocell P c n e.2 ∧ gridAdjacent a b

def metMacrocells (P c n : ℕ) (s : Region) : Region :=
  (square n).filter fun p => ¬ Disjoint s (macrocell P c n p)

def indexComponents (n : ℕ) (E : Finset (Cell × Cell)) : Finset Region :=
  (square n).image (indexComponent n E)

def physicalComponents (P c n : ℕ) (E : Finset (Cell × Cell)) : Finset Region :=
  (indexComponents n E).image fun B => B.biUnion (macrocell P c n)

def tileDiameter (T : TileFamily) : ℕ :=
  Finset.univ.sup fun t => ((T.shape t).product (T.shape t)).sup fun p =>
    max (p.1.1 - p.2.1).natAbs (p.1.2 - p.2.2).natAbs

def macroWindow (P c n : ℕ) (p : Cell) : Region :=
  ({p, p + (1, 0), p + (0, 1), p + (1, 1)} : Region).biUnion (macrocell P c n)

def closedNeighbourhood (d : ℕ) (s : Region) : Region :=
  s.biUnion fun p =>
    ((Finset.Icc (-(d : ℤ)) (d : ℤ)).product (Finset.Icc (-(d : ℤ)) (d : ℤ))).image
      (fun v => p + v)

def windowPlacements (P c n : ℕ) (T : TileFamily) (pi : Finset (Placement T))
    (p : Cell) : Finset (Placement T) :=
  pi.filter fun t => ¬ Disjoint (support T t) (macroWindow P c n p)

end
end FixedPolyominoSquare.SquareCounting


