-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_PolyominoModel
-- name    : FixedPolyominoSquare_SquareCounting_PolyominoModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:53.496775+00:00
-- url     : https://prove2.me/theorems/c3812ef5-c405-4848-a81e-af9640fdd981
-- title:
--   Finite connected polyominoes and translation-only tilings
-- statement:
--   A cell is a point of $\mathbb Z^2$. A region is a finite set of cells. Two cells are grid-adjacent when their difference is a horizontal or vertical unit vector. A polyomino is a nonempty region in which every two cells can be joined by a finite path of such edges lying in the region.
--
--   A finite indexed family $T=(\tau_t)_{t\in\operatorname{Fin}(k)}$ admits placements $(t,v)$, with support $\tau_t+v$. A tiling is a finite set of placements whose supports are pairwise disjoint and whose union is the region. Distinct indices remain distinct, and rotations and reflections are absent. Candidate anchors are enumerated as $b-a$ for a region cell $b$ and a prototile cell $a$; this enumerates every possible placement of each nonempty tile. Filtering the powerset of these candidates counts placement sets once, without multiplying by choices of the witnessing cells.
--
--   $$\mathrm{Square}_n=\{0,\ldots,n-1\}^2,\qquad g_T(n)=|\operatorname{Tilings}_T(\mathrm{Square}_n)|,\qquad G_T(z)=\begin{cases}g_T(n)&z=\operatorname{bin}(n),\\0&\text{otherwise}.\end{cases}$$
--
--   The empty square has one empty tiling, including for the empty family. Empty prototiles are excluded by the polyomino hypotheses of every applicable theorem. The finite candidate enumeration is not intended as a tiling model for families containing an empty prototile.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 3, Section 2

import Mathlib
import Definitions.Def_FixedPolyominoSquare_SquareCounting_BinaryModel

namespace FixedPolyominoSquare.SquareCounting

abbrev Cell := ℤ × ℤ
abbrev Region := Finset Cell

def gridAdjacent (a b : Cell) : Prop :=
  (a.1 = b.1 ∧ (a.2 - b.2).natAbs = 1) ∨
    (a.2 = b.2 ∧ (a.1 - b.1).natAbs = 1)

/-- Connectivity of the induced unit-edge graph, including the nonempty condition. -/
def FourConnected (s : Region) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s,
    Relation.ReflTransGen (fun u v => u ∈ s ∧ v ∈ s ∧ gridAdjacent u v) a b

def IsPolyomino (s : Region) : Prop := FourConnected s

def rect (w h : ℕ) : Region :=
  ((Finset.range w).product (Finset.range h)).image
    (fun p => ((p.1 : ℤ), (p.2 : ℤ)))

def square (n : ℕ) : Region := rect n n

def translate (s : Region) (v : Cell) : Region :=
  s.image (fun a => a + v)

/-- Indices remain distinct even when two prototile supports coincide. -/
structure TileFamily where
  size : ℕ
  shape : Fin size → Region

abbrev Placement (T : TileFamily) := Fin T.size × Cell

def support (T : TileFamily) (p : Placement T) : Region :=
  translate (T.shape p.1) p.2

/-- Every contained placement of a nonempty prototile occurs in this finite set:
choose a prototile cell `a` and its translated region cell `b`, so the anchor is `b-a`.
Containment and exact coverage are checked separately, without counting this witness. -/
def placementCandidates (T : TileFamily) (Ω : Region) : Finset (Placement T) :=
  Finset.univ.biUnion fun t =>
    Ω.biUnion fun b => (T.shape t).image fun a => (t, b - a)

def IsTiling (T : TileFamily) (Ω : Region) (pi : Finset (Placement T)) : Prop :=
  (∀ p ∈ pi, support T p ⊆ Ω) ∧
  (∀ p ∈ pi, ∀ q ∈ pi, p ≠ q → Disjoint (support T p) (support T q)) ∧
  pi.biUnion (support T) = Ω

noncomputable def tilings (T : TileFamily) (Ω : Region) : Finset (Finset (Placement T)) := by
  classical
  exact (placementCandidates T Ω).powerset.filter (IsTiling T Ω)

noncomputable def g (T : TileFamily) (n : ℕ) : ℕ := (tilings T (square n)).card

noncomputable def G (T : TileFamily) (z : Bits) : ℕ :=
  match decode z with
  | some n => g T n
  | none => 0

end FixedPolyominoSquare.SquareCounting


