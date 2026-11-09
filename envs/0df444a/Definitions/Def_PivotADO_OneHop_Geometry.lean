-- Prove2me | Definitions.Def_PivotADO_OneHop_Geometry
-- name    : PivotADO_OneHop_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:16.152124+00:00
-- url     : https://prove2.me/theorems/ad482898-1cf2-4c94-bd80-08320bfc5a52
-- title:
--   Graph geometry and the prescribed radii
-- statement:
--   Let $G$ be a finite simple undirected unweighted graph. Write $\delta_G(u,v)$ for its shortest-path distance, equal to $+\infty$ between components, and $m=|E(G)|$ for its number of unordered edges. For a finite girth $g$, real stretch $k\ge1$, degree $d\ge3$ and integer pivot budget $r\ge1$, define
--
--   $$h=\lfloor g/2\rfloor-1,\qquad c=\lfloor g/(k+1)\rfloor-1,\qquad t=1+\lceil\log_{d-1}(4r)\rceil.$$
--
--   These shared quantities keep the milestone conventions identical. Distances use extended nonnegative reals after conversion from extended naturals; $m$ counts an edge only once. Natural subtraction truncates outside the stated regime; the main counting milestones explicitly require $c\ge2t+1$. The threshold $t$ uses the exact integer ceiling logarithm `Nat.clog`.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), §2 and §5.1, (5.2)–(5.3), p.5,17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Mathlib

set_option autoImplicit false
open scoped Classical ENNReal
noncomputable section

namespace PivotADO.OneHop

/-! Kadria–Roditty, STOC 2027 submission #584 (October 2026), §2, p.5,
and §5.1, equations (5.2)–(5.3), p.17. No connectedness convention is imposed. -/

/-- Unweighted distance, including infinity between components. -/
def distance {V : Type*} (G : SimpleGraph V) (u v : V) : ℝ≥0∞ :=
  (G.edist u v).toENNReal

/-- Number of unordered stored edges; diagonal pairs are not edges. -/
def edgeCount {V : Type*} (G : SimpleGraph V) : ℕ := Nat.card G.edgeSet

/-- The radius h in Lemma 6. -/
def treeRadius (g : ℕ) : ℕ := g / 2 - 1

/-- The distance c fixed by §5.1, with natural subtraction. -/
def pairDistance (g : ℕ) (k : ℝ) : ℕ := ⌊(g : ℝ) / (k + 1)⌋₊ - 1

/-- The alignment threshold t; for d ≥ 3 and r ≥ 1, clog is the exact ceiling. -/
def alignmentDepth (d r : ℕ) : ℕ := 1 + Nat.clog (d - 1) (4 * r)

end PivotADO.OneHop


