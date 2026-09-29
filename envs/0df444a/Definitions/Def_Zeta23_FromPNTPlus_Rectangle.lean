-- Prove2me | Definitions.Def_Zeta23_FromPNTPlus_Rectangle
-- name    : Zeta23_FromPNTPlus_Rectangle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T19:57:51.32387+00:00
-- url     : https://prove2.me/theorems/eecb5b52-3102-4960-8727-baa0c0253630
-- title:
--   Rectangles in $\mathbb{C}$: the border of a rectangle
-- statement:
--   This bundle (ported from the PrimeNumberTheoremAnd project, file `Rectangle.lean`) defines **`RectangleBorder`**: for two corners $z, w \in \mathbb{C}$, the border of the axis-parallel rectangle they determine, as the union of its four sides
--   $$[\![z.\mathrm{re}, w.\mathrm{re}]\!] \times \{z.\mathrm{im}\}\ \cup\ \{z.\mathrm{re}\} \times [\![z.\mathrm{im}, w.\mathrm{im}]\!]\ \cup\ [\![z.\mathrm{re}, w.\mathrm{re}]\!] \times \{w.\mathrm{im}\}\ \cup\ \{w.\mathrm{re}\} \times [\![z.\mathrm{im}, w.\mathrm{im}]\!]$$
--   (using unordered intervals, so the definition is symmetric in the corners; $A \times B$ here denotes the complex product set $\{x + iy : x \in A, y \in B\}$).
--
--   The surrounding module develops the basic geometry of rectangles in $\mathbb{C}$ used by the contour-integration machinery. In the project it underlies `ResidueCalcOnRectangles`, the `RectangleLogDeriv` weighted argument principle, and the `ZetaBounds` port — the complex-analytic backbone of the zero-counting side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/Rectangle.lean

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Rectangle.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
@[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle

/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]


