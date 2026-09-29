-- Prove2me | Definitions.Def_Rectangle_defs
-- name    : Rectangle_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:49:01.5988+00:00
-- url     : https://prove2.me/theorems/f0413c26-b3e9-4a89-8c2c-581c3b41fb28
-- title:
--   Axis-parallel rectangles in $\mathbb{C}$: the rectangle border determined by two corners
-- statement:
--   This bundle provides the basic geometry of axis-parallel rectangles in the complex plane, the domains over which all contour integration in the PNT+ project takes place. A rectangle is determined by two opposite corners $z, w \in \mathbb{C}$: it is the product set $[z.\mathrm{re}, w.\mathrm{re}] \times_{\mathbb{C}} [z.\mathrm{im}, w.\mathrm{im}]$ of points whose real part lies between the real parts of the corners and whose imaginary part lies between their imaginary parts (unordered intervals $[[\cdot,\cdot]]$ make the definition symmetric in the corners).
--
--   **Main definition.**
--
--   - `RectangleBorder z w` — the boundary of the rectangle with corners $z$ and $w$, given as the union of its four sides: the bottom edge $[[z.\mathrm{re}, w.\mathrm{re}]] \times_{\mathbb{C}} \{z.\mathrm{im}\}$, the left edge $\{z.\mathrm{re}\} \times_{\mathbb{C}} [[z.\mathrm{im}, w.\mathrm{im}]]$, the top edge $[[z.\mathrm{re}, w.\mathrm{re}]] \times_{\mathbb{C}} \{w.\mathrm{im}\}$, and the right edge $\{w.\mathrm{re}\} \times_{\mathbb{C}} [[z.\mathrm{im}, w.\mathrm{im}]]$.
--
--   **Downstream use.** Rectangle membership, interiors, and borders are the combinatorial backbone of the rectangle residue calculus: contour integrals over rectangles are defined edge by edge, holomorphy hypotheses are stated on rectangles minus finitely many poles, and pole-location arguments distinguish interior points from border points. These are used to shift vertical contours and extract residues of $-\zeta'/\zeta$ in the prime number theorem proof.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean (definitions vendored from this file)

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle


end Rectangle

/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]


