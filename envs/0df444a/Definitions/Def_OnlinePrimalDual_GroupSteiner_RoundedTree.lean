-- Prove2me | Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
-- name    : OnlinePrimalDual_GroupSteiner_RoundedTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:55:21.659199+00:00
-- url     : https://prove2.me/theorems/9a8cdbf0-7883-4530-95d3-158c26ead07c
-- title:
--   The rooted tree data the rounding algorithm runs on
-- statement:
--   `RoundedTree E` bundles: `parent : E → Option E`, the edge adjacent to `e` and closer to the
--   root (`e(p)` in the book's notation, `none` exactly when `e` is incident to the root), and a
--   non-negative cost function `cost : E → ℝ`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 224, 229, Section 11.1-11.2

import Mathlib

namespace OnlinePrimalDual.GroupSteiner

/-- The rooted tree data the online group-Steiner rounding algorithm runs on (Buchbinder & Naor,
FnT TCS 2009, Section 11.2, p. 229): a finite edge type `E`, each edge's parent edge `parent e`
(the edge adjacent to `e` and closer to the root `r`, `e(p)` in the book's notation, `none`
exactly when `e` is incident to `r`), and a non-negative cost function. -/
structure RoundedTree (E : Type*) [Fintype E] [DecidableEq E] where
  /-- `parent e` is the edge adjacent to `e` and closer to the root (`e(p)`, p. 229); `none` iff
  `e` is incident to the root. -/
  parent : E → Option E
  /-- The non-negative edge cost `c : E → ℝ₊` (p. 224). -/
  cost : E → ℝ
  hcost_nonneg : ∀ e, 0 ≤ cost e

end OnlinePrimalDual.GroupSteiner


