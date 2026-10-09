-- Prove2me | Definitions.Def_InventoryBounds_Primitives
-- name    : InventoryBounds_Primitives
-- status  : Definition
-- author  : @visuddhi
-- created : 2026-10-08T15:30:51.057922+00:00
-- url     : https://prove2.me/theorems/b80068cd-9293-42c4-9cd4-aa4d6bfc7a8d
-- title:
--   Inventory stage cost, sales and lost-sales transition
-- statement:
--   Real-valued stage cost h max(y-d,0)+p max(d-y,0), sales min(d,y), and leftover inventory max(y-d,0). Domain and positivity assumptions belong to theorems, not these total algebraic definitions.
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Sections 2.1 and 3.3

import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace InventoryBounds

noncomputable def stageCost (h p y d : ℝ) : ℝ :=
  h * max (y - d) 0 + p * max (d - y) 0

def lostNext (y d : ℝ) : ℝ := max (y - d) 0

def sales (y d : ℝ) : ℝ := min d y

end InventoryBounds


