-- Prove2me | Definitions.Def_TreeCoverLB_simplexAct
-- name    : TreeCoverLB_simplexAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:02.34865+00:00
-- url     : https://prove2.me/theorems/a3d2ba4c-ae75-48f1-9fd3-780d8353451e
-- title:
--   Translation action of $\mathbb Z_p$ on $|\Delta_{\mathbb Z_p}|$
-- statement:
--   $G=\mathbb Z_p$ acts on the full simplex $\Delta_G$ by translation of its vertex set; on $|\Delta_G|\subseteq\mathbb R^G$ this permutes coordinates:
--   $$
--   (s\cdot a)_g=a_{g-s}\qquad(s,g\in G).
--   $$
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §5.2, p.19 (PDF p.21)

import Mathlib

namespace TreeCoverLB

/-- The action of `G = ℤ_p` on `|∆_G| ⊆ ℝ^G` induced by translation of the vertex set
(Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §5.2, p.19 (PDF p.21)): `(s · a)_g = a_{g − s}`. -/
def simplexAct {p : ℕ} (s : ZMod p) (a : ZMod p → ℝ) : ZMod p → ℝ :=
  fun g => a (g - s)

end TreeCoverLB


