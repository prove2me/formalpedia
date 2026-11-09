-- Prove2me | Definitions.Def_SecondBestMatch_discVirtualCost
-- name    : SecondBestMatch_discVirtualCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:31.776905+00:00
-- url     : https://prove2.me/theorems/2fb7b957-ca56-48e1-9a91-9e96363dae6d
-- title:
--   Discrete virtual cost $\psi_j$
-- statement:
--   Let a seller prior have support $0\le c_1<\dots<c_H\le1$ with $g_h = \Pr[c=c_h]>0$ and $G_h = \sum_{\ell\le h} g_\ell$. The **virtual cost** is
--   $$
--   \psi(c_h) := c_h + \frac{(c_h - c_{h-1})G_{h-1}}{g_h}\quad(h>1),\qquad \psi(c_1) = c_1.
--   $$
--
--   **Formalization Note** $c_{h-1}$ is the greatest atom below $c_h$, $G_{h-1} = \mu(-\infty,c_h)$ and $g_h = \mu\{c_h\}$. At the bottom atom $\mu(-\infty,c_1) = 0$, so the formula gives $\psi(c_1) = c_1$. Values off the support are never used.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.2, p.10

import Mathlib
import Definitions.Def_SecondBestMatch_atoms

open MeasureTheory Set

namespace SecondBestMatch

/-- The discrete virtual cost of a seller (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2, p.10): at the support point `c_h`,
`ψ(c_h) = c_h + (c_h − c_{h−1}) G_{h−1}/g_h` for `h > 1`, and `ψ(c_1) = c_1`.

**Formalization Note** `c_{h−1}` is the greatest atom below `c`, `G_{h−1} = μ(−∞, c)` and
`g_h = μ{c}`. At the bottom atom `μ(−∞, c) = 0`, so the junk value of `sSup ∅` is multiplied by
`0` and `ψ(c_1) = c_1` as printed. Values off the atoms are never used. -/
noncomputable def discVirtualCost (μ : Measure ℝ) (c : ℝ) : ℝ :=
  c + (c - sSup (atoms μ ∩ Iio c)) * μ.real (Iio c) / μ.real {c}

end SecondBestMatch


