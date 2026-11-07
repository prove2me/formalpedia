-- Prove2me | Definitions.Def_SecondBestBT_alphaVirtualS
-- name    : SecondBestBT_alphaVirtualS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:03.086816+00:00
-- url     : https://prove2.me/theorems/cfe1feeb-aee0-4a47-9c7d-13736e5e1bb9
-- title:
--   Seller's $\alpha$-virtual value $\varphi^\alpha_S(s)$
-- statement:
--   Given $\alpha\ge0$ and a discrete seller prior on the unit integer grid, the seller's **$\alpha$-virtual value** at a positive-mass point $s$ is
--   $$
--   \varphi^\alpha_S(s)=(1+\alpha)s+\alpha\,\frac{F_S(s-1)}{f_S(s)},\qquad F_S(-1)=0 .
--   $$
--
--   **Formalization Note** $F_S(s-1)=\sum_{k<s}f_S(k)$. The value is used only at points of a full-support seller's support $\{0,\dots,K\}$, where $f_S(s)>0$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Definition 4.1, p.9

import Mathlib

namespace SecondBestBT

/-- The seller's `α`-virtual value on the unit integer grid,
`φ^α_S(s) := (1 + α) s + α F_S(s − 1) / f_S(s)` with `F_S(−1) = 0` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Definition 4.1, p.9).

**Formalization Note** `F_S(s − 1) = ∑_{k < s} f_S(k)`. The paper defines `φ^α_S` on
positive-mass points only; every use in the mission is at a point of a full-support seller's
support `{0, …, K}`, where `f_S(s) > 0`. -/
noncomputable def alphaVirtualS (α : ℝ) (fS : ℕ → ℝ) (s : ℕ) : ℝ :=
  (1 + α) * s + α * (∑ k ∈ Finset.range s, fS k) / fS s

end SecondBestBT


