-- Prove2me | Definitions.Def_AdaDiscRL_packingNum
-- name    : AdaDiscRL_packingNum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:57.164262+00:00
-- url     : https://prove2.me/theorems/86f27512-ed71-4a8a-a7f7-f489079748e6
-- title:
--   $r$-packing number $N_r(X)$
-- statement:
--   For a set $X$ in a space with distance $d$ and a radius $r$, the **$r$-packing number** $N_r(X)$ is the largest number of points of $X$ that are pairwise at distance at least $r$:
--   $$
--   N_r(X)=\sup\{|F|: F\subseteq X \text{ finite},\ d(x,y)\ge r\ \text{for all distinct }x,y\in F\}.
--   $$
--   It enters the definition of the zooming dimension and the metric-specific regret bound.
--
--   **Formalization Note** The separation is non-strict ($\ge r$), as the centers of a hierarchical partition are "at distance at least $2^{-\ell}$" (Mathlib's `Metric.packingNumber` is strict). The value lies in $\mathbb N\cup\{\infty\}$. The distance is a parameter, since packings of $\mathcal S\times\mathcal A$ are taken in $\mathcal D$.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, §2.3, p.10

import Mathlib

namespace AdaDiscRL

/-- **`r`-packing number** `N_r(X)` (arXiv:2110.15843v3, §2.3, p.10, used in Definitions 2.6–2.7):
the largest size of a finite subset of `X` whose points are pairwise at distance at least `r`
under the distance function `d`.

**Formalization Note.** Non-strict separation (`r ≤ d x y`), as the paper's packings are the
centers of the hierarchical partition "at a distance at least `2^{−ℓ}`" (p.14, p.37); Mathlib's
`Metric.packingNumber` is strict. Valued in `ℕ∞` (`⊤` if unbounded). The distance is a parameter
because packings of `S × A` are taken in the metric `D`. -/
noncomputable def packingNum {α : Type*} (d : α → α → ℝ) (r : ℝ) (X : Set α) : ℕ∞ :=
  ⨆ (F : Finset α) (_ : (F : Set α) ⊆ X) (_ : (F : Set α).Pairwise (fun x y => r ≤ d x y)),
    (F.card : ℕ∞)

end AdaDiscRL


