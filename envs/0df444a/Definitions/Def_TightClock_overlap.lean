-- Prove2me | Definitions.Def_TightClock_overlap
-- name    : TightClock_overlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:44.677984+00:00
-- url     : https://prove2.me/theorems/1c469e59-f32d-445d-8846-7519f66aeb0f
-- title:
--   Maximum overlap $d$ of the maximal feasible sets
-- statement:
--   Let $G_1,\dots,G_k$ be the distinct maximal sets of a feasibility family $\mathcal F\subseteq 2^N$. For a bidder $i$ put $\Gamma_i=\{j: i\in G_j\}$. The **overlap** of $\mathcal F$ is
--
--   $$d=\max_{i\in N}|\Gamma_i|,$$
--
--   the largest number of maximal feasible sets containing one bidder. Theorem 6.1 notes that its instances have $d\le k$.
--
--   **Formalization Note** Bidders are `Fin n`, and with no bidders the maximum is $0$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_BayesClock_maximalSets

set_option autoImplicit false

namespace TightClock

/-- The maximum overlap `d = maxᵢ |Γᵢ|` of the maximal feasible sets at a bidder, where
`Γᵢ = {j : i ∈ Gⱼ}`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript
(STOC 2027 submission), §3, p.13 (PDF 16).

**Formalization Note** Bidders are `Fin n`. With no bidders the maximum is `0`. -/
def overlap {n : ℕ} (F : Finset (Finset (Fin n))) : ℕ :=
  Finset.univ.sup (fun i : Fin n => ((BayesClock.maximalSets F).filter (fun G => i ∈ G)).card)

end TightClock


