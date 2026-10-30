-- Prove2me | Definitions.Def_DDROFB_supportFn
-- name    : DDROFB_supportFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:02:36.320892+00:00
-- url     : https://prove2.me/theorems/3454baec-f70f-47a2-817d-359a90a9e9da
-- title:
--   Support function $\delta^*(v \mid \mathcal U)$ of a set
-- statement:
--   Let $\mathcal U \subseteq \mathbb R^d$ and $v \in \mathbb R^d$. The **support function** of $\mathcal U$ at $v$ is
--
--   $$
--   \delta^*(v \mid \mathcal U) \;=\; \sup_{u \in \mathcal U} v^\top u .
--   $$
--
--   The support function links uncertainty sets to probabilistic guarantees: by Theorem 1(a) of the paper, a nonempty convex compact set implies a guarantee at level $\epsilon$ as soon as its support function dominates the Value at Risk in every direction.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $v^\top u$ the Euclidean inner product. The supremum is a real `sSup`, which Lean sets to $0$ on the empty set and on sets where $u \mapsto v^\top u$ is unbounded above; the mission applies it only to nonempty compact sets, and states the support function (24) of the set (23) as a least upper bound instead.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 2.1, p. 7 (unnumbered definition of δ∗(v| U))

import Mathlib
open InnerProductSpace

namespace DDROFB

/-- **Support function of a set** `δ*(v | U)`.
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 2.1, p. 7
(unnumbered): "`δ∗(v| U) ≡ sup_{u∈U} vᵀu`".

`supportFn U v` is the supremum of `⟪v, u⟫` over `u ∈ U`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` and `vᵀu` is the Euclidean inner
product. The value is a real `sSup`, which Lean sets to `0` on the empty set and on sets on which
`u ↦ vᵀu` is unbounded above. The statements of this mission apply `supportFn` only to nonempty
compact sets (Theorems 1(a) and 3(a)), where it is the true supremum; the support function (24) of
the forward–backward set (23) is stated with `IsLUB` instead. -/
noncomputable def supportFn {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun u => ⟪v, u⟫_ℝ) '' U)

end DDROFB


