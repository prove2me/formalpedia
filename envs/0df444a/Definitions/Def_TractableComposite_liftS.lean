-- Prove2me | Definitions.Def_TractableComposite_liftS
-- name    : TractableComposite_liftS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:11.962147+00:00
-- url     : https://prove2.me/theorems/4e6ffee3-2c79-482d-a7a1-aacf9c49261e
-- title:
--   The lifting $\bar u\mapsto\bar s$ (the set $PQ'$)
-- statement:
--   For $u\in P$ and each $i$, let $\xi_i(\cdot;u_i)$ be the discrete function on $[a_{i0},a_{in}]$ equal to $u_{ij}$ at $a_{ij}$ and $-\infty$ elsewhere. The lifting is
--
--   $$\bar s_{ij}=\operatorname{conc}(\xi_i)(a_{ij};u_i),$$
--
--   the value at $a_{ij}$ of the upper concave envelope of the points $(a_{ik},u_{ik})$, $k=0,\dots,n$; $PQ'=\{(u,s)\mid u\in P,\ s=\bar s(u)\}$.
--
--   **Formalization Note.** The envelope at $a_{ij}$ is the supremum of $\sum_k w_ku_{ik}$ over weights $w\ge0$, $\sum_kw_k=1$, $\sum_kw_ka_{ik}=a_{ij}$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (4), p.4

import Mathlib

namespace TractableComposite

/-- **The lifting ū ↦ s̄**, (4), p.4: `s̄ᵢⱼ = conc(ξᵢ)(aᵢⱼ; ūᵢ)`, where `ξᵢ(a; w) = wⱼ` at `a = aᵢⱼ` and `−∞`
otherwise, and `conc(ξᵢ)(·; uᵢ)` is its concave envelope over `[aᵢ₀, aᵢₙ]`; `(ū, s̄)` is the point of
`PQ'`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (4), p.4.

**Formalization Note.** The concave envelope of the discrete function `ξᵢ` at `aᵢⱼ` is the supremum of
`∑ₖ wₖ uᵢₖ` over weights `w ≥ 0`, `∑ wₖ = 1`, with `∑ₖ wₖ aᵢₖ = aᵢⱼ` (convex combinations of the points
`(aᵢₖ, uᵢₖ)`; repeated points add nothing). The set is nonempty (`w = eⱼ`) and bounded above by
`maxₖ uᵢₖ`. -/
noncomputable def liftS {d n : ℕ} (a u : Fin d → Fin (n + 1) → ℝ) : Fin d → Fin (n + 1) → ℝ :=
  fun i j => sSup {y : ℝ | ∃ w : Fin (n + 1) → ℝ, (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
    ∑ k, w k * a i k = a i j ∧ y = ∑ k, w k * u i k}

end TractableComposite


