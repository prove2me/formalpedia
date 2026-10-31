-- Prove2me | Definitions.Def_TractableComposite_zeta
-- name    : TractableComposite_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:46.980434+00:00
-- url     : https://prove2.me/theorems/2994bcfe-b1f1-46d3-8538-1296989ec0b1
-- title:
--   The vertices $\zeta_j$ of $\Delta_i$
-- statement:
--   $\zeta_{j}=\sum_{j'=0}^{j}e_{j'}\in\mathbb R^{n+1}$ is the 0/1 vector with ones in coordinates $0,\dots,j$. The points $\zeta_0\le\dots\le\zeta_n$ are the vertices of $\Delta_i$ and form a chain.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), p.9 and Appendix A, p.35

import Mathlib

namespace TractableComposite

/-- **The vertices ζⱼ of Δᵢ**, Appendix A, p.35 (and p.9): `ζᵢⱼ = ∑_{j'=0}^{j} e_{ij'}`, the 0/1 vector
with ones in coordinates `0,…,j`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), p.9 and Appendix A, p.35.

**Formalization Note.** The vertex does not depend on `i`; `zeta n j l = 1` iff `l ≤ j`. -/
def zeta (n : ℕ) (j : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun l => if l ≤ j then 1 else 0

end TractableComposite


