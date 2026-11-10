-- Prove2me | Definitions.Def_RandTreeUniv_InT1
-- name    : RandTreeUniv_InT1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:15.450551+00:00
-- url     : https://prove2.me/theorems/f2bdcdf0-290d-411f-8916-0070dc96b2c1
-- title:
--   The family $\mathcal T_1$ (trees with $K\alpha$ long bare paths)
-- statement:
--   Let $K$ be the large constant of §4 and $\alpha=n\ln\ln n/(K^3\ln n)$ (display (11)). The family $\mathcal T_1\subseteq\mathcal T_{n,\Delta}$ consists of the trees on $n$ vertices with maximum degree at most $\Delta$ that have $K\alpha$ vertex-disjoint bare paths of length $n/(K^2\alpha)$.
--
--   **Formalization Note** Rounded up: $\lceil K\alpha\rceil$ paths of length $\lceil n/(K^2\alpha)\rceil$. Since a sub-path of a bare path is bare, this equals "at least $K\alpha$ such paths of length at least $n/(K^2\alpha)$".
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §4, p.21 (PDF 22); α with ψ = 1 as in §6, p.31 (PDF 32)

import Mathlib
import Definitions.Def_RandTreeUniv_InTreeFamily
import Definitions.Def_RandTreeUniv_IsBarePathFamily
import Definitions.Def_RandTreeUniv_alpha

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `T ∈ T₁` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §4, p.21 (PDF 22)): `T` is a tree on `n` vertices with maximum degree at most
`∆` that has `Kα` vertex-disjoint bare paths of length `n/(K²α)`, where `α = n ln ln n/(K³ ln n)`
(display (11); `ψ = 1`, the convention of §6, p.31 (PDF 32)).

**Formalization Note** Rounded up: `⌈Kα⌉` paths of length `⌈n/(K²α)⌉`. Since a sub-path of a bare
path is bare, this is the same as "at least `Kα` vertex-disjoint bare paths of length at least
`n/(K²α)`". -/
def InT1 (n : ℕ) (K : ℝ) (Δ : ℕ) (T : SimpleGraph (Fin n)) : Prop :=
  InTreeFamily Δ T ∧
    ∃ (u w : Fin ⌈K * alpha K 1 n⌉₊ → Fin n) (P : ∀ i, T.Walk (u i) (w i)),
      IsBarePathFamily T u w P ⌈(n : ℝ) / (K ^ 2 * alpha K 1 n)⌉₊

end RandTreeUniv


