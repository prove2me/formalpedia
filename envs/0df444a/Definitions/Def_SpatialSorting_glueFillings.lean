-- Prove2me | Definitions.Def_SpatialSorting_glueFillings
-- name    : SpatialSorting_glueFillings
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:00.44194+00:00
-- url     : https://prove2.me/theorems/5f7684cb-e1f3-4672-8b23-e8c979d1e83e
-- title:
--   The glued configuration $\omega_{\mathcal S}\sqcup\bigsqcup_j\xi_j$
-- statement:
--   For fillings $\xi_j:V^{(j)}\to\{0,\dots,q-1\}$ of the label groups, $\sigma=\omega_{\mathcal S}\sqcup\bigsqcup_j\xi_j$ is the assignment equal to $\xi_j$ on $V^{(j)}$ and to $\omega_{\mathcal S}$ elsewhere (so $0$ outside $D_L$).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.4, p. 37 (PDF p. 38)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_jointColor
import Definitions.Def_SpatialSorting_labelGroup
open Classical Filter Topology

namespace SpatialSorting

/-- `σ = ω_𝒮 ⊔ ⨆_j ξ_j`: `ξ_j` on `V^{(j)}` and `ω_𝒮` elsewhere.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.4, p. 37 (PDF p. 38). -/
noncomputable def glueFillings {q : ℕ} [NeZero q] (L : ℕ) (S : Finset (Contour q))
    (lab : Finset (ℤ × ℤ) → Fin q)
    (ξ : (j : Fin q) → ({v // v ∈ labelGroup L S lab j} → Fin q)) : ℤ × ℤ → Fin q :=
  fun v => if h : ∃ j, v ∈ labelGroup L S lab j then ξ h.choose ⟨v, h.choose_spec⟩
    else jointColor S v

end SpatialSorting


