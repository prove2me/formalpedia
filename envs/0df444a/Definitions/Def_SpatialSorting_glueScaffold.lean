-- Prove2me | Definitions.Def_SpatialSorting_glueScaffold
-- name    : SpatialSorting_glueScaffold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:20.692169+00:00
-- url     : https://prove2.me/theorems/3417b469-01bc-42f2-b30e-0f725b0e28b6
-- title:
--   The gluing map $\Psi_{\mathcal S}$
-- statement:
--   For a family of regional configurations $\tau_k:V_k\to\{0,\dots,q-1\}$ on the complementary components of $\mathcal S$, $\Psi_{\mathcal S}((\tau_k)_k)=\sigma$ with $\sigma|_{\overline{\mathcal S}}=\omega_{\mathcal S}$ and $\sigma|_{V_k}=\tau_k$.
--
--   **Formalization Note** The result is recorded by its values on $I_L$ (a `Coloring`); the values on $B_L$ are read back through the extension by $0$, so Lemma 3.11's statement that $\Phi_{\mathcal S}\circ\Psi_{\mathcal S}=\mathrm{id}$ includes the claim that the glued configuration vanishes on $B_L$.
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.11, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_jointColor
import Definitions.Def_SpatialSorting_comps
open Classical Filter Topology

namespace SpatialSorting

/-- `Ψ_𝒮((τ_k)_k)`: the configuration equal to `ω_𝒮` on `𝒮̄` and to `τ_k` on `V_k`.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.11, p. 21 (PDF p. 22). -/
noncomputable def glueScaffold {q L : ℕ} [NeZero q] (S : Finset (Contour q))
    (τ : (V : {V // V ∈ comps L S}) → ({v // v ∈ V.1} → Fin q)) : Coloring q L :=
  fun v => if h : ∃ V : {V // V ∈ comps L S}, v.1 ∈ V.1 then τ h.choose ⟨v.1, h.choose_spec⟩
    else jointColor S v.1

end SpatialSorting


