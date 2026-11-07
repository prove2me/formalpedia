-- Prove2me | Definitions.Def_DimFreeShadow_gridValue
-- name    : DimFreeShadow_gridValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:44.471289+00:00
-- url     : https://prove2.me/theorems/dc6f0a77-b932-4188-9582-b0b4f4e35455
-- title:
--   The output grid $\mathcal Z_\epsilon=\{k/K_\epsilon\}^M$, $K_\epsilon=\lceil 2/\epsilon\rceil$
-- statement:
--   For an accuracy $\epsilon\in(0,1]$ put $K_\epsilon=\lceil 2/\epsilon\rceil$ and
--
--   $$
--   \mathcal Z_\epsilon=\{k/K_\epsilon: 0\le k\le K_\epsilon\}^M .
--   $$
--
--   This finite alphabet is fixed before any prior is chosen, so all prior-dependent measurements lie in one compact convex space of POVMs.
--
--   **Formalization Note** A grid point is stored by its integer coordinates, $z:\mathrm{Fin}\,M\to\mathrm{Fin}(K_\epsilon+1)$; `gridValue` returns $z_j=k_j/K_\epsilon$, which is the identity decoder $g(z)=z$ of §5.1.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), §5.1, p.20 (grid), p.21 (identity decoder)

import Mathlib

namespace DimFreeShadow

/-- **Grid resolution** `K_ϵ := ⌈2/ϵ⌉` (arXiv:2608.06345, sha256 a1a42249…, §5.1, p.20). -/
noncomputable def gridSize (ϵ : ℝ) : ℕ := ⌈2 / ϵ⌉₊

/-- **The output grid** `Z_ϵ := {k/K_ϵ : 0 ≤ k ≤ K_ϵ}^M` (arXiv:2608.06345, sha256 a1a42249…,
§5.1, p.20), encoded by the integer coordinates `k`.

**Formalization Note** A grid point is `z : Fin M → Fin (K_ϵ + 1)`; its value is `gridValue`. -/
abbrev Grid (M : ℕ) (ϵ : ℝ) : Type := Fin M → Fin (gridSize ϵ + 1)

/-- **Value of a grid point** `z_j = k_j / K_ϵ ∈ [0,1]` (arXiv:2608.06345, §5.1, p.20). This is
the identity decoder `g(z) = z` of §5.1, p.21. -/
noncomputable def gridValue {M : ℕ} {ϵ : ℝ} (z : Grid M ϵ) (j : Fin M) : ℝ :=
  ((z j : ℕ) : ℝ) / (gridSize ϵ : ℝ)

end DimFreeShadow


