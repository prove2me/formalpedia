-- Prove2me | Definitions.Def_TractableComposite_AmapJ
-- name    : TractableComposite_AmapJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:52.169992+00:00
-- url     : https://prove2.me/theorems/c72075b5-f972-4ccf-8c68-b1586aa5e205
-- title:
--   The affine map $A:s_J\mapsto\tilde s$ of (18)
-- statement:
--   For $J\in\mathcal J$, $A$ sends $s_J$ to $\tilde s$ with $\tilde s_{ij}=s_{ij}$ for $j\in J_i$ and $\tilde s_{ij}=(1-\gamma_{ij})s_{i\,l(i,j)}+\gamma_{ij}s_{i\,r(i,j)}$ for $j\notin J_i$. It maps $Q_J$ onto $F_J$.
--
--   **Formalization Note.** $A(y)=\Gamma_J((y,0))$; since $\Gamma_J$ reads only coordinates in $J$, the padding is never read.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (18), pp.13–14

import Mathlib
import Definitions.Def_TractableComposite_gammaJ
import Definitions.Def_TractableComposite_padJ

namespace TractableComposite

/-- **The affine map A : s_J ↦ s̃**, (18), pp.13–14: `s̃ᵢⱼ = sᵢⱼ` for `j ∈ Jᵢ` and
`s̃ᵢⱼ = (1 − γᵢⱼ) s_{i l(i,j)} + γᵢⱼ s_{i r(i,j)}` for `j ∉ Jᵢ`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (18), pp.13–14.

**Formalization Note.** `A(y) = Γ_J((y, 0))`: for `J ∈ 𝒥`, `Γ_J` reads only coordinates in `J`, so the
padding by `0` is never read and this is exactly (18). -/
noncomputable def AmapJ {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (J : Fin d → Finset (Fin (n + 1)))
    (y : (i : Fin d) → J i → ℝ) : Fin d → Fin (n + 1) → ℝ :=
  gammaJ a J (padJ J y)

end TractableComposite


