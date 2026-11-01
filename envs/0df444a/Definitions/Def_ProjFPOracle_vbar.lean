-- Prove2me | Definitions.Def_ProjFPOracle_vbar
-- name    : ProjFPOracle_vbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:24.473276+00:00
-- url     : https://prove2.me/theorems/a9be0986-3e5b-4765-b386-7e4835c42958
-- title:
--   The projected fixed point $\bar v$
-- statement:
--   Given a bounded operator $L$ on $\mathbb X$, a vector $b\in\mathbb X$ and the subspace $\mathbb S$, the **projected fixed point** $\bar v$ is the solution $v\in\mathbb S$ of
--   $$
--   v=\Pi_{\mathbb S}(Lv+b).
--   $$
--   Writing $v=\Phi_d^*\vartheta$ the equation reads $\vartheta=M\vartheta+\Phi_d b$, so when $I_d-M$ is invertible (for instance when $\kappa(M)<1$),
--   $$
--   \bar v=\Phi_d^*\,(I_d-M)^{-1}\,\Phi_d b .
--   $$
--   It is the target that the stochastic approximation algorithm estimates, and its distance to the true fixed point $v^*$ is the approximation error of the mission.
--
--   **Formalization Note** $\bar v$ is defined by the closed form above, computed from $(L,b,\varphi)$, not pinned by a hypothesis; `Solutions/verification/ProjFPOracle_vbar.lean` checks $\bar v\in\mathbb S$ and $\bar v=\Pi_{\mathbb S}(L\bar v+b)$ whenever $I_d-M$ is invertible.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Eq. (2), p.2, and §2.1, p.7

import Mathlib
import Definitions.Def_ProjFPOracle_Phi
import Definitions.Def_ProjFPOracle_projMat

open Matrix

namespace ProjFPOracle

/-- **The projected fixed point `v̄`** (Mou, Pananjady & Wainwright, *Optimal Oracle Inequalities
for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (2), p.2, and §2.1, p.7): the unique
`v ∈ 𝕊` with `v = Π_𝕊(L v + b)`. When `κ(M) < 1` the matrix `I_d − M` is invertible (p.7) and
`v̄ = Φ_d^* (I_d − M)⁻¹ Φ_d b`.

**Formalization Note** `v̄` is computed from the data `(L, b, φ)` by the closed form above, not
pinned by a hypothesis. Writing `v = Φ_d^* ϑ`, the equation `v = Π_𝕊(Lv + b)` reads
`ϑ = M ϑ + Φ_d b`, whence the formula. `(1 − M)⁻¹` is Mathlib's matrix inverse; it is the true
inverse under `κ(M) < 1`, which every statement of the mission assumes. -/
noncomputable def vbar {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {S : Submodule ℝ X} {d : ℕ} (L : X →L[ℝ] X) (b : X) (φ : OrthonormalBasis (Fin d) ℝ S) : X :=
  PhiStar φ ((1 - projMat L φ)⁻¹ *ᵥ Phi φ b)

end ProjFPOracle


