-- Prove2me | Definitions.Def_ParamSDPTraj_pinv
-- name    : ParamSDPTraj_pinv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:40.400724+00:00
-- url     : https://prove2.me/theorems/a990798c-9a1b-4294-bb53-1ee7207b3220
-- title:
--   The pseudo-inverse $\mathcal A^*(t)(\mathcal A(t)\mathcal A^*(t))^{-1}$
-- statement:
--   The **pseudo-inverse** of $\mathcal A(t)$ is the map
--
--   $$v\longmapsto \mathcal A^*(t)\big[(\mathcal A(t)\mathcal A^*(t))^{-1}v\big].$$
--
--   Assumption 3.1 asks that its norm be bounded uniformly in $t$.
--
--   **Formalization Note** Lean's matrix inverse is $0$ on a singular matrix. Every statement using this map assumes LICQ on $T$, so the Gram matrix is invertible at each $t\in T$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Assumption 3.1, p.12

import Mathlib
import Definitions.Def_ParamSDPTraj_adjA
import Definitions.Def_ParamSDPTraj_gram

namespace ParamSDPTraj

/-- **The pseudo-inverse 𝒜*(t)(𝒜(t)𝒜*(t))⁻¹.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Assumption 3.1, p.12: "its pseudo-inverse A∗(t)(A(t)A∗(t))−1".

**Formalization Note** `Matrix.inv` returns `0` on a singular matrix. Every statement using `pinv`
assumes LICQ on T, under which the Gram matrix is invertible at every t ∈ T. -/
noncomputable def pinv {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (v : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  adjA A t ((gram A t)⁻¹.mulVec v)

end ParamSDPTraj


