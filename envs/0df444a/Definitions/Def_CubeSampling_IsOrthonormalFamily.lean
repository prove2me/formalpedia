-- Prove2me | Definitions.Def_CubeSampling_IsOrthonormalFamily
-- name    : CubeSampling_IsOrthonormalFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:11.735928+00:00
-- url     : https://prove2.me/theorems/6f81934e-8cc8-489c-9c0d-0ddfd3d80602
-- title:
--   Orthonormal family $\Phi = (\varphi_1,\dots,\varphi_m)$ in $L^2(\mu_d)$
-- statement:
--   A family $\Phi = (\varphi_1, \dots, \varphi_m)$ of real functions on $\{-1,1\}^d$ is **orthonormal** if
--   $$
--   \mathbb E[\varphi_i \varphi_j] = \begin{cases} 1, & i = j,\\ 0, & i \ne j.\end{cases}
--   $$
--   An $m$-dimensional model $V$ is supplied to the learner through such an orthonormal basis $\Phi_V$, so that $f_\theta = \theta^\top \Phi_V$.
--
--   **Formalization Note** The subspace $V$ is encoded by its orthonormal basis ($V = \operatorname{span}\Phi$, $\dim V = m$); the paper notes that the choice of the basis does not affect the estimation problem.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_cubeMean

namespace CubeSampling

/-- `Φ = (φ_1, …, φ_m)` is orthonormal in `L²(μ_d)`: `E[φ_i φ_j] = 1` if `i = j` and `0` otherwise
(Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3).

**Formalization Note** The paper's subspace `V` of dimension `m` is encoded by an orthonormal basis
`Φ_V` of it (`V = span Φ`); the paper notes that the choice of the basis does not affect the
estimation problem. -/
def IsOrthonormalFamily {d m : ℕ} (Φ : Fin m → Cube d → ℝ) : Prop :=
  ∀ i j, cubeMean d (fun x => Φ i x * Φ j x) = if i = j then 1 else 0

end CubeSampling


