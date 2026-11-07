-- Prove2me | Definitions.Def_ArgmaxDeFinetti_hsDist
-- name    : ArgmaxDeFinetti_hsDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:15.201897+00:00
-- url     : https://prove2.me/theorems/c94191c8-c4f8-4e11-b17d-d001baa2cb4f
-- title:
--   Hilbert–Schmidt distance $D_{\mathrm{HS}}(\rho,\sigma)=\|\rho-\sigma\|_2$
-- statement:
--   The unnormalized Hilbert–Schmidt distance of two square matrices is
--   $$
--   D_{\mathrm{HS}}(\rho,\sigma)=\|\rho-\sigma\|_2,\qquad \|X\|_2=(\operatorname{Tr}X^\dagger X)^{1/2}.
--   $$
--   It enters the Hilbert–Schmidt halves (2.10), (2.12) of the distance duality.
--
--   **Formalization Note** $\|\cdot\|_2$ is the published `WildeQIT.hsNorm`.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18, eq. (2.2)

import Mathlib
import Definitions.Def_WildeQIT_hsNorm

open Matrix

namespace ArgmaxDeFinetti

/-- The unnormalized Hilbert–Schmidt distance `D_HS(ρ, σ) = ∥ρ − σ∥₂`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (2.2), p.18.

**Formalization Note** `∥X∥₂ = (Tr X†X)^{1/2}` is the published `WildeQIT.hsNorm`. -/
noncomputable def hsDist {ι : Type} [Fintype ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  WildeQIT.hsNorm (ρ - σ)

end ArgmaxDeFinetti


