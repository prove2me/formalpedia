-- Prove2me | Definitions.Def_IsotropicSpin_densityOutputEntropies
-- name    : IsotropicSpin_densityOutputEntropies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:25.007355+00:00
-- url     : https://prove2.me/theorems/c9cb9d38-31a5-4678-b8b2-e2a43fb06b04
-- title:
--   Output entropies $\{S(\Lambda(\rho))\}$ over density matrices
-- statement:
--   For a linear map $\Lambda$ from $n\times n$ to $m\times m$ complex matrices, this is the set of real numbers
--
--   $$
--   \{\,S(\Lambda(\rho)) : \rho \text{ a density matrix}\,\},
--   $$
--
--   where a density matrix is a positive semidefinite matrix of trace one and $S(\sigma)=-\operatorname{tr}(\sigma\log\sigma)$ is the von Neumann entropy. Its infimum is the first form of the minimal entropy output $S[\Lambda]$ of eq. (1).
--
--   **Formalization Note** $S$ and "density matrix" are the published `WHAdditivity.Renyi.vonNeumannEntropy` (natural logarithm, $0\log 0=0$) and `WHAdditivity.Renyi.IsDensity`.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (1), p.1

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace IsotropicSpin

/-- The set of output entropies `{S(Λ(ρ)) : ρ a density matrix}` whose infimum is the first form
of the minimal entropy output, Alicki, arXiv:quant-ph/0402080v1, eq. (1), p. 1.

**Formalization Note** `S` is the von Neumann entropy `−tr(ρ log ρ)` of the published bundle
`WHAdditivity.Renyi` (natural logarithm, `0 log 0 = 0`); a density matrix is a positive
semidefinite matrix of trace one (`WHAdditivity.Renyi.IsDensity`). -/
def densityOutputEntropies {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) : Set ℝ :=
  {x | ∃ ρ : Matrix ι ι ℂ, WHAdditivity.Renyi.IsDensity ρ ∧
    x = WHAdditivity.Renyi.vonNeumannEntropy (Φ ρ)}

end IsotropicSpin


