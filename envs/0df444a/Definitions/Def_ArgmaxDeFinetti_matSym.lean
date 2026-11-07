-- Prove2me | Definitions.Def_ArgmaxDeFinetti_matSym
-- name    : ArgmaxDeFinetti_matSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:36.10729+00:00
-- url     : https://prove2.me/theorems/26bebcb9-a16a-4308-a19d-8dbd7d9511e5
-- title:
--   The matrix $\mathrm{Mat}(\zeta)$ of a two-site vector
-- statement:
--   For $\zeta\in\mathbb C^d\otimes\mathbb C^d$ and the standard basis $(e_i)$ of $\mathbb C^d$, $Z=\mathrm{Mat}(\zeta)$ is the coefficient matrix in
--   $$
--   \zeta=\sum_{i,j=1}^d Z_{ij}\,e_i\otimes e_j ;
--   $$
--   for $\zeta\in\mathrm{Sym}^2(\mathbb C^d)$ it is complex symmetric, $Z^{\mathsf T}=Z$. The module also views $\zeta$ as an element of $\mathcal X\otimes\mathcal Y$ with $\mathcal X=\mathcal Y=\mathbb C^d$, to which the tensor norms (2.13)–(2.14) apply.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §3.1.3, p.25, eq. (3.12)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_tensorPow

open Matrix

namespace ArgmaxDeFinetti

/-- A two-site vector `ζ ∈ ℂ^d ⊗ ℂ^d` as a function of a pair of indices, i.e. as an element of `X ⊗ Y` with
`X = Y = ℂ^d`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.3, p.21. -/
def pairOf {d : ℕ} (ζ : Vec 2 d) : Fin d × Fin d → ℂ :=
  fun p => ζ ![p.1, p.2]

/-- `Mat(ζ)`: the coefficient matrix `Z` in `ζ = Σ_{i,j} Z_{ij} e_i ⊗ e_j` for the standard orthonormal basis
`(e_i)` of `ℂ^d`; for `ζ ∈ Sym²` it satisfies `Zᵀ = Z`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eq. (3.12), p.25. -/
def matSym {d : ℕ} (ζ : Vec 2 d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ζ ![i, j]

end ArgmaxDeFinetti


