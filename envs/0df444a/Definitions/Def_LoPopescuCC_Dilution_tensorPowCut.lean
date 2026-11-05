-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_tensorPowCut
-- name    : LoPopescuCC_Dilution_tensorPowCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:08.287109+00:00
-- url     : https://prove2.me/theorems/4d5a59eb-1be6-420f-abe4-313fd264d6b5
-- title:
--   $\psi^{N}$ across the cut $A^N:B^N$
-- statement:
--   Let $\psi\in\mathcal H_A\otimes\mathcal H_B$ be a bipartite vector with amplitudes $\psi(i,j)$ in product bases. Its $N$-th tensor power, regarded as a bipartite vector of Alice's $N$ systems and Bob's $N$ systems, is the vector $\psi^{N}\in\mathcal H_A^{\otimes N}\otimes\mathcal H_B^{\otimes N}$ with amplitudes
--
--   $$
--   \psi^{N}(u,v)=\prod_{j=1}^{N}\psi(u_j,v_j).
--   $$
--
--   All Schmidt data of $\psi^{N}$ in this mission are taken across this cut, which is the one the paper's Theorem speaks about.
--
--   **Formalization Note** The amplitudes are the published `WildeQIT.EntManip.tensorPowVec`, repackaged as a vector of `EuclideanSpace`. For $N=0$ the vector is the scalar $1$.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Theorem, pp. 4-5, Eq. (9)

import Mathlib
import Definitions.Def_WildeQIT_EntManip_tensorPowVec

namespace LoPopescuCC.Dilution

/-- **`ψ^N` across the cut Alice : Bob** (Lo, Popescu, *The classical communication cost of
entanglement manipulation*, arXiv:quant-ph/9902045v2, Theorem, pp. 4–5, Eq. (9)): the `N`-fold
tensor power of a bipartite vector `ψ ∈ H_A ⊗ H_B`, as a vector of `H_A^{⊗N} ⊗ H_B^{⊗N}`, with
amplitudes `ψ^N(u, v) = ∏_j ψ(u_j, v_j)`.

**Formalization Note** The amplitudes are the published `WildeQIT.EntManip.tensorPowVec`, repackaged
as a vector of `EuclideanSpace`. Alice's `N` factors are grouped in `Fin N → a` and Bob's in
`Fin N → b`, so Schmidt data of `ψ^N` are taken across the cut `A^N : B^N`. The published
`QAlgorithms.tensorPow`, indexed by `Fin N → a × b`, does not split by party. -/
noncomputable def tensorPowCut {a b : Type} (ψ : EuclideanSpace ℂ (a × b)) (N : ℕ) :
    EuclideanSpace ℂ ((Fin N → a) × (Fin N → b)) :=
  WithLp.toLp 2 (WildeQIT.EntManip.tensorPowVec (fun z => ψ z) N)

end LoPopescuCC.Dilution


