-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_productVec
-- name    : LoPopescuCC_Dilution_productVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:12.138405+00:00
-- url     : https://prove2.me/theorems/3a736af2-9090-4a4f-9896-3c0802cf81cb
-- title:
--   Product Schmidt vector $\alpha_x$
-- statement:
--   For a family $(\alpha_i)_i$ of vectors of $\mathcal H$ and a string $x=(x_1,\dots,x_N)$ of labels, $\alpha_x=\alpha_{x_1}\otimes\cdots\otimes\alpha_{x_N}\in\mathcal H^{\otimes N}$ has amplitudes $\alpha_x(u)=\prod_{j}\alpha_{x_j}(u_j)$. These are the Schmidt vectors of $\psi^N$ on one side.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Proof of the Theorem, p. 5

import Mathlib

namespace LoPopescuCC.Dilution

/-- **Product Schmidt vector `α_x = α_{x_1} ⊗ ⋯ ⊗ α_{x_N}`** (Lo, Popescu,
arXiv:quant-ph/9902045v2, Proof of the Theorem, p. 5): for a family `α` of vectors of `H` and a
string `x` of `N` labels, the vector of `H^{⊗N}` with amplitude `α_x(u) = ∏_j α_{x_j}(u_j)`. These
are the Schmidt vectors of `ψ^N` on one side. -/
noncomputable def productVec {ι a : Type} (α : ι → EuclideanSpace ℂ a) {N : ℕ} (x : Fin N → ι) :
    EuclideanSpace ℂ (Fin N → a) :=
  WithLp.toLp 2 fun u => ∏ j, α (x j) (u j)

end LoPopescuCC.Dilution


