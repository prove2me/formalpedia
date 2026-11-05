-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_pairTensor
-- name    : LoPopescuCC_Dilution_pairTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:01.216785+00:00
-- url     : https://prove2.me/theorems/4a89d3e9-dde7-4d00-a71b-d671780e83bb
-- title:
--   Product $\Phi\otimes\Delta$ of two bipartite vectors
-- statement:
--   For $\Phi\in\mathcal H_\alpha\otimes\mathcal H_\beta$ and $\Delta\in\mathcal H_\gamma\otimes\mathcal H_\delta$, this is the product vector regrouped so that Alice holds $\mathcal H_\alpha\otimes\mathcal H_\gamma$ and Bob holds $\mathcal H_\beta\otimes\mathcal H_\delta$:
--
--   $$
--   (\Phi\otimes\Delta)\big((p,r),(q,s)\big)=\Phi(p,q)\,\Delta(r,s).
--   $$
--
--   This is the sense of $\otimes$ in Eqs. (8) and (9), where both factors are shared between Alice and Bob.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Eq. (8), p. 4 and Eq. (9), p. 5

import Mathlib

namespace LoPopescuCC.Dilution

/-- **`Φ ⊗ Δ` of two bipartite vectors** (Lo, Popescu, arXiv:quant-ph/9902045v2, Eq. (8), p. 4 and
Eq. (9), p. 5): the product of a vector of `H_α ⊗ H_β` and a vector of `H_γ ⊗ H_δ`, regrouped so
that Alice holds `H_α ⊗ H_γ` and Bob holds `H_β ⊗ H_δ`. Its amplitude at `((p, r), (q, s))` is
`Φ(p, q) Δ(r, s)`. -/
noncomputable def pairTensor {α β γ δ : Type} (Φ : EuclideanSpace ℂ (α × β))
    (Δ : EuclideanSpace ℂ (γ × δ)) : EuclideanSpace ℂ ((α × γ) × (β × δ)) :=
  WithLp.toLp 2 fun z => Φ (z.1.1, z.2.1) * Δ (z.1.2, z.2.2)

end LoPopescuCC.Dilution


