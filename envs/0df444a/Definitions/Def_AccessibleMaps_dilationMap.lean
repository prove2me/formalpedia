-- Prove2me | Definitions.Def_AccessibleMaps_dilationMap
-- name    : AccessibleMaps_dilationMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:05:39.00479+00:00
-- url     : https://prove2.me/theorems/ed03100e-ac20-4e91-bd9b-12809321a8e6
-- title:
--   The product-term map $\Lambda_\rho(\sigma)=\operatorname{tr}_B[U(\sigma\otimes\omega(\rho))U^\dagger]$
-- statement:
--   For an affine assignment, a unitary $U$ and a matrix $\rho$, the map $\Lambda_\rho$ on $a\times a$ matrices is
--   $$
--   \Lambda_\rho(\sigma)=\operatorname{tr}_B\big[U\,(\sigma\otimes\omega(\rho))\,U^\dagger\big],
--   $$
--   the image of the product term of the decomposition (14) with the environment marginal frozen at $\omega(\rho)$. For each $\rho$ it is a map of $\sigma$; the dependence on $\rho$ enters only through $\omega(\rho)$. In the proof of Proposition 1 this is "the first term on the RHS", the trace-preserving completely positive part of $\Phi$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (15), p.3 and the proof of Proposition 1, pp.4–5

import Mathlib
import Definitions.Def_AccessibleMaps_AffineAssignment_marginal
import Definitions.Def_AccessibleMaps_tensorOp
import Definitions.Def_AccessibleMaps_reducedEvolution

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The map `Λ_ρ : σ ↦ tr_B [U (σ ⊗ ω(ρ)) U†]`, the product term of the decomposition with the
environment marginal frozen at `ω(ρ)`, as a map on all matrices `σ`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (15), p.3 (PDF p.3) (with `ρ` in the role of `σ`)
and the proof of Proposition 1, pp.4–5: "the first term on the RHS yields a trace-preserving
CP-map".

**Formalization Note.** The state `ρ` selects the marginal and `σ` is the argument, so this is
a family of maps indexed by `ρ`; the map `ρ ↦ Λ_ρ` is at most linear (p.4, PDF p.4). -/
noncomputable def dilationMap (E : AffineAssignment a H)
    (U : unitary (Composite a H →L[ℂ] Composite a H)) (ρ σ : Matrix a a ℂ) : Matrix a a ℂ :=
  reducedEvolution U (tensorOp σ (E.marginal ρ))

end AccessibleMaps


