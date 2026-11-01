-- Prove2me | Definitions.Def_AccessibleMaps_tensorOp
-- name    : AccessibleMaps_tensorOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:54.886985+00:00
-- url     : https://prove2.me/theorems/797e1e39-a126-4092-81d2-5753ecf59b41
-- title:
--   The product operator $\sigma\otimes\omega$ with blocks $\sigma_{ij}\,\omega$
-- statement:
--   For an $a\times a$ complex matrix $\sigma$ and a bounded operator $\omega$ on $\mathcal H$, the **product operator** $\sigma\otimes\omega$ on $\mathbb C^{a}\otimes\mathcal H$ is
--   $$
--   \sigma\otimes\omega=\sum_{i,j\in a}|i\rangle\langle j|\otimes\sigma_{ij}\,\omega,\qquad\big((\sigma\otimes\omega)x\big)_i=\sum_j\sigma_{ij}\,\omega(x_j).
--   $$
--   It is the tensor-product assignment $\rho\otimes\omega$ of Eq. (6) and the first term of the decomposition (14).
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (6), p.1 and Eq. (14), p.3

import Mathlib
import Definitions.Def_AccessibleMaps_inject

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The product operator `σ ⊗ ω` on the composite space, for an `a × a` matrix `σ` and an operator
`ω` on `H`: its blocks are `(σ ⊗ ω)_{ij} = σ i j • ω`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (6), p.1 (PDF p.1) and Eq. (14), p.3 (PDF p.3).

**Formalization Note.** Written as `∑ᵢⱼ |i⟩⟨j| ⊗ σᵢⱼ ω`: read block `j`, apply `σ i j • ω`, write
the result into block `i`. On vectors, `((σ ⊗ ω) x) i = ∑ j, σ i j • ω (x j)`. -/
noncomputable def tensorOp (σ : Matrix a a ℂ) (ω : H →L[ℂ] H) :
    Composite a H →L[ℂ] Composite a H :=
  ∑ i, ∑ j, inject i ∘L (σ i j • ω) ∘L PiLp.proj 2 (fun _ : a => H) j

end AccessibleMaps


