-- Prove2me | Definitions.Def_AccessibleMaps_inject
-- name    : AccessibleMaps_inject
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:56.870994+00:00
-- url     : https://prove2.me/theorems/1ed99951-b050-444c-bd1c-dc06b2ba0278
-- title:
--   The injection $\psi\mapsto|j\rangle\otimes\psi$ into the composite space
-- statement:
--   For $j\in a$, the **injection** $\iota_j:\mathcal H\to\mathbb C^{a}\otimes\mathcal H$ is the bounded linear map $\psi\mapsto|j\rangle\otimes\psi$: the tuple with $\psi$ in slot $j$ and $0$ in every other slot.
--
--   It is used to read off the blocks of an operator on the composite space and to build product operators $\sigma\otimes\omega$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §I, p.1

import Mathlib
import Definitions.Def_AccessibleMaps_Composite

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The injection `ψ ↦ |j⟩ ⊗ ψ` of `H` as the `j`-th block of the composite space.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §I, p.1 (PDF p.1).

**Formalization Note.** The vector with `ψ` in block `j` and `0` in every other block. -/
noncomputable def inject (j : a) : H →L[ℂ] Composite a H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : a => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : a => H) j

end AccessibleMaps


