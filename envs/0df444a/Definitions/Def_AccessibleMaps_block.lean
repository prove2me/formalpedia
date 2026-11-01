-- Prove2me | Definitions.Def_AccessibleMaps_block
-- name    : AccessibleMaps_block
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:36.506821+00:00
-- url     : https://prove2.me/theorems/e964b332-eff7-4070-bc43-01a5e9112122
-- title:
--   The block $T_{ij}=(\langle i|\otimes\mathbb 1)\,T\,(|j\rangle\otimes\mathbb 1)$ of a composite operator
-- statement:
--   For a bounded operator $T$ on $\mathbb C^{a}\otimes\mathcal H$ and $i,j\in a$, the **block** $T_{ij}$ is the bounded operator on $\mathcal H$
--   $$
--   T_{ij}=(\langle i|\otimes\mathbb 1)\,T\,(|j\rangle\otimes\mathbb 1),
--   $$
--   obtained by injecting into slot $j$, applying $T$, and reading off slot $i$.
--
--   Every operator on the composite space is the $a\times a$ operator matrix of its blocks; partial traces are defined blockwise.
--
--   **Formalization Note** Row index first, column index second, as for a matrix: the blocks of $\sigma\otimes\omega$ are $\sigma_{ij}\,\omega$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §I, p.1

import Mathlib
import Definitions.Def_AccessibleMaps_inject

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The block `T_{ij} = (⟨i| ⊗ 𝟙) T (|j⟩ ⊗ 𝟙)` of an operator `T` on the composite space, an
operator on `H`: inject into block `j`, apply `T`, read off block `i`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §I, p.1 (PDF p.1).

**Formalization Note.** Row index first, column index second, as for a matrix: the blocks of
`σ ⊗ ω` are `σ i j • ω` (`AccessibleMaps.tensorOp`). -/
noncomputable def block (T : Composite a H →L[ℂ] Composite a H) (i j : a) : H →L[ℂ] H :=
  PiLp.proj 2 (fun _ : a => H) i ∘L T ∘L inject j

end AccessibleMaps


