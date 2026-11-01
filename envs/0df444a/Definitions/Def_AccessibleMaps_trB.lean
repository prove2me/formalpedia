-- Prove2me | Definitions.Def_AccessibleMaps_trB
-- name    : AccessibleMaps_trB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:51.034172+00:00
-- url     : https://prove2.me/theorems/cdbc89f3-8153-4341-a040-4c38d25c16f4
-- title:
--   Partial trace over the environment, $(\operatorname{tr}_B T)_{ij}=\operatorname{tr}T_{ij}$
-- statement:
--   For a bounded operator $T$ on $\mathbb C^{a}\otimes\mathcal H$, the **partial trace over the environment** $B$ is the $a\times a$ complex matrix
--   $$
--   (\operatorname{tr}_B T)_{ij}=\operatorname{tr} T_{ij}\qquad(i,j\in a),
--   $$
--   where $\operatorname{tr}$ is the trace on $\mathcal H$. For a state $\tau_{AB}$, $\rho=\operatorname{tr}_B\tau_{AB}$ is the reduced state of the system. With this index order $\operatorname{tr}_B(\sigma\otimes\omega)=(\operatorname{tr}\omega)\,\sigma$.
--
--   **Formalization Note** The trace is the published `basisOperatorTrace`, $\sum_k\langle e_k,Se_k\rangle$ over a fixed Hilbert basis $(e_k)$ of $\mathcal H$. It equals the trace on trace-class operators and is a junk value otherwise, so $\operatorname{tr}_B$ is meaningful, and additive, on trace-class $T$.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §I, p.1 ("the reduced density operator ρ = tr_B τ_AB")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_AccessibleMaps_block

open QAlgorithms.Papers.Independent.Next46.P02

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The partial trace over the ancilla, the `a × a` matrix with entries `(tr_B T) i j = tr T_{ij}`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §I, p.1 (PDF p.1):
"the reduced density operator ρ = tr_B τ_AB".

**Formalization Note.** The trace is the published `basisOperatorTrace` (the sum of diagonal
entries over the reference Hilbert basis of `H`). It is a junk value when `T_{ij}` is not trace
class, so `trB` carries meaning, and is additive, on trace-class `T` only. The index order is the
one for which `tr_B (σ ⊗ ω) = (tr ω) σ`, not its transpose. -/
noncomputable def trB (T : Composite a H →L[ℂ] Composite a H) : Matrix a a ℂ :=
  Matrix.of fun i j => basisOperatorTrace (block T i j)

end AccessibleMaps


