-- Prove2me | Definitions.Def_AccessibleMaps_trA
-- name    : AccessibleMaps_trA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:34.204286+00:00
-- url     : https://prove2.me/theorems/27c06d78-12f3-4f7d-9991-7889b04614c3
-- title:
--   Partial trace over the system, $\operatorname{tr}_A T=\sum_i T_{ii}$
-- statement:
--   For a bounded operator $T$ on $\mathbb C^{a}\otimes\mathcal H$, the **partial trace over the system** $A$ is the operator on $\mathcal H$
--   $$
--   \operatorname{tr}_A T=\sum_{i\in a} T_{ii}.
--   $$
--   For a state $\tau_{AB}$, $\omega=\operatorname{tr}_A\tau_{AB}$ is the reduced state of the environment.
--
--   **Formalization Note** A finite sum of blocks: it is a bounded operator for every bounded $T$ and additive with no trace-class condition.
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §I, p.1 ("the reduced density operator ω = tr_A τ_AB")

import Mathlib
import Definitions.Def_AccessibleMaps_block

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The partial trace over the system, `tr_A T = ∑ i, T_{ii}`, an operator on `H`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §I, p.1 (PDF p.1):
"the reduced density operator ω = tr_A τ_AB".

**Formalization Note.** A finite sum of blocks, so it is a bounded operator for every bounded `T`
and is additive with no trace-class condition. -/
noncomputable def trA (T : Composite a H →L[ℂ] Composite a H) : H →L[ℂ] H :=
  ∑ i, block T i i

end AccessibleMaps


