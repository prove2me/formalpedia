-- Prove2me | Definitions.Def_MixedManna_decodePrice
-- name    : MixedManna_decodePrice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:19.963216+00:00
-- url     : https://prove2.me/theorems/b7d2fbce-f92d-4c70-8120-582cd93d3c0f
-- title:
--   Decoded equilibrium prices $p^*$ and allocation $x^*$
-- statement:
--   From a point with $p_j<P$, the decoded prices are
--   $$
--   p^*_j=P-p_j\ (j\in M^+),\qquad p^*_j=-(P-p_j)\ (j\in M^-),
--   $$
--   and the decoded allocation is $x^*_{ij}=\sum_k f_{ijk}/(P-p_j)$, the sum over the segments of $(i,j)$ carrying variables (zero if there are none).
--
--   **Formalization Note** The paper writes $x^*_{ij}=\sum_k f_{ijk}/p^*_j$; for a bad $p^*_j<0\le f_{ijk}$ and $-f_{ijk}$ is what the agent earns, so the amount is $\sum_kf_{ijk}/|p^*_j|$.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, Lemma 9, p.20, and its proof, p.45

import Mathlib
import Definitions.Def_MixedManna_LCPVar

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

open Classical

/-- **The decoded prices** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a Mixed
Manna*, arXiv:2008.02753v1, Lemma 9, p.20): `p*_j = P − p_j` for goods `j ∈ M⁺` and
`p*_j = −(P − p_j)` for bads `j ∈ M⁻`. -/
noncomputable def decodePrice (I : Instance N M) (P : ℝ) (p : M → ℝ) (j : M) : ℝ :=
  if IsGood I j then P - p j else -(P - p j)

/-- **The decoded allocation** (proof of Lemma 9, p.45): `x*_ij = Σ_k f_ijk / (P − p_j)`, the sum
over the segments `(i, j, k)` that carry variables (0 if there are none).

**Formalization Note** The paper writes `x*_ij = Σ_k f_ijk / p*_j`; for a bad `p*_j < 0 ≤ f`, and
`−f_ijk` is the amount earned (p.17), so the amount is `Σ_k f_ijk / |p*_j| = Σ_k f_ijk / (P − p_j)`.
-/
noncomputable def decodeAlloc (I : Instance N M) (P : ℝ) (x : LCPVar I) (i : N) (j : M) : ℝ :=
  (∑ σ : Seg I, if segAgent σ = i ∧ segItem σ = j then fv x σ else 0) / (P - pv x j)

end MixedManna


