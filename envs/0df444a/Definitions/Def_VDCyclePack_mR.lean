-- Prove2me | Definitions.Def_VDCyclePack_mR
-- name    : VDCyclePack_mR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:12.589231+00:00
-- url     : https://prove2.me/theorems/38fe0c9d-102c-4b86-a90f-cde96a84db51
-- title:
--   $m_R(C)=\sum_{C'\in N_R[C]}x_{C'}$: the weight discarded by selecting $C$
-- statement:
--   For a weighted family $R$ and a cycle $C$,
--   $$
--   m_R(C)=\sum_{C'\in N_R[C]}x_{C'},
--   $$
--   the weight discarded when the greedy rounding selects $C$ from the remaining family $R$. Lemma 5.3 bounds the minimum of $m_R$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 5, p.14

import Mathlib
import Definitions.Def_VDCyclePack_nbhd

namespace VDCyclePack

/-- **m_R(C): the weight discarded when C is selected.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 5, p.14: "m_R(C) = Σ_{C′∈N_R[C]} x_{C′}".

`mR R x C = Σ_{C′ ∈ N_R[C]} x C′`. -/
noncomputable def mR {V : Type*} {G : SimpleGraph V} (R : Finset G.Subgraph) (x : G.Subgraph → ℝ)
    (C : G.Subgraph) : ℝ :=
  ∑ C' ∈ nbhd R C, x C'

end VDCyclePack


