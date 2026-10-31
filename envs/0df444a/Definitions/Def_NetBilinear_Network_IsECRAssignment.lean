-- Prove2me | Definitions.Def_NetBilinear_Network_IsECRAssignment
-- name    : NetBilinear_Network_IsECRAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:42:23.571648+00:00
-- url     : https://prove2.me/theorems/42ef3011-c7f2-46a7-b5ce-2d882a7a5957
-- title:
--   EC&R assignment of class $l^\pm$ for the network polytope, $m=1$
-- statement:
--   For a network $G=(V,A)$, an arc $l\in A$, a sign $\sigma$ and two sets $\mathcal I_1,\bar{\mathcal I}$ of flow-balance rows $i^\pm$, **$[\mathcal I_1,\bar{\mathcal I}]$ is an EC&R assignment for class-$l^\sigma$** when it is an EC&R assignment (for $m=1$, conditions (C1) and (C2)) for the constraint rows of the augmented node-arc incidence matrix,
--   $$E_{i^s,k}=s\,\big([t(k)=i]-[h(k)=i]\big),$$
--   with bilinear terms $y_1x_k$ indexed by the arcs $k\in A$ and base equality $y_1x_l-z_l=0$.
--
--   For example, $[\{i^+\},\{j^-\}]$ means that the positive flow-balance inequality at $i$ is multiplied by $y_1$ and the negative one at $j$ by $1-y_1$. This is the predicate in Theorem 2's conclusions.
--
--   **Formalization Note** Defined as `IsECRAssignmentOne G.incRow l σ I₁ Ī`.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, §2, p.3; Remark 1, p.5; §3.1, p.6 ("an EC&R assignment [{i+},{j−}] implies that …")

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_IsECRAssignmentOne

namespace NetBilinear

/-- **An EC&R assignment `[I₁, Ī]` of class `l±` for the network polytope, `m = 1`.**
arXiv:2302.14151v2, §2, p.3 (EC&R procedure, (C1), (C2)), Remark 1, p.5 (reduced form
`[I₁, Ī]`), and §3.1, p.6 (rows `i⁺`, `i⁻` of the flow-balance inequalities; "an EC&R
assignment [{i+},{j−}] implies that … the positive flow-balance inequality corresponding to the
node i ∈ V is multiplied with y1, and the negative flow-balance inequality corresponding to the
node j ∈ V is multiplied with 1 − y1").

`G.IsECRAssignment l σ I₁ Ī` is `IsECRAssignmentOne` for the augmented node-arc incidence rows
`E = G.incRow`, the bilinear terms `y₁x_k` indexed by the arcs `k ∈ A`, and base arc `l`. -/
def Network.IsECRAssignment {V A : Type*} [DecidableEq V] [Fintype A] [DecidableEq A]
    (G : Network V A) (l : A) (σ : Sign) (I₁ Ibar : Finset (V × Sign)) : Prop :=
  IsECRAssignmentOne G.incRow l σ I₁ Ibar

end NetBilinear


