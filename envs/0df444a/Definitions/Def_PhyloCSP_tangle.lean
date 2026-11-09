-- Prove2me | Definitions.Def_PhyloCSP_tangle
-- name    : PhyloCSP_tangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:44.04227+00:00
-- url     : https://prove2.me/theorems/c83e4ede-9431-4f5e-9f0a-9f3f085fc381
-- title:
--   Tanglegrams and their number $t_k$
-- statement:
--   A **tanglegram** on $k$ leaves is an ordered pair $(P,Q)$ of rooted binary trees on $\{1,\dots,k\}$, taken up to simultaneous relabeling of the leaves of both trees; $(P,Q)$ and $(Q,P)$ are not identified. The number of tanglegrams is $t_k$; for example $t_4=13$.
--
--   $t_k$ bounds the number of components in Theorem 12.1.
--
--   **Formalization Note** Leaves are `Fin k`; $t_k$ is the cardinality of the quotient of pairs of patterns by simultaneous relabeling.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 12, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_PhyloCSP_Pattern

set_option autoImplicit false

namespace PhyloCSP

/-- **Tanglegrams and their number `t_k`.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 12, p.40 (PDF p.42): "Let tk be the number of ordered
pairs (P, Q) of rooted binary trees on {1, . . . , k}, up to simultaneous relabeling of their
leaves. These pairs are called tanglegrams; the input and output trees have distinct roles, so we
do not identify (P, Q) with (Q, P)."

`TangleRel k` relates two ordered pairs of patterns on `Fin k` when one is a simultaneous
relabeling of the other; `tangle k` is the number of classes.

**Formalization Note.** Leaves `{1, …, k}` are `Fin k`. `TangleRel k` is already an equivalence
relation (relabelings form a group), so `Quot (TangleRel k)` is the set of its classes. -/
def TangleRel (k : ℕ) (a b : Pattern (Fin k) × Pattern (Fin k)) : Prop :=
  ∃ σ : Equiv.Perm (Fin k), b = (a.1.relabel σ, a.2.relabel σ)

/-- `t_k`, the number of tanglegrams on `k` leaves. -/
noncomputable def tangle (k : ℕ) : ℕ := Nat.card (Quot (TangleRel k))

end PhyloCSP


