-- Prove2me | Definitions.Def_PermInvCC_Supplement_IsIndepRelabelInvariant
-- name    : PermInvCC_Supplement_IsIndepRelabelInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:54:52.746129+00:00
-- url     : https://prove2.me/theorems/161ac4dc-a64b-4079-b7cd-6044ea4df24a
-- title:
--   Invariance under independent relabelling of the two local graphs
-- statement:
--   A partial function $g$ of two labelled graphs on $[v]$, with values in $\{-1,+1,*\}$, is **invariant under independent relabelling** if
--
--   $$g(\pi A, \pi' C) = g(A, C) \qquad \text{for all graphs } A, C \text{ and all } \pi, \pi' \in S_v,$$
--
--   including equality of undefined values. Such a function depends only on the isomorphism types of the two local graphs.
--
--   It is the symmetry of Theorem 1.3(iii) and Theorem 5.4.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.3(iii), p.3 (PDF p.6), and Theorem 5.4, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_PermInvCC_Supplement_relabel

namespace PermInvCC

namespace Supplement

/-- **Invariance under independent relabelling of the two local graphs** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, Theorem 1.3(iii), p.3, and Theorem 5.4, p.26): `g(πA, π'C) = g(A, C)` for all
`π, π' ∈ S_v`, including equality of undefined values.

**Formalization Note.** A partial graph function is
`SimpleGraph (Fin v) → SimpleGraph (Fin v) → Option Bool` (`none` = `∗`). -/
def IsIndepRelabelInvariant {v : ℕ}
    (g : SimpleGraph (Fin v) → SimpleGraph (Fin v) → Option Bool) : Prop :=
  ∀ (π π' : Equiv.Perm (Fin v)) (A C : SimpleGraph (Fin v)), g (relabel π A) (relabel π' C) = g A C

end Supplement

end PermInvCC


