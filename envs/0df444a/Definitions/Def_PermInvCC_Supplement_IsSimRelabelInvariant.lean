-- Prove2me | Definitions.Def_PermInvCC_Supplement_IsSimRelabelInvariant
-- name    : PermInvCC_Supplement_IsSimRelabelInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:54:16.85781+00:00
-- url     : https://prove2.me/theorems/c64d63f4-b18e-4045-9678-64be8060116e
-- title:
--   Invariance under simultaneous vertex relabelling
-- statement:
--   A partial function $g$ of two labelled graphs on $[v]$, with values in $\{-1,+1,*\}$, is **invariant under simultaneous vertex relabelling** if
--
--   $$g(\pi A, \pi C) = g(A, C) \qquad \text{for all graphs } A, C \text{ and all } \pi \in S_v,$$
--
--   including equality of undefined values, so the promise is invariant as well.
--
--   This is the graph analogue of the coordinate-permutation invariance of Definition 2.2, used in Theorem 1.3(ii).
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), §5.3, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_PermInvCC_Supplement_relabel

namespace PermInvCC

namespace Supplement

/-- **Simultaneous relabelling invariance** of a partial function of two labelled graphs
(Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, §5.3, p.25): `g(πA, πC) = g(A, C)` for every `π ∈ S_v`, "including equality of
undefined values".

**Formalization Note.** A partial graph function is
`SimpleGraph (Fin v) → SimpleGraph (Fin v) → Option Bool` (`none` = `∗`, `some true` = `+1`). -/
def IsSimRelabelInvariant {v : ℕ} (g : SimpleGraph (Fin v) → SimpleGraph (Fin v) → Option Bool) :
    Prop :=
  ∀ (π : Equiv.Perm (Fin v)) (A C : SimpleGraph (Fin v)), g (relabel π A) (relabel π C) = g A C

end Supplement

end PermInvCC


