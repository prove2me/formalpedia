-- Prove2me | Definitions.Def_PermInvCC_Supplement_IsLabelledCopy
-- name    : PermInvCC_Supplement_IsLabelledCopy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:55:26.821193+00:00
-- url     : https://prove2.me/theorems/6f5a57e2-654b-4473-8bec-cd30759756ca
-- title:
--   Labelled copy $\sigma B$ of a graph $B$
-- statement:
--   Let $A$ and $B$ be simple graphs on $[v]$. The graph $A$ is a **labelled copy** of $B$ if $A = \sigma B$ for some vertex relabelling $\sigma \in S_v$; equivalently, $A$ is isomorphic to $B$ on the same vertex set.
--
--   Labelled copies of one fixed rigid tree are the promised local inputs of Theorem 1.3(ii), and labelled copies of encoding graphs are the promised inputs of Theorem 5.4.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), §5.3, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_PermInvCC_Supplement_relabel

namespace PermInvCC

namespace Supplement

/-- `A` is a **labelled copy** of `B` (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, §5.3, p.25: "every labelled copy has a
representation `σB`, with `σ ∈ S_v`"): `A = σB` for some vertex relabelling `σ`.

**Formalization Note.** Equivalently, `A` is a graph on the same vertex set `[v]` isomorphic
to `B`. -/
def IsLabelledCopy {v : ℕ} (B A : SimpleGraph (Fin v)) : Prop :=
  ∃ σ : Equiv.Perm (Fin v), A = relabel σ B

end Supplement

end PermInvCC


