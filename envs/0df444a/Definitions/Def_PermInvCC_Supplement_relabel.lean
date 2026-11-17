-- Prove2me | Definitions.Def_PermInvCC_Supplement_relabel
-- name    : PermInvCC_Supplement_relabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:53:46.351561+00:00
-- url     : https://prove2.me/theorems/feddcd06-7688-4d8c-ae74-76d948fb2abd
-- title:
--   Vertex relabelling $\pi A$ of a labelled graph
-- statement:
--   A labelled graph on $v$ vertices is a simple graph $A$ on the vertex set $[v]$. For a permutation $\pi \in S_v$, the **relabelled graph** $\pi A$ is obtained by applying $\pi$ to both endpoints of every edge:
--
--   $$\{u,w\} \in E(A) \iff \{\pi(u),\pi(w)\} \in E(\pi A).$$
--
--   Relabelling is the action under which the paper's graph communication problems are invariant (Theorems 1.3 and 5.4).
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), §5.3, p.25 (PDF p.28)

import Mathlib

namespace PermInvCC

namespace Supplement

/-- **Vertex relabelling** of a labelled graph (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, §5.3, p.25): "For `π ∈ S_v`, the graph
`πA` is obtained by applying `π` to both endpoints of every edge."

**Formalization Note.** A labelled graph on `[v]` is `SimpleGraph (Fin v)`; `πA` is the image
`A.map π` (equivalently `A.comap π⁻¹`). -/
def relabel {v : ℕ} (π : Equiv.Perm (Fin v)) (A : SimpleGraph (Fin v)) : SimpleGraph (Fin v) :=
  A.map π.toEmbedding

end Supplement

end PermInvCC


