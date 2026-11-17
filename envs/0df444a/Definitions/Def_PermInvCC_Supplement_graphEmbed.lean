-- Prove2me | Definitions.Def_PermInvCC_Supplement_graphEmbed
-- name    : PermInvCC_Supplement_graphEmbed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:56:40.837635+00:00
-- url     : https://prove2.me/theorems/1dba38ef-153d-4de3-826f-32d12f3cc2b0
-- title:
--   Graph function $\widetilde F$ induced by an encoding of strings as graphs
-- statement:
--   Let $F : \{0,1\}^m \times \{0,1\}^m \to \{-1,+1,*\}$ be a partial communication function and let $\mathrm{enc}$ assign to every $x \in \{0,1\}^m$ a simple graph $\mathrm{enc}(x)$ on $[v]$. The **induced graph function** $\widetilde F$ on pairs of graphs on $[v]$ is
--
--   $$\widetilde F(A, C) := \begin{cases} F(x,y) & \text{if } A \text{ is a labelled copy of } \mathrm{enc}(x) \text{ and } C \text{ a labelled copy of } \mathrm{enc}(y),\\ * & \text{otherwise.}\end{cases}$$
--
--   Each party decodes its own graph locally, so when the encodings of distinct strings are non-isomorphic, $\widetilde F$ is well defined and inherits the complexity of $F$ (Theorem 5.4).
--
--   **Formalization Note** The strings $x, y$ are picked by choice; they are unique whenever distinct strings have non-isomorphic encodings. The zero padding of the paper's construction belongs to its particular encoding, not to this definition.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), proof of Theorem 5.4, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PermInvCC_Supplement_IsLabelledCopy

namespace PermInvCC

namespace Supplement

open Classical in
/-- The **graph function induced by an encoding** `enc` of `m`-bit strings as graphs on `[v]`
(Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, proof of Theorem 5.4, p.27): "Promise that each local graph is a labelled copy of an
encoding. Decode each graph locally … Define `F̃_v(G(x̄), G(ȳ)) := F_m(x, y)`. Leave the value
undefined if either structural promise or the promise of `F_m` fails."

**Formalization Note.** `F̃ A C = F x y` when `A` is a labelled copy of `enc x` and `C` of
`enc y`, and `none` otherwise. The strings `x, y` are picked by choice; when encodings of
distinct strings are non-isomorphic (as in Theorem 5.4) they are unique. The zero padding of the
paper's proof is part of its particular `enc`, not of this definition. -/
noncomputable def graphEmbed {m v : ℕ} (enc : (Fin m → Bool) → SimpleGraph (Fin v))
    (F : (Fin m → Bool) → (Fin m → Bool) → Option Bool) :
    SimpleGraph (Fin v) → SimpleGraph (Fin v) → Option Bool :=
  fun A C =>
    if h : (∃ x, IsLabelledCopy (enc x) A) ∧ (∃ y, IsLabelledCopy (enc y) C) then
      F h.1.choose h.2.choose
    else none

end Supplement

end PermInvCC


