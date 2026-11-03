-- Prove2me | Definitions.Def_BaconThesis_Collective_dfsWeak
-- name    : BaconThesis_Collective_dfsWeak
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:02.345452+00:00
-- url     : https://prove2.me/theorems/a0abcd98-5786-4966-acf3-2cc917fbdedf
-- title:
--   Weak collective decoherence DF subspace $\mathrm{DFS}_n(h)$
-- statement:
--   For $n$ qubits and $h\in\mathbb N$, the **weak collective decoherence DF subspace**
--   $$
--   \mathrm{DFS}_n(h)=\operatorname{span}\{\,|i\rangle : H(i)=h\,\}
--   $$
--   is spanned by the computational basis states of Hamming weight $h$ (Definition 8.5.1). On it $S_z^{[n]}$ acts as the scalar $\tfrac12(n-2h)$ by (8.34).
--
--   **Formalization Note** The book labels these subspaces by $0\le h\le n$; for $h>n$ the definition gives $\{0\}$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Definition 8.5.1, §8.5, p.115 (PDF p.132)

import Mathlib
import Definitions.Def_BaconThesis_Collective_hammingWeight

open scoped Matrix

namespace BaconThesis.Collective

/-- **The weak collective decoherence DF subspace `DFS_n(h)`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, Definition 8.5.1, §8.5, p.115 (PDF p.132): "`DFS_n(h)` is spanned by basis states in the
computational basis `|i⟩` which have Hamming weight `H(i)` equal to `h`."

`dfsWeak n h` is the span in `ℂ^(Fin n → Fin 2)` of the basis vectors `|x⟩` with
`hammingWeight x = h`.

**Formalization Note.** The book labels these subspaces by `0 ≤ h ≤ n`; for `h > n` the
definition gives the zero subspace. -/
def dfsWeak (n h : ℕ) : Submodule ℂ ((Fin n → Fin 2) → ℂ) :=
  Submodule.span ℂ ((fun x => Pi.single x (1 : ℂ)) '' {x | hammingWeight x = h})

end BaconThesis.Collective


