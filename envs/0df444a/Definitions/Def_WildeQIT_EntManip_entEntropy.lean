-- Prove2me | Definitions.Def_WildeQIT_EntManip_entEntropy
-- name    : WildeQIT_EntManip_entEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:30.685322+00:00
-- url     : https://prove2.me/theorems/fc89ec95-0cb3-4aea-97b7-1f14ad0e362f
-- title:
--   Entropy of entanglement $H(A)_\psi$ of a bipartite pure state
-- statement:
--   For a bipartite pure state $|\psi\rangle_{AB}\in\mathcal H_A\otimes\mathcal H_B$, the **entropy of entanglement** is the quantum entropy of its reduced state on $A$:
--
--   $$
--   H(A)_\psi \equiv H(\psi_A),\qquad \psi_A=\operatorname{Tr}_B\{|\psi\rangle\langle\psi|_{AB}\}.
--   $$
--
--   It is the quantity that governs the asymptotic interconversion of pure entangled states (Theorem 19.4.1).
--
--   **Formalization Note** $\operatorname{Tr}_B$ is the published `WildeQIT.partialTraceRight` and $|\psi\rangle\langle\psi|$ the published `ObliviousRSP.pureState` (entries $\psi(i)\overline{\psi(j)}$); entropy in bits.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Ch. 19, p. 533, and Theorem 19.4.1, p. 541

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_QMemory_vonNeumann
import Definitions.Def_ObliviousRSP_pureState

namespace WildeQIT.EntManip

/-- **Entropy of entanglement `H(A)_ψ`** of a bipartite pure state (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, Ch. 19, p. 533 and Theorem 19.4.1, p. 541): the
quantum entropy of the reduced state `ψ_A = Tr_B{|ψ⟩⟨ψ|_{AB}}`.

**Formalization Note** `|ψ⟩_{AB}` is a vector on `a × b`; `Tr_B` is the published
`WildeQIT.partialTraceRight`; `|ψ⟩⟨ψ|` is the published `ObliviousRSP.pureState`;
entropy in bits. -/
noncomputable def entEntropy {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    (ψ : a × b → ℂ) : ℝ :=
  WildeQIT.QMemory.vonNeumann (WildeQIT.partialTraceRight (ObliviousRSP.pureState ψ))

end WildeQIT.EntManip


