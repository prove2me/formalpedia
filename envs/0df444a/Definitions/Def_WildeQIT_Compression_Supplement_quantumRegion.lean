-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_quantumRegion
-- name    : WildeQIT_Compression_Supplement_quantumRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:05:23.007796+00:00
-- url     : https://prove2.me/theorems/49478f07-7917-53ca-a98b-3641d1397eb3
-- title:
--   Quantum capacity region $\mathcal C_Q(\mathcal N)$
-- statement:
--   The **quantum capacity region** of a quantum channel $\mathcal N$ is the part of the quantum dynamic capacity region on the ray of quantum communication without entanglement assistance or classical communication:
--
--   $$
--   \mathcal C_Q(\mathcal N)=\{Q\ge0:(0,Q,0)\in\mathcal C_{CQE}(\mathcal N)\}.
--   $$
--
--   These five regions are the special cases of the quantum dynamic capacity theorem listed in §25.2.1.
--
--   **Formalization Note** The quantum dynamic capacity region $\mathcal C_{CQE}(\mathcal N)$ is `operationalDynamicRegion` of the published `Claimed50.P20` (Wilde–Hsieh, arXiv:1004.0458, the paper §25.1 reproduces), the region of Theorem 25.2.1. Rate triples are $(C,Q,E)$ of net rates; a consumed entanglement rate $E\ge0$ appears as the coordinate $-E$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §25.2.1, p. 698

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698, scenario 2 and Theorem 25.2.3.
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **Quantum capacity region `C_Q(N)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §25.2.1, p. 698): "Quantum communication (Q) when there is no entanglement
assistance or classical communication. The achievable rate region lies on the `(0, Q, 0)` ray
extending from the origin": `C_Q(N) = {Q ≥ 0 : (0, Q, 0) ∈ C_CQE(N)}`.

**Formalization Note.** `C_CQE(N)` is `operationalDynamicRegion N` of the published
`QAlgorithms.Papers.Independent.Claimed50.P20` (Wilde–Hsieh, arXiv:1004.0458, the paper §25.1
reproduces), the region the book's Theorem 25.2.1 is stated for; channels are superoperators
`Superop A B` there. Rate vectors are `![C, Q, E]`, with `E` the net entanglement rate, so a
consumed entanglement rate `E ≥ 0` sits at the coordinate `−E`, as in the book. -/
def quantumRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Superop A B) :
    Set ℝ :=
  {Q | 0 ≤ Q ∧ ![0, Q, 0] ∈ operationalDynamicRegion N}

end WildeQIT.Compression.Supplement


