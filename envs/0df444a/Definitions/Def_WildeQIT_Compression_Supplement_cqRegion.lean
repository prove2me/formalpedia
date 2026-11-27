-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_cqRegion
-- name    : WildeQIT_Compression_Supplement_cqRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:07:46.645478+00:00
-- url     : https://prove2.me/theorems/a673c07c-ade7-5010-89b3-2248444b26b8
-- title:
--   Classically enhanced quantum capacity region $\mathcal C_{CQ}(\mathcal N)$
-- statement:
--   The **classically enhanced quantum capacity region** of a quantum channel $\mathcal N$ is the part of the quantum dynamic capacity region in the $(C,Q,0)$ quarter-plane (no entanglement assistance):
--
--   $$
--   \mathcal C_{CQ}(\mathcal N)=\{(C,Q):C,Q\ge0,\ (C,Q,0)\in\mathcal C_{CQE}(\mathcal N)\}.
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
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698, scenario 4 and Theorem 25.2.5.
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **Classically enhanced quantum capacity region `C_CQ(N)`** (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698): "Classically enhanced quantum communication
(CQ) when there is no entanglement assistance. The achievable rate region lies in the `(C, Q, 0)`
quarter-plane": `C_CQ(N) = {(C, Q) : C, Q ≥ 0, (C, Q, 0) ∈ C_CQE(N)}`.

**Formalization Note.** `C_CQE(N)` is `operationalDynamicRegion N` of the published
`QAlgorithms.Papers.Independent.Claimed50.P20` (Wilde–Hsieh, arXiv:1004.0458, the paper §25.1
reproduces), the region the book's Theorem 25.2.1 is stated for; channels are superoperators
`Superop A B` there. Rate vectors are `![C, Q, E]`, with `E` the net entanglement rate, so a
consumed entanglement rate `E ≥ 0` sits at the coordinate `−E`, as in the book. -/
def cqRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Superop A B) :
    Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ ![x.1, x.2, 0] ∈ operationalDynamicRegion N}

end WildeQIT.Compression.Supplement


