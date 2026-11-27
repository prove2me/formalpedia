-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_ceRegion
-- name    : WildeQIT_Compression_Supplement_ceRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:08:23.553609+00:00
-- url     : https://prove2.me/theorems/edbf5384-cfd5-5b98-8c0a-1c6fafba4160
-- title:
--   Entanglement-assisted classical capacity region $\mathcal C_{CE}(\mathcal N)$
-- statement:
--   The **entanglement-assisted classical capacity region** of a quantum channel $\mathcal N$ is the part of the quantum dynamic capacity region in the $(C,0,-E)$ quarter-plane (no quantum communication, entanglement consumed at rate $E$):
--
--   $$
--   \mathcal C_{CE}(\mathcal N)=\{(C,E):C,E\ge0,\ (C,0,-E)\in\mathcal C_{CQE}(\mathcal N)\}.
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
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698, scenario 5 and Theorem 25.2.6.
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **Entanglement-assisted classical capacity region `C_CE(N)`** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698): "Entanglement-assisted classical
communication (CE) when there is no quantum communication. The achievable rate region lies in the
`(C, 0, −E)` quarter-plane": `C_CE(N) = {(C, E) : C, E ≥ 0, (C, 0, −E) ∈ C_CQE(N)}`, with `E` the
rate of consumed entanglement.

**Formalization Note.** `C_CQE(N)` is `operationalDynamicRegion N` of the published
`QAlgorithms.Papers.Independent.Claimed50.P20` (Wilde–Hsieh, arXiv:1004.0458, the paper §25.1
reproduces), the region the book's Theorem 25.2.1 is stated for; channels are superoperators
`Superop A B` there. Rate vectors are `![C, Q, E]`, with `E` the net entanglement rate, so a
consumed entanglement rate `E ≥ 0` sits at the coordinate `−E`, as in the book. -/
def ceRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Superop A B) :
    Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ ![x.1, 0, -x.2] ∈ operationalDynamicRegion N}

end WildeQIT.Compression.Supplement


