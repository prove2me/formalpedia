-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_eaQuantumRegion
-- name    : WildeQIT_Compression_Supplement_eaQuantumRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:06:35.990794+00:00
-- url     : https://prove2.me/theorems/aae91299-217f-5f71-8bf9-5fb3c697044a
-- title:
--   Entanglement-assisted quantum capacity region $\mathcal C_{QE}(\mathcal N)$
-- statement:
--   The **entanglement-assisted quantum capacity region** of a quantum channel $\mathcal N$ is the part of the quantum dynamic capacity region in the $(0,Q,-E)$ quarter-plane (no classical communication, entanglement consumed at rate $E$):
--
--   $$
--   \mathcal C_{QE}(\mathcal N)=\{(Q,E):Q,E\ge0,\ (0,Q,-E)\in\mathcal C_{CQE}(\mathcal N)\}.
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
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698, scenario 3 and Theorem 25.2.4.
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **Entanglement-assisted quantum capacity region `C_QE(N)`** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698): "Entanglement-assisted quantum
communication (QE) when there is no classical communication. The achievable rate region lies in
the `(0, Q, −E)` quarter-plane": `C_QE(N) = {(Q, E) : Q, E ≥ 0, (0, Q, −E) ∈ C_CQE(N)}`, with `E`
the rate of consumed entanglement.

**Formalization Note.** `C_CQE(N)` is `operationalDynamicRegion N` of the published
`QAlgorithms.Papers.Independent.Claimed50.P20` (Wilde–Hsieh, arXiv:1004.0458, the paper §25.1
reproduces), the region the book's Theorem 25.2.1 is stated for; channels are superoperators
`Superop A B` there. Rate vectors are `![C, Q, E]`, with `E` the net entanglement rate, so a
consumed entanglement rate `E ≥ 0` sits at the coordinate `−E`, as in the book. -/
def eaQuantumRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Superop A B) :
    Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ ![0, x.1, -x.2] ∈ operationalDynamicRegion N}

end WildeQIT.Compression.Supplement


