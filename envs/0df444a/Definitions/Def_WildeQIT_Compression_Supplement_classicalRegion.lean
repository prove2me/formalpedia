-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_classicalRegion
-- name    : WildeQIT_Compression_Supplement_classicalRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:04:31.914104+00:00
-- url     : https://prove2.me/theorems/193182fe-825d-40f4-8c90-4f311112f7f6
-- title:
--   Classical capacity region $\mathcal C_C(\mathcal N)$
-- statement:
--   The **classical capacity region** of a quantum channel $\mathcal N$ is the part of the quantum dynamic capacity region $\mathcal C_{CQE}(\mathcal N)$ on the ray of classical communication without entanglement assistance or quantum communication:
--
--   $$
--   \mathcal C_C(\mathcal N)=\{C\ge0:(C,0,0)\in\mathcal C_{CQE}(\mathcal N)\}.
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
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §25.2.1, p. 698, scenario 1 and Theorem 25.2.2.
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **Classical capacity region `C_C(N)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §25.2.1, p. 698): "Classical communication (C) when there is no entanglement
assistance or quantum communication. The achievable rate region lies on the `(C, 0, 0)` ray
extending from the origin" of the quantum dynamic capacity region `C_CQE(N)`:
`C_C(N) = {C ≥ 0 : (C, 0, 0) ∈ C_CQE(N)}`.

**Formalization Note.** `C_CQE(N)` is `operationalDynamicRegion N` of the published
`QAlgorithms.Papers.Independent.Claimed50.P20` (Wilde–Hsieh, arXiv:1004.0458, the paper §25.1
reproduces), the region the book's Theorem 25.2.1 is stated for; channels are superoperators
`Superop A B` there. Rate vectors are `![C, Q, E]`, with `E` the net entanglement rate, so a
consumed entanglement rate `E ≥ 0` sits at the coordinate `−E`, as in the book. -/
def classicalRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Superop A B) :
    Set ℝ :=
  {C | 0 ≤ C ∧ ![C, 0, 0] ∈ operationalDynamicRegion N}

end WildeQIT.Compression.Supplement


