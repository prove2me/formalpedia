-- Prove2me | Definitions.Def_DepthOptQC_Synth_wideThresholdGateSet
-- name    : DepthOptQC_Synth_wideThresholdGateSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:16:25.975783+00:00
-- url     : https://prove2.me/theorems/acb88c0a-f309-481d-87b8-074b8a2a11f6
-- title:
--   The gate set of Lemma 4: $X$, Fan-Out with $\le b$ targets, Toffoli with $\le b$ controls
-- statement:
--   For a width bound $b\in\mathbb N$, this is the set consisting of the $X$ gate, the Fan-Out gates with $k$ targets and the generalized Toffoli gates with $k$ controls, for $1\le k\le b$. With $b=b_{\max}$ it is the gate set of Lemma 4: "only X gates, Fan-Out gates with at most $b_{\max}$ targets, and Toffoli gates with at most $b_{\max}$ controls". A CNOT is the Fan-Out gate with one target, so it belongs to the set whenever $b\ge 1$.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Lemma 4, p.18; p.19

import Definitions.Def_DepthOptQC_Synth_gToffoli
import Definitions.Def_DepthOptQC_Synth_fanOut

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The gate set of Lemma 4 with width bound `b`** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Lemma 4, p.18: "only X gates, Fan-Out gates with at most `b_max`
targets, and Toffoli gates with at most `b_max` controls"): `X`, the Fan-Out gates with `k` targets
and the generalized Toffoli gates with `k` controls, for `1 ≤ k ≤ b`.

**Formalization Note.** A CNOT is the Fan-Out gate with one target (p.19), so it belongs to the set
whenever `b ≥ 1`. The width of a Fan-Out gate is its number of targets and that of a generalized
Toffoli its number of controls, as in Lemma 4's wording (reading R5). -/
def wideThresholdGateSet (b : ℕ) : Set Gate :=
  {Gate.ofMatrix1 pauliX} ∪ {g | ∃ k, 1 ≤ k ∧ k ≤ b ∧ g = fanOut k} ∪
    {g | ∃ k, 1 ≤ k ∧ k ≤ b ∧ g = gToffoli k}

end DepthOptQC.Synth


