-- Prove2me | Definitions.Def_DepthOptQC_Synth_gqacfGateSet
-- name    : DepthOptQC_Synth_gqacfGateSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:16:23.2031+00:00
-- url     : https://prove2.me/theorems/7069fd45-7cb1-40bc-932a-71a3c417c555
-- title:
--   The wide gate set $G_{\mathrm{QACf}}$ with Fan-Out width $\le w_F$ and Toffoli width $\le w_T$
-- statement:
--   For width bounds $w_F,w_T\in\mathbb N$, the wide gate set of Corollary 1 is
--   $$
--   G_{\mathrm{QACf}} := \{H, X, Z, S, S^\dagger, \mathrm{CNOT}, CZ\}\ \cup\ \{\text{Fan-Out with } k \text{ targets} : 1\le k\le w_F\}\ \cup\ \{\text{generalized Toffoli with } k \text{ controls} : 1\le k\le w_T\}.
--   $$
--   Corollary 1 takes $w_F=O_\gamma(\log^{1/2+\gamma}(1/\varepsilon))$ and $w_T=O(\log(1/\varepsilon))$; here the widths are parameters, bounded by the statements that use the set.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Corollary 1, Eq. (101), p.26

import Definitions.Def_DepthOptQC_Synth_phaseSdg
import Definitions.Def_DepthOptQC_Synth_cz
import Definitions.Def_DepthOptQC_Synth_gToffoli
import Definitions.Def_DepthOptQC_Synth_fanOut

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The wide gate set `G_QACf` with width bounds `wF`, `wT`** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Corollary 1, Eq. (101), p.26):
`G_QACf := {H, X, Z, S, S†, CNOT, CZ, Fan-Out, GToffoli}`, where Fan-Out ranges over the Fan-Out gates
with `k` targets, `1 ≤ k ≤ wF`, and GToffoli over the generalized Toffoli gates with `k` controls,
`1 ≤ k ≤ wT`.

**Formalization Note.** The paper bounds the widths by `O_γ(log^{1/2+γ}(1/ε))` and `O(log(1/ε))`;
here the widths are parameters, and the statements using this set bound them (reading R5: width
is the number of Fan-Out targets, resp. Toffoli controls). -/
def gqacfGateSet (wF wT : ℕ) : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 pauliX, Gate.ofMatrix1 pauliZ, Gate.ofMatrix1 phaseS,
    Gate.ofMatrix1 phaseSdg, Gate.ofMatrix2 cnot, Gate.ofMatrix2 cz} ∪
    {g | ∃ k, 1 ≤ k ∧ k ≤ wF ∧ g = fanOut k} ∪ {g | ∃ k, 1 ≤ k ∧ k ≤ wT ∧ g = gToffoli k}

end DepthOptQC.Synth


