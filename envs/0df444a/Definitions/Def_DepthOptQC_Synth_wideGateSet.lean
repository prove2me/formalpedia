-- Prove2me | Definitions.Def_DepthOptQC_Synth_wideGateSet
-- name    : DepthOptQC_Synth_wideGateSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:16:32.864182+00:00
-- url     : https://prove2.me/theorems/06183708-1cd0-488c-9cfb-57c7059a2e88
-- title:
--   Theorem 1's wide gate set: $H$, $S$, Fan-Out with $\le w_F$ targets, generalized Toffoli with $\le w_T$ controls
-- statement:
--   For width bounds $w_F,w_T\in\mathbb N$, this is the gate set of the second clause of Theorem 1, "$H$ and $S$, together with … generalized Toffoli gates and … Fan-Out gates":
--   $$
--   \{H, S\}\ \cup\ \{\text{Fan-Out with } k \text{ targets} : 1\le k\le w_F\}\ \cup\ \{\text{generalized Toffoli with } k \text{ controls} : 1\le k\le w_T\}.
--   $$
--   The only single-qubit gates are $H$ and $S$; in particular $X$, $Z$, $S^\dagger$ and $T$ are not members.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 1, p.6; §1.1, p.5

import Definitions.Def_DepthOptQC_Synth_gToffoli
import Definitions.Def_DepthOptQC_Synth_fanOut

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The gate set of Theorem 1's second clause with width bounds `wF`, `wT`** (Vasconcelos,
*Depth-Optimal Quantum Compilation*, arXiv:2609.34659, Theorem 1, p.6: "a constant-depth circuit
over H and S, together with width-`O(log(1/ε))` generalized Toffoli gates and
width-`O_γ(log^{1/2+γ}(1/ε))` Fan-Out gates"; §1.1, p.5): the single-qubit gates `H` and `S`, the
Fan-Out gates with `k` targets for `1 ≤ k ≤ wF`, and the generalized Toffoli gates with `k` controls
for `1 ≤ k ≤ wT`.

**Formalization Note.** No other single-qubit gate is in the set (`X`, `Z`, `S†` are not members);
the widths are parameters that the statements using this set bound (reading R5). -/
def wideGateSet (wF wT : ℕ) : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 phaseS} ∪
    {g | ∃ k, 1 ≤ k ∧ k ≤ wF ∧ g = fanOut k} ∪ {g | ∃ k, 1 ≤ k ∧ k ≤ wT ∧ g = gToffoli k}

end DepthOptQC.Synth


