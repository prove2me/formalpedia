-- Prove2me | Definitions.Def_DepthOptQC_Synth_gqncGateSet
-- name    : DepthOptQC_Synth_gqncGateSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:15:11.580515+00:00
-- url     : https://prove2.me/theorems/56d86818-f374-4021-98b0-9828f983851b
-- title:
--   The bounded-width gate set $G_{\mathrm{QNC}}=\{H,X,Z,S,S^\dagger,\mathrm{CNOT},CZ,\mathrm{Toffoli}\}$
-- statement:
--   The bounded-width gate set of Theorem 8 is
--   $$
--   G_{\mathrm{QNC}} := \{H, X, Z, S, S^\dagger, \mathrm{CNOT}, CZ, \mathrm{Toffoli}\},
--   $$
--   where $H$ is the Hadamard gate, $X$ and $Z$ the Pauli gates, $S=\operatorname{diag}(1,i)$, CNOT the controlled NOT (control first), $CZ=\operatorname{diag}(1,1,1,-1)$ and Toffoli the ordinary three-qubit Toffoli gate. Every gate acts on at most three qubits.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 8, Eq. (79), p.23

import Definitions.Def_DepthOptQC_Synth_phaseSdg
import Definitions.Def_DepthOptQC_Synth_cz
import Definitions.Def_DepthOptQC_Synth_gToffoli

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The bounded-width gate set `G_QNC`** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Theorem 8, Eq. (79), p.23):
`G_QNC := {H, X, Z, S, S†, CNOT, CZ, Toffoli}`, where Toffoli is the ordinary three-qubit Toffoli
gate (`gToffoli 2`). Single-qubit members are `Gate.ofMatrix1` of the shared matrices, two-qubit
members `Gate.ofMatrix2` (gate wire `0` the control of `CNOT`). -/
def gqncGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 pauliX, Gate.ofMatrix1 pauliZ, Gate.ofMatrix1 phaseS,
    Gate.ofMatrix1 phaseSdg, Gate.ofMatrix2 cnot, Gate.ofMatrix2 cz, gToffoli 2}

end DepthOptQC.Synth


