-- Prove2me | Definitions.Def_DepthOptQC_Synth_intVal
-- name    : DepthOptQC_Synth_intVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:41.602205+00:00
-- url     : https://prove2.me/theorems/4b619247-975d-4640-a026-71676d31228e
-- title:
--   The integer $\mathrm{int}(\vec x)=\sum_j 2^j x_j$ of a bit string
-- statement:
--   For an $m$-bit string $\vec x = x_{m-1}\cdots x_1x_0\in\{0,1\}^m$, where $x_{m-1}$ is the most significant bit, the encoded integer is
--   $$
--   \mathrm{int}(\vec x) := \sum_{j=0}^{m-1} 2^j x_j \in \{0,1,\dots,2^m-1\}.
--   $$
--
--   **Formalization Note** Bit $x_j$ is carried by wire $j$ of the register, so the last wire is the most significant.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §3.2, Eq. (31), p.16

import Definitions.Def_QAlgorithms_Defs_Basic

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The integer encoded by a bit string** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Eq. (31), p.16): `int(x) := Σ_{j=0}^{m−1} 2^j x_j`, where `x_{m−1}` is the most
significant bit.

**Formalization Note.** Bit `x_j` is carried by wire `j` of the `m`-qubit register (reading R9), so
the last wire is the most significant; this is the reverse of `QAlgorithms.bitsToNat`, which reads
wire `0` as the most significant bit. -/
def intVal {m : ℕ} (x : Qubits m) : ℕ :=
  ∑ j : Fin m, if x j then 2 ^ (j : ℕ) else 0

end DepthOptQC.Synth


