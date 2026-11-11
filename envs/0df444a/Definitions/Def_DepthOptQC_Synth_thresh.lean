-- Prove2me | Definitions.Def_DepthOptQC_Synth_thresh
-- name    : DepthOptQC_Synth_thresh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:16:51.747121+00:00
-- url     : https://prove2.me/theorems/5110c082-c2e2-4d98-9ff1-22a9d81a5304
-- title:
--   The value thresholding function $f^m_M(\vec x)=\mathbf 1[\mathrm{int}(\vec x)<M]$
-- statement:
--   For $m\ge1$ and a hardwired integer $M\in\{0,1,\dots,2^m\}$, the **value thresholding function** is
--   $$
--   f^m_M(\vec x) := \mathbf 1[\mathrm{int}(\vec x) < M],\qquad \vec x\in\{0,1\}^m .
--   $$
--   It compares the integer stored in an address register with a classical constant; three of these comparisons split the $2^m$ addresses into the four intervals of the block encoding. It is not the Hamming-weight threshold of circuit complexity.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §3.2, Eq. (32), p.16

import Definitions.Def_DepthOptQC_Synth_intVal

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The value thresholding function** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Eq. (32), p.16): `f^m_M(x) := 1[int(x) < M]` for a hardwired integer `M`
(the paper takes `M ∈ {0, 1, …, 2^m}`; the statements using it assume `M ≤ 2^m`). -/
def thresh (m M : ℕ) (x : Qubits m) : Bool :=
  decide (intVal x < M)

end DepthOptQC.Synth


