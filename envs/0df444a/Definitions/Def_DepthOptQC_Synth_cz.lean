-- Prove2me | Definitions.Def_DepthOptQC_Synth_cz
-- name    : DepthOptQC_Synth_cz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:12:27.908223+00:00
-- url     : https://prove2.me/theorems/6e359934-aa3f-4f99-bfb3-7c82b01e8af8
-- title:
--   The controlled-$Z$ gate $CZ=\operatorname{diag}(1,1,1,-1)$
-- statement:
--   The two-qubit gate
--   $$
--   CZ=\operatorname{diag}(1,1,1,-1),\qquad CZ\,|a,b\rangle=(-1)^{ab}|a,b\rangle ,
--   $$
--   which multiplies $|11\rangle$ by $-1$ and fixes the other basis states. It is symmetric in its two qubits. It belongs to $G_{\mathrm{QNC}}$ and $G_{\mathrm{QACf}}$, and applies $Z$ to the system qubit conditioned on an interval label in the SELECT step.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Eq. (79), p.23; Eq. (91), p.24

import Definitions.Def_QAlgorithms_Defs_Gates

namespace DepthOptQC.Synth

/-- **The controlled-Z gate `CZ = diag(1, 1, 1, −1)`** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Eq. (79), p.23, and Eq. (91), p.24): the two-qubit gate that puts a
phase `−1` on `|11⟩`. Indexed by `Bool × Bool`, first factor the first qubit (it is symmetric). -/
def cz : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.diagonal fun p => if p.1 && p.2 then -1 else 1

end DepthOptQC.Synth


