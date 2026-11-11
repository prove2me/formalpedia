-- Prove2me | Definitions.Def_DepthOptQC_Synth_phaseSdg
-- name    : DepthOptQC_Synth_phaseSdg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:12:23.464713+00:00
-- url     : https://prove2.me/theorems/52da2c76-42e9-43bf-b7a6-9042117c866b
-- title:
--   The gate $S^\dagger=\operatorname{diag}(1,-i)$
-- statement:
--   The single-qubit gate
--   $$
--   S^\dagger=\begin{pmatrix}1&0\\0&-i\end{pmatrix},
--   $$
--   the adjoint of the phase gate $S=\operatorname{diag}(1,i)$. It belongs to the bounded-width gate set $G_{\mathrm{QNC}}$ and to $G_{\mathrm{QACf}}$, and is used in the SELECT step of the block encoding.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Eq. (79), p.23; Eq. (91), p.24

import Definitions.Def_QAlgorithms_Defs_Gates

namespace DepthOptQC.Synth

/-- **The gate `S† = diag(1, −i)`** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Eq. (79), p.23, and Eq. (91), p.24), the adjoint of the phase gate
`S = diag(1, i)` (`QAlgorithms.phaseS`). -/
def phaseSdg : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then -Complex.I else 1

end DepthOptQC.Synth


