-- Prove2me | Definitions.Def_CollectiveDFS_pauli
-- name    : CollectiveDFS_pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:29.500072+00:00
-- url     : https://prove2.me/theorems/5efab13d-67ad-4b22-994d-a76ccb4a7521
-- title:
--   Pauli matrices $\sigma_x,\sigma_y,\sigma_z$
-- statement:
--   The **Pauli matrices** of (5.2),
--   $$\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad \sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},$$
--   written in the basis of $\sigma_z$-eigenstates $|0\rangle,|1\rangle$, collected as one family $\sigma_\alpha$ indexed by $\alpha\in\{x,y,z\}$.
--
--   They are the one-qubit building blocks of the collective spin operators.
--
--   **Formalization Note** The index is $\alpha:\mathrm{Fin}\,3$ with $0,1,2$ standing for $x,y,z$; the three matrices are the platform's `QAlgorithms.pauliX`, `pauliY`, `pauliZ`, indexed by `Bool` with `false` $=|0\rangle$.
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (5.2), p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates

open QAlgorithms

namespace CollectiveDFS

/-- The Pauli matrices `σ_x, σ_y, σ_z` of (5.2), indexed by `α : Fin 3` (`0 = x`, `1 = y`,
`2 = z`) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eq. (5.2), p.12, PDF p.12).

**Formalization Note** Matrices are indexed by `Bool`, `false` being `|0⟩` and `true` being
`|1⟩`; so `σ_z |0⟩ = |0⟩` as in (5.2). §VII calls `|1⟩` "up" only symbolically (p.21); every
statement of this mission quantifies over all magnetic numbers, so the choice changes nothing. -/
def pauli : Fin 3 → Matrix Bool Bool ℂ :=
  ![pauliX, pauliY, pauliZ]

end CollectiveDFS


