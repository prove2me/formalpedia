-- Prove2me | Definitions.Def_BaconOQEC_Xbar
-- name    : BaconOQEC_Xbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:28.781623+00:00
-- url     : https://prove2.me/theorems/f105b4f8-a421-4cc6-a635-04bb69b2a572
-- title:
--   Logical operator $\bar X$ (a full row of $X$)
-- statement:
--   The logical $X$ operator of the encoded qubit is a full row of Pauli $X$ operators,
--
--   $$
--   \bar X = \prod_{j=1}^n X_{1,j}.
--   $$
--
--   **Formalization Note** Rows are 0-based, so the paper's row $1$ is row $0$: $\bar X = P(a,0)$ with $a_{i,j} = 1$ exactly when $i = 0$.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.D, eq. (25), p.8

import Mathlib
import Definitions.Def_BaconOQEC_pauliXZ

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.D, eq. (25), p.8: the logical `X` operator
"X̄ = ∏_{j=1}^n X_{1,j}", a full row of `X` operators on the first row.

**Formalization Note.** Rows are 0-based, so the paper's row 1 is row `0`; `X̄ = P(a, 0)` with
`a_{i,j} = 1` iff `i = 0`. `n = m + 1`. -/
noncomputable def Xbar {m : ℕ} :
    Matrix (Qubits ((m + 1) * (m + 1))) (Qubits ((m + 1) * (m + 1))) ℂ :=
  pauliXZ (fun i _ => if i = 0 then 1 else 0) 0

end BaconOQEC


