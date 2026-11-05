-- Prove2me | Definitions.Def_BaconOQEC_Zbar
-- name    : BaconOQEC_Zbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:24.818609+00:00
-- url     : https://prove2.me/theorems/00e40339-02d8-4756-8e33-71ec2c41a2c1
-- title:
--   Logical operator $\bar Z$ (a full column of $Z$)
-- statement:
--   The logical $Z$ operator of the encoded qubit is a full column of Pauli $Z$ operators,
--
--   $$
--   \bar Z = \prod_{i=1}^n Z_{i,1}.
--   $$
--
--   **Formalization Note** Columns are 0-based, so the paper's column $1$ is column $0$: $\bar Z = P(0,b)$ with $b_{i,j} = 1$ exactly when $j = 0$.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.D, eq. (26), p.8

import Mathlib
import Definitions.Def_BaconOQEC_pauliXZ

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.D, eq. (26), p.8: the logical `Z` operator
"Z̄ = ∏_{i=1}^n Z_{i,1}", a full column of `Z` operators on the first column.

**Formalization Note.** Columns are 0-based, so the paper's column 1 is column `0`; `Z̄ = P(0, b)`
with `b_{i,j} = 1` iff `j = 0`. `n = m + 1`. -/
noncomputable def Zbar {m : ℕ} :
    Matrix (Qubits ((m + 1) * (m + 1))) (Qubits ((m + 1) * (m + 1))) ℂ :=
  pauliXZ 0 (fun _ j => if j = 0 then 1 else 0)

end BaconOQEC


