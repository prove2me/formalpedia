-- Prove2me | Definitions.Def_BaconOQEC_recovery
-- name    : BaconOQEC_recovery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:25.939915+00:00
-- url     : https://prove2.me/theorems/b69762f2-caae-429f-b9ca-b3fdfa41b4eb
-- title:
--   Recovery operator $Q(s)$
-- statement:
--   The recovery applied after the syndrome $s = (s^X,s^Z)$ has been measured combines the $Z$-correction $Q_1(f'')$ of (24) on column $j_0$ with its $X$ analogue on row $i_0$:
--
--   $$
--   Q(s) = P\big(a_{\mathrm{rec}}(s, i_0),\ b_{\mathrm{rec}}(s, j_0)\big).
--   $$
--
--   Here $a_{\mathrm{rec}}$ is the bit matrix of the $X$-correction and $b_{\mathrm{rec}}$ that of the $Z$-correction ("Pauli $Y$ errors are taken care of by the combined action of these two procedures").
--
--   **Formalization Note** $Q$ is a function of the syndrome and the two free indices only. Its phase is irrelevant to every statement about it.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, eq. (24) and p.8

import Mathlib
import Definitions.Def_BaconOQEC_pauliXZ
import Definitions.Def_BaconOQEC_recX
import Definitions.Def_BaconOQEC_recZ

open QAlgorithms

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, pp.7–8: the recovery Pauli operator applied after the syndrome
`s = (s^X, s^Z)` has been measured: the `Z`-correction `Q₁(f″)` of (24) on column `j₀` combined with
its `X` analogue on row `i₀` ("Pauli Y errors are taken care of by the combined action of these two
procedures"), `Q(s) = P(recX s i₀, recZ s j₀)`.

**Formalization Note.** A function of the syndrome and the two free indices only (never of the
error). The phase of `Q` is irrelevant for every statement about it; `P = X^a Z^b` as in (7). -/
noncomputable def recovery {m : ℕ} (s : (Fin m → ZMod 2) × (Fin m → ZMod 2))
    (i0 j0 : Fin (m + 1)) :
    Matrix (Qubits ((m + 1) * (m + 1))) (Qubits ((m + 1) * (m + 1))) ℂ :=
  pauliXZ (recX s i0) (recZ s j0)

end BaconOQEC


