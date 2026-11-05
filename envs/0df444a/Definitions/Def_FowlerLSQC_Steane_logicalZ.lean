-- Prove2me | Definitions.Def_FowlerLSQC_Steane_logicalZ
-- name    : FowlerLSQC_Steane_logicalZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:18.601956+00:00
-- url     : https://prove2.me/theorems/4441eef0-ba4a-40d6-af61-771f0944f974
-- title:
--   The logical $Z$ operator $\mathtt{ZZZIIII}$
-- statement:
--   The logical $Z$ of the Steane code is the seven-qubit Pauli operator
--
--   $$\bar Z=\mathtt{ZZZIIII}=Z\otimes Z\otimes Z\otimes I\otimes I\otimes I\otimes I .$$
--
--   It separates the two logical states: it fixes $|0_L\rangle$ and negates $|1_L\rangle$.
--
--   **Formalization Note** Fig. 10.2(c) of the source applies $Z$ to all seven qubits with the last four in brackets, "optional as they implement stabilizers". This definition takes the three unbracketed gates; the bracketed product $\mathtt{IIIZZZZ}$ is the stabilizer (10.10).
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.3, Fig. 10.2(c), p.117 (PDF p.135)

import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace FowlerLSQC.Steane

open QAlgorithms QAlgorithms.Stabilizer

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.3, Fig. 10.2(c),
p.117 (PDF p.135): the logical `Z` operator `ZZZIIII`, that is `Z` on the first three qubits.

**Formalization Note.** Fig. 10.2(c) brackets the `Z` gates on the last four qubits, "optional as
they implement stabilizers", so the figure has two representatives, `ZZZIIII` and `ZZZZZZZ`, whose
product is the stabilizer `IIIZZZZ` of (10.10). This definition takes the unbracketed gates. Phase
exponent `0`; position `q` from the left acts on wire `q`. -/
def logicalZ : PauliString 7 :=
  ⟨0, ![.Z, .Z, .Z, .I, .I, .I, .I]⟩

end FowlerLSQC.Steane


