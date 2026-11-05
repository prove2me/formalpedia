-- Prove2me | Definitions.Def_BaconOQEC_InCS
-- name    : BaconOQEC_InCS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:51.609889+00:00
-- url     : https://prove2.me/theorems/5b4ffccf-e722-4b1f-b679-b605f5c37db8
-- title:
--   Commuting with the stabilizer, $P(a,b)\in C(\mathcal S)$
-- statement:
--   The predicate says that the Pauli operator $P(a,b)$ commutes with every stabilizer generator $S^X_i$ and $S^Z_i$, $i = 1,\dots,n-1$, and hence with all of $\mathcal S$. These are the operators that preserve every syndrome sector $\mathcal H_{s^X,s^Z}$; those among them outside $\mathcal T$ act on the encoded qubit ("modulo the stabilizer structure of $\mathcal S$, $\mathcal L$ is a single encoded qubit", p.6).
--
--   **Formalization Note** Defined by commutation (the bit $\langle\cdot,\cdot\rangle = 0$) with the $2(n-1)$ generators, modulo phase. It is not defined through any parity characterization; that characterization is part of what the goal theorem asserts.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.B–C, pp.6–8

import Mathlib
import Definitions.Def_BaconOQEC_symp
import Definitions.Def_BaconOQEC_SX
import Definitions.Def_BaconOQEC_SZ

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.B–C, pp.6–8: `P(a, b)` commutes with the whole stabilizer `S` (the
centralizer `C(S)`): it commutes with every generator `S^X_i` and `S^Z_i` of (12). These are the
Pauli operators that preserve every syndrome sector `H_{s^X,s^Z}` of (14); those outside `T` act on
the encoded qubit (p.6: "modulo the stabilizer structure of S, L is a single encoded qubit").

**Formalization Note.** Defined by commutation (`symp = 0`) with the `2(n − 1)` generators, not by
any parity characterization (that is the content of the goal theorem). Modulo phase, on pairs
of bit matrices; `n = m + 1`, generators indexed by `Fin m`. -/
def InCS {m : ℕ} (a b : Bits m) : Prop :=
  ∀ i : Fin m, symp (a, b) (SX i) = 0 ∧ symp (a, b) (SZ i) = 0

end BaconOQEC


