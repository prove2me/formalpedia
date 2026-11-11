-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Verifier
-- name    : UnitaryQIPPSPACE_Verifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:02.762927+00:00
-- url     : https://prove2.me/theorems/35b37a80-9f16-424c-bd27-a51e86b02a20
-- title:
--   Quantum verifiers and provers
-- statement:
--   A $k$-round **quantum verifier** is a sequence of circuits $V=(V_1,\dots,V_k)$ acting on registers $(Z,M)$, where the private register $Z$ consists of a work register $Z_{\mathrm{work}}$ ($w$ qubits), a flag qubit $Z_{\mathrm{flag}}$ and an output register $Z_{\mathrm{out}}$ ($o$ qubits), and $M$ is the message register ($m$ qubits). Each $V_i$ is a well-formed circuit on the $w+1+o+m$ qubits of $(Z,M)$. The size of $V$ is the sum of the sizes of the $V_i$; its description lists the register sizes and the descriptions of $V_1,\dots,V_k$.
--
--   A **quantum prover** chooses a private register $Y$ of any number $y$ of qubits and a unitary $P$ on $M\otimes Y$, applied in every prover step. "This unitary model of the prover is without loss of generality, since the prover may use an arbitrarily large private register."
--
--   **Formalization Note** The register layout on $(Z,M)$ is $Z_{\mathrm{work}}$, $Z_{\mathrm{flag}}$, $Z_{\mathrm{out}}$, $M$ in this order. The module also defines the prover given by a unitary circuit on $M$ followed by $Y$ (Theorem 3.1) and the state $|0\cdots0\rangle$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2, Quantum interactive proof systems, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_Circuit

open Matrix QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- A **quantum verifier** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*, arXiv:2611.02819, held
version sha256 9e357a00…, §2 Quantum interactive proof systems, p. 11 (PDF p. 13)): "A `k`-round
quantum verifier is a sequence of quantum circuits `V = (V_i)_{i=1}^k`. Each `V_i` acts on a pair of
registers `(Z, M)`, and represents the action of the verifier in the `i`-th round of interaction
with the prover. The register `Z` is the private register of the verifier and consists of three
sub-registers: the work register `Z_work` for intermediate computations, the flag register `Z_flag`
recording the accept/reject decision, and the output register `Z_out` storing the output state, if
any. The register `M` is the message register for communication with the prover. The size of `V` is
the sum of the sizes of the circuits `V_i`."

Register layout on the `w + 1 + o + m` qubits of `(Z, M)`: qubits `0, …, w-1` are `Z_work`, qubit
`w` is `Z_flag`, qubits `w+1, …, w+o` are `Z_out`, qubits `w+1+o, …, w+o+m` are `M`. The rounds
are `V_1, …, V_k` in order (`k = rounds.length`).

**Formalization Note** The register sizes are part of the verifier and of its description. -/
structure Verifier where
  /-- number of qubits of `Z_work` -/
  w : ℕ
  /-- number of qubits of `Z_out` -/
  o : ℕ
  /-- number of qubits of the message register `M` -/
  m : ℕ
  /-- the circuits `V_1, …, V_k` -/
  rounds : List Circuit

namespace Verifier

/-- The number of qubits of `(Z, M)`. -/
def dim (V : Verifier) : ℕ := V.w + 1 + V.o + V.m

/-- The flag qubit `Z_flag`. -/
def flagIdx (V : Verifier) : Fin V.dim := ⟨V.w, by unfold dim; omega⟩

/-- The `i`-th qubit of `Z_out`. -/
def outIdx (V : Verifier) (i : Fin V.o) : Fin V.dim := ⟨V.w + 1 + i.val, by unfold dim; omega⟩

/-- Every round is a well-formed circuit on the `dim` qubits of `(Z, M)` returning `dim` qubits. -/
def WF (V : Verifier) : Prop := ∀ c ∈ V.rounds, c.WF V.dim V.dim

/-- The size: the sum of the sizes of the rounds. -/
def size (V : Verifier) : ℕ := (V.rounds.map List.length).sum

/-- The description: the register sizes followed by the descriptions of `V_1, …, V_k`. -/
def code (V : Verifier) : Str :=
  tup ([natCode V.w, natCode V.o, natCode V.m] ++ V.rounds.map Circuit.code)

end Verifier

/-- A **quantum prover** (p. 11, PDF p. 13): "A quantum prover is modeled as a unitary channel `P`
acting on a pair of registers `(M, Y)`, where `Y` is the private register of the prover. We note
that this unitary model of the prover is without loss of generality, since the prover may use an
arbitrarily large private register to purify its operations and to keep track of the current
round."

Here `y` is the number of qubits of `Y`, chosen by the prover (any `y ∈ ℕ`), and `U` is any unitary
on `M ⊗ Y` (`m` message qubits). -/
structure Prover (m : ℕ) where
  /-- number of qubits of the private register `Y` -/
  y : ℕ
  /-- the unitary applied in every prover step -/
  U : Matrix.unitaryGroup (Bits m × Bits y) ℂ

/-- The prover operator on `M ⊗ Y` (`m` and `y` qubits) given by a unitary circuit on `m + y`
qubits whose first `m` qubits are `M` and last `y` qubits are `Y` (Theorem 3.1, p. 13: "a
space-uniform family of unitary circuits `{P_n}` such that the prover `P_n` …"). -/
noncomputable def circuitProver (c : Circuit) (m y : ℕ) :
    Matrix (Bits m × Bits y) (Bits m × Bits y) ℂ :=
  Matrix.reindex (Bits.splitEquiv m y) (Bits.splitEquiv m y) (c.umat (m + y))

/-- The state `|0⋯0⟩⟨0⋯0|` of `y` qubits. -/
def zeroState (y : ℕ) : Matrix (Bits y) (Bits y) ℂ :=
  fun a b => if a = Bits.zero y ∧ b = Bits.zero y then 1 else 0

end UnitaryQIPPSPACE


