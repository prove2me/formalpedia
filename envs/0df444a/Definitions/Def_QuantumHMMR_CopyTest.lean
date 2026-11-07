-- Prove2me | Definitions.Def_QuantumHMMR_CopyTest
-- name    : QuantumHMMR_CopyTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:04.921178+00:00
-- url     : https://prove2.me/theorems/2110277e-e2ed-4be1-a39c-7c12fcf58bc7
-- title:
--   Test on $K$ copies of a pure state
-- statement:
--   A **copy test** for $n$-qubit states consists of a number $K$ of copies, a number $w$ of ancillas, a circuit of valid gate codes on $Kn + w$ wires and an output wire. On input state $\psi$ it applies the circuit to
--   $$
--   \psi^{\otimes K} \otimes |0^w\rangle
--   $$
--   and accepts when the computational-basis measurement of the output wire gives $1$. Applied to $\psi = U|0^n\rangle$, it makes $K$ parallel forward queries to $U$.
--
--   Its classical description is the binary code of $(K, w, \text{out}, \#\text{gates})$ followed by the codes of the gates.
--
--   **Formalization Note** Intermediate measurements, classical processing and random choices are deferred to the end of the circuit (the QPT model allows ancillas initialized to $|0\rangle$ and traced out). Copy $k$ occupies the wires of the published `copiesInputState`; ancillas come last.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, p.11; Lemma 4.4, p.14; proof of Theorem 1.3, p.16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_StabilizerLearning
import Definitions.Def_QuantumHMMR_GateCode
import Definitions.Def_QuantumHMMR_natListCode

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45

namespace QuantumHMMR

/-- A test on `K` copies of an `n`-qubit pure state (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §3, p.11 (QPT model) and §4.1, pp.14,
16: a test "using `12h + 10` copies", applied to copies of `U|0ⁿ⟩` "prepared by parallel forward
queries"). It is a circuit, a list of gate codes on `K·n + w` wires, that acts on `K` copies of
the input state followed by `w` ancillas in `|0⟩`; the test accepts when the computational-basis
measurement of the output wire `out` reads `1`.

**Formalization Note** All intermediate measurements and classical processing of the paper's test
are deferred to the end (the QPT model allows ancillas initialized to `|0⟩` and traced out). The
copies occupy the wires of the published `copiesInputState` (copy `k` on the wires
`finProdFinEquiv (k, j)`, ancillas last). The number of queries is `K`. -/
structure CopyTest (n : ℕ) where
  /-- The number of copies of the input state (parallel forward queries). -/
  K : ℕ
  /-- The number of ancilla wires, initialized to `|0⟩`. -/
  w : ℕ
  /-- The gates, applied in list order (head first). -/
  gates : List GateCode
  /-- The output wire. -/
  out : ℕ
  /-- Every gate acts on valid wires of the `K·n + w`-wire register. -/
  valid : ∀ g ∈ gates, g.Valid (K * n + w)
  /-- The output wire exists. -/
  out_lt : out < K * n + w

namespace CopyTest

variable {n : ℕ}

/-- The unitary `U_r ⋯ U_1` of the circuit `[U_1, …, U_r]` (the first gate acts first). -/
noncomputable def unitary (C : CopyTest n) : QMat (C.K * n + C.w) :=
  (C.gates.map (GateCode.op (C.K * n + C.w))).reverse.prod

/-- The acceptance probability of the test on `K` copies of `ψ`: the probability that the output
wire reads `1` after the circuit acts on `ψ^{⊗K} ⊗ |0^w⟩`. -/
noncomputable def accept (C : CopyTest n) (ψ : EuclideanSpace ℂ (Qubits n)) : ℝ :=
  probEvent (act C.unitary (copiesInputState n C.K C.w ψ))
    (fun z => z ⟨C.out, C.out_lt⟩ = true)

/-- The classical description of a test: the binary code of `[K, w, out, #gates]` followed by the
gate codes. -/
def encode (C : CopyTest n) : List Bool :=
  natListCode ([C.K, C.w, C.out, C.gates.length] ++ C.gates.flatMap GateCode.toNats)

end CopyTest

end QuantumHMMR


