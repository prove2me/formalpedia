-- Prove2me | Definitions.Def_HeisenbergRep_Knill_GKFamily
-- name    : HeisenbergRep_Knill_GKFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:03.635986+00:00
-- url     : https://prove2.me/theorems/fd36101c-824c-4af9-8451-925c8b0c2658
-- title:
--   Uniform family of classically controlled Clifford computers with Pauli measurements, and the joint law of record and final state
-- statement:
--   A **Knill computer family** consists of polynomials $\mathrm{rbits}$ and $\mathrm{steps}$ and a classical controller. On $n$ qubits, given random bits $r\in\{0,1\}^{\mathrm{rbits}(n)}$ and the transcript of the steps so far, the controller names the next operation (a Clifford gate or a signed Pauli measurement) or halts. It halts after at most $\mathrm{steps}(n)$ operations, and it is computable in polynomial time, as a map from the code of $(n,r,\text{transcript})$ ($n$ in unary) to the code of its answer, by a multi-stack Turing machine.
--
--   A **run** on the input basis state $|x\rangle$, $x\in\{0,1\}^n$, proceeds step by step from $(|x\rangle,\text{empty transcript})$:
--
--   1. if the controller halts, nothing changes;
--   2. a Clifford gate $U$ replaces $|\psi\rangle$ by $U|\psi\rangle$ and appends the entry "gate" to the transcript;
--   3. a measurement of $A$ gives the result $-1$ with probability $\|P_-\psi\|^2$ and $+1$ with probability $\|P_+\psi\|^2$, where $P_\pm=\tfrac12(I\pm A)$; the state becomes $P_\pm\psi/\|P_\pm\psi\|$ and the result is appended to the transcript.
--
--   The **record law** $\mathrm{rec}_F(n,x)$ is the joint distribution of the pair
--
--   $$\bigl(\text{transcript},\ |\psi_{\mathrm{final}}\rangle\langle\psi_{\mathrm{final}}|\bigr)$$
--
--   after $\mathrm{steps}(n)$ steps, when $r$ is uniform and measurement results follow the Born rule.
--
--   **Formalization Note** The structure has the shape of the published `QAlgorithms.Stabilizer.MCCFamily` (de Wolf), with its operation type replaced by all Clifford gates and signed Pauli measurements. The result $+1$ is recorded as `false`. The Born probability is clipped at $1$ (`min 1`), which matters only for non-unit vectors, never reached by a run. The final state is recorded as a density matrix, so its global phase is discarded.
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §8, pp. 17–19, Theorem 1, p. 19; §7, Eq. (35), p. 15

import Mathlib
import Definitions.Def_HeisenbergRep_Knill_GKOp

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- **A uniform family of classically controlled Clifford computers with Pauli measurements
(Knill's computers).**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §8,
Theorem 1 (Knill's theorem), p. 19: "Any quantum computer performing only: a) Clifford group gates,
b) measurements of Pauli group operators, and c) Clifford group operations conditioned on classical
bits, which may be the results of earlier measurements"; p. 17: "add Clifford group operations
conditioned on classical bits (which might, of course, be the results of measurements performed
earlier in the computation)".

On `n` qubits, with random bits `r` (`rbits(n)` of them) and the transcript of the steps so far
(`none` for a gate, `some β` for a measurement with outcome `β`; `β = false` is the result `+1`),
the controller names the next operation (`GKOp n`: any Clifford gate, or the measurement of a
signed Hermitian Pauli operator) or halts (`none`). It halts after at most `steps(n)` operations,
and it is computable in polynomial time from `(n, r, transcript)` (`n` in unary), its answer
written with `GKOp.code`.

**Formalization Note.** This has the shape of the published `QAlgorithms.Stabilizer.MCCFamily`
(de Wolf's measurement-controlled Clifford circuits), with its operation type `CliffordOp`
(Pauli, `H`, `S`, `CNOT` gates and unsigned Pauli measurements) replaced by `GKOp` (every Clifford
unitary, signed Pauli measurements). "Any quantum computer … in polynomial time" is read as a
uniform family with polynomially many random bits and steps and a polynomial-time controller
(Reading R2); the controller may choose any operation, including which operator to measure, from
its random bits and the whole transcript of earlier outcomes (Reading R5). -/
structure GKFamily where
  /-- The number of random bits, a polynomial in `n`. -/
  rbits : Polynomial ℕ
  /-- The bound on the number of operations, a polynomial in `n`. -/
  steps : Polynomial ℕ
  /-- The classical controller. -/
  ctrl : (n : ℕ) → List Bool → List (Option Bool) → Option (GKOp n)
  /-- It halts within `steps(n)` operations. -/
  halts : ∀ n r hist, steps.eval n ≤ hist.length → ctrl n r hist = none
  /-- It is polynomial-time computable. -/
  polytime : ∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ n r hist, g (encCtrlInput n r hist) = GKOp.code (ctrl n r hist)

/-- One step of the run with random bits `r` (Eq. (35), p. 15, and the Born rule): query the
controller on the transcript; apply the Clifford gate `U` (record `none`), or measure the Pauli
operator `A`, or halt (state and transcript unchanged). A measurement of `A` gives the result `−1`
(`β = true`) with probability `‖P₋ ψ‖²` and `+1` (`β = false`) with probability `‖P₊ ψ‖²`, where
`P± = ½(I ± A)`, and leaves the renormalized state `P± ψ / ‖P± ψ‖`; the outcome is appended to the
transcript.

**Formalization Note.** This is `MCCFamily.step` with the signed `A`. The `min 1` only matters
for a non-unit `ψ`, which a run never reaches. -/
noncomputable def GKFamily.step (F : GKFamily) (n : ℕ) (r : List Bool)
    (st : EuclideanSpace ℂ (Qubits n) × List (Option Bool)) :
    PMF (EuclideanSpace ℂ (Qubits n) × List (Option Bool)) :=
  match F.ctrl n r st.2 with
  | none => PMF.pure st
  | some (.clifford U _) => PMF.pure (act (U : Matrix (Qubits n) (Qubits n) ℂ) st.1, st.2 ++ [none])
  | some (.measure A _) =>
      let proj : Bool → Matrix (Qubits n) (Qubits n) ℂ := fun β =>
        (2⁻¹ : ℂ) • (1 + (if β then (-1 : ℂ) else 1) • A.toMatrix)
      (PMF.bernoulli (min 1 (Real.toNNReal (‖act (proj true) st.1‖ ^ 2))) (min_le_left _ _)).map
        fun β => (((‖act (proj β) st.1‖)⁻¹ : ℝ) • act (proj β) st.1, st.2 ++ [some β])

/-- The law of (state, transcript) after `k` steps, from the basis state `|x⟩` with random bits
`r`. -/
noncomputable def GKFamily.run (F : GKFamily) (n : ℕ) (r : List Bool) (x : Qubits n) :
    ℕ → PMF (EuclideanSpace ℂ (Qubits n) × List (Option Bool))
  | 0 => PMF.pure (ket x, [])
  | k + 1 => (F.run n r x k).bind (F.step n r)

/-- **The joint law of the classical record and the final quantum state.** The computer runs on
`|x⟩` with uniformly random bits `r` and Born measurement outcomes for `steps(n)` steps; the result
is the pair (transcript, `|ψ_final⟩⟨ψ_final|`).

**Formalization Note.** The state is recorded as its density matrix, so the global phase is
discarded (a global phase is not observable). This is the joint law of Reading R1: the transcript
of measurement outcomes together with the final state. -/
noncomputable def GKFamily.recordDist (F : GKFamily) (n : ℕ) (x : Qubits n) :
    PMF (List (Option Bool) × Matrix (Qubits n) (Qubits n) ℂ) :=
  (PMF.uniformOfFintype (Fin (F.rbits.eval n) → Bool)).bind fun r =>
    (F.run n (List.ofFn r) x (F.steps.eval n)).map fun st => (st.2, pureDensity st.1)

end HeisenbergRep.Knill


