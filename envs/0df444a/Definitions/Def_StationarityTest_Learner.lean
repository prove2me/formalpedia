-- Prove2me | Definitions.Def_StationarityTest_Learner
-- name    : StationarityTest_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:08.240131+00:00
-- url     : https://prove2.me/theorems/70f6762a-31a9-47a7-85d6-f94456f44d67
-- title:
--   Learners from copies of a mixed state, the dyadic output decoder and circuit channels
-- statement:
--   The paper names no model of computation. "There exists an algorithm using $N$ copies of $\rho$ in time $T$" is read in the model of the published Montanaro learner `QAlgorithms.CopyLearner`, extended from pure to mixed states. A **learner** runs rounds $k=0,\dots,R-1$. In round $k$ it:
--
--   1. takes $c_k\ge1$ fresh copies of the unknown $w$-qubit state $\rho$ and $a_k$ ancillas in $|0\rangle$;
--   2. applies a circuit over $\{H,T,\mathrm{CNOT}\}$, each of whose gates is switched on or off by a control bit computed by a Boolean circuit from the outcomes of earlier rounds;
--   3. measures every qubit in the computational basis.
--
--   The probability of an outcome record is the product of the Born probabilities $\langle z|U(\rho^{\otimes c_k}\otimes|0\rangle\langle0|)U^\dagger|z\rangle$. A final Boolean circuit maps the record to output bits. The **copies used** are $\sum_kc_k$. The **time** counts quantum gates, ancilla preparations and Boolean gates.
--
--   Output bits are read in blocks of $1+\mathrm{len}$ bits: a sign bit and a magnitude $m$ (most significant bit first) giving the dyadic number $\pm m/2^{wp}$. Every dyadic number of this form is reachable. A **circuit channel** $\Phi[\sigma]=\operatorname{tr}_{\mathrm{anc}}[U(\sigma\otimes|0\rangle\langle0|)U^\dagger]$ is given by a circuit over the same gate set on the system and $a$ ancillas.
--
--   This model makes "an algorithm" a finite object fixed before the unknown state, whose cost is charged gate by gate.
--
--   **Formalization Note** Field names and the time formula are those of `QAlgorithms.CopyLearner`. Copy $t$ of a round occupies wires `finProdFinEquiv (t, j)`, with the ancillas last. Randomness comes from measuring ancillas. The success probability of an event $E$ on the output bits is the sum over all outcome records of their probability times the indicator of $E$.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 5.1, p.28; Theorem 2.22, p.18; Lemma 2.23, p.19; Lemma 5.5, p.32 (the paper names no machine)

import Definitions.Def_StationarityTest_Pauli

open Matrix

namespace StationarityTest

/-!
# Learners from copies of a mixed state, output decoders and circuit channels

T. Bergamaschi, *The stationarity test*, arXiv:2610.01074 (held file sha256 0b7e46fb…),
Theorem 5.1, p.28; Theorem 2.22, p.18; Lemma 2.23, p.19; Lemma 5.5, p.32. The paper names no
model of computation; this is the model of the published `QAlgorithms.CopyLearner`
(Montanaro, arXiv:1707.04012v2), extended from pure to mixed states.

**Formalization Note.** A learner proceeds in rounds `k < R`. Round `k` takes `copies k ≥ 1`
fresh copies of the unknown `w`-qubit state `ρ` and `anc k` ancillas in `|0⟩`, applies a circuit
over the published gate set `{H, T, CNOT}` (`QAlgorithms.htcxGateSet`) whose gates are switched
on or off by control bits that Boolean circuits compute from the outcomes of the earlier rounds,
and measures every qubit in the computational basis. Copy `t` of a round occupies wires
`finProdFinEquiv (t, j)`, the ancillas come last (the layout of `QAlgorithms.copiesInputState`).
The law of the outcome record is the chain rule of the Born probabilities
`⟨z|U(ρ^{⊗c} ⊗ |0⟩⟨0|)U†|z⟩`. Randomness comes from measuring ancillas. A final Boolean circuit
maps the record to the output bits; the time is the number of quantum gates, ancilla
preparations and Boolean gates, exactly as `QAlgorithms.CopyLearner.time`. Output bits are read by
a fixed decoder: block `j` of `len + 1` bits is a sign bit followed by a `len`-bit magnitude
(most significant bit first), giving the dyadic number `±m/2^{wp}`. The learner is data fixed
before the unknown state.
-/

open QAlgorithms

/-- The input `ρ^{⊗c} ⊗ |0^a⟩⟨0^a|` of a round on `c` copies of the `w`-qubit state `ρ` and `a`
ancillas; copy `t` occupies wires `finProdFinEquiv (t, j)`, the ancillas come last. -/
noncomputable def copiesInputDensity (w c a : ℕ) (ρ : Matrix (Qubits w) (Qubits w) ℂ) :
    Matrix (Qubits (c * w + a)) (Qubits (c * w + a)) ℂ :=
  Matrix.of fun y z =>
    if ∀ b : Fin a, y (Fin.natAdd (c * w) b) = false ∧ z (Fin.natAdd (c * w) b) = false then
      ∏ t : Fin c, ρ (fun j => y (Fin.castAdd a (finProdFinEquiv (t, j))))
        (fun j => z (Fin.castAdd a (finProdFinEquiv (t, j))))
    else 0

/-- An adaptive learner from copies of a `w`-qubit mixed state with `out` output bits (see the
module docstring). -/
structure GibbsLearner (w out : ℕ) where
  /-- The number of rounds. -/
  R : ℕ
  /-- Copies consumed by each round. -/
  copies : Fin R → ℕ
  /-- Every round consumes at least one copy. -/
  copies_pos : ∀ k, 1 ≤ copies k
  /-- Ancillas of each round. -/
  anc : Fin R → ℕ
  /-- Classical control bits of each round. -/
  cbits : Fin R → ℕ
  /-- The circuit of each round, each gate optionally controlled by a control bit. -/
  template : (k : Fin R) → List (GateApp htcxGateSet (copies k * w + anc k) × Option (Fin (cbits k)))
  /-- The Boolean circuit computing the control bits of each round from the outcome record. -/
  ctrl : (k : Fin R) → BoolCircuit (∑ j, (copies j * w + anc j)) (cbits k)
  /-- The Boolean circuit computing the output bits from the outcome record. -/
  outC : BoolCircuit (∑ j, (copies j * w + anc j)) out

namespace GibbsLearner

variable {w out : ℕ}

/-- The unitary of round `k` for control bits `bits`: the template's untagged gates and the gates
whose control bit is `1`, in order. -/
def roundUnitary (L : GibbsLearner w out) (k : Fin L.R) (bits : Fin (L.cbits k) → Bool) :
    Matrix (Qubits (L.copies k * w + L.anc k)) (Qubits (L.copies k * w + L.anc k)) ℂ :=
  Circuit.unitary ((L.template k).filterMap fun g => if g.2.all bits then some g.1 else none)

/-- The number of copies of the unknown state consumed. -/
def copiesUsed (L : GibbsLearner w out) : ℕ :=
  ∑ k, L.copies k

/-- The running time: quantum gates, ancilla preparations and classical Boolean gates (the formula
of `QAlgorithms.CopyLearner.time`). -/
def time (L : GibbsLearner w out) : ℕ :=
  ∑ k, ((L.template k).length + L.anc k + (L.ctrl k).size) + L.outC.size

/-- The record of all outcomes of all rounds, concatenated via `finSigmaFinEquiv`. -/
def record (L : GibbsLearner w out) (z : (k : Fin L.R) → Qubits (L.copies k * w + L.anc k)) :
    Fin (∑ j, (L.copies j * w + L.anc j)) → Bool :=
  fun i => z (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2

/-- The record visible to round `k`: the outcomes of the rounds `< k`, the later bits `0`. -/
def recordBefore (L : GibbsLearner w out) (z : (k : Fin L.R) → Qubits (L.copies k * w + L.anc k))
    (k : Fin L.R) : Fin (∑ j, (L.copies j * w + L.anc j)) → Bool :=
  fun i => if (finSigmaFinEquiv.symm i).1 < k then z (finSigmaFinEquiv.symm i).1
    (finSigmaFinEquiv.symm i).2 else false

/-- The Born probability of outcome `z k` in round `k`, given the earlier outcomes. -/
noncomputable def roundProb (L : GibbsLearner w out) (ρ : Matrix (Qubits w) (Qubits w) ℂ)
    (z : (k : Fin L.R) → Qubits (L.copies k * w + L.anc k)) (k : Fin L.R) : ℝ :=
  let U := L.roundUnitary k ((L.ctrl k).eval (L.recordBefore z k))
  ((U * copiesInputDensity w (L.copies k) (L.anc k) ρ * Uᴴ) (z k) (z k)).re

/-- The probability that the output bits satisfy `E` when the learner runs on copies of `ρ`: the
sum over all outcome records of the chain-rule probability of the record times the indicator of
`E` at the output. -/
noncomputable def successProb (L : GibbsLearner w out) (ρ : Matrix (Qubits w) (Qubits w) ℂ)
    (E : (Fin out → Bool) → Prop) : ℝ :=
  ∑ z : (k : Fin L.R) → Qubits (L.copies k * w + L.anc k),
    (∏ k, L.roundProb ρ z k) * (open Classical in if E (L.outC.eval (L.record z)) then 1 else 0)

end GibbsLearner

/-- The dyadic number written by a block of `len + 1` bits: sign bit `y 0` (`true` = negative),
then the `len`-bit magnitude `m` (most significant bit first), value `±m/2^{wp}`. -/
noncomputable def blockValue (len wp : ℕ) (y : Fin (len + 1) → Bool) : ℝ :=
  (if y 0 then -1 else 1) * ((bitsToNat (fun j : Fin len => y j.succ) : ℕ) : ℝ) / 2 ^ wp

/-- The fixed decoder of a family of real estimates indexed by `ι` (enumerated by `e`): block
`e i` of the output bits, through `finProdFinEquiv`, is read by `blockValue len wp`. -/
noncomputable def decodeBlocks {ι : Type*} {M : ℕ} (e : ι ≃ Fin M) (len wp : ℕ)
    (x : Fin (M * (len + 1)) → Bool) : ι → ℝ :=
  fun i => blockValue len wp fun b => x (finProdFinEquiv (e i, b))

/-- The channel `Φ[σ] = tr_anc[U (σ ⊗ |0^a⟩⟨0^a|) U†]` implemented by a circuit `c` over
`{H, T, CNOT}` on `N` system qubits and `a` ancillas (the last `a` wires), followed by tracing
out the ancillas. -/
noncomputable def circuitChannel {N a : ℕ} (c : Circuit htcxGateSet (N + a))
    (σ : Matrix (Qubits N) (Qubits N) ℂ) : Matrix (Qubits N) (Qubits N) ℂ :=
  let U := c.unitary
  let σin : Matrix (Qubits (N + a)) (Qubits (N + a)) ℂ := Matrix.of fun y z =>
    if ∀ b : Fin a, y (Fin.natAdd N b) = false ∧ z (Fin.natAdd N b) = false then
      σ (fun j => y (Fin.castAdd a j)) (fun j => z (Fin.castAdd a j))
    else 0
  Matrix.of fun y z => ∑ e : Qubits a, (U * σin * Uᴴ) (Fin.append y e) (Fin.append z e)

/-- The circuit `c` acts only on the system qubits in `A` (and on its ancillas): every wire of
every gate is an ancilla or a qubit of `A`. -/
def ActsOnlyOn {N a : ℕ} (c : Circuit htcxGateSet (N + a)) (A : Finset (Fin N)) : Prop :=
  ∀ g ∈ c, ∀ b, ∀ h : (g.wires b : ℕ) < N, (⟨g.wires b, h⟩ : Fin N) ∈ A

end StationarityTest


