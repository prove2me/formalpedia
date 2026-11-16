-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_SpaceBoundedAlg
-- name    : SelectiveDPT_Supplement_SpaceBoundedAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:27:57.318952+00:00
-- url     : https://prove2.me/theorems/fcbd9f2d-777f-4460-bbeb-0265b767e1e7
-- title:
--   General space-bounded quantum query algorithms with intermediate measurements
-- statement:
--   A **$T$-layer algorithm of the general quantum query model** (§2.3, model 1) on inputs $x \in \mathbb Z_d^{\iota}$ with outputs in a set $Z$ works on a register with a finite basis $P$; the space bound $S$ is $|P| \le 2^S$. It starts in an input-independent density matrix $\rho_0$ on $P$, and layer $L_t$ ($t = 1, \dots, T$):
--   1. applies the phase oracle of $x$: a basis state $z \in P$ that queries index $i$ with phase $p$ is multiplied by $\omega_d^{p x_i}$ (states that make no query are unchanged);
--   2. applies an input-independent quantum instrument $\{\Phi_{t,o}\}_o$ from $P$ to $P$ (finitely many Kraus operators per outcome $o$, summing to a trace-preserving map);
--   3. on outcome $o$ writes the output $\mathrm{out}_t(o) \in Z$ to a write-only output tape, or writes nothing.
--
--   For an outcome sequence $s = (s_1, \dots, s_T)$ the unnormalized final state is $\Phi_{T,s_T}(O_x \cdots \Phi_{1,s_1}(O_x\rho_0 O_x^\dagger) \cdots O_x^\dagger)$; its trace is the probability of $s$, and the tape holds the outputs written along $s$, in order. The success probability for a predicate on the tape is the total probability of the outcome sequences whose tape satisfies it. Time is the number of layers $T$.
--
--   This is the model of §2.3 in which outputs can be produced at input-dependent times, with the output order depending on the input; it is used by the time-space tradeoff of Theorem 4.16.
--
--   **Formalization Note** Every layer of §2.3 (fresh ancillas in $|0\rangle$, a unitary $U_t$, a standard-basis measurement of a flag and, on flag $1$, of an output register that is discarded and read as an output pair, and discarding of qubits) is a finite Kraus instrument from the passed register to the next one, and the query register is a labelling of the basis of the passed register; registers of different layers are embedded in one register of the largest dimension, and the start state $|0\rangle$ is generalized to any input-independent state. The instrument is the published `QAlgorithms.CopyMeasurements.QuantumInstrument`.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.3, p.11 (general quantum query model, Fig. 1); §2.2, p.9 (phase oracle)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
import Definitions.Def_SelectiveDPT_phaseOracle

open scoped Matrix

namespace SelectiveDPT.Supplement

open QAlgorithms QAlgorithms.CopyMeasurements

/-- A `T`-layer algorithm of the **general quantum query model** with intermediate measurements
(arXiv:2609.26678, §2.3, p.11, model 1; Fig. 1). The register passed between consecutive layers
has basis `P`; its size `|P| ≤ 2^S` is the space bound `S` (stated where the model is used).
Layer `L_t` (`t = 0, …, T−1`):
1. applies the phase oracle `O` of the input to the passed register: a basis state `z ∈ P`
   queries the index and phase `query t z = (i, p)` and is multiplied by `ω_d^{p·x_i}`
   (`query t z = none`: no phase);
2. applies the input-independent quantum instrument `layer t` with outcomes `Fin K` (this covers
   adding ancillas in `|0⟩`, the unitary `U_t`, the standard-basis measurement of the flag and,
   on flag `1`, of the output register, and discarding qubits);
3. writes `out t o` to the write-only output tape when the outcome is `o`
   (`none`: no output in this layer).
The algorithm starts in the input-independent state `init`. Time is the number of layers `T`.

**Formalization Note.** Every layer of §2.3's model (oracle, fresh ancillas, a unitary, a flag
measurement and, on outcome `1`, the measurement and discarding of an output register read as an
output pair) is an instance: the measurement after `U_t` together with the discarding of
qubits is a finite Kraus instrument from the passed register to the next one, and the query
register `(i, p)` is a labelling of the basis of the passed register. Registers of different
layers are embedded into one register `P` of the largest dimension; the start state `|0⟩` is
generalized to any input-independent density matrix. The instrument is the published
`QAlgorithms.CopyMeasurements.QuantumInstrument`. -/
structure SpaceBoundedAlg (ι P Z : Type*) [Fintype P] [DecidableEq P] (d T : ℕ) where
  /-- The input-independent start state on the passed register. -/
  init : Matrix P P ℂ
  /-- It is a density matrix. -/
  init_density : IsDensityMatrix init
  /-- The query made by each basis state of the passed register in layer `t`. -/
  query : Fin T → P → Option (ι × ZMod d)
  /-- The number of measurement outcomes of a layer. -/
  K : ℕ
  /-- The input-independent instrument of layer `t` (after the query). -/
  layer : Fin T → QuantumInstrument P (Fin K)
  /-- The output pair written in layer `t` on outcome `o`, if any. -/
  out : Fin T → Fin K → Option Z

namespace SpaceBoundedAlg

variable {ι P Z : Type*} [Fintype P] [DecidableEq P] {d T : ℕ}

/-- The phase oracle of the input `x : ι → Z_d` in layer `t`, a diagonal unitary on the passed
register (arXiv:2609.26678, §2.2, p.9: `O|i, p, w⟩|x⟩ = ω_d^{p x_i}|i, p, w⟩|x⟩`). -/
noncomputable def oracle (A : SpaceBoundedAlg ι P Z d T) (x : ι → ZMod d) (t : Fin T) :
    Matrix P P ℂ :=
  Matrix.diagonal fun z =>
    match A.query t z with
    | some q => rootPow d (q.2 * x q.1)
    | none => 1

/-- The unnormalized state after all `T` layers on input `x` when layer `t` has outcome `s t`:
`Φ_{T−1, s_{T−1}}(O ⋯ Φ_{0, s_0}(O ρ_init O†) ⋯ O†)`. Its trace is the probability of the outcome
sequence `s`. -/
noncomputable def runState (A : SpaceBoundedAlg ι P Z d T) (x : ι → ZMod d) (s : Fin T → Fin A.K) :
    Matrix P P ℂ :=
  (List.finRange T).foldl
    (fun ρ t => instrumentBranch (A.layer t) (s t) (A.oracle x t * ρ * (A.oracle x t)ᴴ)) A.init

/-- The list of output pairs written on the output tape, in order, for the outcome sequence `s`. -/
def written (A : SpaceBoundedAlg ι P Z d T) (s : Fin T → Fin A.K) : List Z :=
  (List.finRange T).filterMap fun t => A.out t (s t)

/-- The probability that on input `x` the written output list satisfies `good`. -/
noncomputable def succProb (A : SpaceBoundedAlg ι P Z d T) (x : ι → ZMod d) (good : List Z → Prop) :
    ℝ := by
  classical
  exact ∑ s : Fin T → Fin A.K, if good (A.written s) then (A.runState x s).trace.re else 0

end SpaceBoundedAlg

end SelectiveDPT.Supplement


