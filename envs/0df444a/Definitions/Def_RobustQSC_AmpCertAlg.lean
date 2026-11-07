-- Prove2me | Definitions.Def_RobustQSC_AmpCertAlg
-- name    : RobustQSC_AmpCertAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:49:37.965465+00:00
-- url     : https://prove2.me/theorems/5ec6d17f-4563-4e88-8422-53f1e0a200a2
-- title:
--   Protocols with Definition 1 oracle access and single-qubit measurements
-- statement:
--   A protocol is a finite-depth decision tree whose nodes are:
--
--   1. an oracle query $(z,B)$ with $z\in\{0,1\}^n$, $B\in\{\mathrm{std},\mathrm{had}\}$, answered by the complex number $\langle z|\psi\rangle$ or $\langle z|H^{\otimes n}|\psi\rangle$ (Definition 1);
--   2. a uniformly random choice among $m\ge1$ values;
--   3. a measurement of one qubit of the lab state in an orthonormal basis $\{U|0\rangle,U|1\rangle\}$, $U\in U(2)$;
--   4. an output, accept or reject.
--
--   The tree defines, for each target $\psi$ and lab state $\rho$, the probability of each output: a measurement outcome $j$ maps $\rho$ to $P_j\rho P_j$, $P_j$ the projector $U|j\rangle\langle j|U^\dagger$ on that qubit, and a leaf contributes the trace of the state it receives. The definition also gives the step count (each query, coin and measurement costs one) and the shape predicate of Theorem 1's last sentence: along every run, zero or more measurements all in the $Z$ basis or all in the $X$ basis, followed by at most one further measurement in an arbitrary basis, after which nothing is measured.
--
--   This is the protocol class of Theorem 1: oracle access to a classical description of the target and single-qubit measurements on one copy of the lab state.
--
--   **Formalization Note** The oracle is the published `amplitudeOracle`. Classical computation between nodes is not charged. The basis choice may differ between runs (Protocol 1 samples it), so "all in the $X$-basis or all in the $Z$-basis" is read per run.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 1, p.3; Definition 1, pp.7–8; Protocol 1, p.6

import Definitions.Def_QAlgorithms_Defs_ComplexAmplitudePrograms
import Definitions.Def_QAlgorithms_Defs_Information

namespace RobustQSC

open QAlgorithms QAlgorithms.TwoBasisCertification

/-- The Hadamard gate `H` as an element of the unitary group `U(2)` (it is self-adjoint and
`H² = I`), the basis change of an `X`-basis measurement.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), Protocol 1, p.6 (measurement "in basis
B ∈ {X, Z}"). -/
noncomputable def hadamardU : Matrix.unitaryGroup Bool ℂ :=
  ⟨hadamard, by
    rw [Matrix.mem_unitaryGroup_iff']
    have hs : star hadamard = hadamard := by
      ext a b
      cases a <;> cases b <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]
    rw [hs, hadamard_mul_self]⟩

/-- A protocol with Definition-1 oracle access to a classical description of the target state
`|ψ⟩` and single-qubit measurement access to one copy of the lab state `ρ`: a tree whose nodes are

1. `query had z next`: ask the oracle of Definition 1 for `O_ψ(z, B)` (`had = false` is
   `B = std`, the amplitude `⟨z|ψ⟩`; `had = true` is `B = had`, the amplitude `⟨z|H^{⊗n}|ψ⟩`)
   and continue with the complex answer;
2. `sample m _ next`: a uniformly random choice among `m ≥ 1` values;
3. `measure q U next`: measure qubit `q` of the lab state in the orthonormal basis
   `{U|0⟩, U|1⟩}` and continue with the outcome bit;
4. `output accept` (`true` = accept).

Source: Coladangelo, Li, Slote, arXiv:2607.27184 (sha256 09d2692e…), Theorem 1, p.3 ("an efficient
protocol using single-qubit measurements … Given oracle access to a classical description of the
target state |ψ⟩ (via the model in Definition 1), and a single copy of an n-qubit mixed state ρ"),
Definition 1, pp.7–8, Protocol 1, p.6.

**Formalization Note.** Registers are `Qubits n = Fin n → Bool` (`false` = 0). The oracle is the
published `amplitudeOracle`. No gates and no ancillas act on the lab state; classical
post-processing between nodes is free (the tree may branch on any function of the answers). The
shape copies the published `QAlgorithms.SQCertAlg`, with its product-projector oracle replaced by
Definition 1's amplitude oracle. -/
inductive AmpCertAlg (n : ℕ) where
  | query (had : Bool) (z : Qubits n) (next : ℂ → AmpCertAlg n)
  | sample (m : ℕ) (hm : 0 < m) (next : Fin m → AmpCertAlg n)
  | measure (q : Fin n) (U : Matrix.unitaryGroup Bool ℂ) (next : Bool → AmpCertAlg n)
  | output (accept : Bool)

namespace AmpCertAlg

variable {n : ℕ}

/-- The projector `U|j⟩⟨j|U†` on qubit `q` (identity on the other qubits): outcome `j` of the
measurement of qubit `q` in the basis `{U|0⟩, U|1⟩}`. -/
noncomputable def outcomeProj (q : Fin n) (U : Matrix.unitaryGroup Bool ℂ) (j : Bool) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  qubitOp1 ((U : Matrix Bool Bool ℂ) * Matrix.single j j 1 * star (U : Matrix Bool Bool ℂ)) q

/-- The probability that the protocol outputs `a` (`true` = accept) when the target is `ψ` and the
lab state is `ρ`. The lab state is carried unnormalized along a branch (Lüders rule): outcome `j`
of `measure q U` maps `ρ` to `P_j ρ P_j`, `P_j = outcomeProj q U j`, and a leaf contributes the
trace of the state it receives, the probability of reaching it.

Source: Coladangelo, Li, Slote, arXiv:2607.27184 (sha256 09d2692e…), Theorem 1, p.3 ("Outputs
accept with probability …"). -/
noncomputable def outProb : AmpCertAlg n → EuclideanSpace ℂ (Qubits n) →
    Matrix (Qubits n) (Qubits n) ℂ → Bool → ℝ
  | output b, _, ρ, a => if b = a then ρ.trace.re else 0
  | query had z next, ψ, ρ, a => (next (amplitudeOracle ψ had z)).outProb ψ ρ a
  | sample m _ next, ψ, ρ, a => (m : ℝ)⁻¹ * ∑ i, (next i).outProb ψ ρ a
  | measure q U next, ψ, ρ, a => ∑ j : Bool,
      (next j).outProb ψ (outcomeProj q U j * ρ * outcomeProj q U j) a

/-- Every execution path makes at most `b` steps, each oracle query, coin and single-qubit
measurement costing one step ("efficient protocol", Theorem 1, p.3).

**Formalization Note.** Classical post-processing (computing the next node from the answers) is
not charged: the paper notes (§2.2, p.7) that its test "will generally require inefficient
classical post-processing". -/
def StepsAtMost : AmpCertAlg n → ℕ → Prop
  | output _, _ => True
  | query _ _ next, b => 1 ≤ b ∧ ∀ y, (next y).StepsAtMost (b - 1)
  | sample _ _ next, b => 1 ≤ b ∧ ∀ i, (next i).StepsAtMost (b - 1)
  | measure _ _ next, b => 1 ≤ b ∧ ∀ j, (next j).StepsAtMost (b - 1)

/-- The shape predicate with its state: `mode = none` before the first bulk measurement,
`some false` once the bulk is in the `Z` basis (`U = I`), `some true` once it is in the `X` basis
(`U = H`); `finalDone = true` after the one final measurement in an arbitrary basis. -/
def TwoBasisShapeAux : AmpCertAlg n → Option Bool → Bool → Prop
  | output _, _, _ => True
  | query _ _ next, m, d => ∀ y, (next y).TwoBasisShapeAux m d
  | sample _ _ next, m, d => ∀ i, (next i).TwoBasisShapeAux m d
  | measure _ U next, m, false =>
      (U = 1 ∧ m ≠ some true ∧ ∀ j, (next j).TwoBasisShapeAux (some false) false) ∨
      (U = hadamardU ∧ m ≠ some false ∧ ∀ j, (next j).TwoBasisShapeAux (some true) false) ∨
      (∀ j, (next j).TwoBasisShapeAux m true)
  | measure _ _ _, _, true => False

/-- Theorem 1's "Moreover" clause (p.3): along every execution path the single-qubit
measurements are first zero or more measurements all in the `Z` basis (`U = I`) or all in the
`X` basis (`U = H`), and then at most one further measurement in an arbitrary basis, after which
nothing is measured.

Source: Coladangelo, Li, Slote, arXiv:2607.27184 (sha256 09d2692e…), Theorem 1, p.3 ("Moreover,
the single-qubit measurements are either all in the X-basis or all in the Z-basis, except for one
final (non-Pauli) adaptive measurement").

**Formalization Note.** The basis choice may differ between execution paths (Protocol 1 samples
it, p.6); "all in the X-basis or all in the Z-basis" is read per run. -/
def TwoBasisShape (A : AmpCertAlg n) : Prop :=
  A.TwoBasisShapeAux none false

end AmpCertAlg

/-! ### Sanity tests -/

example {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (ρ : Matrix (Qubits n) (Qubits n) ℂ) :
    (AmpCertAlg.output true).outProb ψ ρ true = ρ.trace.re ∧
      (AmpCertAlg.output true).outProb ψ ρ false = 0 := by
  simp [AmpCertAlg.outProb]

example {n : ℕ} (next : Fin 1 → AmpCertAlg n) :
    ¬ (AmpCertAlg.sample 1 one_pos next).StepsAtMost 0 := by
  simp [AmpCertAlg.StepsAtMost]

/-- Two arbitrary measurements in a row violate the shape. -/
example (U V : Matrix.unitaryGroup Bool ℂ) (hU : U ≠ 1) (hU' : U ≠ hadamardU) :
    ¬ (AmpCertAlg.measure (0 : Fin 1) U fun _ =>
        AmpCertAlg.measure 0 V fun _ => AmpCertAlg.output true).TwoBasisShape := by
  simp [AmpCertAlg.TwoBasisShape, AmpCertAlg.TwoBasisShapeAux, hU, hU']

end RobustQSC


