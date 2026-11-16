-- Prove2me | Definitions.Def_QMultiMean_Supplement_PhaseCircuit
-- name    : QMultiMean_Supplement_PhaseCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:13:55.053567+00:00
-- url     : https://prove2.me/theorems/6c0c4143-abb5-4da5-b92f-cac0e5ecdbd7
-- title:
--   Oracle circuits and quantum estimators in the phase-oracle model ($U_{\mathbb P}$ and controlled $\mathcal P_X$)
-- statement:
--   A **phase-oracle circuit** acts on $r$ copies of the register pair $\mathcal H_\Omega\otimes\mathbb C^d$ and an ancilla $\mathbb C^{A+1}$, starting from a fixed computational-basis state. It applies unitary gates $G_0,\dots,G_T$ interleaved with $T$ oracle calls $O_1,\dots,O_T$, implementing
--   $$W=G_T\,O_T\cdots G_1\,O_1\,G_0 .$$
--   Each oracle call is one of:
--
--   1. the quantum experiment $U_{\mathbb P}$ or $U_{\mathbb P}^{-1}$ on the sample register $\mathcal H_\Omega$ of one copy;
--   2. the phase oracle $\mathcal P_X$ or $\mathcal P_X^{-1}$ on one copy $\mathcal H_\Omega\otimes\mathbb C^d$, controlled by the ancilla: it is applied when the ancilla's basis label lies in a prescribed set and acts as the identity otherwise.
--
--   The circuit counts its **quantum experiments** (calls of the first kind) and its **phase oracle queries** (calls of the second kind) separately. A **quantum estimator** in this model is such a circuit followed by a measurement of every register in the computational basis and a classical map from the outcome to $\mathbb R^d$. Its success probability for a set $S$ of outputs is the probability that the output lies in $S$.
--
--   This is the query model of Theorems 4.3–4.10: the circuit is fixed before the distribution $\mathbb P$, the random variable $X$ and the oracles, and its cost is the two query counts.
--
--   **Formalization Note** The paper gives no formal model; this mirrors the published binary-oracle `QMultiMean.Estimator`. Controlled calls of $\mathcal P_X$ are provided because the paper uses them (p.17, and Lemma 2.12); a qubit control in any basis reduces to an ancilla basis condition by the free gates. $U_{\mathbb P}$ is uncontrolled, as in Definition 2.5 and the base model. Gates are arbitrary unitaries (no gate count); adaptive classical control and intermediate measurements are absorbed by deferred measurement.
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, pp.7 and 15–17 (Definitions 2.5, 2.7; the access model of Section 4; controlled calls of P_X on p.17)

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable
import Definitions.Def_QMultiMean_Supplement_phaseOracle

set_option autoImplicit false

namespace QMultiMean.Supplement

open QMultiMean

/-- The four kinds of oracle call of the phase-oracle model of §4 (Cornelissen, Hamoudi, Jerbi,
arXiv:2111.09787v2, p.15; Definitions 2.5 and 2.7, p.7): a quantum experiment `U_P` or `U_P⁻¹`, and
a phase oracle query `P_X` or `P_X⁻¹`. -/
inductive PhaseCallKind where
  | U
  | Uinv
  | Ph
  | Phinv
  deriving DecidableEq

/-- The computational-basis labels of a phase-oracle circuit: `r` copies of the register pair
`H_Ω ⊗ ℂ^d` (a sample register and a coordinate register) and an ancilla `ℂ^{A+1}`. -/
abbrev PLabel (N d r A : ℕ) : Type :=
  (Fin r → Fin (N + 1) × Fin d) × Fin (A + 1)

/-- A **phase-oracle circuit** for the model of arXiv:2111.09787v2, §4 (p.15: `X` is accessed
through the quantum experiment `U_P` of Definition 2.5 and the phase oracle `P_X` of
Definition 2.7). It has `r` copies of the register pair `H_Ω ⊗ ℂ^d`, an ancilla `ℂ^{A+1}`, a fixed
initial basis state, `T` oracle calls, unitary gates `G₀, …, G_T`, and for each call `t < T` its kind
(`U_P`, `U_P⁻¹`, `P_X`, `P_X⁻¹`), the copy it acts on, and a control set of ancilla labels.

**Formalization Note.** The fields do not mention the probability mass function, the random
variable or the oracles: the gates, the initial state and the control sets may depend only on what
the structure is built from (in the theorems: `d`, the parameters and `N`). Free gates are arbitrary
unitaries (the query model). `U_P` and `U_P⁻¹` act on the sample register of a copy, uncontrolled, as
in Definition 2.5 and the published binary-oracle model `QMultiMean.OracleCircuit`. `P_X` and `P_X⁻¹`
act on a whole copy `H_Ω ⊗ ℂ^d` and are **controlled** by the ancilla: they apply when the ancilla
label lies in `ctrl t` and act as the identity otherwise (`ctrl t = univ` is an uncontrolled call;
any control qubit can be rotated into the ancilla's computational basis by the free gates). This is
the access the paper uses ("every controlled call of `P_X`", p.17; Lemma 2.12). The control set of a
`U_P` call is ignored. Adaptive classical control and intermediate measurements are absorbed by
deferred measurement into fresh registers. -/
structure PhaseCircuit (N d : ℕ) where
  /-- Number of copies of the register pair `H_Ω ⊗ ℂ^d`. -/
  r : ℕ
  /-- The ancilla is `ℂ^{A+1}`. -/
  A : ℕ
  /-- Number of oracle calls. -/
  T : ℕ
  /-- The initial computational-basis state. -/
  init : PLabel N d r A
  /-- The gates `G₀, …, G_T`. -/
  gate : Fin (T + 1) → Matrix (PLabel N d r A) (PLabel N d r A) ℂ
  /-- Every gate is unitary. -/
  gate_unitary : ∀ t, gate t ∈ Matrix.unitaryGroup (PLabel N d r A) ℂ
  /-- The kind of the `t`-th oracle call. -/
  kind : Fin T → PhaseCallKind
  /-- The copy of `H_Ω ⊗ ℂ^d` the `t`-th oracle call acts on. -/
  copy : Fin T → Fin r
  /-- The ancilla labels on which the `t`-th phase-oracle call is applied (control). -/
  ctrl : Fin T → Finset (Fin (A + 1))

open Classical in
/-- A matrix `M` on one register pair `H_Ω ⊗ ℂ^d`, acting on copy `i` of a circuit's space when the
ancilla label lies in `S`, and as the identity otherwise (and always as the identity on the other
copies and on the ancilla): the `S`-controlled version of `M` on copy `i`. -/
noncomputable def onCopyCtrl {N d r A : ℕ} (i : Fin r) (S : Finset (Fin (A + 1)))
    (M : Matrix (Fin (N + 1) × Fin d) (Fin (N + 1) × Fin d) ℂ) :
    Matrix (PLabel N d r A) (PLabel N d r A) ℂ :=
  fun p q =>
    if p.2 = q.2 ∧ (∀ j, j ≠ i → p.1 j = q.1 j) then
      (if p.2 ∈ S then M (p.1 i) (q.1 i)
        else (1 : Matrix (Fin (N + 1) × Fin d) (Fin (N + 1) × Fin d) ℂ) (p.1 i) (q.1 i))
    else 0

open Classical in
/-- A matrix on `H_Ω`, acting on the sample register of a pair `H_Ω ⊗ ℂ^d` (identity on `ℂ^d`). -/
noncomputable def onSampleP {N d : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Matrix (Fin (N + 1) × Fin d) (Fin (N + 1) × Fin d) ℂ :=
  fun p q => if p.2 = q.2 then U p.1 q.1 else 0

/-- The matrix of the `t`-th oracle call of a phase-oracle circuit, given the quantum experiment `U`
(on `H_Ω`) and the random variable `X` (whose phase oracle `P_X` is `phaseOracle X`): `U_P` or
`U_P⁻¹ = U_P†` on the sample register of the chosen copy (uncontrolled), or the controlled `P_X` or
`P_X⁻¹ = P_X†` on the chosen copy. -/
noncomputable def PhaseCircuit.call {N d : ℕ} (C : PhaseCircuit N d)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (X : Fin (N + 1) → Vec d) (t : Fin C.T) :
    Matrix (PLabel N d C.r C.A) (PLabel N d C.r C.A) ℂ :=
  match C.kind t with
  | .U => onCopyCtrl (C.copy t) Finset.univ (onSampleP U)
  | .Uinv => onCopyCtrl (C.copy t) Finset.univ (onSampleP (star U))
  | .Ph => onCopyCtrl (C.copy t) (C.ctrl t) (phaseOracle X)
  | .Phinv => onCopyCtrl (C.copy t) (C.ctrl t) (star (phaseOracle X))

/-- The operator a phase-oracle circuit implements with the quantum experiment `U` and the phase
oracle of `X`: `G_T · O_T ⋯ G_1 · O_1 · G_0`, where `O_t` is the `t`-th oracle call. -/
noncomputable def PhaseCircuit.implemented {N d : ℕ} (C : PhaseCircuit N d)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (X : Fin (N + 1) → Vec d) :
    Matrix (PLabel N d C.r C.A) (PLabel N d C.r C.A) ℂ :=
  ((List.finRange C.T).map (fun t => C.gate t.succ * C.call U X t)).reverse.prod * C.gate 0

open Classical in
/-- The number of quantum experiments (calls to `U_P` or `U_P⁻¹`) of a phase-oracle circuit. -/
noncomputable def PhaseCircuit.numU {N d : ℕ} (C : PhaseCircuit N d) : ℕ :=
  (Finset.univ.filter (fun t => C.kind t = .U ∨ C.kind t = .Uinv)).card

open Classical in
/-- The number of phase oracle queries (calls to `P_X` or `P_X⁻¹`, controlled or not) of a
phase-oracle circuit. -/
noncomputable def PhaseCircuit.numPh {N d : ℕ} (C : PhaseCircuit N d) : ℕ :=
  (Finset.univ.filter (fun t => C.kind t = .Ph ∨ C.kind t = .Phinv)).card

/-- A **quantum estimator in the phase-oracle model** with outputs in `Out`: a phase-oracle circuit
followed by a measurement of every register in the computational basis and a classical output map
from the measured label to `Out`.

**Formalization Note.** This is the reading of the paper's informal "quantum algorithm" /
"estimator" of §4 (arXiv:2111.09787v2, pp.15–27), mirroring the published binary-oracle
`QMultiMean.Estimator`. The output map, like the gates, does not see the probability mass function,
the random variable or the oracles. -/
structure PhaseEstimator (N d : ℕ) (Out : Type) extends PhaseCircuit N d where
  /-- The classical output computed from the measured label. -/
  out : PLabel N d r A → Out

open Classical in
/-- The probability that a phase-oracle estimator, run with the quantum experiment `U` and the phase
oracle of `X` from its initial basis state, outputs an element of `S`: the sum of `|⟨ℓ| W |init⟩|²`
over the labels `ℓ` whose output lies in `S`, where `W` is the implemented operator. -/
noncomputable def PhaseEstimator.successProb {N d : ℕ} {Out : Type} (M : PhaseEstimator N d Out)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (X : Fin (N + 1) → Vec d) (S : Set Out) : ℝ :=
  ∑ ℓ : PLabel N d M.r M.A,
    if M.out ℓ ∈ S then
      Complex.normSq (M.toPhaseCircuit.implemented U X ℓ M.init)
    else 0

end QMultiMean.Supplement


