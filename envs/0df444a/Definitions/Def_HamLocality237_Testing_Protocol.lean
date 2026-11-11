-- Prove2me | Definitions.Def_HamLocality237_Testing_Protocol
-- name    : HamLocality237_Testing_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:49.178658+00:00
-- url     : https://prove2.me/theorems/eb126acf-52f3-4d89-bc8e-85f176a93970
-- title:
--   Adaptive forward-evolution experiment protocols
-- statement:
--   Fix $n$ qubits. An experiment prepares an arbitrary positive semidefinite trace-one matrix on the qubits and a nonempty finite ancillary space. It chooses a finite list of real query durations $t_j\ge0$ and arbitrary input-independent unitaries $V_j$. Its final unitary is
--
--   $$V_r(U_H(t_r)\otimes I)V_{r-1}\cdots V_1(U_H(t_1)\otimes I)V_0,\qquad U_H(t)=e^{-itH}.$$
--
--   Computational-basis measurement supplies a classical outcome. A protocol is a finite tree of such experiments, with an experiment's outcome selecting its successor and each leaf carrying a binary answer. The acceptance probability is the recursive sum of the Born probabilities times the child acceptance probabilities. True means local; false means far.
--
--   A transcript has probability equal to the product of its outcome probabilities, and its charged time is the sum of all query durations along it. Preparation, the unitaries, and measurement carry no charge. The testing predicate requires success at least $9/10$ on each entire promise set. The time-bound predicate for the goal restricts only positive-probability transcripts on promise inputs.
--
--   This model includes mixed states, arbitrary ancillas, interleaved unitaries, arbitrary nonnegative real times, and classical adaptivity. All tree data are fixed before the input Hamiltonian. Finite ancillary spaces are enumerated by $\operatorname{Fin}(w)$; an arbitrary finite space can be embedded in finitely many ancilla qubits without changing its output probabilities.
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Figure 1, p.3; §2.3, pp.9–10; Definition 2.1, p.10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Locality

open QAlgorithms
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

namespace HamLocality237.Testing

/-- Figure 1 and §2.3, p.9. All data are fixed independently of the oracle. -/
structure Experiment (n : ℕ) where
  workspaceSize : ℕ
  workspaceNonempty : 0 < workspaceSize
  initial : Matrix (Qubits n × Fin workspaceSize) (Qubits n × Fin workspaceSize) ℂ
  initial_density : QAlgorithms.IsDensityMatrix initial
  queries : ℕ
  duration : Fin queries → NNReal
  control : Fin (queries + 1) → Matrix.unitaryGroup (Qubits n × Fin workspaceSize) ℂ

abbrev Experiment.Outcome {n : ℕ} (E : Experiment n) := Qubits n × Fin E.workspaceSize

/-- §2.2, p.8: the actual matrix exponential. -/
def evolution {n : ℕ} (H : Operator n) (t : ℝ) : Operator n :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)

/-- Figure 1: V_r (U(t_r) ⊗ I) ... V_1 (U(t_1) ⊗ I) V_0. -/
def Experiment.unitary {n : ℕ} (E : Experiment n) (H : Operator n) :
    Matrix E.Outcome E.Outcome ℂ :=
  QAlgorithms.orderedProd (fun j : Fin E.queries =>
    (E.control j.succ : Matrix E.Outcome E.Outcome ℂ) *
      Matrix.kronecker (evolution H (E.duration j : ℝ))
        (1 : Matrix (Fin E.workspaceSize) (Fin E.workspaceSize) ℂ)) *
    (E.control 0 : Matrix E.Outcome E.Outcome ℂ)

/-- Real Born probability in the computational basis after the experiment. -/
def Experiment.probability {n : ℕ} (E : Experiment n) (H : Operator n)
    (z : E.Outcome) : ℝ :=
  let U := E.unitary H
  (U * E.initial * U.conjTranspose) z z |>.re

/-- Only oracle durations are charged. -/
def Experiment.time {n : ℕ} (E : Experiment n) : ℝ :=
  ∑ j, (E.duration j : ℝ)

/-- Finite adaptive tree, with arbitrary experiments at the nodes; true means k-local. -/
inductive Protocol (n : ℕ) where
  | halt : Bool → Protocol n
  | experiment (E : Experiment n) (next : E.Outcome → Protocol n) : Protocol n

/-- Recursive acceptance law, including arbitrary mixed preparations and classical adaptivity. -/
def Protocol.acceptProbability {n : ℕ} (A : Protocol n) (H : Operator n) : ℝ :=
  match A with
  | .halt b => if b then 1 else 0
  | .experiment E next => ∑ z : E.Outcome, E.probability H z * (next z).acceptProbability H

/-- A full measurement transcript ends at a leaf of the finite tree. -/
inductive Protocol.Transcript {n : ℕ} : Protocol n → Type where
  | halt (b : Bool) : Transcript (.halt b)
  | experiment {E : Experiment n} {next : E.Outcome → Protocol n}
      (z : E.Outcome) (rest : Transcript (next z)) : Transcript (.experiment E next)

def Protocol.Transcript.probability {n : ℕ} {A : Protocol n}
    (p : A.Transcript) (H : Operator n) : ℝ :=
  match p with
  | .halt _ => 1
  | .experiment (E := E) z rest => E.probability H z * rest.probability H

def Protocol.Transcript.time {n : ℕ} {A : Protocol n} (p : A.Transcript) : ℝ :=
  match p with
  | .halt _ => 0
  | .experiment (E := E) _ rest => E.time + rest.time

/-- §2.3 p.10 with the declared promise/reachable-transcript generalization. -/
def Protocol.HasPromiseTimeBound {n : ℕ} (A : Protocol n) (k : ℕ) (ε T : ℝ) : Prop :=
  ∀ H : Operator n, IsPromise k ε H → ∀ p : A.Transcript,
    0 < p.probability H → p.time ≤ T

/-- The global branch bound used in the simulation milestone. -/
def Protocol.HasBranchTimeBound {n : ℕ} (A : Protocol n) (T : ℝ) : Prop :=
  ∀ p : A.Transcript, p.time ≤ T

/-- Definition 2.1 p.10 and Corollary 4.2 p.24, success on both entire promise sets. -/
def Protocol.TestsLocality {n : ℕ} (A : Protocol n) (k : ℕ) (ε : ℝ) : Prop :=
  (∀ H : Operator n, IsInput H → IsKLocal k H → (9 / 10 : ℝ) ≤ A.acceptProbability H) ∧
  (∀ H : Operator n, IsInput H → ε < distanceFromLocality k H →
    (9 / 10 : ℝ) ≤ 1 - A.acceptProbability H)

end HamLocality237.Testing


