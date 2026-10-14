-- Prove2me | Definitions.Def_threshold_theorem_noise_model
-- name    : threshold_theorem_noise_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T00:58:06.17139+00:00
-- url     : https://prove2.me/theorems/f41ce754-f398-4525-8e43-fde1cb86418c
-- title:
--   Noisy layered quantum circuits with independent stochastic faults
-- statement:
--   This definition file fixes the circuit and noise model in which every statement of the mission is phrased.
--
--   **Registers and states.** A register of qubits is labelled by a finite type $Q$; its states are $2^{|Q|}\times 2^{|Q|}$ complex density matrices indexed by bit strings $x : Q \to \{0,1\}$. Every circuit starts in $|0\cdots0\rangle\langle 0\cdots 0|$.
--
--   **Operations.** The elementary operations are
--   1. the gates $H=\tfrac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\mathrm{diag}(1,e^{i\pi/4})$ and $\mathrm{CNOT}:|a,b\rangle\mapsto|a,a\oplus b\rangle$;
--   2. **preparation** of one qubit in $|0\rangle$, i.e. the reset channel with Kraus operators $|0\rangle\langle0|$ and $|0\rangle\langle1|$ (available at any time, providing fresh qubits);
--   3. a single-qubit **wait** (identity) step.
--
--   A **location** is one operation applied to an ordered tuple of distinct qubits. A **layer** (time step) is a list of locations whose supports partition the register: every qubit is touched by exactly one location, idle qubits carrying an explicit wait. A **circuit** is a list of layers, and its **size** $|C|$ is its total number of locations, waits included.
--
--   **Noise.** A noise model with rate at most $p$ assigns to location $j$ of layer $t$ a probability $q_{t,j}\in[0,p]$ and an arbitrary quantum channel $\mathcal E_{t,j}$ (a CPTP map given by Kraus operators $\{K_i\}$ with $\sum_i K_i^\dagger K_i = 1$) on the qubits of that location. Faults are independent: the noisy location acts by
--   $$\rho\;\mapsto\;(1-q_{t,j})\,\mathcal U_{t,j}(\rho)+q_{t,j}\,\mathcal E_{t,j}(\rho),$$
--   where $\mathcal U_{t,j}$ is its ideal action. Running all locations in this way gives the noisy final state; running them ideally gives the ideal final state.
--
--   **Outputs.** Measuring every qubit in the computational basis gives the outcome distribution $x\mapsto\langle x|\rho|x\rangle$. For a physical register of $n$ blocks of $b$ qubits (qubits labelled by $\mathrm{Fin}\,n\times\mathrm{Fin}\,b$), a decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ turns each block's outcome into one logical bit; the decoded distribution is the push-forward of the physical outcome distribution. Distributions are compared in total variation distance $\tfrac12\sum_y|P(y)-P'(y)|$.
--
--   This is the "hardware whose components fail with probability at most $p$" of the threshold theorem, made precise as independent stochastic noise with adversarial fault channels.
--
--   **Formalization Note** Kraus families are Lean lists of matrices indexed by `Fin k → Fin 2`; `liftOp` embeds a $k$-qubit operator into the register. Ideal operations need no trace-preservation proof inside the file; the fault channels carry one.
-- source:
--   Wikipedia, "Threshold theorem" (revision oldid=1360742213, https://en.wikipedia.org/w/index.php?title=Threshold_theorem&oldid=1360742213), section "Explanation"; the boxed statement is quoted there from M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, 10th anniversary ed., Cambridge University Press, p. 481.

import Mathlib

/-!
# Noisy quantum circuits with independent stochastic faults

A self-contained model of layered quantum circuits over the gate set `{H, T, CNOT}`
together with qubit (re)preparation in `|0⟩` and explicit idle ("wait") steps, and of
hardware in which every component (gate, preparation or wait) independently fails with
some probability at most `p`, a failed component applying an arbitrary
(adversarially chosen) quantum channel to the qubits it acts on.
-/

open Matrix

namespace ThresholdTheorem

/-- Complex matrices on the `2 ^ k`-dimensional state space of `k` qubits, indexed by
computational basis strings `Fin k → Fin 2`. -/
abbrev QMat (k : ℕ) := Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ

/-- Operators on the state space of a register of qubits labelled by `Q`. -/
abbrev Op (Q : Type*) := Matrix (Q → Fin 2) (Q → Fin 2) ℂ

/-- A quantum channel (completely positive trace-preserving map) on `k` qubits, given by
a finite list of Kraus operators `K` with `∑ Kᴴ K = 1`. -/
structure Channel (k : ℕ) where
  /-- The Kraus operators. -/
  kraus : List (QMat k)
  /-- Trace preservation. -/
  trace_preserving : (kraus.map fun K => Kᴴ * K).sum = 1

/-- The elementary gates: Hadamard, the `π/8` gate `T = diag(1, e^{iπ/4})`, and the
controlled-NOT. -/
inductive Gate
  | H
  | T
  | CNOT
  deriving DecidableEq

/-- Number of qubits a gate acts on. -/
def Gate.arity : Gate → ℕ
  | .H => 1
  | .T => 1
  | .CNOT => 2

/-- The Hadamard matrix `H = (1/√2) [[1, 1], [1, -1]]`. -/
noncomputable def hadamardMat : QMat 1 :=
  fun x y => ((-1 : ℂ) ^ ((x 0).val * (y 0).val)) / (Real.sqrt 2 : ℂ)

/-- The `π/8` gate `T = diag(1, e^{iπ/4})`. -/
noncomputable def tMat : QMat 1 :=
  fun x y => if x = y then (if x 0 = 1 then Complex.exp (Real.pi / 4 * Complex.I) else 1) else 0

/-- The controlled-NOT matrix, with qubit `0` the control and qubit `1` the target:
`|a, b⟩ ↦ |a, b + a⟩`. -/
noncomputable def cnotMat : QMat 2 :=
  fun x y => if x 0 = y 0 ∧ x 1 = y 1 + y 0 then 1 else 0

/-- The unitary matrix of a gate in the computational basis. -/
noncomputable def Gate.unitary : (g : Gate) → QMat g.arity
  | .H => hadamardMat
  | .T => tMat
  | .CNOT => cnotMat

/-- The elementary operations ("components") of a circuit: a gate, the (re)preparation
of a single qubit in the state `|0⟩`, or a single-qubit idle step. -/
inductive Operation
  | gate (g : Gate)
  | prep
  | wait
  deriving DecidableEq

/-- Number of qubits an operation acts on. -/
def Operation.arity : Operation → ℕ
  | .gate g => g.arity
  | .prep => 1
  | .wait => 1

/-- The single-qubit operator `|0⟩⟨i|`. -/
noncomputable def resetKraus (i : Fin 2) : QMat 1 :=
  fun x y => if x 0 = 0 ∧ y 0 = i then 1 else 0

/-- Kraus operators of the ideal (noiseless) action of an operation: the gate unitary,
the reset channel `ρ ↦ |0⟩⟨0|ρ|0⟩⟨0| + |0⟩⟨1|ρ|1⟩⟨0|`, or the identity. -/
noncomputable def Operation.idealKraus : (o : Operation) → List (QMat o.arity)
  | .gate g => [g.unitary]
  | .prep => [resetKraus 0, resetKraus 1]
  | .wait => [1]

/-- A location of a circuit: an operation together with the (distinct) qubits it acts
on, in order. -/
structure Location (Q : Type*) where
  /-- The operation performed. -/
  op : Operation
  /-- The qubits acted on; `support i` plays the role of the `i`-th qubit of `op`. -/
  support : Fin op.arity ↪ Q

/-- One time step of a circuit: a list of locations acting on pairwise disjoint sets of
qubits and covering every qubit exactly once (idle qubits carry an explicit `wait`). -/
structure Layer (Q : Type*) [DecidableEq Q] where
  /-- The locations of this time step. -/
  locs : List (Location Q)
  /-- Every qubit is acted on by exactly one location of the layer. -/
  partition : ∀ q : Q, (locs.flatMap fun ℓ => List.ofFn ℓ.support).count q = 1

/-- A layered quantum circuit on the qubits `Q`: its list of time steps. -/
abbrev Circuit (Q : Type*) [DecidableEq Q] := List (Layer Q)

/-- The size of a circuit: its total number of locations (gates, preparations and idle
steps). Since every qubit is covered in every layer, this is at least
`(number of qubits) * (depth)`, with equality when all gates are single-qubit. -/
def Circuit.size {Q : Type*} [DecidableEq Q] (C : Circuit Q) : ℕ :=
  (C.map fun L => L.locs.length).sum

open Classical in
/-- The operator on the register `Q` acting as `A` on the qubits `s 0, …, s (k-1)` and
as the identity on all other qubits. -/
noncomputable def liftOp {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (A : QMat k) : Op Q :=
  fun x y => if ∀ q, q ∉ Set.range s → x q = y q then A (x ∘ s) (y ∘ s) else 0

/-- Applying the channel with Kraus operators `K`, acting on the qubits `s`, to the
density matrix `ρ`: `ρ ↦ ∑ (K ⊗ 1) ρ (K ⊗ 1)ᴴ`. -/
noncomputable def applyKraus {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q) (K : List (QMat k))
    (ρ : Op Q) : Op Q :=
  (K.map fun A => liftOp s A * ρ * (liftOp s A)ᴴ).sum

open Classical in
/-- The initial state `|0…0⟩⟨0…0|` of the register. -/
noncomputable def initState (Q : Type*) : Op Q :=
  fun x y => if x = 0 ∧ y = 0 then 1 else 0

/-- Noiseless execution of one layer. -/
noncomputable def idealLayer {Q : Type*} [Fintype Q] [DecidableEq Q] (L : Layer Q) (ρ : Op Q) : Op Q :=
  L.locs.foldl (fun σ ℓ => applyKraus ℓ.support ℓ.op.idealKraus σ) ρ

/-- The final state of the noiseless execution of a circuit started in `|0…0⟩`. -/
noncomputable def idealState {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q) : Op Q :=
  C.foldl (fun σ L => idealLayer L σ) (initState Q)

/-- An independent stochastic noise model with fault rate at most `p`. The location
number `j` of layer number `t` (both counted from `0`) is faulty with probability
`prob t j ∈ [0, p]`, independently of all other locations; a faulty location applies,
instead of its ideal operation, the arbitrary channel `fault t j k` on its `k` qubits. -/
structure NoiseModel (p : ℝ) where
  /-- Fault probability of each location. -/
  prob : ℕ → ℕ → ℝ
  /-- The channel applied by each location when it is faulty (for each possible arity). -/
  fault : ℕ → ℕ → (k : ℕ) → Channel k
  prob_nonneg : ∀ t j, 0 ≤ prob t j
  prob_le : ∀ t j, prob t j ≤ p

/-- Noisy execution of layer number `t`: location `j` applies the channel
`(1 - q) · (ideal operation) + q · (fault channel)` with `q = prob t j`. -/
noncomputable def noisyLayer {Q : Type*} [Fintype Q] [DecidableEq Q] {p : ℝ} (N : NoiseModel p) (t : ℕ)
    (L : Layer Q) (ρ : Op Q) : Op Q :=
  L.locs.zipIdx.foldl
    (fun σ ℓj =>
      (1 - N.prob t ℓj.2) • applyKraus ℓj.1.support ℓj.1.op.idealKraus σ +
        N.prob t ℓj.2 • applyKraus ℓj.1.support (N.fault t ℓj.2 ℓj.1.op.arity).kraus σ)
    ρ

/-- The final state of the noisy execution of a circuit started in `|0…0⟩`. -/
noncomputable def noisyState {Q : Type*} [Fintype Q] [DecidableEq Q] {p : ℝ} (N : NoiseModel p)
    (C : Circuit Q) : Op Q :=
  C.zipIdx.foldl (fun σ Lt => noisyLayer N Lt.2 Lt.1 σ) (initState Q)

/-- The outcome distribution of measuring every qubit of the state `ρ` in the
computational basis: `x ↦ ⟨x|ρ|x⟩`. -/
noncomputable def outDist {Q : Type*} (ρ : Op Q) : (Q → Fin 2) → ℝ :=
  fun x => (ρ x x).re

open Classical in
/-- Blockwise classical decoding. The physical qubits are arranged in `n` blocks of `b`
qubits; each block's measured bit string is decoded to one logical bit by `dec`. This is
the push-forward of the physical outcome distribution `P` along that decoding map. -/
noncomputable def decodeDist {n b : ℕ} (dec : (Fin b → Fin 2) → Fin 2)
    (P : (Fin n × Fin b → Fin 2) → ℝ) : (Fin n → Fin 2) → ℝ :=
  fun y => ∑ x ∈ Finset.univ.filter (fun x : Fin n × Fin b → Fin 2 =>
    (fun i => dec (fun j => x (i, j))) = y), P x

/-- Total variation distance `½ ∑ |P y - P' y|` of two functions on a finite type. -/
noncomputable def tvDist {α : Type*} [Fintype α] (P P' : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |P y - P' y|

end ThresholdTheorem


