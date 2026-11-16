-- Prove2me | Definitions.Def_IQPForrelation832_SingleQuery_Supplement_PhaseCircuits
-- name    : IQPForrelation832_SingleQuery_Supplement_PhaseCircuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:51:19.869973+00:00
-- url     : https://prove2.me/theorems/3a6b3a62-fd18-4bc3-a4d0-7e8efbd903dd
-- title:
--   Generic finite phase-query IQP circuits and parity vectors
-- statement:
--   Let $n,m\ge0$ be the oracle address length and register width. A middle block is an actual finite list of the shared gate applications and oracle calls. Each non-oracle gate must be a diagonal unitary; each oracle occurrence is a plain call on an ordered tuple of distinct wires. Different occurrences may overlap or repeat. The phase oracle is $O_x|a\rangle=x_a|a\rangle$ for $a\in\{0,1\}^n$. Starting in $|0^m\rangle$, apply $H^{\otimes m}$, the middle block, then $H^{\otimes m}$. Its acceptance probability is the unconditioned sum of Born probabilities over an arbitrary finite accepting set $F$.
--   $$
--   A(u)=\mathop{\triangle}_{t=1}^d\{\pi_t(u)\},\qquad
--   v_A(u)=2^{-m/2}D_{uu}\,\mathbf1_{A(u)=A}.
--   $$
--   The list of queried addresses is read from the actual wire embeddings. Odd multiplicities define the symmetric difference, and $D$ is the product of the non-oracle gates extracted from that same list. The pre-final-Hadamard state is computed from the full circuit. No decomposition, orthogonality, normalization or degree identity is a field of the model. This extends the published joint-oracle substrate to the single $n$-wire phase oracle of Section 5 and permits all finite middle blocks, including every polynomial-size IQP circuit.
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 13, Definition 3; pp. 24–25, Section 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Circuits

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open QAlgorithms

/-- Section 5 uses an n-wire SINGLE phase oracle, rather than the n+1-wire joint oracle. -/
abbrev PhaseMiddle (n m : ℕ) := OracleCircuit Set.univ (fun _ : Fin 1 => n) m

def PhaseIQP {n m : ℕ} (c : PhaseMiddle n m) : Prop :=
  ∀ s ∈ c, match s with
  | .gate g => DiagonalUnitary g.gate
  | .query _ adj control _ _ => adj = false ∧ control = none

noncomputable def phaseOracle {n : ℕ} (x : Cube n → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal (fun z => (x (cubeEquiv n z) : ℂ))

noncomputable def phaseBefore {n m : ℕ} (c : PhaseMiddle n m) (x : Cube n → ℝ) :
    EuclideanSpace ℂ (Qubits m) :=
  act (OracleCircuit.unitary c (fun _ => phaseOracle x)) (act (hadamardN m) (zeroKet m))

noncomputable def phaseRun {n m : ℕ} (c : PhaseMiddle n m) (x : Cube n → ℝ) :
    EuclideanSpace ℂ (Qubits m) := act (hadamardN m) (phaseBefore c x)

noncomputable def phaseBorn {n m : ℕ} (c : PhaseMiddle n m)
    (F : Finset (Qubits m)) (x : Cube n → ℝ) : ℝ := by
  classical
  exact probEvent (phaseRun c x) (fun z => z ∈ F)

/-- The input-independent part of the actual finite middle gate list. -/
def diagonalPart {n m : ℕ} (c : PhaseMiddle n m) : Circuit Set.univ m :=
  c.filterMap (fun s => match s with | .gate g => some g | .query _ _ _ _ _ => none)

/-- One address per actual occurrence, in list order. Repeated addresses are retained. -/
def queriedAddresses {n m : ℕ} (c : PhaseMiddle n m) (u : Qubits m) : List (Cube n) :=
  c.filterMap (fun s => match s with
    | .gate _ => none
    | .query _ _ _ w _ => some (cubeEquiv n (u ∘ w)))

/-- Symmetric difference of the queried singletons: only odd multiplicities survive. -/
noncomputable def paritySet {n m : ℕ} (c : PhaseMiddle n m) (u : Qubits m) : Finset (Cube n) := by
  classical
  exact Finset.univ.filter (fun a => (queriedAddresses c u).count a % 2 = 1)

/-- These are computed vectors, not assumed Fourier coefficients or state axioms. -/
noncomputable def parityVector {n m : ℕ} (c : PhaseMiddle n m) (A : Finset (Cube n)) :
    EuclideanSpace ℂ (Qubits m) := by
  classical
  exact WithLp.toLp 2 (fun u => if paritySet c u = A then
    ((Real.sqrt ((2 : ℝ)^m) : ℂ)⁻¹ * (diagonalPart c).unitary u u) else 0)

end IQPForrelation832.SingleQuery.Supplement


