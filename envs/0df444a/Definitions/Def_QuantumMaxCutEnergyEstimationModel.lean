-- Prove2me | Definitions.Def_QuantumMaxCutEnergyEstimationModel
-- name    : QuantumMaxCutEnergyEstimationModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-31T23:27:45.572495+00:00
-- url     : https://prove2.me/theorems/9667c96f-5c01-484f-b845-cd688f3836f9
-- title:
--   Classical polynomial-time energy estimation for Quantum Max-Cut
-- statement:
--   A Quantum Max-Cut input is a finite graph with nonnegative rational edge weights. Its Hamiltonian is $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$, and $\mathrm{OPT}(G)$ is the largest expected energy over all normalized quantum states, including entangled states.
--
--   An algorithm is a classical numerical computation. It receives the graph and a uniformly random bit string of length $c(|\mathrm{enc}(G)|+1)^k$, where the natural-number constants $c,k$ are fixed by the algorithm, and returns a nonnegative rational estimate $v$. Setting $c=0$ includes deterministic algorithms. The polynomial-time predicate requires an explicit classical Turing-machine certificate for this input-to-number computation.
--
--   The approximation predicate at ratio $\alpha$ requires, for every input graph,
--
--   $$0\le v\le\mathrm{OPT}(G)\quad\text{for every random outcome},\qquad\mathbb E[v]\ge\alpha\,\mathrm{OPT}(G).$$
--
--   The expectation is the uniform finite average over the prescribed random bits. The guarantee concerns the optimal energy value. No preparation circuit or output quantum state is required. Empty graphs and zero edge weights are included.
--
--   **Formalization Note.** The optimum is defined as the real supremum of a finite-dimensional normalized-state energy functional. Rational numerators and denominators have self-delimiting binary encodings; graph order is unary. Random bits follow the self-delimiting graph encoding, and output rationals use the same numeric encoding.
-- source:
--   Peer-reviewed published sources: Anuj Apte, Eunou Lee, Kunal Marwaha, Ojas Parekh, and James Sud, Improved Algorithms for Quantum MaxCut via Partially Entangled Matchings, ESA 2025, Introduction (numerical approximation objective and QMC normalization), https://doi.org/10.4230/LIPIcs.ESA.2025.101 ; Sevag Gharibian and Ojas Parekh, Almost Optimal Classical Approximation Algorithms for a Quantum Generalization of Max-Cut, APPROX/RANDOM 2019, Introduction and Theorem 6, https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.31 . This formal model fixes rational output, finite fair randomness, and explicit bit complexity; implementing these is part of the proof obligation.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Computability.TuringMachine.Computable

/-!
Classical numerical approximation of the Quantum Max-Cut optimum.

An algorithm receives the encoded weighted graph and a polynomial-length
uniform random bit string, and returns a nonnegative rational number.
Every output is a valid lower estimate of the optimum; the approximation
ratio is guaranteed in expectation over the random bits.

Convention: h_ij = I - SWAP_ij = (I - XX - YY - ZZ) / 2.
-/

noncomputable section
open scoped BigOperators
namespace QuantumMaxCutEnergy

abbrev Basis (n : ℕ) := Fin n → Bool
abbrev Wave (n : ℕ) := Basis n → ℂ
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Weights (n : ℕ) := Edge n → ℚ≥0

structure Input where
  n : ℕ
  weights : Weights n

def squaredNorm {n : ℕ} (ψ : Wave n) : ℝ :=
  ∑ x, Complex.normSq (ψ x)

/-- The expectation of the QMC Hamiltonian on a graph-state amplitude vector. -/
def energy {n : ℕ} (w : Weights n) (ψ : Wave n) : ℝ :=
  ∑ e, (w e : ℝ) / 2 * ∑ x,
    Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2))

/-- The maximum QMC energy, expressed as a supremum over normalized states. -/
def optimum (G : Input) : ℝ :=
  sSup {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ}

/-- A binary natural prefixed by the unary length of its binary representation. -/
def encodeNumber (k : ℕ) : List Bool :=
  let bits := Computability.encodeNat k
  List.replicate bits.length true ++ [false] ++ bits

/-- Unary graph order followed by binary rational weights in endpoint order. -/
def encodeInput (G : Input) : List Bool :=
  List.replicate G.n true ++ [false] ++
    (List.finRange G.n).flatMap (fun i =>
      (List.finRange G.n).flatMap (fun j =>
        if hij : i < j then
          let q := G.weights ⟨(i, j), hij⟩
          encodeNumber q.num ++ encodeNumber q.den
        else []))

/-- The graph encoding is self-delimiting; the remaining bits are the random tape. -/
def encodeRequest (request : Input × List Bool) : List Bool :=
  encodeInput request.1 ++ request.2

def encodeValue (v : ℚ≥0) : List Bool :=
  encodeNumber v.num ++ encodeNumber v.den

/-- One classical numerical algorithm, with a fixed polynomial random-bit budget. -/
structure Algorithm where
  randomFactor : ℕ
  randomDegree : ℕ
  run : Input → List Bool → ℚ≥0

def randomBits (A : Algorithm) (G : Input) : ℕ :=
  A.randomFactor * ((encodeInput G).length + 1) ^ A.randomDegree

/-- A genuine classical polynomial-time certificate for numerical output. -/
def PolynomialTime (A : Algorithm) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeRequest encodeValue
    (fun request : Input × List Bool => A.run request.1 request.2))

/-- Each random outcome is a lower estimate of OPT; its uniform average has ratio α. -/
def ApproximationRatio (A : Algorithm) (α : ℝ) : Prop :=
  ∀ G : Input,
    (∀ r : Fin (randomBits A G) → Bool,
      (A.run G (List.ofFn r) : ℝ) ≤ optimum G) ∧
    α * optimum G ≤
      (∑ r : Fin (randomBits A G) → Bool, (A.run G (List.ofFn r) : ℝ)) /
        (Fintype.card (Fin (randomBits A G) → Bool) : ℝ)

end QuantumMaxCutEnergy


