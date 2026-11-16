-- Prove2me | Definitions.Def_TightQLB_Supplement_UnitaryAccess
-- name    : TightQLB_Supplement_UnitaryAccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:20:17.970672+00:00
-- url     : https://prove2.me/theorems/d25dd981-2693-4148-b4fa-c9faf973a454
-- title:
--   Haar-random unitary access: the Haar law on $U(N)$, queries to $U$, $U^\dagger$ and their controlled versions, and the score
-- statement:
--   With **Haar-random unitary access** the algorithm may apply a Haar-random unitary $U$ on $\mathbb C^N$, its inverse $U^\dagger$, and controlled versions of both, each one query, and the state scored is $|\phi\rangle=U|0^n\rangle$. An algorithm consists of an oracle-independent joint state $\rho_{AE}$ of the device register $A=(C\times\mathbb C^N)\times W$ and Eve's register $E$, $q+1$ oracle-independent CPTP rounds on $A$, one query in each of the $q$ slots, of a fixed kind among $U$, $U^\dagger$, $cU$, $cU^\dagger$, and a final POVM $\{M_z\}$. Its expected score is
--
--   $$
--   B(\mathcal A)=\mathbb E_U\sum_z\Pr[Z=z\mid U]\,N\,|\langle z|U|0^n\rangle|^2 .
--   $$
--
--   These objects state Theorems 5.25 and 6.12, which transfer the canonical-oracle lower bounds to unitary access.
--
--   **Formalization Note** The Haar law on $U(N)$ is any probability measure on matrices concentrated on unitaries and invariant under left multiplication by every unitary (`IsHaarUnitaryLaw`); on a compact group this is the unique Haar probability measure. The model is Kretschmer's, in the channel form of the base mission's experiment; a controlled query with control $|0\rangle$ is the identity, so fewer queries along a path are covered.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, p. 14 (PDF p. 17); §5.6, pp. 44–45 (PDF pp. 47–48)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Haar
open QAlgorithms MeasureTheory
open scoped ComplexOrder Matrix

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# Haar-random unitary access

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, p.14 (PDF p.17);
§5.6, pp.44–45 (PDF pp.47–48).

"With Haar-random unitary access, the algorithm may instead apply a Haar-random unitary `U` on
`C^N`, its inverse `U†`, and controlled versions of both, and the state scored is `|ϕ⟩ = U|0ⁿ⟩`.
Both forms of access are the models of Kretschmer [Kre21]."

**Formalization Note.**
* A unitary is a matrix `Qubits n → Qubits n → ℂ`. The Haar law on `U(N)` is characterized by
  `IsHaarUnitaryLaw μ`: a probability measure on matrices, concentrated on unitaries, and invariant
  under left multiplication by every unitary. A left-invariant probability on the compact group
  `U(N)` is its unique Haar probability measure, so a statement for every such `μ` is a statement
  about the Haar measure.
* An algorithm is Kretschmer's model in the channel form of `TightQLB.Experiment`: an
  oracle-independent density matrix on `A × E` with `A = (C × X) × W` (control qubit, the register
  `C^N` on which `U` acts, a finite workspace), `q + 1` oracle-independent CPTP rounds on `A`, and
  in slot `t` a query of the fixed kind `kind t ∈ {U, U†, cU, cU†}` (each one query), then a POVM.
  A controlled query whose control is `|0⟩` acts as the identity, so a path with fewer queries is
  covered. Nothing acts on `E`.
-/

/-- `μ` is the Haar probability measure on `U(N)`, `N = 2^n`: concentrated on unitaries and
invariant under left multiplication by every unitary. -/
def IsHaarUnitaryLaw {n : ℕ} (μ : Measure (Qubits n → Qubits n → ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ᵐ U ∂μ, (Matrix.of U : Matrix (Qubits n) (Qubits n) ℂ) ∈ Matrix.unitaryGroup (Qubits n) ℂ) ∧
    ∀ V ∈ Matrix.unitaryGroup (Qubits n) ℂ,
      μ.map (fun U : Qubits n → Qubits n → ℂ => fun i j => (V * Matrix.of U) i j) = μ

/-- The scored state `|ϕ⟩ = U|0ⁿ⟩` (§3.1, p.14, PDF p.17). -/
noncomputable def unitaryState {n : ℕ} (U : Qubits n → Qubits n → ℂ) :
    EuclideanSpace ℂ (Qubits n) :=
  act (Matrix.of U) (zeroKet n)

/-- The four kinds of query of unitary access: `U`, `U†`, controlled `U`, controlled `U†`. -/
inductive QueryKind
  | plain
  | inv
  | ctrlPlain
  | ctrlInv

/-- The query of kind `k` on the control qubit and the register `C^N`. -/
noncomputable def kindMatrix {n : ℕ} (U : Qubits n → Qubits n → ℂ) :
    QueryKind → Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ
  | .plain => Matrix.kronecker (1 : Matrix Bool Bool ℂ) (Matrix.of U)
  | .inv => Matrix.kronecker (1 : Matrix Bool Bool ℂ) (Matrix.of U)ᴴ
  | .ctrlPlain => ctrl (Matrix.of U)
  | .ctrlInv => ctrl (Matrix.of U)ᴴ

/-- An algorithm with Haar-random unitary access making `q` queries (with inverse and controlled
access), device workspace `W`, Eve register `E`. -/
structure UnitaryExperiment (n q : ℕ) (W E : Type) [Fintype W] [DecidableEq W] [Fintype E]
    [DecidableEq E] where
  /-- The oracle-independent joint initial state. -/
  ρ₀ : Matrix ((((Bool × Qubits n) × W)) × E) ((((Bool × Qubits n) × W)) × E) ℂ
  /-- It is a density matrix. -/
  ρ₀_density : PeresTerno.IsDensityMatrix ρ₀
  /-- The oracle-independent rounds. -/
  Φ : Fin (q + 1) → Matrix ((Bool × Qubits n) × W) ((Bool × Qubits n) × W) ℂ →
    Matrix ((Bool × Qubits n) × W) ((Bool × Qubits n) × W) ℂ
  /-- Each round is CPTP. -/
  Φ_cptp : ∀ t, AKNMixed.FQP.IsQuantumOperation (Φ t)
  /-- The kind of the query in each slot. -/
  kind : Fin q → QueryKind
  /-- The output POVM. -/
  M : Qubits n → Matrix ((Bool × Qubits n) × W) ((Bool × Qubits n) × W) ℂ
  /-- Positive semidefinite elements. -/
  M_psd : ∀ z, (M z).PosSemidef
  /-- Summing to the identity. -/
  M_sum : ∑ z, M z = 1

namespace UnitaryExperiment

variable {n q : ℕ} {W E : Type} [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]

/-- The query of slot `t` on `A × E`. -/
noncomputable def queryAt (A : UnitaryExperiment n q W E) (U : Qubits n → Qubits n → ℂ)
    (t : Fin q) : Matrix ((((Bool × Qubits n) × W)) × E) ((((Bool × Qubits n) × W)) × E) ℂ :=
  Matrix.kronecker (Matrix.kronecker (kindMatrix U (A.kind t)) (1 : Matrix W W ℂ))
    (1 : Matrix E E ℂ)

/-- The state of `A × E` after round `t`. -/
noncomputable def state (A : UnitaryExperiment n q W E) (U : Qubits n → Qubits n → ℂ) :
    Fin (q + 1) → Matrix ((((Bool × Qubits n) × W)) × E) ((((Bool × Qubits n) × W)) × E) ℂ :=
  Fin.induction (PeresTerno.ampliate (A.Φ 0) A.ρ₀)
    (fun t ρ => PeresTerno.ampliate (A.Φ t.succ) (A.queryAt U t * ρ * (A.queryAt U t)ᴴ))

/-- `Pr[Z = z | U]`. -/
noncomputable def outProb (A : UnitaryExperiment n q W E) (U : Qubits n → Qubits n → ℂ)
    (z : Qubits n) : ℝ :=
  (WildeQIT.partialTraceLeft
    (Matrix.kronecker (A.M z) (1 : Matrix E E ℂ) * A.state U (Fin.last q))).trace.re

/-- Eq. (12) for unitary access: `B(A) = E_U Σ_z Pr[Z = z | U] · N |⟨z|U|0ⁿ⟩|²`. -/
noncomputable def score (A : UnitaryExperiment n q W E) (μ : Measure (Qubits n → Qubits n → ℂ)) :
    ℝ :=
  ∫ U, ∑ z, A.outProb U z * ((2 : ℝ) ^ n * pOf (unitaryState U) z) ∂μ

end UnitaryExperiment

end TightQLB.Supplement


