-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
-- name    : QAlgorithms_Papers_Independent_Information100_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:35:44.645729+00:00
-- url     : https://prove2.me/theorems/e0d8628a-40c3-49e0-89c2-5ce884c0f7a2
-- title:
--   Definitions for Geometric Aspects of Entanglement
-- statement:
--   The objects the formalized statements of *Geometric Aspects of Entanglement* (arXiv:2610.03446) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ket`: PDF p.3: an M-qubit ket in the frozen, most-significant-wire-first register.
--   - `Direction`: PDF p.3: real three-dimensional Euclidean space for Pauli directions.
--   - `directionDomain`: PDF p.3, Eq.(18): independently chosen unit directions, including the empty family.
--   - `pauli`: PDF p.3: Pauli components in X,Y,Z order, using the frozen matrices.
--   - `localPauli`: PDF p.3: the indicated Pauli on one wire, identity on all other wires.
--   - `directionalPauli`: PDF p.3: sigma_v on wire q is the real directional linear combination.
--   - `bloch`: PDF p.3, Eq.(19): the real Bloch expectations, without a unit-norm restriction.
--   - `fsForm`: PDF p.2, Eq.(7): the projective Hermitian form on ambient tangent vectors.
--   - `orbitTangent`: PDF p.3, Eqs.(14)-(15): the actual local-rotation tangent, with no factor 1/2.
--   - `orbitMetric`: PDF p.3, Eq.(16): pull back the Fubini-Study form on the local tangents.
--   - `traceObjective`: PDF p.3, Eq.(18): real trace of the geometric pullback.
--   - `entanglementDistance`: PDF p.3, Eq.(18): ED is defined geometrically, not by its later closed formula.
--   - `fsSquared`: PDF p.2, Eq.(8), p.7 note [46]: squared chordal Fubini-Study distance.
--   - `distanceObjective`: PDF p.4, Eqs.(23)-(24): sum of distances to the directional Pauli conjugates.
--   - `localED`: PDF p.3, Eq.(22): the local contribution, defined for the possibly zero Bloch vector.
--   - `FullySeparable`: PDF pp.2,4: pure full separability, allowing a unit global phase and the empty product.
--   - `appendKet`: PDF pp.4-5, Eq.(34): tensor product reindexed onto the concatenated wire register.
--   - `appendDirections`: PDF p.4, Eq.(33): concatenate the independent directions of two factors.
--   - `concurrence`: PDF p.5, Eq.(36): concurrence from the spin flip Y tensor Y and conjugation.
--   - `reducedFirst`: PDF p.5: reduce the actual pure density to its first qubit, tracing out the second.
--   - `entropyOfEntanglement`: PDF p.5, Eq.(40): entropy from the reduced density, in natural-log physical units.
--   - `entropyProfile`: PDF p.5, Eqs.(40)-(41): scalar entropy profile on ED in [0,2].
--   - `threeQubitFamily`: PDF p.5, Eq.(42): the four displayed amplitudes, including the negative |111> term.
--   - `examplePair`: PDF p.5, paragraph after Eq.(43): the two-qubit factor at phi=0.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, https://arxiv.org/abs/2610.03446v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-! Statements from *Geometric Aspects of Entanglement*, arXiv:2610.03446v1.
Only pure qubit states are considered. Property iii is deferred: its printed
outcome-by-outcome monotonicity argument is false (see the unit's HARD.md).
All new definitions are paper-local; the accepted library is unchanged. -/

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.3: an M-qubit ket in the frozen, most-significant-wire-first register. -/
abbrev Ket (M : ℕ) := EuclideanSpace ℂ (Qubits M)

/-- PDF p.3: real three-dimensional Euclidean space for Pauli directions. -/
abbrev Direction := EuclideanSpace ℝ (Fin 3)

/-- PDF p.3, Eq.(18): independently chosen unit directions, including the empty family. -/
def directionDomain (M : ℕ) : Set (Fin M → Direction) := {v | ∀ q, ‖v q‖ = 1}

/-- PDF p.3: Pauli components in X,Y,Z order, using the frozen matrices. -/
def pauli (a : Fin 3) : Matrix Bool Bool ℂ := ![pauliX, pauliY, pauliZ] a

/-- PDF p.3: the indicated Pauli on one wire, identity on all other wires. -/
noncomputable def localPauli {M : ℕ} (q : Fin M) (a : Fin 3) :
    Matrix (Qubits M) (Qubits M) ℂ :=
  kronAll (fun j => if j = q then pauli a else 1)

/-- PDF p.3: sigma_v on wire q is the real directional linear combination. -/
noncomputable def directionalPauli {M : ℕ} (q : Fin M) (v : Direction) :
    Matrix (Qubits M) (Qubits M) ℂ :=
  ∑ a, (v a : ℂ) • localPauli q a

/-- PDF p.3, Eq.(19): the real Bloch expectations, without a unit-norm restriction. -/
noncomputable def bloch {M : ℕ} (psi : Ket M) (q : Fin M) : Direction :=
  WithLp.toLp 2 (fun a => (inner ℂ psi (act (localPauli q a) psi)).re)

/-- PDF p.2, Eq.(7): the projective Hermitian form on ambient tangent vectors. -/
noncomputable def fsForm {M : ℕ} (psi a b : Ket M) : ℂ :=
  inner ℂ a b - inner ℂ a psi * inner ℂ psi b

/-- PDF p.3, Eqs.(14)-(15): the actual local-rotation tangent, with no factor 1/2. -/
noncomputable def orbitTangent {M : ℕ} (psi : Ket M) (q : Fin M) (v : Direction) : Ket M :=
  (-Complex.I) • act (directionalPauli q v) psi

/-- PDF p.3, Eq.(16): pull back the Fubini-Study form on the local tangents. -/
noncomputable def orbitMetric {M : ℕ} (psi : Ket M) (v : Fin M → Direction) :
    Matrix (Fin M) (Fin M) ℂ :=
  fun q r => fsForm psi (orbitTangent psi q (v q)) (orbitTangent psi r (v r))

/-- PDF p.3, Eq.(18): real trace of the geometric pullback. -/
noncomputable def traceObjective {M : ℕ} (psi : Ket M) (v : Fin M → Direction) : ℝ :=
  (orbitMetric psi v).trace.re

/-- PDF p.3, Eq.(18): ED is defined geometrically, not by its later closed formula. -/
noncomputable def entanglementDistance {M : ℕ} (psi : Ket M) : ℝ :=
  sInf (traceObjective psi '' directionDomain M)

/-- PDF p.2, Eq.(8), p.7 note [46]: squared chordal Fubini-Study distance. -/
noncomputable def fsSquared {M : ℕ} (phi psi : Ket M) : ℝ :=
  1 - ‖inner ℂ phi psi‖ ^ 2

/-- PDF p.4, Eqs.(23)-(24): sum of distances to the directional Pauli conjugates. -/
noncomputable def distanceObjective {M : ℕ} (psi : Ket M) (v : Fin M → Direction) : ℝ :=
  ∑ q, fsSquared psi (act (directionalPauli q (v q)) psi)

/-- PDF p.3, Eq.(22): the local contribution, defined for the possibly zero Bloch vector. -/
noncomputable def localED {M : ℕ} (psi : Ket M) (q : Fin M) : ℝ :=
  1 - ‖bloch psi q‖ ^ 2

/-- PDF pp.2,4: pure full separability, allowing a unit global phase and the empty product. -/
def FullySeparable {M : ℕ} (psi : Ket M) : Prop :=
  ∃ (z : ℂ) (f : Fin M → EuclideanSpace ℂ Bool),
    ‖z‖ = 1 ∧ (∀ q, IsState (f q)) ∧ psi = z • prodState f

/-- PDF pp.4-5, Eq.(34): tensor product reindexed onto the concatenated wire register. -/
noncomputable def appendKet {a b : ℕ} (psi : Ket a) (phi : Ket b) : Ket (a + b) :=
  WithLp.toLp 2 (fun z => tensorVec psi phi (qubitsAppendEquiv a b z))

/-- PDF p.4, Eq.(33): concatenate the independent directions of two factors. -/
def appendDirections {a b : ℕ} (v : Fin a → Direction) (w : Fin b → Direction) :
    Fin (a + b) → Direction := Fin.append v w

/-- PDF p.5, Eq.(36): concurrence from the spin flip Y tensor Y and conjugation. -/
noncomputable def concurrence (psi : Ket 2) : ℝ :=
  ‖inner ℂ psi (act (kronAll (fun _ : Fin 2 => pauliY))
    (WithLp.toLp 2 (fun z => conj (psi z))))‖

/-- PDF p.5: reduce the actual pure density to its first qubit, tracing out the second. -/
noncomputable def reducedFirst (psi : Ket 2) : Matrix Bool Bool ℂ :=
  traceRight (fun x y => pureDensity psi ![x.1, x.2] ![y.1, y.2])

/-- PDF p.5, Eq.(40): entropy from the reduced density, in natural-log physical units. -/
noncomputable def entropyOfEntanglement (kB : ℝ) (psi : Ket 2) : ℝ :=
  kB * Real.log 2 * vnEntropy (reducedFirst psi)

/-- PDF p.5, Eqs.(40)-(41): scalar entropy profile on ED in [0,2]. -/
noncomputable def entropyProfile (kB e : ℝ) : ℝ :=
  kB * Real.binEntropy ((1 + Real.sqrt (1 - e / 2)) / 2)

/-- PDF p.5, Eq.(42): the four displayed amplitudes, including the negative |111> term. -/
noncomputable def threeQubitFamily (theta phi : ℝ) : Ket 3 :=
  (Real.cos phi * Real.cos theta : ℂ) • ket (natToBits 3 0) +
  (Real.cos phi * Real.sin theta : ℂ) • ket (natToBits 3 6) +
  (Real.sin phi * Real.cos theta : ℂ) • ket (natToBits 3 3) -
  (Real.sin phi * Real.sin theta : ℂ) • ket (natToBits 3 7)

/-- PDF p.5, paragraph after Eq.(43): the two-qubit factor at phi=0. -/
noncomputable def examplePair (theta : ℝ) : Ket 2 :=
  (Real.cos theta : ℂ) • ket (natToBits 2 0) +
  (Real.sin theta : ℂ) • ket (natToBits 2 3)

/-! Sanity examples for the paper-local definitions; no admitted definition bodies. -/

example : pauli 0 = pauliX := rfl

example : pauli 1 = pauliY := rfl

example : pauli 2 = pauliZ := rfl

example : (fun _ : Fin 0 => (0 : Direction)) ∈ directionDomain 0 := by
  simp [directionDomain]

example (psi : Ket 0) (v : Fin 0 → Direction) : traceObjective psi v = 0 := by
  simp [traceObjective, Matrix.trace]

example (psi : Ket 0) : entanglementDistance psi = 0 := by
  have h : traceObjective psi '' directionDomain 0 = {0} := by
    ext x
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, _, rfl⟩
      simp [traceObjective, Matrix.trace]
    · intro hx
      refine ⟨fun _ => 0, ?_, ?_⟩
      · simp [directionDomain]
      · simp [traceObjective, Matrix.trace, hx]
  rw [entanglementDistance, h, csInf_singleton]

example (psi : Ket 2) : entropyOfEntanglement 0 psi = 0 := by
  simp [entropyOfEntanglement]

example : threeQubitFamily 0 0 = ket (natToBits 3 0) := by
  simp [threeQubitFamily]

example : examplePair 0 = ket (natToBits 2 0) := by
  simp [examplePair]

end QAlgorithms.Papers.Independent.Information100.P10


