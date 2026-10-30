-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18
-- name    : QAlgorithms_Papers_Independent_Advance50_P18
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:43:47.514771+00:00
-- url     : https://prove2.me/theorems/f4103575-e8ea-4061-9295-b3da3656325d
-- title:
--   Definitions for Private Quantum Channels and the Cost of Randomizing Quantum Information
-- statement:
--   The objects the formalized statements of *Private Quantum Channels and the Cost of Randomizing Quantum Information* (arXiv:quant-ph/0003101) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `KeyedUnitaryEnsemble`: PDF pp.3–4: finite classical law and keyed full-space matrices, fixed before the input. Validity is separate so that explicit constructed ensembles carry no unproved proof fields.
--   - `KeyedUnitaryEnsemble.Valid`: PDF p.3: nonnegative probabilities of total mass one; each keyed operator is unitary. Zero-probability key labels are allowed, and still have unitary operators.
--   - `keyEntropy`: PDF p.3, §2.2: Shannon entropy in bits, including the convention 0 log 0 = 0.
--   - `encrypt`: PDF p.3: the average conjugation map, with probability p (not its square root). The source's Kraus operator for key k is sqrt(p k) times U k.
--   - `sourceMixedIdentity`: PDF p.3: normalized identity; all uses below have a nonempty qubit basis.
--   - `allPure`: PDF p.3: the set of all normalized pure states.
--   - `classicalSource`: PDF p.6: classical messages are precisely computational-basis vectors.
--   - `BarePQC`: PDF p.4, Definition 3.1, with no ancilla. The key is independent of the input; unitarity gives exact inverse decoding for each key, without an extra recovery assumption.
--   - `PQC`: PDF p.4, Definition 3.1: an exact private quantum channel with a fixed mixed ancilla. All of I × A is transmitted. The same ancilla, law and unitaries serve every source state.
--   - `IsSourceMixture`: PDF p.4: a density is a finite probability mixture of normalized source-state projectors. The empty mixture is excluded by the sum-one condition, even when S is empty.
--   - `ExactSourceRandomization`: PDF p.8, §6: forgetting only the classical key in the same full-output model.
--   - `BareRandomizes`: PDF pp.8–9: the same randomization model with no ancillary environment.
--   - `sourcePauli`: PDF p.3: sigma_0, sigma_1, sigma_2, sigma_3 are I, X, Y, Z in this order.
--   - `fullPauli`: PDF p.5, Theorem 4.1: uniform, phase-zero tensor Paulis, each of probability 2^(-2n).
--   - `realPauli`: PDF p.5, Theorem 4.2: independent uniform choices of I and Y, each string of probability 2^(-n). A true bit selects sigma_2 = Y.
--   - `realProductVector`: PDF p.5: tensor product of the real qubits cos(theta_j)|0> + sin(theta_j)|1>. For n = 0 the amplitude of the empty bit string is the empty product, namely 1.
--   - `realProductSource`: PDF p.5: exactly B tensor n, not its linear span or all real entangled vectors.
--   - `exampleSource`: PDF p.5: the particular source {|0>, |+>} in the nonmaximal-output example.
--   - `exampleEnsemble`: PDF p.5: the example's two equally likely unitaries I and H.
--   - `hadamardExampleDensity`: PDF p.5: the example's fixed output [[3/4,1/4],[1/4,1/4]], in basis order 0,1.
--   - `reductionOutput`: PDF pp.6–7, Theorem 5.2: (I/2^n) tensor rho0, reassociated from I × (I × A) to (I × I) × A. No register is discarded.
-- source:
--   Private Quantum Channels and the Cost of Randomizing Quantum Information, arXiv:quant-ph/0003101v2, https://arxiv.org/abs/quant-ph/0003101v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_QAlgorithms_Defs_LocalHamiltonian

/-!
Private Quantum Channels and the Cost of Randomizing Quantum Information,
arXiv:quant-ph/0003101v2. All new interfaces are local to this paper.
Matrix and EuclideanSpace are used directly from Mathlib; no local type aliases
duplicate accepted-library declarations. Same-named definitions in other accepted
papers were checked for equivalence; incompatible source models are not imported.
Product basis indices keep the entire ancillary output visible. No partial trace
occurs in the security condition. A bare channel is the canonical ancilla-free
version, so there is no artificial zero-qubit tensor factor in its statements.
-/

namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

/-- PDF pp.3–4: finite classical law and keyed full-space matrices, fixed before the input.
Validity is separate so that explicit constructed ensembles carry no unproved proof fields. -/
structure KeyedUnitaryEnsemble (K I : Type*) where
  p : K → ℝ
  U : K → (Matrix I I ℂ)

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- PDF p.3: nonnegative probabilities of total mass one; each keyed operator is unitary.
Zero-probability key labels are allowed, and still have unitary operators. -/
def KeyedUnitaryEnsemble.Valid (E : KeyedUnitaryEnsemble K I) : Prop :=
  (∀ k, 0 ≤ E.p k) ∧ (∑ k, E.p k) = 1 ∧
    ∀ k, E.U k ∈ Matrix.unitaryGroup I ℂ

/-- PDF p.3, §2.2: Shannon entropy in bits, including the convention 0 log 0 = 0. -/
def keyEntropy (p : K → ℝ) : ℝ :=
  -∑ k, if p k = 0 then 0 else p k * (Real.log (p k) / Real.log 2)

/-- PDF p.3: the average conjugation map, with probability p (not its square root).
The source's Kraus operator for key k is sqrt(p k) times U k. -/
def encrypt (E : KeyedUnitaryEnsemble K I) (rho : (Matrix I I ℂ)) : (Matrix I I ℂ) :=
  ∑ k, (E.p k : ℂ) • (E.U k * rho * (E.U k).conjTranspose)

/-- PDF p.3: normalized identity; all uses below have a nonempty qubit basis. -/
def sourceMixedIdentity (I : Type*) [Fintype I] [DecidableEq I] : (Matrix I I ℂ) :=
  ((Fintype.card I : ℂ)⁻¹) • 1

/-- PDF p.3: the set of all normalized pure states. -/
def allPure (I : Type*) [Fintype I] : Set ((EuclideanSpace ℂ I)) :=
  {psi | IsState psi}

/-- PDF p.6: classical messages are precisely computational-basis vectors. -/
def classicalSource (I : Type*) [DecidableEq I] : Set ((EuclideanSpace ℂ I)) :=
  Set.range (fun x : I => ket x)

/-- PDF p.4, Definition 3.1, with no ancilla. The key is independent of the input;
unitarity gives exact inverse decoding for each key, without an extra recovery assumption. -/
def BarePQC (S : Set ((EuclideanSpace ℂ I))) (E : KeyedUnitaryEnsemble K I) (rho0 : (Matrix I I ℂ)) : Prop :=
  E.Valid ∧ IsDensityMatrix rho0 ∧
    ∀ psi ∈ S, IsState psi ∧ encrypt E (pureDensity psi) = rho0

/-- PDF p.4, Definition 3.1: an exact private quantum channel with a fixed mixed ancilla.
All of I × A is transmitted. The same ancilla, law and unitaries serve every source state. -/
def PQC (S : Set ((EuclideanSpace ℂ I))) (E : KeyedUnitaryEnsemble K (I × A))
    (anc : (Matrix A A ℂ)) (rho0 : (Matrix (I × A) (I × A) ℂ)) : Prop :=
  E.Valid ∧ IsDensityMatrix anc ∧ IsDensityMatrix rho0 ∧
    ∀ psi ∈ S, IsState psi ∧
      encrypt E (Matrix.kronecker (pureDensity psi) anc) = rho0

/-- PDF p.4: a density is a finite probability mixture of normalized source-state projectors.
The empty mixture is excluded by the sum-one condition, even when S is empty. -/
def IsSourceMixture (S : Set ((EuclideanSpace ℂ I))) (rho : (Matrix I I ℂ)) : Prop :=
  ∃ (r : ℕ) (q : Fin r → ℝ) (psi : Fin r → (EuclideanSpace ℂ I)),
    (∀ j, 0 ≤ q j) ∧ (∑ j, q j) = 1 ∧
    (∀ j, psi j ∈ S ∧ IsState (psi j)) ∧
    rho = ∑ j, (q j : ℂ) • pureDensity (psi j)

/-- PDF p.8, §6: forgetting only the classical key in the same full-output model. -/
def ExactSourceRandomization (S : Set ((EuclideanSpace ℂ I))) (E : KeyedUnitaryEnsemble K (I × A))
    (anc : (Matrix A A ℂ)) (rho0 : (Matrix (I × A) (I × A) ℂ)) : Prop :=
  PQC S E anc rho0

/-- PDF pp.8–9: the same randomization model with no ancillary environment. -/
def BareRandomizes (S : Set ((EuclideanSpace ℂ I))) (E : KeyedUnitaryEnsemble K I) (rho0 : (Matrix I I ℂ)) : Prop :=
  BarePQC S E rho0

/-- PDF p.3: sigma_0, sigma_1, sigma_2, sigma_3 are I, X, Y, Z in this order. -/
def sourcePauli (j : Fin 4) : Stabilizer.Pauli :=
  if j.val = 0 then .I else if j.val = 1 then .X else if j.val = 2 then .Y else .Z

/-- PDF p.5, Theorem 4.1: uniform, phase-zero tensor Paulis, each of probability 2^(-2n). -/
def fullPauli (n : ℕ) : KeyedUnitaryEnsemble (Fin n → Fin 4) (Qubits n) where
  p := fun _ => ((2 : ℝ) ^ (2 * n))⁻¹
  U := fun x => (Stabilizer.PauliString.mk 0 (fun j => sourcePauli (x j))).toMatrix

/-- PDF p.5, Theorem 4.2: independent uniform choices of I and Y, each string of
probability 2^(-n). A true bit selects sigma_2 = Y. -/
def realPauli (n : ℕ) : KeyedUnitaryEnsemble (Qubits n) (Qubits n) where
  p := fun _ => ((2 : ℝ) ^ n)⁻¹
  U := fun x => (Stabilizer.PauliString.mk 0
    (fun j => if x j then Stabilizer.Pauli.Y else Stabilizer.Pauli.I)).toMatrix

/-- PDF p.5: tensor product of the real qubits cos(theta_j)|0> + sin(theta_j)|1>.
For n = 0 the amplitude of the empty bit string is the empty product, namely 1. -/
def realProductVector {n : ℕ} (theta : Fin n → ℝ) : (EuclideanSpace ℂ (Qubits n)) :=
  WithLp.toLp 2 (fun b => ∏ j, ((if b j then Real.sin (theta j)
    else Real.cos (theta j)) : ℂ))

/-- PDF p.5: exactly B tensor n, not its linear span or all real entangled vectors. -/
def realProductSource (n : ℕ) : Set ((EuclideanSpace ℂ (Qubits n))) :=
  {psi | ∃ theta : Fin n → ℝ,
    (∀ j, 0 ≤ theta j ∧ theta j < 2 * Real.pi) ∧ psi = realProductVector theta}

/-- PDF p.5: the particular source {|0>, |+>} in the nonmaximal-output example. -/
def exampleSource : Set ((EuclideanSpace ℂ Bool)) :=
  {psi | psi = ket false ∨ psi = act hadamard (ket false)}

/-- PDF p.5: the example's two equally likely unitaries I and H. -/
def exampleEnsemble : KeyedUnitaryEnsemble Bool Bool where
  p := fun _ => 1 / 2
  U := fun k => if k then hadamard else 1

/-- PDF p.5: the example's fixed output [[3/4,1/4],[1/4,1/4]], in basis order 0,1. -/
def hadamardExampleDensity : (Matrix Bool Bool ℂ) :=
  fun b c => if b = false ∧ c = false then 3 / 4 else 1 / 4

/-- PDF pp.6–7, Theorem 5.2: (I/2^n) tensor rho0, reassociated from
I × (I × A) to (I × I) × A. No register is discarded. -/
def reductionOutput {n a : ℕ} (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ)) :
    (Matrix ((Qubits n × Qubits n) × Qubits a) ((Qubits n × Qubits n) × Qubits a) ℂ) :=
  fun x y => sourceMixedIdentity (Qubits n) x.1.1 y.1.1 * rho0 (x.1.2, x.2) (y.1.2, y.2)

/-! Local definition sanity examples; none use a theorem under draft. -/

example : sourcePauli 2 = Stabilizer.Pauli.Y := by rfl

example : (fullPauli 0).p (fun j => Fin.elim0 j) = 1 := by
  simp [fullPauli]

example : (realPauli 1).p (fun _ => true) = 1 / 2 := by
  norm_num [realPauli]

example : keyEntropy (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
  simp [keyEntropy]

example (E : KeyedUnitaryEnsemble (Fin 0) Bool) : ¬ E.Valid := by
  simp [KeyedUnitaryEnsemble.Valid]

example (theta : Fin 0 → ℝ) (b : Qubits 0) : realProductVector theta b = 1 := by
  simp [realProductVector]

example : hadamardExampleDensity false false = 3 / 4 := by rfl

example : hadamardExampleDensity true false = 1 / 4 := by rfl

example (S : Set ((EuclideanSpace ℂ I))) (E : KeyedUnitaryEnsemble K (I × A)) (anc : (Matrix A A ℂ))
    (rho0 : (Matrix (I × A) (I × A) ℂ)) : ExactSourceRandomization S E anc rho0 ↔ PQC S E anc rho0 := by
  rfl

example : sourceMixedIdentity Bool false false = 1 / 2 := by
  norm_num [sourceMixedIdentity]

example (E : KeyedUnitaryEnsemble K I) : encrypt E 0 = 0 := by
  simp [encrypt]

end

end QAlgorithms.Papers.Independent.Advance50.P18


