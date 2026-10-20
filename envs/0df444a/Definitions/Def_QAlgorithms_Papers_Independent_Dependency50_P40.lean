-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40
-- name    : QAlgorithms_Papers_Independent_Dependency50_P40
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:16:02.473513+00:00
-- url     : https://prove2.me/theorems/c2ffe4d6-0152-472d-aa03-ade39ff2e8e6
-- title:
--   Definitions for Optimum Quantum Error Recovery using Semidefinite Programming
-- statement:
--   The objects the formalized statements of *Optimum Quantum Error Recovery using Semidefinite Programming* (arXiv:quant-ph/0606035) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `operatorKet`: PDF p.3, (10): the unnormalized operator ket, output factor first.
--   - `matrixAction`: PDF pp.2–3, (6), (11): matrix action, also for rectangular operators.
--   - `complexQuadraticForm`: PDF pp.2–3, (6), (17): the complex quadratic form, without normalizing its vector. The frozen declarations named quadratic instead encode real forms or binary graph phases.
--   - `IsPurification`: PDF p.2, (5): a normalized purification on reference tensor input.
--   - `purificationFidelity`: PDF p.2, (6): squared fidelity of the purification after identity tensor channel.
--   - `outputFirstChoi`: PDF p.3, (13): output-first Choi matrix, obtained by swapping both indices of the frozen input-first Choi construction. No normalization factor is introduced.
--   - `krausChoi`: PDF p.3, (13): the Choi matrix formed from any finite Kraus family.
--   - `fromOutputFirstChoi`: PDF p.3, (13): reconstruct from output-first Choi coordinates by swapping both indices into the frozen input-first inverse. This computes the source's partial-trace formula with basis transpose, without conjugating the input.
--   - `ChoiFeasible`: PDF pp.3–4, (15), (22): PSD with partial trace over the output equal to input identity.
--   - `recoveryCoefficient`: PDF p.4, (21): the coefficient is computed from the density and the noise.
--   - `encodingCoefficient`: PDF p.7, §VI C: the encoding coefficient obtained by expanding (16). For fixed noise E and decoder D, its vectors are (D_i E_j)† rho.
--   - `ensembleFidelity`: PDF p.2, (4): the discrete ensemble's average squared root fidelity.
--   - `channelMix`: PDF p.2, following (4): pointwise convex mixing of channels.
--   - `codeProjector`: PDF pp.4–5, (23)–(24): the code projector constructed from the encoder.
--   - `HasCodeOutputs`: PDF p.4, Fig.1: every output of the ambient recovery is supported on the code.
--   - `encodedPurification`: PDF p.4, Fig.1: encode the input factor of a purification; reference stays first.
-- source:
--   Optimum Quantum Error Recovery using Semidefinite Programming, arXiv:quant-ph/0606035v1, https://arxiv.org/abs/quant-ph/0606035v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Statements from Fletcher–Shor–Win, arXiv:quant-ph/0606035v1.
All Hilbert spaces are finite with fixed bases. Choi matrices are unnormalized,
with output index first. Entanglement fidelity is defined from (6), rather than
from the Kraus or Choi identities to be stated. A purification is supplied explicitly;
the results quantify over every normalized purification of the given density.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF p.3, (10): the unnormalized operator ket, output factor first. -/
def operatorKet {o i : Type*} (A : Matrix o i ℂ) : EuclideanSpace ℂ (o × i) :=
  WithLp.toLp 2 fun p => A p.1 p.2

/-- PDF pp.2–3, (6), (11): matrix action, also for rectangular operators. -/
def matrixAction {o i : Type*} [Fintype i] (A : Matrix o i ℂ)
    (v : EuclideanSpace ℂ i) : EuclideanSpace ℂ o :=
  WithLp.toLp 2 fun a => ∑ b, A a b * v b

/-- PDF pp.2–3, (6), (17): the complex quadratic form, without normalizing its vector.
The frozen declarations named quadratic instead encode real forms or binary graph phases. -/
def complexQuadraticForm {i : Type*} [Fintype i] (v : EuclideanSpace ℂ i)
    (A : Matrix i i ℂ) : ℂ :=
  ∑ a, ∑ b, conj (v a) * A a b * v b

/-- PDF p.2, (5): a normalized purification on reference tensor input. -/
def IsPurification {a h : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) : Prop :=
  IsState psi ∧ traceLeft (pureDensity psi) = rho

/-- PDF p.2, (6): squared fidelity of the purification after identity tensor channel. -/
def purificationFidelity {a h : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin h))
    (B : Superop (Fin h) (Fin h)) : ℝ :=
  (complexQuadraticForm psi (idTensorSuperop B (pureDensity psi))).re

/-- PDF p.3, (13): output-first Choi matrix, obtained by swapping both indices
of the frozen input-first Choi construction. No normalization factor is introduced. -/
def outputFirstChoi {h k : ℕ} (B : Superop (Fin h) (Fin k)) :
    Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ :=
  fun p q => QAlgorithms.Papers.Independent.Information100.P34.choi B
    (p.2, p.1) (q.2, q.1)

/-- PDF p.3, (13): the Choi matrix formed from any finite Kraus family. -/
def krausChoi {h k m : ℕ} (E : Fin m → Matrix (Fin k) (Fin h) ℂ) :
    Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ :=
  ∑ j, dyad (operatorKet (E j)) (operatorKet (E j))

/-- PDF p.3, (13): reconstruct from output-first Choi coordinates by swapping
both indices into the frozen input-first inverse. This computes the source's
partial-trace formula with basis transpose, without conjugating the input. -/
def fromOutputFirstChoi {h k : ℕ} (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) :
    Superop (Fin h) (Fin k) :=
  QAlgorithms.Papers.Independent.Information100.P34.fromChoi
    (fun p q => X (p.2, p.1) (q.2, q.1))

/-- PDF pp.3–4, (15), (22): PSD with partial trace over the output equal to input identity. -/
def ChoiFeasible {h k : ℕ} (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) : Prop :=
  X.PosSemidef ∧ traceLeft X = 1

/-- PDF p.4, (21): the coefficient is computed from the density and the noise. -/
def recoveryCoefficient {h k m : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ)
    (E : Fin m → Matrix (Fin k) (Fin h) ℂ) :
    Matrix (Fin h × Fin k) (Fin h × Fin k) ℂ :=
  ∑ j, dyad (operatorKet (rho * (E j)ᴴ)) (operatorKet (rho * (E j)ᴴ))

/-- PDF p.7, §VI C: the encoding coefficient obtained by expanding (16).
For fixed noise E and decoder D, its vectors are (D_i E_j)† rho. -/
def encodingCoefficient {h k m n : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) :
    Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ :=
  ∑ i, ∑ j, dyad (operatorKet ((D i * E j)ᴴ * rho))
    (operatorKet ((D i * E j)ᴴ * rho))

/-- PDF p.2, (4): the discrete ensemble's average squared root fidelity. -/
def ensembleFidelity {I : Type*} {h : ℕ} (p : I → ℝ)
    (psi : I → EuclideanSpace ℂ (Fin h)) (B : Superop (Fin h) (Fin h)) : ℝ :=
  ∑' i, p i * rootFidelity (pureDensity (psi i)) (B (pureDensity (psi i))) ^ 2

/-- PDF p.2, following (4): pointwise convex mixing of channels. -/
def channelMix {h k : ℕ} (t : ℝ) (B C : Superop (Fin h) (Fin k)) :
    Superop (Fin h) (Fin k) :=
  fun M => (t : ℂ) • B M + ((1 - t : ℝ) : ℂ) • C M

/-- PDF pp.4–5, (23)–(24): the code projector constructed from the encoder. -/
def codeProjector {h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ) :
    Matrix (Fin k) (Fin k) ℂ := U * Uᴴ

/-- PDF p.4, Fig.1: every output of the ambient recovery is supported on the code. -/
def HasCodeOutputs {h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ)
    (R : Superop (Fin k) (Fin k)) : Prop :=
  ∀ M, codeProjector U * R M * codeProjector U = R M

/-- PDF p.4, Fig.1: encode the input factor of a purification; reference stays first. -/
def encodedPurification {a h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) : EuclideanSpace ℂ (Fin a × Fin k) :=
  matrixAction (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) U) psi

/-! Sanity examples for the local concepts. These are definitional checks, not paper proofs. -/

example : operatorKet (1 : Matrix (Fin 1) (Fin 1) ℂ) (0, 0) = 1 := by
  simp [operatorKet]

example {o i : Type*} (A : Matrix o i ℂ) (x : o) (y : i) :
    operatorKet A (x, y) = A x y := by rfl

example {i : Type*} (v w : EuclideanSpace ℂ i) (x y : i) :
    dyad v w x y = v x * conj (w y) := by rfl

example {o i : Type*} [Fintype i] (A : Matrix o i ℂ) (v : EuclideanSpace ℂ i) (x : o) :
    matrixAction A v x = ∑ y, A x y * v y := by rfl

example {i : Type*} [Fintype i] (v : EuclideanSpace ℂ i) :
    complexQuadraticForm v (0 : Matrix i i ℂ) = 0 := by simp [complexQuadraticForm]

example {a h : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) :
    IsPurification rho psi ↔ IsState psi ∧ traceLeft (pureDensity psi) = rho := by rfl

example {a h : ℕ} (psi : EuclideanSpace ℂ (Fin a × Fin h)) :
    purificationFidelity psi (fun _ => 0) = 0 := by
  simp [purificationFidelity, complexQuadraticForm, idTensorSuperop]

example {h k : ℕ} (B : Superop (Fin h) (Fin k)) (o p : Fin k) (i j : Fin h) :
    outputFirstChoi B (o, i) (p, j) = B (Matrix.single i j 1) o p := by rfl

example {h k : ℕ} (E : Fin 0 → Matrix (Fin k) (Fin h) ℂ) :
    krausChoi E = 0 := by simp [krausChoi]

example {h k : ℕ} : fromOutputFirstChoi (0 : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) =
    (fun _ => 0) := by
  funext M
  ext a b
  simp [fromOutputFirstChoi, QAlgorithms.Papers.Independent.Information100.P34.fromChoi]

example {h k : ℕ} (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) :
    ChoiFeasible X ↔ X.PosSemidef ∧ traceLeft X = 1 := by rfl

example {h k : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ)
    (E : Fin 0 → Matrix (Fin k) (Fin h) ℂ) :
    recoveryCoefficient rho E = 0 := by simp [recoveryCoefficient]

example {h k m : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ)
    (D : Fin 0 → Matrix (Fin h) (Fin k) ℂ) :
    encodingCoefficient rho E D = 0 := by simp [encodingCoefficient]

example {I : Type*} {h : ℕ} (psi : I → EuclideanSpace ℂ (Fin h))
    (B : Superop (Fin h) (Fin h)) : ensembleFidelity (fun _ => 0) psi B = 0 := by
  simp [ensembleFidelity]

example {h k : ℕ} (B C : Superop (Fin h) (Fin k)) : channelMix 1 B C = B := by
  funext M
  simp [channelMix]

example {h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ) : codeProjector U = U * Uᴴ := by rfl

example {h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ) : HasCodeOutputs U (fun _ => 0) := by
  intro M
  simp

example {a h k : ℕ} (U : Matrix (Fin k) (Fin h) ℂ)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) :
    encodedPurification U psi =
      matrixAction (Matrix.kronecker (1 : Matrix (Fin a) (Fin a) ℂ) U) psi := by rfl

end QAlgorithms.Papers.Independent.Dependency50.P40


