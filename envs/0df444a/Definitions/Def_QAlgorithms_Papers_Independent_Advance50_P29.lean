-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29
-- name    : QAlgorithms_Papers_Independent_Advance50_P29
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T22:02:16.947158+00:00
-- url     : https://prove2.me/theorems/68410af6-8f27-44aa-b62e-6071aed7755f
-- title:
--   Definitions for A random-coding based proof for the quantum coding theorem
-- statement:
--   The objects the formalized statements of *A random-coding based proof for the quantum coding theorem* (arXiv:0712.2558) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `KrausTraceBound`: PDF pp.3–4: a Kraus family for a completely positive trace-nonincreasing operation. The positive-semidefinite defect is exactly sum A_i^dagger A_i <= identity.
--   - `HasFiniteKrausOperation`: PDF pp.2–3: a finite, possibly empty, Kraus representation of a quantum operation.
--   - `operationLength`: PDF p.2: minimum Kraus length, not the length of a possibly redundant supplied list. The empty family represents the zero operation. All uses below are Kraus-representable.
--   - `MinimalKraus`: PDF pp.2,14,16: minimality compares the represented map on every operator.
--   - `CodeProjection`: PDF p.5: a nonzero subspace represented by its orthogonal projection and dimension. The trace fixes the actual rank; no arbitrary scalar is used as the code dimension.
--   - `codeDensity`: PDF pp.4–5: the normalized projection pi_C = Pi_C / dim(C).
--   - `stateEntanglementFidelity`: PDF pp.3–4, (1): squared entanglement fidelity for an endomorphism, evaluated on the canonical normalized purification. Trace-decreasing outputs are never renormalized.
--   - `recoveredEntanglementFidelity`: PDF p.5: optimize over all CPTP decoders J -> I, after fixing the code density. For density inputs and quantum operations the value set is nonempty and bounded in [0,1]; its supremum equals the attained finite-dimensional maximum. No decoder leakage is removed.
--   - `exchangeEntropy`: PDF p.6: entropy exchange in bits, evaluated on the actual reference/output state.
--   - `AchievableCodeRate`: PDF p.6: a single sequence of nonzero codes for every positive block length. The rate condition is the source's limsup, and every real R is permitted.
--   - `limsupCodeCapacity`: PDF p.6: operational capacity is the supremum of achievable rates. For positive-dimensional CPTP channels the rate set contains all nonpositive rates and is bounded above by log2(card I), so the real supremum has no empty/unbounded default.
--   - `blockCoherentMaximumRate`: PDF p.6: normalized optimal coherent information of a positive block. The tensor superoperator acts on every matrix, including entangled densities.
--   - `regularizedInformation`: PDF pp.6–7: regularization, written as a limsup; the headline theorem also asserts convergence to this value, retaining the source's actual limit.
--   - `unitaryOn`: PDF p.11, (12): write a unitary on Fin(card I) in the named coordinate basis I.
--   - `rotatedDensity`: PDF p.11, (12): rotate the fixed normalized code projection by a Haar unitary.
--   - `codeAverage`: PDF p.11, (12): normalized Haar average over the entire unitary group. Each theorem using this integral asserts integrability, preventing a default-zero integral.
--   - `decoupling`: PDF pp.8–10, (10): Kraus decoupling operator in blocks indexed by (input,Kraus). Its i,j block uses A_i^dagger A_j in precisely the printed order.
--   - `frobeniusSq`: PDF p.11: squared Frobenius norm, with no ambient matrix-norm convention.
--   - `middlePartialTrace`: PDF p.8, (8): trace out Qprime, retaining reference R and environment E.
--   - `NormalizedUnital`: PDF p.14: normalized-unital means N(I/card I)=I/card J, also for rectangular channels.
--   - `UniformKraus`: PDF p.14: uniformity includes minimality, Hilbert–Schmidt orthogonality, and equal weights.
--   - `weakTypicalWords`: PDF p.15: the closed weak-typicality probability window.
--   - `weakTypicalMass`: PDF p.15: probability mass of all weakly typical IID words.
--   - `weakTypicalProjector`: PDF pp.15–16: the spectral projector onto ALL eigenspaces in the closed typical window. Continuous functional calculus is valid for this indicator on the finite spectrum. Zero eigenvalues are excluded because the lower endpoint is strictly positive.
--   - `krausWeight`: PDF p.16: Kraus weights with respect to the maximally mixed input.
--   - `tensorKraus`: PDF p.16: product Kraus operator associated to a word, acting on the full tensor space.
--   - `typicalOperation`: PDF pp.16–17: keep exactly the typical Kraus words of the fixed minimal orthogonal list.
--   - `reducedOperation`: PDF p.17: project the typical operation onto the OUTPUT typical subspace of N(pi). The source's input-space label here is a typo; the map's types force output coordinates.
--   - `HermitianForm`: PDF pp.19–20: Hermitian sesquilinearity, conjugate-linear first, with no positivity axiom.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, https://arxiv.org/abs/0712.2558v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P43

/-!
Klesse, arXiv:0712.2558v1. All page references are PDF pages.
Operational capacity is defined independently of coherent information. Entropies are in bits,
fidelities are squared and unconditional, and recovery maps are CPTP into the ambient input.
The false general subspace-average identity on p.4 is deferred in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter
open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)
open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)
open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]
variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]
variable [Fintype L] [DecidableEq L]

/-!
Accepted-library reuse: `shannon`, `wordProbability`, and `tensorDensity` are imported
without local aliases or wrappers. The remaining source-specific concepts have descriptive
names because the accepted same-short-name objects are different: intrinsic-algebra trace
bounds, Choi operations, classical/exact-correctability codes, cloning fidelity, PPT
achievability, other capacities, Renyi cq information, a fixed unitary/pure-ancilla RE state,
and frequency-typical sets/projectors do not express this paper's definitions.
The exact candidate declarations and type/semantic mismatches are recorded in
ASSESSMENT.json and MODERATION_NOTES.md. No theorem content changes in this repair.
-/

/-- PDF pp.3–4: a Kraus family for a completely positive trace-nonincreasing operation.
The positive-semidefinite defect is exactly sum A_i^dagger A_i <= identity. -/
def KrausTraceBound (A : L → Matrix J I ℂ) : Prop :=
  (1 - ∑ i, (A i)ᴴ * A i).PosSemidef

/-- PDF pp.2–3: a finite, possibly empty, Kraus representation of a quantum operation. -/
def HasFiniteKrausOperation (N : Superop I J) : Prop :=
  ∃ (r : ℕ) (A : Fin r → Matrix J I ℂ),
    KrausTraceBound A ∧ ∀ X, N X = krausApply A X

/-- PDF p.2: minimum Kraus length, not the length of a possibly redundant supplied list.
The empty family represents the zero operation. All uses below are Kraus-representable. -/
def operationLength (N : Superop I J) : ℕ :=
  sInf {r : ℕ | ∃ A : Fin r → Matrix J I ℂ, ∀ X, N X = krausApply A X}

/-- PDF pp.2,14,16: minimality compares the represented map on every operator. -/
def MinimalKraus (A : L → Matrix J I ℂ) : Prop :=
  ∀ (r : ℕ) (B : Fin r → Matrix J I ℂ),
    (∀ X, krausApply A X = krausApply B X) → Fintype.card L ≤ r

/-- PDF p.5: a nonzero subspace represented by its orthogonal projection and dimension.
The trace fixes the actual rank; no arbitrary scalar is used as the code dimension. -/
structure CodeProjection (I : Type) [Fintype I] [DecidableEq I] where
  dimension : ℕ
  positive : 0 < dimension
  le_ambient : dimension ≤ Fintype.card I
  projector : Matrix I I ℂ
  hermitian : projector.IsHermitian
  idempotent : projector * projector = projector
  trace_eq : projector.trace = (dimension : ℂ)

/-- PDF pp.4–5: the normalized projection pi_C = Pi_C / dim(C). -/
def codeDensity (C : CodeProjection I) : Matrix I I ℂ :=
  (C.dimension : ℂ)⁻¹ • C.projector

/-- PDF pp.3–4, (1): squared entanglement fidelity for an endomorphism, evaluated on the
canonical normalized purification. Trace-decreasing outputs are never renormalized. -/
def stateEntanglementFidelity (N : Superop I I) (rho : Matrix I I ℂ) : ℝ :=
  let psi := pureDensity (densityPurification rho)
  (psi * idTensorSuperop (R := I) N psi).trace.re

/-- PDF p.5: optimize over all CPTP decoders J -> I, after fixing the code density.
For density inputs and quantum operations the value set is nonempty and bounded in [0,1];
its supremum equals the attained finite-dimensional maximum. No decoder leakage is removed. -/
def recoveredEntanglementFidelity (N : Superop I J) (rho : Matrix I I ℂ) : ℝ :=
  sSup {f | ∃ D : Superop J I, IsChannel D ∧
    f = stateEntanglementFidelity (D ∘ N) rho}

/-- PDF p.6: entropy exchange in bits, evaluated on the actual reference/output state. -/
def exchangeEntropy (N : Superop I J) (rho : Matrix I I ℂ) : ℝ :=
  vnEntropy (idTensorSuperop (R := I) N (pureDensity (densityPurification rho)))

/-- PDF p.6: a single sequence of nonzero codes for every positive block length.
The rate condition is the source's limsup, and every real R is permitted. -/
def AchievableCodeRate (N : Superop I J) (R : ℝ) : Prop :=
  ∃ C : (t : ℕ) → CodeProjection (Fin (t + 1) → I),
    R ≤ limsup (fun t => Real.logb 2 ((C t).dimension : ℝ) / (t + 1 : ℝ)) atTop ∧
    Tendsto (fun t => recoveredEntanglementFidelity (piSuperop (fun _ : Fin (t + 1) => N))
      (codeDensity (C t))) atTop (nhds 1)

/-- PDF p.6: operational capacity is the supremum of achievable rates.
For positive-dimensional CPTP channels the rate set contains all nonpositive rates and is
bounded above by log2(card I), so the real supremum has no empty/unbounded default. -/
def limsupCodeCapacity (N : Superop I J) : ℝ := sSup {R : ℝ | AchievableCodeRate N R}

/-- PDF p.6: normalized optimal coherent information of a positive block.
The tensor superoperator acts on every matrix, including entangled densities. -/
def blockCoherentMaximumRate (N : Superop I J) (t : ℕ) : ℝ :=
  singleUseInformation (piSuperop (fun _ : Fin (t + 1) => N)) / (t + 1 : ℝ)

/-- PDF pp.6–7: regularization, written as a limsup; the headline theorem also asserts
convergence to this value, retaining the source's actual limit. -/
def regularizedInformation (N : Superop I J) : ℝ := limsup (blockCoherentMaximumRate N) atTop

/-- PDF p.11, (12): write a unitary on Fin(card I) in the named coordinate basis I. -/
def unitaryOn (U : Matrix.unitaryGroup (Fin (Fintype.card I)) ℂ) : Matrix I I ℂ :=
  fun i j => U (Fintype.equivFin I i) (Fintype.equivFin I j)

/-- PDF p.11, (12): rotate the fixed normalized code projection by a Haar unitary. -/
def rotatedDensity (C : CodeProjection I)
    (U : Matrix.unitaryGroup (Fin (Fintype.card I)) ℂ) : Matrix I I ℂ :=
  unitaryOn U * codeDensity C * (unitaryOn U)ᴴ

/-- PDF p.11, (12): normalized Haar average over the entire unitary group.
Each theorem using this integral asserts integrability, preventing a default-zero integral. -/
def codeAverage (C : CodeProjection I) (f : Matrix I I ℂ → ℝ) : ℝ :=
  ∫ U, f (rotatedDensity C U) ∂(Schur.unitaryHaar (Fintype.card I))

/-- PDF pp.8–10, (10): Kraus decoupling operator in blocks indexed by (input,Kraus).
Its i,j block uses A_i^dagger A_j in precisely the printed order. -/
def decoupling (A : L → Matrix J I ℂ) (K : ℕ) (rho : Matrix I I ℂ) :
    Matrix (I × L) (I × L) ℂ :=
  fun p q => (K : ℂ) *
    ((rho * (A p.2)ᴴ * A q.2 * rho) p.1 q.1 -
      (rho * (A p.2)ᴴ * A q.2 * rho).trace * rho p.1 q.1)

/-- PDF p.11: squared Frobenius norm, with no ambient matrix-norm convention. -/
def frobeniusSq (X : Matrix J I ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (X i j)

/-- PDF p.8, (8): trace out Qprime, retaining reference R and environment E. -/
def middlePartialTrace {R : Type} (X : Matrix (R × (J × E)) (R × (J × E)) ℂ) :
    Matrix (R × E) (R × E) ℂ :=
  fun p q => ∑ j, X (p.1,(j,p.2)) (q.1,(j,q.2))

/-- PDF p.14: normalized-unital means N(I/card I)=I/card J, also for rectangular channels. -/
def NormalizedUnital (N : Superop I J) : Prop := N (mixed I) = mixed J

/-- PDF p.14: uniformity includes minimality, Hilbert–Schmidt orthogonality, and equal weights. -/
def UniformKraus (A : L → Matrix J I ℂ) : Prop :=
  MinimalKraus A ∧
  (∀ i j, i ≠ j → ((A i)ᴴ * A j).trace = 0) ∧
  ∀ i, ((A i)ᴴ * A i).trace.re / (Fintype.card I : ℝ) = (Fintype.card L : ℝ)⁻¹

/-- PDF p.15: the closed weak-typicality probability window. -/
def weakTypicalWords (P : L → ℝ) (epsilon : ℝ) (n : ℕ) : Finset (Fin n → L) :=
  Finset.univ.filter fun w =>
    (2 : ℝ) ^ (-(n : ℝ) * (shannon P + epsilon)) ≤ wordProbability P w ∧
    wordProbability P w ≤ (2 : ℝ) ^ (-(n : ℝ) * (shannon P - epsilon))

/-- PDF p.15: probability mass of all weakly typical IID words. -/
def weakTypicalMass (P : L → ℝ) (epsilon : ℝ) (n : ℕ) : ℝ :=
  ∑ w ∈ weakTypicalWords P epsilon n, wordProbability P w

/-- PDF pp.15–16: the spectral projector onto ALL eigenspaces in the closed typical window.
Continuous functional calculus is valid for this indicator on the finite spectrum.
Zero eigenvalues are excluded because the lower endpoint is strictly positive. -/
def weakTypicalProjector (rho : Matrix I I ℂ) (epsilon : ℝ) (n : ℕ) :
    Matrix (Fin n → I) (Fin n → I) ℂ :=
  cfc (fun x : ℝ => if
    (2 : ℝ) ^ (-(n : ℝ) * (vnEntropy rho + epsilon)) ≤ x ∧
    x ≤ (2 : ℝ) ^ (-(n : ℝ) * (vnEntropy rho - epsilon)) then 1 else 0)
    (tensorDensity rho n)

/-- PDF p.16: Kraus weights with respect to the maximally mixed input. -/
def krausWeight (A : L → Matrix J I ℂ) : L → ℝ :=
  fun i => ((A i)ᴴ * A i).trace.re / (Fintype.card I : ℝ)

/-- PDF p.16: product Kraus operator associated to a word, acting on the full tensor space. -/
def tensorKraus (A : L → Matrix J I ℂ) {n : ℕ} (w : Fin n → L) :
    Matrix (Fin n → J) (Fin n → I) ℂ :=
  fun x y => ∏ t, A (w t) (x t) (y t)

/-- PDF pp.16–17: keep exactly the typical Kraus words of the fixed minimal orthogonal list. -/
def typicalOperation (A : L → Matrix J I ℂ) (epsilon : ℝ) (n : ℕ) :
    Superop (Fin n → I) (Fin n → J) :=
  fun X => ∑ w ∈ weakTypicalWords (krausWeight A) epsilon n,
    tensorKraus A w * X * (tensorKraus A w)ᴴ

/-- PDF p.17: project the typical operation onto the OUTPUT typical subspace of N(pi).
The source's input-space label here is a typo; the map's types force output coordinates. -/
def reducedOperation (A : L → Matrix J I ℂ) (epsilon : ℝ) (n : ℕ) :
    Superop (Fin n → I) (Fin n → J) :=
  fun X => let P := weakTypicalProjector (krausApply A (mixed I)) epsilon n
           P * typicalOperation A epsilon n X * P

/-- PDF pp.19–20: Hermitian sesquilinearity, conjugate-linear first, with no positivity axiom. -/
def HermitianForm (b : Matrix I I ℂ → Matrix I I ℂ → ℂ) : Prop :=
  (∀ V W X, b (V + W) X = b V X + b W X) ∧
  (∀ a V W, b (a • V) W = conj a * b V W) ∧
  (∀ V W X, b V (W + X) = b V W + b V X) ∧
  (∀ a V W, b V (a • W) = a * b V W) ∧
  ∀ V W, b V W = conj (b W V)

/-- Sanity: an empty Kraus list gives the zero operation, without postselection. -/
example (X : Matrix I I ℂ) : krausApply (fun i : Fin 0 => (0 : Matrix J I ℂ)) X = 0 := by
  simp [krausApply]

/-- Sanity: the empty word has probability one; positive n is required in the results. -/
example (P : L → ℝ) (w : Fin 0 → L) : wordProbability P w = 1 := by
  simp [wordProbability]

/-- Sanity: the one-letter IID probability has exactly one factor. -/
example (P : L → ℝ) (w : Fin 1 → L) : wordProbability P w = P (w 0) := by
  simp [wordProbability]

/-- Sanity: the zero-block tensor operator is the scalar identity. -/
example (rho : Matrix I I ℂ) (x y : Fin 0 → I) : tensorDensity rho 0 x y = 1 := by
  simp [tensorDensity]

/-- Sanity: Frobenius square of the zero matrix is zero. -/
example : frobeniusSq (0 : Matrix J I ℂ) = 0 := by simp [frobeniusSq]

/-- Sanity: no Kraus indices gives the zero decoupling matrix. -/
example (rho : Matrix I I ℂ) (K : ℕ) :
    decoupling (fun _ : Fin 0 => (0 : Matrix J I ℂ)) K rho = 0 := by
  ext p q
  exact Fin.elim0 p.2

/-- Sanity: the singleton ambient space admits a one-dimensional normalized code. -/
example : ∃ C : CodeProjection (Fin 1), codeDensity C = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  let C : CodeProjection (Fin 1) := {
    dimension := 1
    positive := by decide
    le_ambient := by simp
    projector := 1
    hermitian := by change (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = 1; simp
    idempotent := by simp
    trace_eq := by simp [Matrix.trace] }
  exact ⟨C, by simp [codeDensity, C]⟩

/-- Sanity: an operation which always outputs zero has zero unconditional fidelity. -/
example (rho : Matrix I I ℂ) :
    stateEntanglementFidelity (fun _ => (0 : Matrix I I ℂ)) rho = 0 := by
  change (pureDensity (densityPurification rho) *
    (0 : Matrix (I × I) (I × I) ℂ)).trace.re = 0
  simp

end QAlgorithms.Papers.Independent.Advance50.P29


