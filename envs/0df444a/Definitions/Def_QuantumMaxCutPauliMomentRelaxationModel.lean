-- Prove2me | Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
-- name    : QuantumMaxCutPauliMomentRelaxationModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-01T14:52:31.166082+00:00
-- url     : https://prove2.me/theorems/944bff0f-6d7f-4dca-ab01-0f5f6138bdaf
-- title:
--   Finite-level Pauli moment relaxation for Quantum Max-Cut energy
-- statement:
--   Fix a natural relaxation level k >= 2. A canonical n-qubit Pauli word assigns one of I, X, Y, Z to every vertex; its support is the set of nonidentity labels. Multiply words using the explicit Pauli label and complex phase tables. A real moment assignment L is feasible when L(I)=1 and the real matrix indexed by words of support at most k, with entry Re(phase(P,Q)) L(product(P,Q)), is positive semidefinite. Its objective is sum_{i<j} w_ij (1-L(X_i X_j)-L(Y_i Y_j)-L(Z_i Z_j))/2, matching the campaign Hamiltonian sum w(I-SWAP). The value value(k,G) is the real supremum of the objectives of these feasible assignments. This is one specified relaxation, not an existentially chosen upper-bound function. Moments outside support 2k are unused coordinates and can be projected away. The definition alone does not assert a gap bound or a polynomial-time solver. Supporting local proofs give a feasible maximally mixed assignment, moment bounds, bounded/nonempty objective values, and the zero-weight case. The physical-state embedding and any source-equivalence theorem remain proof obligations.
-- source:
--   Public primary source: Gribling, Sinjorgo, Sotirov, arXiv:2504.11120v1, Section2, real SDP^k, Eq.(2.4), canonical-word moment matrix and Lemma2.1; https://arxiv.org/html/2504.11120v1#S2 . Its Hamiltonian is twice the campaign normalization; the formal objective includes factor1/2. Also Lee and Parekh, ICALP2024, Definition1, https://doi.org/10.4230/LIPIcs.ICALP.2024.105 . Public preprints explicitly authorized by the user. This file fixes the concrete Pauli moment relaxation; it assumes no QMC approximation algorithm.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

/-!
An explicit weighted Pauli moment relaxation, with the campaign QMC
normalization. Local labels 0,1,2,3 denote I,X,Y,Z. Their multiplication
table records both the resulting label and the complex phase.

The moments are real on canonical Hermitian Pauli words. The real Gram
matrix enforces the corresponding signed multiplication relations.
Its rows are all words of support at most k. Values of L on words of
support greater than 2k are irrelevant auxiliary coordinates; a finite
implementation must project them away rather than enumerate 4^n values.

This definition does not assert any approximation guarantee, state
embedding theorem, or polynomial-time SDP solver.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PauliSDP

abbrev Label := Fin 4
abbrev Word (n : ℕ) := Fin n → Label

def localProduct : Label → Label → Label :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

def localPhase : Label → Label → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, Complex.I, -Complex.I],
    ![1, -Complex.I, 1, Complex.I], ![1, Complex.I, -Complex.I, 1]]

def identityWord (n : ℕ) : Word n := fun _ => 0

def support {n : ℕ} (P : Word n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => P i ≠ 0)

def wordProduct {n : ℕ} (P Q : Word n) : Word n :=
  fun i => localProduct (P i) (Q i)

def wordPhase {n : ℕ} (P Q : Word n) : ℂ :=
  ∏ i, localPhase (P i) (Q i)

abbrev Index (n k : ℕ) := {P : Word n // (support P).card ≤ k}

def realGram {n : ℕ} (k : ℕ) (L : Word n → ℝ) :
    Matrix (Index n k) (Index n k) ℝ :=
  fun P Q => (wordPhase P.val Q.val).re * L (wordProduct P.val Q.val)

def Feasible {n : ℕ} (k : ℕ) (L : Word n → ℝ) : Prop :=
  L (identityWord n) = 1 ∧ (realGram k L).PosSemidef

def twoBody {n : ℕ} (a : Label) (e : Edge n) : Word n :=
  fun i => if i = e.val.1 ∨ i = e.val.2 then a else 0

def objective {n : ℕ} (w : Weights n) (L : Word n → ℝ) : ℝ :=
  ∑ e, (w e : ℝ) *
    (1 - L (twoBody 1 e) - L (twoBody 2 e) - L (twoBody 3 e)) / 2

/-- The value of the specified finite-level relaxation, not an
existentially chosen upper-bound function. Intended for k >= 2. -/
def value (k : ℕ) (G : Input) : ℝ :=
  sSup {v : ℝ | ∃ L : Word G.n → ℝ,
    Feasible k L ∧ v = objective G.weights L}


end QuantumMaxCutEnergy.PauliSDP


