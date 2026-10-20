-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49
-- name    : QAlgorithms_Papers_Independent_Dependency50_P49
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T18:16:55.909816+00:00
-- url     : https://prove2.me/theorems/936900ea-56a2-4d49-ac86-526c27c91c9a
-- title:
--   Definitions for The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation
-- statement:
--   The objects the formalized statements of *The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation* (arXiv:quant-ph/0605009) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsQuantumChannel`: PDF p.3: a Heisenberg channel is complex-linear, completely positive and unital.
--   - `traceDual`: PDF p.3, (4): trace-bilinear Schroedinger dual, using the accepted coordinate extension. This is distinct from the finite-field orthogonal-code dual.
--   - `complement`: PDF p.9, (30): the complement determined by the actual dilation V.
--   - `dilationDistance`: PDF p.1, (1): optimize over all positive finite common environments and both isometries. The accepted Schroedinger representation is applied to the trace dual, which is equivalent to T(X)=V^*(X tensor I)V. On physical channels the distance set is nonempty and contained in [0,2].
--   - `operationalFidelity`: PDF p.7, (19), corrected to normalized density operators as required by states and Uhlmann's argument. Root fidelity is imported unchanged from the frozen layer. On positive-dimensional channels this infimum ranges over a nonempty subset of [0,1].
--   - `stateReplacement`: PDF p.9, (33): X -> tr(sigma X) I in Heisenberg picture. Unlike signal-mixture depolarizers, this allows every fixed environment state.
--   - `optimalDecodingError`: PDF p.9, (32): infimum over all decoding channels, distinct from a fixed protocol's recovery error. In positive dimensions its value set is nonempty in [0,2].
--   - `broadcastFirst`: PDF p.12, Corollary 4: the first local restriction of a broadcast dilation.
--   - `broadcastSecond`: PDF p.12, Corollary 4: the second local restriction of a broadcast dilation.
--   - `uniformDepolarizing`: PDF p.12, (45): maximally mixed replacement, using the accepted state I/n.
--   - `transposeMap`: PDF p.12, (44): complex-linear transpose, not conjugate transpose.
--   - `transposeMixture`: PDF p.13, (48): (1-p)S+p Theta, with p real.
--   - `compression`: PDF p.15: Heisenberg compression X -> J^* X J to an isometric code. There is no nonunital zero extension.
--   - `basisOutputHolevo`: PDF pp.14–15, (56)–(57): output Holevo information in bits for the uniform ensemble of columns of U. This specialization takes a Heisenberg map and a basis matrix, rather than the accepted general Schroedinger map/ensemble interface. The theorem uses only identity and the normalized frozen Fourier matrix.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, https://arxiv.org/abs/quant-ph/0605009v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

/-!
Statements from Kretschmann, Schlingemann and Werner, quant-ph/0605009v1.
Page numbers are PDF pages. Local definitions use the source's Heisenberg picture.
Source corrections: normalized states in (19), the dimension-one exception to
Proposition 5, and the proof's distinct quantifiers for the two halves of (32).
The false arbitrary-fixed-environment (18) is deliberately not asserted.
Accepted-library imports supply the matrix types, coordinate extension, operator
norms, root fidelity, maximally mixed state and Schroedinger Stinespring predicate.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal
open Filter
open QAlgorithms.Papers.Independent.Information100.P75 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)
open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.
local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)
local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

/-- PDF p.3: a Heisenberg channel is complex-linear, completely positive and unital. -/
def IsQuantumChannel {I J : Type*} [Fintype I] [Fintype J]
    (T : MatrixMap I J) : Prop :=
  Entanglement.IsCompletelyPositive T ∧ T 1 = 1

/-- PDF p.3, (4): trace-bilinear Schroedinger dual, using the accepted coordinate
extension. This is distinct from the finite-field orthogonal-code dual. -/
def traceDual {a b : ℕ} (T : MatrixMap (Fin b) (Fin a)) :
    MatrixMap (Fin a) (Fin b) :=
  coefficientMap fun i j x y => T (Matrix.single j i 1) y x

/-- PDF p.9, (30): the complement determined by the actual dilation V. -/
def complement {a b e : ℕ} (V : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    MatrixMap (Fin e) (Fin a) :=
  coefficientMap fun x y i j => ∑ k, conj (V (k, i) x) * V (k, j) y

/-- PDF p.1, (1): optimize over all positive finite common environments and both
isometries. The accepted Schroedinger representation is applied to the trace dual,
which is equivalent to T(X)=V^*(X tensor I)V. On physical channels the distance set
is nonempty and contained in [0,2]. -/
def dilationDistance {a b : ℕ} (T1 T2 : MatrixMap (Fin b) (Fin a)) : ℝ :=
  sInf {d : ℝ | ∃ (e : ℕ), 0 < e ∧
    ∃ V1 V2 : Matrix (Fin b × Fin e) (Fin a) ℂ,
      QAlgorithms.Papers.Independent.Information100.P71.IsStinespring (traceDual T1) V1 ∧
      QAlgorithms.Papers.Independent.Information100.P71.IsStinespring (traceDual T2) V2 ∧
      d = specNorm (V1 - V2)}

/-- PDF p.7, (19), corrected to normalized density operators as required by states
and Uhlmann's argument. Root fidelity is imported unchanged from the frozen layer.
On positive-dimensional channels this infimum ranges over a nonempty subset of [0,1]. -/
def operationalFidelity {a b : ℕ} (T1 T2 : MatrixMap (Fin b) (Fin a)) : ℝ :=
  sInf {v : ℝ | ∃ rho : Mat (Fin a × Fin a), IsDensityMatrix rho ∧
    v = rootFidelity (idTensorSuperop (R := Fin a) (traceDual T1) rho)
      (idTensorSuperop (R := Fin a) (traceDual T2) rho)}

/-- PDF p.9, (33): X -> tr(sigma X) I in Heisenberg picture.
Unlike signal-mixture depolarizers, this allows every fixed environment state. -/
def stateReplacement {a e : ℕ} (sigma : Mat (Fin e)) : MatrixMap (Fin e) (Fin a) :=
  coefficientMap fun x y i j => if x = y then sigma j i else 0

/-- PDF p.9, (32): infimum over all decoding channels, distinct from a fixed
protocol's recovery error. In positive dimensions its value set is nonempty in [0,2]. -/
def optimalDecodingError {a b : ℕ} (T : MatrixMap (Fin b) (Fin a)) : ℝ :=
  sInf {r : ℝ | ∃ D : MatrixMap (Fin a) (Fin b), IsQuantumChannel D ∧
    r = cbNorm (T.comp D - LinearMap.id)}

/-- PDF p.12, Corollary 4: the first local restriction of a broadcast dilation. -/
def broadcastFirst {a b c e : ℕ}
    (V : Matrix ((Fin b × Fin c) × Fin e) (Fin a) ℂ) : MatrixMap (Fin b) (Fin a) :=
  coefficientMap fun x y i j => ∑ k, ∑ l,
    conj (V ((i, k), l) x) * V ((j, k), l) y

/-- PDF p.12, Corollary 4: the second local restriction of a broadcast dilation. -/
def broadcastSecond {a b c e : ℕ}
    (V : Matrix ((Fin b × Fin c) × Fin e) (Fin a) ℂ) : MatrixMap (Fin c) (Fin a) :=
  coefficientMap fun x y i j => ∑ k, ∑ l,
    conj (V ((k, i), l) x) * V ((k, j), l) y

/-- PDF p.12, (45): maximally mixed replacement, using the accepted state I/n. -/
def uniformDepolarizing (n : ℕ) : MatrixMap (Fin n) (Fin n) :=
  stateReplacement (maximallyMixed n)

/-- PDF p.12, (44): complex-linear transpose, not conjugate transpose. -/
def transposeMap (n : ℕ) : MatrixMap (Fin n) (Fin n) where
  toFun X := X.transpose
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl

/-- PDF p.13, (48): (1-p)S+p Theta, with p real. -/
def transposeMixture (n : ℕ) (p : ℝ) : MatrixMap (Fin n) (Fin n) :=
  ((1 - p : ℝ) : ℂ) • uniformDepolarizing n + (p : ℂ) • transposeMap n

/-- PDF p.15: Heisenberg compression X -> J^* X J to an isometric code.
There is no nonunital zero extension. -/
def compression {a c : ℕ} (J : Matrix (Fin a) (Fin c) ℂ) :
    MatrixMap (Fin a) (Fin c) :=
  coefficientMap fun i j x y => conj (J x i) * J y j

/-- PDF pp.14–15, (56)–(57): output Holevo information in bits for the uniform
ensemble of columns of U. This specialization takes a Heisenberg map and a basis
matrix, rather than the accepted general Schroedinger map/ensemble interface.
The theorem uses only identity and the normalized frozen Fourier matrix. -/
def basisOutputHolevo {n : ℕ} (T : MatrixMap (Fin n) (Fin n)) (U : Mat (Fin n)) : ℝ :=
  let rho : Fin n → Mat (Fin n) := fun i =>
    traceDual T (U * Matrix.single i i 1 * Uᴴ)
  vnEntropy (((n : ℂ)⁻¹) • ∑ i, rho i) -
    (n : ℝ)⁻¹ * ∑ i, vnEntropy (rho i)

/-! Sanity checks for the paper-local interfaces. Explicit `change` exposes
linear-map application before simplifying, avoiding opaque structure projections. -/

example {I : Type*} [Fintype I] :
    IsQuantumChannel (LinearMap.id : MatrixMap I I) := by
  constructor
  · intro r X hX
    exact hX
  · rfl

example {a b : ℕ} : traceDual (0 : MatrixMap (Fin b) (Fin a)) = 0 := by
  ext X i j
  change (∑ x, ∑ y, (0 : ℂ) * X x y) = 0
  simp

example {a b e : ℕ} :
    complement (0 : Matrix (Fin b × Fin e) (Fin a) ℂ) = 0 := by
  ext X i j
  change (∑ x, ∑ y, (∑ k : Fin b, conj (0 : ℂ) * 0) * X x y) = 0
  simp

example {a e : ℕ} : stateReplacement (a := a) (0 : Mat (Fin e)) = 0 := by
  ext X i j
  change (∑ x, ∑ y, (if i = j then (0 : ℂ) else 0) * X x y) = 0
  simp

example (n : ℕ) (X : Mat (Fin n)) : transposeMap n (transposeMap n X) = X := by
  rfl

example (n : ℕ) : transposeMixture n 0 = uniformDepolarizing n := by
  simp [transposeMixture]

example {a c : ℕ} : compression (0 : Matrix (Fin a) (Fin c) ℂ) = 0 := by
  ext X i j
  change (∑ x, ∑ y, conj (0 : ℂ) * 0 * X x y) = 0
  simp

example {I : Type*} [Fintype I] (sigma : Mat I) :
    rootFidelity (0 : Mat I) sigma = 0 := by
  simp [rootFidelity, cfc_zero]

end QAlgorithms.Papers.Independent.Dependency50.P49


