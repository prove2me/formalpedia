-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
-- name    : QAlgorithms_Papers_Independent_Information100_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:32:32.960989+00:00
-- url     : https://prove2.me/theorems/a7843f37-d554-4ee1-9e90-cacc0b77f13c
-- title:
--   Definitions for Complete Classification of Reversible Entanglement Transformations of Two Qutrits
-- statement:
--   The objects the formalized statements of *Complete Classification of Reversible Entanglement Transformations of Two Qutrits* (arXiv:2610.05234) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Local`
--   - `Joint`
--   - `Space`
--   - `operatorRange`: PDF pp.2,7: operator range in computational coordinates.
--   - `projection`: PDF p.7: orthogonal projection, including the zero subspace.
--   - `support`: PDF pp.3,5: support projection, used on positive operators.
--   - `localRanks`: PDF p.7: subspace local ranks use partial traces of its projector.
--   - `IsCES`: PDF p.2: a CES has no nonzero product vector.
--   - `Entangled`: PDF p.3: entangled normalized two-qutrit state.
--   - `IsProjection`: PDF p.2: orthogonal projectors are Hermitian idempotents.
--   - `LU`: PDF pp.2,9: LU equivalence of operators, without normalization.
--   - `positivePart`: PDF p.5: positive Jordan part of a Hermitian matrix.
--   - `negativePart`: PDF pp.2,7: negative Jordan part, a positive operator.
--   - `positiveProjection`: PDF p.5: full positive spectral projection.
--   - `negativeProjection`: PDF p.5: full negative spectral projection.
--   - `IsProduct`: PDF pp.9,11: product operator, with no unitarity assumption.
--   - `ScalarProductUnitary`: PDF pp.5,11: zero is allowed as a scalar multiple of a product unitary.
--   - `MixedLU`: PDF p.7: mixed LU is a convex mixture of product-unitary channels.
--   - `SeparableChannel`: PDF pp.5,12: separable CPTP channels admit a finite product Kraus representation.
--   - `CountableRepresentation`: PDF p.5: arbitrary countable product Kraus representations, with explicit convergence.
--   - `Preserves`: PDF pp.9–11: invariant subspace of an operator.
--   - `Weights`: PDF p.9, Eq.(S9): nonnegative probabilities, including zero terms.
--   - `Protects`: PDF p.10, Eq.(S11): same Kraus family and weights. A full unitary extension merely represents a unitary on the subspace, and imposes no condition on K outside it.
--   - `ProductProtects`: PDF p.9, Eq.(S9): product-unitary restrictions on a rectangular subspace.
--   - `coherenceSpace`: PDF p.10: coherence closure constructed from omega and L.
--   - `schmidtRectangle`: PDF p.9: Schmidt rectangle from the two reduced pure-state supports.
--   - `Admissible`: PDF p.3: admissibility of full product blocks with local ranks two or three.
--   - `leastRange`: PDF pp.3,19: intersection of ranges, constructed before proving admissibility.
--   - `leastProjection`: PDF pp.3,19: projection onto that intersection.
--   - `retainedBlock`: PDF p.3, Eq.(7): the unnormalized canonical block.
--   - `retainedWeight`: PDF p.3, Eq.(7): retained weight, not BSA weight.
--   - `negativeAlice`: PDF p.3, Eq.(9): the transpose is required on Alice's side.
--   - `negativeBob`: PDF p.3, Eq.(9): Bob's negative-part local support.
--   - `candidateZero`: PDF p.3, Eq.(10): smallest spectral rectangle.
--   - `candidateAlice`: PDF p.3, Eq.(10): Alice-sided candidate.
--   - `candidateBob`: PDF p.3, Eq.(10): Bob-sided candidate.
--   - `wingCoherence`: PDF p.4, Eq.(11): coherence between the two exterior wings.
--   - `testZero`: PDF p.4, Eq.(11): both terms are required for the smallest candidate.
--   - `testAlice`: PDF p.4, Eq.(11): Alice-sided exact zero test.
--   - `testBob`: PDF p.4, Eq.(11): Bob-sided exact zero test.
--   - `zeroTestProjection`: PDF p.20, Eq.(S42): complete exact rule, including all local-rank regimes.
--   - `Feasible`: PDF p.16, Eq.(S28): feasible separable positive suboperators.
--   - `bestSeparableWeight`: PDF p.16: trace supremum; the result below supplies attainment.
--   - `optimalSet`: PDF p.16, Eq.(S28): the full optimizer set.
--   - `cesaro`: PDF p.16, Eq.(S29): Cesaro averages; bounds exclude n=0.
--   - `RealVariables`: PDF p.20, Eq.(S44): 36 real coordinates for two complex 3 by 3 matrices.
--   - `decodeMatrix`: PDF p.20: real and imaginary parts of each local matrix entry.
--   - `Intertwining`: PDF p.20, Eq.(S44): exact unitary intertwining equations.
--   - `pencilColumns`: PDF p.13, Eq.(S21): fixed two-column pencil, in the occupied 2 by 3 space.
--   - `PhaseRelated`: PDF p.20, Eq.(S43): phases in aligned ordered marginal eigenbases.
--   - `swapParties`: PDF p.2: exchanging the names of the parties in a case predicate, not an allowed operation.
--   - `OneSidedCase`: PDF p.2, Case 3: a one-sided orthogonal flag, with arbitrary normalized exterior local states.
--   - `TwoSidedCase`: PDF p.2, Case 4: a two-sided flag with normalized separable exteriors on orthogonal complements.
--   - `CasesTwoThroughFour`: PDF pp.2–3: precisely Cases 2–4, including the exchanged-party Case 3.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, https://arxiv.org/abs/2610.05234v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-! Algebraic statements from arXiv:2610.05234v1. Alice is the first tensor factor.
New definitions are confined to this paper. Operational deferrals are in GAPS.json. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Local := Matrix (Fin 3) (Fin 3) ℂ

abbrev Joint := Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ

abbrev Space := EuclideanSpace ℂ (Fin 3 × Fin 3)

/-- PDF pp.2,7: operator range in computational coordinates. -/
def operatorRange {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :
    Submodule ℂ (EuclideanSpace ℂ I) := LinearMap.range (Matrix.toEuclideanLin X)

/-- PDF p.7: orthogonal projection, including the zero subspace. -/
def projection {I : Type*} [Fintype I] [DecidableEq I]
    (S : Submodule ℂ (EuclideanSpace ℂ I)) : Matrix I I ℂ :=
  Matrix.toEuclideanLin.symm S.starProjection.toLinearMap

/-- PDF pp.3,5: support projection, used on positive operators. -/
def support {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : Matrix I I ℂ :=
  projection (operatorRange X)

/-- PDF p.7: subspace local ranks use partial traces of its projector. -/
def localRanks {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (S : Submodule ℂ (EuclideanSpace ℂ (I × J))) : ℕ × ℕ :=
  ((traceRight (projection S)).rank, (traceLeft (projection S)).rank)

/-- PDF p.2: a CES has no nonzero product vector. -/
def IsCES {I J : Type*} [Fintype I] [Fintype J]
    (S : Submodule ℂ (EuclideanSpace ℂ (I × J))) : Prop :=
  ∀ (a : EuclideanSpace ℂ I) (b : EuclideanSpace ℂ J), tensorVec a b ∈ S → a = 0 ∨ b = 0

/-- PDF p.3: entangled normalized two-qutrit state. -/
def Entangled (X : Joint) : Prop := IsDensityMatrix X ∧ ¬ IsSeparableDensity X

/-- PDF p.2: orthogonal projectors are Hermitian idempotents. -/
def IsProjection {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- PDF pp.2,9: LU equivalence of operators, without normalization. -/
def LU {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X Y : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ U : Matrix.unitaryGroup I ℂ, ∃ V : Matrix.unitaryGroup J ℂ,
    Y = Matrix.kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ) * X *
      (Matrix.kronecker (U : Matrix I I ℂ) (V : Matrix J J ℂ))ᴴ

/-- PDF p.5: positive Jordan part of a Hermitian matrix. -/
def positivePart {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun t : ℝ => max t 0) X

/-- PDF pp.2,7: negative Jordan part, a positive operator. -/
def negativePart {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun t : ℝ => max (-t) 0) X

/-- PDF p.5: full positive spectral projection. -/
def positiveProjection {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :=
  support (positivePart X)

/-- PDF p.5: full negative spectral projection. -/
def negativeProjection {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :=
  support (negativePart X)

/-- PDF pp.9,11: product operator, with no unitarity assumption. -/
def IsProduct (K : Joint) : Prop := ∃ A B : Local, K = Matrix.kronecker A B

/-- PDF pp.5,11: zero is allowed as a scalar multiple of a product unitary. -/
def ScalarProductUnitary (K : Joint) : Prop :=
  ∃ z : ℂ, ∃ U V : Matrix.unitaryGroup (Fin 3) ℂ,
    K = z • Matrix.kronecker (U : Local) (V : Local)

/-- PDF p.7: mixed LU is a convex mixture of product-unitary channels. -/
def MixedLU (Phi : Superop (Fin 3 × Fin 3) (Fin 3 × Fin 3)) : Prop :=
  ∃ m : ℕ, ∃ p : Fin m → ℝ, ∃ U V : Fin m → Matrix.unitaryGroup (Fin 3) ℂ,
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∀ X,
    Phi X = ∑ i, (p i : ℂ) • (Matrix.kronecker (U i : Local) (V i : Local) * X *
      (Matrix.kronecker (U i : Local) (V i : Local))ᴴ)

/-- PDF pp.5,12: separable CPTP channels admit a finite product Kraus representation. -/
def SeparableChannel (Phi : Superop (Fin 3 × Fin 3) (Fin 3 × Fin 3)) : Prop :=
  ∃ m : ℕ, ∃ K : Fin m → Joint, IsKrausFamily K ∧ (∀ i, IsProduct (K i)) ∧
    ∀ X, Phi X = krausApply K X

/-- PDF p.5: arbitrary countable product Kraus representations, with explicit convergence. -/
def CountableRepresentation {I : Type*} (K : I → Joint)
    (Phi : Superop (Fin 3 × Fin 3) (Fin 3 × Fin 3)) : Prop :=
  (∀ i, IsProduct (K i)) ∧ HasSum (fun i => (K i)ᴴ * K i) 1 ∧
    ∀ X, HasSum (fun i => K i * X * (K i)ᴴ) (Phi X)

/-- PDF pp.9–11: invariant subspace of an operator. -/
def Preserves {I : Type*} [Fintype I] [DecidableEq I] (W : Matrix I I ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ I)) : Prop := ∀ x ∈ S, act W x ∈ S

/-- PDF p.9, Eq.(S9): nonnegative probabilities, including zero terms. -/
def Weights {m : ℕ} (p : Fin m → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- PDF p.10, Eq.(S11): same Kraus family and weights. A full unitary extension merely
represents a unitary on the subspace, and imposes no condition on K outside it. -/
def Protects {m : ℕ} (K : Fin m → Joint) (S : Submodule ℂ Space) (p : Fin m → ℝ) : Prop :=
  Weights p ∧ ∀ i, ∃ W : Matrix.unitaryGroup (Fin 3 × Fin 3) ℂ,
    Preserves (W : Joint) S ∧ ∀ x ∈ S, act (K i) x = (Real.sqrt (p i) : ℂ) • act (W : Joint) x

/-- PDF p.9, Eq.(S9): product-unitary restrictions on a rectangular subspace. -/
def ProductProtects {m : ℕ} (K : Fin m → Joint) (P Q : Local) (p : Fin m → ℝ) : Prop :=
  Weights p ∧ ∀ i, ∃ U V : Matrix.unitaryGroup (Fin 3) ℂ,
    Preserves (U : Local) (operatorRange P) ∧ Preserves (V : Local) (operatorRange Q) ∧
    ∀ x ∈ operatorRange (Matrix.kronecker P Q),
      act (K i) x = (Real.sqrt (p i) : ℂ) • act (Matrix.kronecker (U : Local) (V : Local)) x

/-- PDF p.10: coherence closure constructed from omega and L. -/
def coherenceSpace (omega : Joint) (L : Submodule ℂ Space) : Submodule ℂ Space :=
  Submodule.span ℂ {y | ∃ k : ℕ, ∃ x ∈ L, y = act (omega ^ k) x}

/-- PDF p.9: Schmidt rectangle from the two reduced pure-state supports. -/
def schmidtRectangle (psi : Space) : Joint :=
  Matrix.kronecker (support (traceRight (pureDensity psi))) (support (traceLeft (pureDensity psi)))

/-- PDF p.3: admissibility of full product blocks with local ranks two or three. -/
def Admissible (rho R : Joint) : Prop :=
  (∃ P Q : Local, IsProjection P ∧ IsProjection Q ∧
    (P.rank = 2 ∨ P.rank = 3) ∧ (Q.rank = 2 ∨ Q.rank = 3) ∧ R = Matrix.kronecker P Q) ∧
    rho * R = R * rho ∧ IsSeparablePositive (rho - R * rho * R)

/-- PDF pp.3,19: intersection of ranges, constructed before proving admissibility. -/
def leastRange (rho : Joint) : Submodule ℂ Space :=
  ⨅ R : {R : Joint // Admissible rho R}, operatorRange R.val

/-- PDF pp.3,19: projection onto that intersection. -/
def leastProjection (rho : Joint) : Joint := projection (leastRange rho)

/-- PDF p.3, Eq.(7): the unnormalized canonical block. -/
def retainedBlock (rho : Joint) : Joint := leastProjection rho * rho * leastProjection rho

/-- PDF p.3, Eq.(7): retained weight, not BSA weight. -/
def retainedWeight (rho : Joint) : ℝ := (retainedBlock rho).trace.re

/-- PDF p.3, Eq.(9): the transpose is required on Alice's side. -/
def negativeAlice (rho : Joint) : Local :=
  (support (traceRight (negativePart (partialTransposeFirst rho)))).transpose

/-- PDF p.3, Eq.(9): Bob's negative-part local support. -/
def negativeBob (rho : Joint) : Local := support (traceLeft (negativePart (partialTransposeFirst rho)))

/-- PDF p.3, Eq.(10): smallest spectral rectangle. -/
def candidateZero (rho : Joint) : Joint := Matrix.kronecker (negativeAlice rho) (negativeBob rho)

/-- PDF p.3, Eq.(10): Alice-sided candidate. -/
def candidateAlice (rho : Joint) : Joint := Matrix.kronecker (negativeAlice rho) 1

/-- PDF p.3, Eq.(10): Bob-sided candidate. -/
def candidateBob (rho : Joint) : Joint := Matrix.kronecker 1 (negativeBob rho)

/-- PDF p.4, Eq.(11): coherence between the two exterior wings. -/
def wingCoherence (rho : Joint) : Joint :=
  Matrix.kronecker (negativeAlice rho) (1 - negativeBob rho) * rho *
    Matrix.kronecker (1 - negativeAlice rho) (negativeBob rho)

/-- PDF p.4, Eq.(11): both terms are required for the smallest candidate. -/
def testZero (rho : Joint) : ℝ :=
  frobNorm (candidateZero rho * rho * (1 - candidateZero rho)) ^ 2 + frobNorm (wingCoherence rho) ^ 2

/-- PDF p.4, Eq.(11): Alice-sided exact zero test. -/
def testAlice (rho : Joint) : ℝ := frobNorm (candidateAlice rho * rho * (1 - candidateAlice rho)) ^ 2

/-- PDF p.4, Eq.(11): Bob-sided exact zero test. -/
def testBob (rho : Joint) : ℝ := frobNorm (candidateBob rho * rho * (1 - candidateBob rho)) ^ 2

/-- PDF p.20, Eq.(S42): complete exact rule, including all local-rank regimes. -/
def zeroTestProjection (rho : Joint) : Joint :=
  if (negativeAlice rho).rank = 2 then
    if (negativeBob rho).rank = 2 then
      if testZero rho = 0 then candidateZero rho else
        if testAlice rho = 0 then candidateAlice rho else
          if testBob rho = 0 then candidateBob rho else 1
    else if testAlice rho = 0 then candidateAlice rho else 1
  else if (negativeBob rho).rank = 2 then
    if testBob rho = 0 then candidateBob rho else 1
  else 1

/-- PDF p.16, Eq.(S28): feasible separable positive suboperators. -/
def Feasible (rho S : Joint) : Prop := S.PosSemidef ∧ (rho - S).PosSemidef ∧ IsSeparablePositive S

/-- PDF p.16: trace supremum; the result below supplies attainment. -/
def bestSeparableWeight (rho : Joint) : ℝ := sSup {t | ∃ S, Feasible rho S ∧ t = S.trace.re}

/-- PDF p.16, Eq.(S28): the full optimizer set. -/
def optimalSet (rho : Joint) : Set Joint := {S | Feasible rho S ∧ S.trace.re = bestSeparableWeight rho}

/-- PDF p.16, Eq.(S29): Cesaro averages; bounds exclude n=0. -/
def cesaro (Phi : Joint → Joint) (S : Joint) (n : ℕ) : Joint :=
  ((n : ℂ)⁻¹) • ∑ k ∈ Finset.range n, (Phi^[k]) S

/-- PDF p.20, Eq.(S44): 36 real coordinates for two complex 3 by 3 matrices. -/
abbrev RealVariables := Fin 2 × Fin 2 × Fin 3 × Fin 3

/-- PDF p.20: real and imaginary parts of each local matrix entry. -/
def decodeMatrix (x : RealVariables → ℝ) (s : Fin 2) : Local :=
  fun i j => (x (s, 0, i, j) : ℂ) + Complex.I * (x (s, 1, i, j) : ℂ)

/-- PDF p.20, Eq.(S44): exact unitary intertwining equations. -/
def Intertwining (C D : Joint) (U V : Local) : Prop :=
  Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧ Matrix.kronecker U V * C = D * Matrix.kronecker U V

/-- PDF p.13, Eq.(S21): fixed two-column pencil, in the occupied 2 by 3 space. -/
def pencilColumns : Matrix (Fin 2 × Fin 3) (Fin 2) ℂ :=
  fun ij k => if (k = 0 ∧ (ij = (0, 0) ∨ ij = (1, 1))) ∨
    (k = 1 ∧ (ij = (0, 1) ∨ ij = (1, 2))) then 1 else 0

/-- PDF p.20, Eq.(S43): phases in aligned ordered marginal eigenbases. -/
def PhaseRelated (eta zeta : Joint) : Prop :=
  ∃ alpha beta : Fin 3 → ℝ, ∀ i j k l,
    zeta (i,j) (k,l) = Complex.exp (Complex.I *
      ((alpha i - alpha k + beta j - beta l : ℝ) : ℂ)) * eta (i,j) (k,l)

/-- Sanity: zero has zero range. -/
example : operatorRange (0 : Joint) = ⊥ := by
  simp [operatorRange]

/-- Sanity: continuous Jordan parts both vanish on the zero positive operator (PDF pp.5,7). -/
example : positivePart (0 : Joint) = 0 ∧ negativePart (0 : Joint) = 0 := by
  simp [positivePart, negativePart, cfc_zero]

/-- Sanity: an empty family cannot carry the probability weights required by (S9). -/
example (p : Fin 0 → ℝ) : ¬ Weights p := by
  simp [Weights]

/-- Sanity: zero weights force vanishing on every protected vector. -/
example {m : ℕ} (K : Fin m → Joint) (S : Submodule ℂ Space) (p : Fin m → ℝ)
    (h : Protects K S p) (i : Fin m) (hi : p i = 0) (x : Space) (hx : x ∈ S) :
    act (K i) x = 0 := by
  obtain ⟨W, _, heq⟩ := h.2 i
  simpa [hi] using heq x hx

/-- Sanity: the prescribed pencil columns include the two distinct final coordinates. -/
example : pencilColumns (1, 1) 0 = 1 ∧ pencilColumns (1, 2) 1 = 1 := by
  norm_num [pencilColumns]

/-- Sanity: zero real coordinates decode to the zero matrix. -/
example (s : Fin 2) : decodeMatrix (fun _ => 0) s = 0 := by
  ext i j
  simp [decodeMatrix]

/-- PDF p.2: exchanging the names of the parties in a case predicate, not an allowed operation. -/
def swapParties (X : Joint) : Joint := fun p q => X (p.2,p.1) (q.2,q.1)

/-- PDF p.2, Case 3: a one-sided orthogonal flag, with arbitrary normalized exterior local states. -/
def OneSidedCase (rho sigma : Joint) : Prop :=
  ∃ P Z : Local, ∃ n z : EuclideanSpace ℂ (Fin 3), ∃ w : ℝ,
  ∃ eta theta : Joint, ∃ tau upsilon : Local,
    IsProjection P ∧ IsProjection Z ∧ P.rank = 2 ∧ Z.rank = 2 ∧
    IsState n ∧ IsState z ∧ act P n = 0 ∧ act Z z = 0 ∧ 0 < w ∧ w < 1 ∧
    Entangled eta ∧ Entangled theta ∧ LU eta theta ∧
    Matrix.kronecker P (1 : Local) * eta * Matrix.kronecker P (1 : Local) = eta ∧
    Matrix.kronecker Z (1 : Local) * theta * Matrix.kronecker Z (1 : Local) = theta ∧
    IsDensityMatrix tau ∧ IsDensityMatrix upsilon ∧
    rho = (w : ℂ) • eta + ((1-w : ℝ) : ℂ) • Matrix.kronecker (pureDensity n) tau ∧
    sigma = (w : ℂ) • theta + ((1-w : ℝ) : ℂ) • Matrix.kronecker (pureDensity z) upsilon

/-- PDF p.2, Case 4: a two-sided flag with normalized separable exteriors on orthogonal complements. -/
def TwoSidedCase (rho sigma : Joint) : Prop :=
  ∃ P Q Z T : Local, ∃ w : ℝ, ∃ eta theta tau upsilon : Joint,
    IsProjection P ∧ IsProjection Q ∧ IsProjection Z ∧ IsProjection T ∧
    P.rank = 2 ∧ Q.rank = 2 ∧ Z.rank = 2 ∧ T.rank = 2 ∧ 0 < w ∧ w < 1 ∧
    Entangled eta ∧ Entangled theta ∧ LU eta theta ∧
    Matrix.kronecker P Q * eta * Matrix.kronecker P Q = eta ∧
    Matrix.kronecker Z T * theta * Matrix.kronecker Z T = theta ∧
    IsDensityMatrix tau ∧ IsDensityMatrix upsilon ∧ IsSeparableDensity tau ∧ IsSeparableDensity upsilon ∧
    (1-Matrix.kronecker P Q) * tau * (1-Matrix.kronecker P Q) = tau ∧
    (1-Matrix.kronecker Z T) * upsilon * (1-Matrix.kronecker Z T) = upsilon ∧
    rho = (w : ℂ) • eta + ((1-w : ℝ) : ℂ) • tau ∧
    sigma = (w : ℂ) • theta + ((1-w : ℝ) : ℂ) • upsilon

/-- PDF pp.2–3: precisely Cases 2–4, including the exchanged-party Case 3. -/
def CasesTwoThroughFour (rho sigma : Joint) : Prop :=
  LU rho sigma ∨ OneSidedCase rho sigma ∨
    OneSidedCase (swapParties rho) (swapParties sigma) ∨ TwoSidedCase rho sigma

/-- Sanity: exchanging party labels twice is the identity. -/
example (X : Joint) : swapParties (swapParties X) = X := rfl

end QAlgorithms.Papers.Independent.Information100.P07


