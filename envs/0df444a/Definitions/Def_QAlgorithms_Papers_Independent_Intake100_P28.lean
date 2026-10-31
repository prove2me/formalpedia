-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28
-- name    : QAlgorithms_Papers_Independent_Intake100_P28
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T17:25:33.385988+00:00
-- url     : https://prove2.me/theorems/bc6cc3a3-bc6c-4320-82ea-3560744eefab
-- title:
--   Definitions for A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity
-- statement:
--   The objects the formalized statements of *A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity* (arXiv:0710.4167) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `realMixture`: Real mixtures, PDF p.2, including endpoints.
--   - `psd`: The PSD cone includes zero, PDF p.2.
--   - `psdPairs`: Pairs of PSD matrices, PDF p.9.
--   - `regularPairs`: A semidefinite first factor and definite inverse factor, PDF pp.8–10.
--   - `tuples`: The m-fold PSD cone, PDF p.2.
--   - `tupleTraceFunctional`: Equation (1.1), PDF p.2; used only for p,q>0.
--   - `partialTraceFunctional`: Equation (1.2), PDF p.2: J is traced out without normalization.
--   - `sandwichedTraceFunctional`: Equation (1.3), PDF p.2: B is fixed and arbitrary; there is no root.
--   - `UConvex`: Dimension-free Upsilon convexity, PDF pp.2,13; B is fixed inside ConvexOn.
--   - `UConcave`: Dimension-free Upsilon concavity, PDF pp.2,13.
--   - `PhiConvex`: Every positive tuple length and matrix size, PDF p.2.
--   - `PhiConcave`: Every positive tuple length and matrix size, PDF p.2.
--   - `PsiConvex`: Psi convexity on all nonzero finite factors, PDF p.2.
--   - `PsiConcave`: Psi concavity on all nonzero finite factors, PDF p.2.
--   - `minkowskiLeft`: Left side of (1.7), PDF p.4: the q/p power precedes the final trace.
--   - `minkowskiRight`: Right side of (1.7), PDF p.4: Tr_1 follows the power.
--   - `selfAdjointGauge`: Equation (1.12), PDF p.5. On Hermitian X spectral positive/negative parts make the feasible set nonempty; its objective is bounded below by zero. No attainment is used. Off that subspace the real sInf has no source meaning.
--   - `offDiagonalHermitianDilation`: Equation (1.13), PDF p.6, on I tensor (J tensor C^2), in false,true order.
--   - `fullGauge`: Equation (1.14), PDF p.6: printed factor 1/2 and printed tensor placement.
--   - `IsHermitianNorm`: All real norm axioms on the Hermitian real vector subspace, PDF pp.5–6.
--   - `IsMatrixNorm`: All complex norm axioms on all operators, PDF p.6.
--   - `variationalObjective`: Unscaled objective inside (2.5)–(2.6), PDF p.8: B then X^(1-r) then B*.
--   - `jointTrace`: Equation (2.7), PDF p.9: B* then X^(1-r) then B.
--   - `tensorPowerPair`: Lemma 2.4, PDF p.9: tensor powers with independent exponents.
--   - `OperatorConvexOn`: Operator convexity means Loewner order, PDF p.9.
--   - `OperatorConcaveOn`: Operator concavity means Loewner order, PDF p.9.
--   - `classicalBlock`: Retained index first, classical block label traced second, PDF p.12.
--   - `binaryPhi`: Binary specialization of (1.1), PDF p.14.
--   - `traceProduct`: Trace product with the exponent proved in (5.3)–(5.5), PDF p.15.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, https://arxiv.org/abs/0710.4167v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

/-! Carlen–Lieb, arXiv:0710.4167v3. Finite matrix statements.
The pinned accepted library supplies spectral powers and unnormalized partial traces.
Negative powers are used only on positive definite matrices. See HARD.md for
undefined endpoints and unspecified infinite-dimensional domains. The paper-local
trace functionals and Hermitian dilation differ from the unrelated frozen declarations
named phi, psi, upsilon, mix, dilation, and tensorMap; see ASSESSMENT.json. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Real mixtures, PDF p.2, including endpoints. -/
def realMixture {E : Type} [Add E] [SMul ℝ E] (t : ℝ) (X Y : E) : E :=
  t • X + (1 - t) • Y

/-- The PSD cone includes zero, PDF p.2. -/
def psd (I : Type) [Fintype I] : Set (Mat I) := {A | A.PosSemidef}

/-- Pairs of PSD matrices, PDF p.9. -/
def psdPairs (I : Type) [Fintype I] : Set (Mat I × Mat I) :=
  {Z | Z.1.PosSemidef ∧ Z.2.PosSemidef}

/-- A semidefinite first factor and definite inverse factor, PDF pp.8–10. -/
def regularPairs (I : Type) [Fintype I] : Set (Mat I × Mat I) :=
  {Z | Z.1.PosSemidef ∧ Z.2.PosDef}

/-- The m-fold PSD cone, PDF p.2. -/
def tuples (m n : ℕ) : Set (Fin m → Mat (Fin n)) :=
  {A | ∀ j, (A j).PosSemidef}

/-- Equation (1.1), PDF p.2; used only for p,q>0. -/
def tupleTraceFunctional {m n : ℕ} (p q : ℝ) (A : Fin m → Mat (Fin n)) : ℝ :=
  (tr (spectralPower (∑ j, spectralPower (A j) p) (q / p))) ^ (1 / q)

/-- Equation (1.2), PDF p.2: J is traced out without normalization. -/
def partialTraceFunctional {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (p q : ℝ) (A : Mat (I × J)) : ℝ :=
  (tr (spectralPower (leftMarginal (spectralPower A p)) (q / p))) ^ (1 / q)

/-- Equation (1.3), PDF p.2: B is fixed and arbitrary; there is no root. -/
def sandwichedTraceFunctional {I : Type} [Fintype I] [DecidableEq I]
    (p q : ℝ) (B A : Mat I) : ℝ :=
  tr (spectralPower (B.conjTranspose * spectralPower A p * B) (q / p))

/-- Dimension-free Upsilon convexity, PDF pp.2,13; B is fixed inside ConvexOn. -/
def UConvex (p q : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ B : Mat (Fin n),
    ConvexOn ℝ (psd (Fin n)) (sandwichedTraceFunctional p q B)

/-- Dimension-free Upsilon concavity, PDF pp.2,13. -/
def UConcave (p q : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ B : Mat (Fin n),
    ConcaveOn ℝ (psd (Fin n)) (sandwichedTraceFunctional p q B)

/-- Every positive tuple length and matrix size, PDF p.2. -/
def PhiConvex (p q : ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → ConvexOn ℝ (tuples m n) (tupleTraceFunctional p q)

/-- Every positive tuple length and matrix size, PDF p.2. -/
def PhiConcave (p q : ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → ConcaveOn ℝ (tuples m n) (tupleTraceFunctional p q)

/-- Psi convexity on all nonzero finite factors, PDF p.2. -/
def PsiConvex (p q : ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    ConvexOn ℝ (psd (Fin m × Fin n)) (partialTraceFunctional p q)

/-- Psi concavity on all nonzero finite factors, PDF p.2. -/
def PsiConcave (p q : ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    ConcaveOn ℝ (psd (Fin m × Fin n)) (partialTraceFunctional p q)

/-- Left side of (1.7), PDF p.4: the q/p power precedes the final trace. -/
def minkowskiLeft {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (p q : ℝ) (A : Mat (I × (J × K))) : ℝ :=
  tr (spectralPower
    (rightMarginal (spectralPower (rightMarginal (spectralPower A q)) (p / q))) (q / p))

/-- Right side of (1.7), PDF p.4: Tr_1 follows the power. -/
def minkowskiRight {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (p q : ℝ) (A : Mat (I × (J × K))) : ℝ :=
  tr (rightMarginal (spectralPower (marginalAC (spectralPower A p)) (q / p)))

/-- Equation (1.12), PDF p.5. On Hermitian X spectral positive/negative parts
make the feasible set nonempty; its objective is bounded below by zero.
No attainment is used. Off that subspace the real sInf has no source meaning. -/
def selfAdjointGauge {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (p q : ℝ) (X : Mat (I × J)) : ℝ :=
  sInf {v : ℝ | ∃ A B : Mat (I × J), A.PosSemidef ∧ B.PosSemidef ∧
    X = A - B ∧ v = partialTraceFunctional p q A + partialTraceFunctional p q B}

/-- Equation (1.13), PDF p.6, on I tensor (J tensor C^2), in false,true order. -/
def offDiagonalHermitianDilation {I J : Type} (X : Mat (I × J)) : Mat (I × (J × Bool)) :=
  fun a b => if a.2.2 = false ∧ b.2.2 = true then X (a.1,a.2.1) (b.1,b.2.1)
  else if a.2.2 = true ∧ b.2.2 = false then X.conjTranspose (a.1,a.2.1) (b.1,b.2.1)
  else 0

/-- Equation (1.14), PDF p.6: printed factor 1/2 and printed tensor placement. -/
def fullGauge {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (p q : ℝ) (X : Mat (I × J)) : ℝ :=
  (1 / 2 : ℝ) * selfAdjointGauge p q (offDiagonalHermitianDilation X)

/-- All real norm axioms on the Hermitian real vector subspace, PDF pp.5–6. -/
def IsHermitianNorm {I : Type} [Fintype I] (N : Mat I → ℝ) : Prop :=
  (∀ X, X.IsHermitian → 0 ≤ N X) ∧
  (∀ X, X.IsHermitian → (N X = 0 ↔ X = 0)) ∧
  (∀ (t : ℝ) X, X.IsHermitian → N (t • X) = |t| * N X) ∧
  (∀ X Y, X.IsHermitian → Y.IsHermitian → N (X + Y) ≤ N X + N Y)

/-- All complex norm axioms on all operators, PDF p.6. -/
def IsMatrixNorm {I : Type} [Fintype I] (N : Mat I → ℝ) : Prop :=
  (∀ X, 0 ≤ N X) ∧ (∀ X, N X = 0 ↔ X = 0) ∧
  (∀ (z : ℂ) X, N (z • X) = ‖z‖ * N X) ∧
  (∀ X Y, N (X + Y) ≤ N X + N Y)

/-- Unscaled objective inside (2.5)–(2.6), PDF p.8: B then X^(1-r) then B*. -/
def variationalObjective {I : Type} [Fintype I] [DecidableEq I]
    (p q : ℝ) (B A X : Mat I) : ℝ :=
  tr (spectralPower A (p / 2) * B * spectralPower X (1 - p / q) *
    B.conjTranspose * spectralPower A (p / 2) + (p / q - 1) • X)

/-- Equation (2.7), PDF p.9: B* then X^(1-r) then B. -/
def jointTrace {I : Type} [Fintype I] [DecidableEq I]
    (p r : ℝ) (B : Mat I) (Z : Mat I × Mat I) : ℝ :=
  tr (spectralPower Z.1 (p / 2) * B.conjTranspose * spectralPower Z.2 (1-r) *
    B * spectralPower Z.1 (p / 2))

/-- Lemma 2.4, PDF p.9: tensor powers with independent exponents. -/
def tensorPowerPair {I : Type} [Fintype I] [DecidableEq I]
    (p r : ℝ) (Z : Mat I × Mat I) : Mat (I × I) :=
  Matrix.kronecker (spectralPower Z.1 p) (spectralPower Z.2 (1-r))

/-- Operator convexity means Loewner order, PDF p.9. -/
def OperatorConvexOn {E I : Type} [Add E] [SMul ℝ E] [Fintype I]
    (S : Set E) (f : E → Mat I) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (realMixture t (f X) (f Y) - f (realMixture t X Y)).PosSemidef

/-- Operator concavity means Loewner order, PDF p.9. -/
def OperatorConcaveOn {E I : Type} [Add E] [SMul ℝ E] [Fintype I]
    (S : Set E) (f : E → Mat I) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (f (realMixture t X Y) - realMixture t (f X) (f Y)).PosSemidef

/-- Retained index first, classical block label traced second, PDF p.12. -/
def classicalBlock {m n : ℕ} (A : Fin m → Mat (Fin n)) : Mat (Fin n × Fin m) :=
  fun a b => if a.2 = b.2 then A a.2 a.1 b.1 else 0

/-- Binary specialization of (1.1), PDF p.14. -/
def binaryPhi {n : ℕ} (p q : ℝ) (Z : Mat (Fin n) × Mat (Fin n)) : ℝ :=
  tupleTraceFunctional p q ![Z.1, Z.2]

/-- Trace product with the exponent proved in (5.3)–(5.5), PDF p.15. -/
def traceProduct {I : Type} [Fintype I] [DecidableEq I]
    (p r : ℝ) (Z : Mat I × Mat I) : ℝ :=
  tr (spectralPower Z.1 p * spectralPower Z.2 (1-r))

/-! Definitional sanity checks pin domains, tensor order, adjoints, and scaling.
These do not enumerate theorem cases. -/

example {I : Type} [Fintype I] : (0 : Mat I) ∈ psd I := by
  exact Matrix.PosSemidef.zero

example {I : Type} [Fintype I] [DecidableEq I] (A : Mat I) :
    spectralPower A 0 = 1 := by simp [spectralPower]

example {E : Type} [AddCommGroup E] [Module ℝ E] (X Y : E) : realMixture 1 X Y = X := by
  simp [realMixture]

example {m n : ℕ} (A : Fin m → Mat (Fin n)) :
    A ∈ tuples m n ↔ ∀ j, (A j).PosSemidef := Iff.rfl

example {I : Type} [Fintype I] (A B : Mat I) :
    (A,B) ∈ regularPairs I ↔ A.PosSemidef ∧ B.PosDef := Iff.rfl

example {I J : Type} (X : Mat (I × J)) (i k : I) (j l : J) :
    offDiagonalHermitianDilation X (i,(j,false)) (k,(l,true)) = X (i,j) (k,l) := by simp [offDiagonalHermitianDilation]

example {I J : Type} (X : Mat (I × J)) (i k : I) (j l : J) :
    offDiagonalHermitianDilation X (i,(j,true)) (k,(l,false)) = X.conjTranspose (i,j) (k,l) := by
  simp [offDiagonalHermitianDilation]

example {m n : ℕ} (A : Fin m → Mat (Fin n)) (i k : Fin n) (j : Fin m) :
    classicalBlock A (i,j) (k,j) = A j i k := by simp [classicalBlock]

example {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (p q : ℝ) (X : Mat (I × J)) :
    fullGauge p q X = (1/2 : ℝ) * selfAdjointGauge p q (offDiagonalHermitianDilation X) := rfl

example {I : Type} [Fintype I] [DecidableEq I]
    (p q : ℝ) (A X : Mat I) :
    variationalObjective p q 0 A X = tr ((p / q - 1) • X) := by
  simp [variationalObjective]

example {I : Type} [Fintype I] [DecidableEq I]
    (p r : ℝ) (Z : Mat I × Mat I) : jointTrace p r 0 Z = 0 := by
  simp [jointTrace, tr]

example {I : Type} [Fintype I] [DecidableEq I] (Z : Mat I × Mat I) :
    tensorPowerPair 0 1 Z = Matrix.kronecker (1 : Mat I) (1 : Mat I) := by
  simp [tensorPowerPair, spectralPower]

example {I : Type} [Fintype I] [DecidableEq I] (Z : Mat I × Mat I) :
    traceProduct 0 1 Z = tr (1 : Mat I) := by
  simp [traceProduct, spectralPower]

end QAlgorithms.Papers.Independent.Intake100.P28


