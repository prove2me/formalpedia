-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18
-- name    : QAlgorithms_Papers_Independent_Claimed50_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:59:27.800847+00:00
-- url     : https://prove2.me/theorems/b3c1c94d-6fa0-4bc2-8c09-ce277f2978bc
-- title:
--   Definitions for Quantum conditional entropy for infinite-dimensional systems
-- statement:
--   The objects the formalized statements of *Quantum conditional entropy for infinite-dimensional systems* (arXiv:1004.4519) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteFirstConditionalEntropy`: Equation (2), PDF p.2: H(first|second), used on finite-first-entropy states. Unlike the accepted finite-dimensional real-valued conditionalEntropy, this is the signed extended-real definition for arbitrary separable systems, in nats. The extended embedding retains infinite relative entropy as negative infinity. Values outside the defining domain are not asserted to be conditional entropies.
--   - `swapCoeff`: Exchange two completed tensor factors; PDF p.2, H(C|A).
--   - `associateRight`: Canonical reassociation (AB)C to A(BC); PDF pp.2,6.
--   - `associateLeft`: Inverse reassociation A(BC) to (AB)C, used to trace C in (7), PDF p.3.
--   - `dropMiddle`: Trace out B from A(BC), retaining AC; PDF pp.2,6.
--   - `marginalBD`: The BD marginal of the same four-party state, tracing out AC; PDF p.3, (9).
--   - `normalizeCompression`: Normalize a positive-mass compression; zero-mass prefixes use the original state. PDF pp.3,6 specify the positive-mass formula; the fallback affects no limit.
--   - `FiniteRankProjection`: Arbitrary finite-rank orthogonal projection on the completed Hilbert space; PDF pp.3,6. No restriction to coordinate or spectral projections.
--   - `ProjectionApproximation`: Increasing finite-rank orthogonal projectors converging strongly to identity; PDF pp.3,6. Pointwise Hilbert-norm convergence, with no operator-norm requirement.
--   - `localCompression`: Equation (10), PDF p.3: normalized (P tensor Q) rho (P tensor Q). The accepted tensor action operates on all entangled blocks in completed coordinates.
--   - `conditioningCompression`: PDF p.6: normalize (Id_AB tensor P_CD) rho (Id_AB tensor P_CD). Only the grouped conditioning register is projected.
--   - `marginalSet`: Exact set of C marginals of a trace-norm state subset; Proposition 2, PDF p.7. No arbitrary choice of marginal representatives or topology on raw arrays is used.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, https://arxiv.org/abs/1004.4519v2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

/-!
Kuznetsova, arXiv:1004.4519v2, PDF pp.1–7. Natural logarithms.
Countable orthonormal coordinates describe arbitrary separable complex Hilbert
spaces; products describe completed Hilbert tensor products. Accepted P33 states
are positive nuclear trace-class operators of trace one, with trace-norm topology.
Accepted P01 supplies extended spectral entropy, relative entropy and partial traces.
Every use of conditional entropy below has finite first-marginal entropy, either
explicitly or as a consequence of marginal subadditivity or finite-rank truncation.
Its initial codomain is EReal; infinite mutual information is never converted to zero.
The accepted-library imports are authorized by the independent-paper workflow.
Compilation is pending the mechanical handoff.
-/

noncomputable section

open Filter
open scoped ENNReal BigOperators
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P01
open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Equation (2), PDF p.2: H(first|second), used on finite-first-entropy states.
Unlike the accepted finite-dimensional real-valued conditionalEntropy, this is
the signed extended-real definition for arbitrary separable systems, in nats.
The extended embedding retains infinite relative entropy as negative infinity.
Values outside the defining domain are not asserted to be conditional entropies. -/
def finiteFirstConditionalEntropy {A B : Type} (X : Matrix (A × B) (A × B) ℂ) : EReal :=
  (homogeneousEntropy (traceSecond X) : EReal) -
    (generalizedRelativeEntropy X (productCoeff (traceSecond X) (traceFirst X)) : EReal)

/-- Exchange two completed tensor factors; PDF p.2, H(C|A). -/
def swapCoeff {A B : Type} (X : Matrix (A × B) (A × B) ℂ) :
    Matrix (B × A) (B × A) ℂ := fun p q => X (p.2, p.1) (q.2, q.1)

/-- Canonical reassociation (AB)C to A(BC); PDF pp.2,6. -/
def associateRight {A B C : Type} (X : Matrix ((A × B) × C) ((A × B) × C) ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  fun p q => X ((p.1, p.2.1), p.2.2) ((q.1, q.2.1), q.2.2)

/-- Inverse reassociation A(BC) to (AB)C, used to trace C in (7), PDF p.3. -/
def associateLeft {A B C : Type} (X : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    Matrix ((A × B) × C) ((A × B) × C) ℂ :=
  fun p q => X (p.1.1, (p.1.2, p.2)) (q.1.1, (q.1.2, q.2))

/-- Trace out B from A(BC), retaining AC; PDF pp.2,6. -/
def dropMiddle {A B C : Type} (X : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    Matrix (A × C) (A × C) ℂ :=
  fun p q => ∑' b : B, X (p.1, (b, p.2)) (q.1, (b, q.2))

/-- The BD marginal of the same four-party state, tracing out AC; PDF p.3, (9). -/
def marginalBD {A B C D : Type}
    (X : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ) :
    Matrix (B × D) (B × D) ℂ :=
  fun p q => ∑' a : A, ∑' c : C, X ((a, p.1), (c, p.2)) ((a, q.1), (c, q.2))

/-- Normalize a positive-mass compression; zero-mass prefixes use the original
state. PDF pp.3,6 specify the positive-mass formula; the fallback affects no limit. -/
def normalizeCompression {I : Type} (original cut : Matrix I I ℂ) : Matrix I I ℂ :=
  if 0 < operatorTrace cut then ((operatorTrace cut)⁻¹ : ℂ) • cut else original

/-- Arbitrary finite-rank orthogonal projection on the completed Hilbert space;
PDF pp.3,6. No restriction to coordinate or spectral projections. -/
structure FiniteRankProjection (I : Type) where
  operator : Hilbert I →L[ℂ] Hilbert I
  idempotent : operator.comp operator = operator
  selfAdjoint : ∀ u v : Hilbert I, inner ℂ (operator u) v = inner ℂ u (operator v)
  finiteRank : FiniteDimensional ℂ (LinearMap.range operator.toLinearMap)

/-- Increasing finite-rank orthogonal projectors converging strongly to identity;
PDF pp.3,6. Pointwise Hilbert-norm convergence, with no operator-norm requirement. -/
structure ProjectionApproximation (I : Type) where
  projection : ℕ → FiniteRankProjection I
  increasing : ∀ n m : ℕ, n ≤ m →
    LinearMap.range (projection n).operator.toLinearMap ≤
      LinearMap.range (projection m).operator.toLinearMap
  converges : ∀ u : Hilbert I,
    Tendsto (fun n => (projection n).operator u) atTop (nhds u)

/-- Equation (10), PDF p.3: normalized (P tensor Q) rho (P tensor Q).
The accepted tensor action operates on all entangled blocks in completed coordinates. -/
def localCompression {A B : Type} (X : Matrix (A × B) (A × B) ℂ)
    (P : FiniteRankProjection A) (Q : FiniteRankProjection B) :
    Matrix (A × B) (A × B) ℂ :=
  normalizeCompression X
    (channelTensorAction (boundedConjugation P.operator) (boundedConjugation Q.operator) X)

/-- PDF p.6: normalize (Id_AB tensor P_CD) rho (Id_AB tensor P_CD).
Only the grouped conditioning register is projected. -/
def conditioningCompression {A B C D : Type}
    (X : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ)
    (P : FiniteRankProjection (C × D)) :
    Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ :=
  normalizeCompression X (channelTensorAction (fun Y => Y) (boundedConjugation P.operator) X)

/-- Exact set of C marginals of a trace-norm state subset; Proposition 2, PDF p.7.
No arbitrary choice of marginal representatives or topology on raw arrays is used. -/
def marginalSet {A C : Type} (S : Set (State (A × C))) : Set (State C) :=
  {omega | ∃ rho ∈ S, omega.coefficients = traceFirst rho.coefficients}

/-! Sanity examples pin grouping, summation, normalization, and strong convergence. -/

example {A B : Type} (X : Matrix (A × B) (A × B) ℂ) :
    swapCoeff (swapCoeff X) = X := rfl

example {A B C : Type} (X : Matrix ((A × B) × C) ((A × B) × C) ℂ)
    (a a2 : A) (b b2 : B) (c c2 : C) :
    associateRight X (a, (b, c)) (a2, (b2, c2)) = X ((a,b),c) ((a2,b2),c2) := rfl

example {A B C : Type} (X : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    associateRight (associateLeft X) = X := rfl

example {A C : Type} (X : Matrix (A × (Unit × C)) (A × (Unit × C)) ℂ)
    (p q : A × C) : dropMiddle X p q = X (p.1, ((),p.2)) (q.1, ((),q.2)) := by
  simp [dropMiddle]

example {A C : Type}
    (X : Matrix ((A × Unit) × (C × Unit)) ((A × Unit) × (C × Unit)) ℂ)
    (p q : A × C) : traceSecond (associateLeft (dropMiddle (associateRight X))) p q = X ((p.1,()),(p.2,())) ((q.1,()),(q.2,())) := by
  simp [traceSecond, associateLeft, dropMiddle, associateRight]

example {B D : Type}
    (X : Matrix ((Unit × B) × (Unit × D)) ((Unit × B) × (Unit × D)) ℂ)
    (p q : B × D) : marginalBD X p q = X (((),p.1),((),p.2)) (((),q.1),((),q.2)) := by
  simp [marginalBD]

example {I : Type} (rho : State I) : operatorTrace rho.coefficients = 1 :=
  rho.density.2.2.2

example (I : Type) : Nonempty (FiniteRankProjection I) := by
  refine ⟨{
    operator := 0
    idempotent := ?_
    selfAdjoint := ?_
    finiteRank := ?_
  }⟩
  · ext u
    simp
  · intro u v
    simp
  · change FiniteDimensional ℂ (LinearMap.range (0 : Hilbert I →ₗ[ℂ] Hilbert I))
    rw [LinearMap.range_zero]
    infer_instance

example {I : Type} (X : Matrix I I ℂ) : normalizeCompression X 0 = X := by
  simp [normalizeCompression, operatorTrace]

example {I : Type} (P : ProjectionApproximation I) (u : Hilbert I) :
    Tendsto (fun n => (P.projection n).operator u) atTop (nhds u) := P.converges u

example {A B : Type} (P : FiniteRankProjection A) (Q : FiniteRankProjection B) :
    localCompression (0 : Matrix (A × B) (A × B) ℂ) P Q = 0 := by
  simp [localCompression, channelTensorAction, boundedConjugation,
    normalizeCompression, operatorTrace]

example {A B C D : Type} (P : FiniteRankProjection (C × D)) :
    conditioningCompression (0 : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ) P = 0 := by
  simp [conditioningCompression, channelTensorAction, boundedConjugation,
    normalizeCompression, operatorTrace]

example {A C : Type} : marginalSet (∅ : Set (State (A × C))) = ∅ := by
  ext omega
  simp [marginalSet]

example {A B : Type} (X : Matrix (A × B) (A × B) ℂ) :
    finiteFirstConditionalEntropy X = (homogeneousEntropy (traceSecond X) : EReal) -
      (generalizedRelativeEntropy X (productCoeff (traceSecond X) (traceFirst X)) : EReal) := rfl

end QAlgorithms.Papers.Independent.Claimed50.P18


