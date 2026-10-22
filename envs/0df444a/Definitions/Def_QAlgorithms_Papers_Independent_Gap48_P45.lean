-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
-- name    : QAlgorithms_Papers_Independent_Gap48_P45
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:43:27.011691+00:00
-- url     : https://prove2.me/theorems/4d85600a-51bb-4d98-9a7d-b941ad01cebe
-- title:
--   Definitions for Reversibility conditions for quantum channels and their applications
-- statement:
--   The objects the formalized statements of *Reversibility conditions for quantum channels and their applications* (arXiv:1203.0262) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `dimensionCount`: PDF pp.4,7: finite cardinality or infinity, never default-zero infinite finrank.
--   - `operatorRank`: PDF pp.5,7,10: operator range dimension, with every infinite dimension retained.
--   - `generatedSpace`: PDF pp.7,14: the closed span of the state supports; includes mixed states.
--   - `CompleteFamily`: Definition 5, PDF p.7: equivalent closed-support formulation of completeness.
--   - `familyProjection`: PDF pp.14–15: projection computed from the family's closed generated space.
--   - `outputSpace`: PDF p.7: actual output support, without imposing minimality on a dilation.
--   - `outputProjection`: PDF p.7: output-support projection constructed from Phi.
--   - `boundedTracePair`: PDF pp.3,6: Tr(BX). Form the actual bounded product before summing its diagonal.
--   - `channelDual`: PDF pp.6–7: normal dual determined by matrix-unit trace pairings.
--   - `restrictedDualNullity`: PDF p.7: m(Phi), the dual kernel restricted to operators supported on H_B^Phi. The defining set is a complex vector space; its span has exactly its dimension.
--   - `rankMultiplicity`: PDF pp.8,10: min(m(Phi)+r^2,dim H_B^Phi), including infinite values.
--   - `BoundIndex`: PDF p.12 n.7: m labels in finite dimension; countably many at infinity.
--   - `coefficientTraceHasSum`: PDF pp.4–5: coefficient adapter to the accepted bounded-operator TraceHasSum. The coefficient trace-class guards exclude an invalid-array zero fallback.
--   - `PartiallyEntanglementBreaking`: Definition 3, PDF pp.5–6: outputs lie in the trace-closed convex hull of normalized pure states with Schmidt rank at most r, for every separable ancilla.
--   - `CountableSchmidtOutputs`: The explanatory paragraph after Theorem 3, PDF p.8: every ancilla output has an actual countable pure Schmidt-rank-r decomposition, stronger than merely belonging to the closed Schmidt class. Zero weights include finite mixtures.
--   - `HasBoundedRankKraus`: PDF pp.8,20: actual countable Kraus representation, count and rank bounds.
--   - `StatesOrthogonal`: PDF pp.13–15: orthogonality of the state supports.
--   - `OrthogonallyNondecomposable`: Definition 6 as used in Lemmas 4–5, PDF pp.13–15: no two nonempty mutually orthogonal subfamilies partition S. Unused ambient subspaces do not split S.
--   - `connectedComponent`: Lemma 5 proof, PDF pp.14–15: states reachable by finite nonorthogonal chains.
--   - `componentSets`: PDF pp.14–15: canonical component collection; empty for the empty family.
--   - `Component`: PDF p.15: canonical nonempty-component labels.
--   - `componentProjection`: PDF p.15: component projections are computed from S, never freely supplied.
--   - `IsONDPartition`: Lemma 5, PDF pp.14–15: nonempty disjoint OND pieces, orthogonal across pieces. Set-valued partitions encode uniqueness up to relabeling.
--   - `vectorStates`: PDF pp.11–12: pure-state family of a vector system; phases are immaterial.
--   - `OrthonormalBasisFamily`: PDF pp.11–12: orthonormality plus strong Parseval completeness.
--   - `OrthogonalResolution`: PDF pp.12,15,20–21: nonzero orthogonal projections strongly summing to identity.
--   - `blockDiagonalStates`: PDF p.15(ii): all block-diagonal states, with trace-norm pinching sum.
--   - `blockPureStates`: PDF p.21, Corollary 4(i): all pure states within individual blocks.
--   - `HasBlockCQForm`: PDF pp.11,15: c-q/block measure-and-prepare form with normalized sigma_k, correct ranks and trace-norm output convergence on the entire trace class.
--   - `NormalizedOrthogonalRows`: PDF pp.11–12,15: rowwise orthogonality and squared norms summing to one. Zero vectors allow padding a smaller spectral decomposition to m labels.
--   - `blockNormalMap`: PDF p.15(iv): exactly <psi_t^l|psi_p^k>, in H_A tensor H_m coordinates.
--   - `HasBlockNormalForm`: PDF pp.11–12,15(iv): displayed CPTP normal form and both partial-isometry identities. The condition is a conclusion, not an extra source hypothesis.
--   - `UnitarilyEquivalent`: PDF pp.17–18: unitary equivalence on the entire output spaces.
--   - `gramNormalMap`: PDF pp.17–18: c_kl=<psi_l|psi_k>, retaining the source conjugation order.
--   - `HasGramNormalForm`: PDF p.17: Gram form; the no-zero-entry clause is conditional on dual injectivity.
--   - `DualInjective`: PDF p.17: ker Phi*={0} on all bounded operators.
--   - `SimplifiedRegime`: PDF p.17: the two advertised channel conditions are alternatives.
--   - `PositiveLaw`: PDF pp.8,17: arbitrary strictly positive normalized weights.
--   - `vectorAverage`: Equation (9), PDF p.8: computed barycenter, not an arbitrary free parameter.
--   - `inverseRootImage`: PDF p.8(9): inverse square root on its spectral domain, defined by its unique least-norm preimage. Off-domain fallback is zero; theorems assert domain membership through the defining equation, never as an additional input hypothesis.
--   - `whitenedVector`: PDF p.8(9): sqrt(pi_i rho_bar^{-1})v_i, with inverse exponent -1/2.
--   - `HasWhitenedForm`: PDF p.8(8): computed frame and orthogonal spectral rows, both output series in trace norm. The inverse equation explicitly excludes an off-domain fallback.
--   - `orderedPartialSum`: PDF pp.16–17,25: ordered partial sums, allowing conditional basis expansions.
--   - `UniqueConvergentBasis`: PDF pp.16–17,25: unique convergent-expansion basis; neither Hamel nor ONB.
--   - `coefficientSupportProjection`: PDF pp.6–7: support projection on arbitrary completed countable coordinates. The accepted Information100.P06 supportProjection returns a finite matrix and cannot represent this domain. This coefficient adapter uses Mathlib's closed-range projection.
--   - `petzSupportedDual`: PDF pp.6–7,23–24: the supported solution B of S_out B S_out = Phi(S_in A S_in). It is unique and bounded for CPTP Phi and a reference state, even when S_out has no bounded inverse. Off this domain the total fallback is zero. No recovery property is assumed in this definition.
--   - `petzExtendedDual`: PDF pp.6–7: explicit extension off output support; the predual prepares sigma from the trace outside that support. This makes the total map unital on the dual.
--   - `petzRecovery`: PDF pp.6–7,23–24: computed predual, specified by every matrix-unit pairing.
--   - `DiscreteEnsemble`: PDF p.18: finite or countable discrete ensemble; zero weights are allowed.
--   - `discreteProbabilityLaw`: PDF p.18: the actual probability mass function of the normalized weights.
--   - `discreteAverageCoefficients`: PDF p.18: coefficient adapter to the accepted operator barycenter. No independent average variable or new summation convention is introduced.
--   - `discreteHolevo`: PDF pp.18–19: relative-entropy Holevo functional in nats, including infinity. Zero weights times infinite relative entropy contribute zero.
--   - `activeStates`: PDF p.19: recovery family with zero-weight entries removed.
--   - `FullRank`: PDF pp.7,20,22: full rank means zero kernel, without a bounded inverse.
--   - `finiteEntropyGain`: PDF p.19: entropy gain, used only when both entropies are finite.
--   - `separableConditionalEntropyNats`: PDF p.22(21): conditional entropy in nats on arbitrary countable coordinates; discard the FIRST factor and retain B. The accepted Dependency50.P15 definition is for finite matrices in bits, so it cannot represent this source domain.
--   - `ResolutionClassification`: PDF p.21: all four explicit clauses of Theorem 4 for the resolution P. This predicate is a conclusion, never a premise substituting for the theorem.
--   - `appendingMap`: PDF p.13(13): append a fixed normalized mixed state on a completed tensor.
--   - `IrreducibleUnitaryAction`: PDF p.21: strongly continuous unitary group action, irreducible on the whole finite-dimensional Hilbert space, rather than just one commuting pair.
--   - `tensorIdentityEffect`: Equation (12), PDF p.12: P tensor identity, on completed tensor coordinates.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, https://arxiv.org/abs/1203.0262v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

/-!
Shirokov, arXiv:1203.0262v3. Countable nonempty coordinates represent every
nonzero separable complex Hilbert space, and products are completed tensors.
All new definitions are paper-local; imports are pinned accepted libraries.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)
open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)
open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)
open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)
open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

/-- PDF pp.4,7: finite cardinality or infinity, never default-zero infinite finrank. -/
def dimensionCount (I : Type) : ℕ∞ := Cardinal.toENat (Cardinal.mk I)

/-- PDF pp.5,7,10: operator range dimension, with every infinite dimension retained. -/
def operatorRank {I J : Type} (A : Hilbert I →L[ℂ] Hilbert J) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℂ (LinearMap.range A.toLinearMap))

/-- PDF pp.7,14: the closed span of the state supports; includes mixed states. -/
def generatedSpace {I : Type} (S : Set (State I)) : Submodule ℂ (Hilbert I) :=
  (Submodule.span ℂ {v | ∃ rho ∈ S, ∃ w, boundedOperator rho.coefficients w = v}).topologicalClosure

/-- Definition 5, PDF p.7: equivalent closed-support formulation of completeness. -/
def CompleteFamily {I : Type} (S : Set (State I)) : Prop := generatedSpace S = ⊤

/-- PDF pp.14–15: projection computed from the family's closed generated space. -/
def familyProjection {I : Type} (S : Set (State I)) : Hilbert I →L[ℂ] Hilbert I :=
  letI : CompleteSpace (generatedSpace S) :=
    (show IsClosed (generatedSpace S : Set (Hilbert I)) from
      Submodule.isClosed_topologicalClosure _).completeSpace_coe
  (generatedSpace S).starProjection

/-- PDF p.7: actual output support, without imposing minimality on a dilation. -/
def outputSpace {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) : Submodule ℂ (Hilbert J) :=
  (Submodule.span ℂ {v | ∃ rho : State I, ∃ w, boundedOperator (Phi rho.coefficients) w = v}).topologicalClosure

/-- PDF p.7: output-support projection constructed from Phi. -/
def outputProjection {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) :
    Hilbert J →L[ℂ] Hilbert J :=
  letI : CompleteSpace (outputSpace Phi) :=
    (show IsClosed (outputSpace Phi : Set (Hilbert J)) from
      Submodule.isClosed_topologicalClosure _).completeSpace_coe
  (outputSpace Phi).starProjection

/-- PDF pp.3,6: Tr(BX). Form the actual bounded product before summing its diagonal. -/
def boundedTracePair {I : Type} (X : Matrix I I ℂ) (B : Hilbert I →L[ℂ] Hilbert I) : ℂ :=
  ∑' i, operatorCoeff (B.comp (boundedOperator X)) i i

/-- PDF pp.6–7: normal dual determined by matrix-unit trace pairings. -/
def channelDual {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (B : Hilbert J →L[ℂ] Hilbert J) : Hilbert I →L[ℂ] Hilbert I :=
  boundedOperator (fun i j => boundedTracePair (Phi (Matrix.single j i (1 : ℂ))) B)

/-- PDF p.7: m(Phi), the dual kernel restricted to operators supported on H_B^Phi.
The defining set is a complex vector space; its span has exactly its dimension. -/
def restrictedDualNullity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) : ℕ∞ :=
  Cardinal.toENat (Module.rank ℂ (Submodule.span ℂ
    {B : Hilbert J →L[ℂ] Hilbert J |
      (outputProjection Phi).comp (B.comp (outputProjection Phi)) = B ∧ channelDual Phi B = 0}))

/-- PDF pp.8,10: min(m(Phi)+r^2,dim H_B^Phi), including infinite values. -/
def rankMultiplicity {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (r : ℕ) : ℕ∞ :=
  min (restrictedDualNullity Phi + (r : ℕ∞) ^ 2)
    (Cardinal.toENat (Module.rank ℂ (outputSpace Phi)))

/-- PDF p.12 n.7: m labels in finite dimension; countably many at infinity. -/
abbrev BoundIndex (m : ℕ∞) := {n : ℕ // (n : ℕ∞) < m}

/-- PDF pp.4–5: coefficient adapter to the accepted bounded-operator TraceHasSum.
The coefficient trace-class guards exclude an invalid-array zero fallback. -/
def coefficientTraceHasSum {I K : Type} (X : K → Matrix I I ℂ) (Y : Matrix I I ℂ) : Prop :=
  IsTraceClass Y ∧ (∀ k, IsTraceClass (X k)) ∧
    QAlgorithms.Papers.Independent.Dependency50.P39.TraceHasSum
      (fun k => boundedOperator (X k)) (boundedOperator Y)

/-- Definition 3, PDF pp.5–6: outputs lie in the trace-closed convex hull of
normalized pure states with Schmidt rank at most r, for every separable ancilla. -/
def PartiallyEntanglementBreaking {I J : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (r : ℕ) : Prop :=
  ∀ (K : Type) [Countable K] [Nonempty K] (rho : State (I × K)),
    tensorApply Phi rho.coefficients ∈ traceClosure
      (convexHull ℝ {X : Matrix (J × K) (J × K) ℂ |
        ∃ u : Hilbert (J × K), ‖u‖ = 1 ∧ tensorRankLE r u ∧ X = rankOne u})

/-- The explanatory paragraph after Theorem 3, PDF p.8: every ancilla output
has an actual countable pure Schmidt-rank-r decomposition, stronger than merely
belonging to the closed Schmidt class. Zero weights include finite mixtures. -/
def CountableSchmidtOutputs {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (r : ℕ) : Prop :=
  ∀ (K : Type) [Countable K] [Nonempty K] (rho : State (I × K)),
    ∃ (w : ℕ → ℝ) (u : ℕ → Hilbert (J × K)),
      (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧ (∀ i, ‖u i‖ = 1 ∧ tensorRankLE r (u i)) ∧
      coefficientTraceHasSum (fun i => (w i : ℂ) • rankOne (u i)) (tensorApply Phi rho.coefficients)

/-- PDF pp.8,20: actual countable Kraus representation, count and rank bounds. -/
def HasBoundedRankKraus {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (r : ℕ) (bound : ℕ∞) : Prop :=
  ∃ (K : Type) (_ : Countable K) (V : K → (Hilbert I →L[ℂ] Hilbert J)),
    dimensionCount K ≤ bound ∧ IsKrausRepresentation Phi V ∧ ∀ k, operatorRank (V k) ≤ r

/-- PDF pp.13–15: orthogonality of the state supports. -/
def StatesOrthogonal {I : Type} (rho sigma : State I) : Prop :=
  (boundedOperator rho.coefficients).comp (boundedOperator sigma.coefficients) = 0

/-- Definition 6 as used in Lemmas 4–5, PDF pp.13–15: no two nonempty mutually
orthogonal subfamilies partition S. Unused ambient subspaces do not split S. -/
def OrthogonallyNondecomposable {I : Type} (S : Set (State I)) : Prop :=
  ∀ T ⊆ S, T.Nonempty → (S \ T).Nonempty →
    ∃ rho ∈ T, ∃ sigma ∈ S \ T, ¬ StatesOrthogonal rho sigma

/-- Lemma 5 proof, PDF pp.14–15: states reachable by finite nonorthogonal chains. -/
def connectedComponent {I : Type} (S : Set (State I)) (rho : State I) : Set (State I) :=
  {sigma | rho ∈ S ∧ sigma ∈ S ∧ Relation.ReflTransGen
    (fun a b : State I => a ∈ S ∧ b ∈ S ∧ ¬ StatesOrthogonal a b) rho sigma}

/-- PDF pp.14–15: canonical component collection; empty for the empty family. -/
def componentSets {I : Type} (S : Set (State I)) : Set (Set (State I)) :=
  {C | ∃ rho ∈ S, C = connectedComponent S rho}

/-- PDF p.15: canonical nonempty-component labels. -/
abbrev Component {I : Type} (S : Set (State I)) := {C // C ∈ componentSets S}

/-- PDF p.15: component projections are computed from S, never freely supplied. -/
def componentProjection {I : Type} (S : Set (State I)) (k : Component S) :
    Hilbert I →L[ℂ] Hilbert I := familyProjection k.val

/-- Lemma 5, PDF pp.14–15: nonempty disjoint OND pieces, orthogonal across pieces.
Set-valued partitions encode uniqueness up to relabeling. -/
def IsONDPartition {I : Type} (S : Set (State I)) (parts : Set (Set (State I))) : Prop :=
  ⋃₀ parts = S ∧ (∀ C ∈ parts, C.Nonempty ∧ OrthogonallyNondecomposable C) ∧
  (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D ∧
    ∀ rho ∈ C, ∀ sigma ∈ D, StatesOrthogonal rho sigma)

/-- PDF pp.11–12: pure-state family of a vector system; phases are immaterial. -/
def vectorStates {I L : Type} (v : L → Hilbert I) : Set (State I) :=
  {rho | ∃ i, rho.coefficients = rankOne (v i)}

/-- PDF pp.11–12: orthonormality plus strong Parseval completeness. -/
def OrthonormalBasisFamily {I L : Type} (v : L → Hilbert I) : Prop :=
  Orthonormal ℂ v ∧ IsParsevalFrame v

/-- PDF pp.12,15,20–21: nonzero orthogonal projections strongly summing to identity. -/
def OrthogonalResolution {I K : Type} (P : K → (Hilbert I →L[ℂ] Hilbert I)) : Prop :=
  (∀ k, (P k).adjoint = P k ∧ (P k).comp (P k) = P k ∧ P k ≠ 0) ∧
  (∀ k l, k ≠ l → (P k).comp (P l) = 0) ∧ ∀ x, HasSum (fun k => P k x) x

/-- PDF p.15(ii): all block-diagonal states, with trace-norm pinching sum. -/
def blockDiagonalStates {I K : Type} (P : K → (Hilbert I →L[ℂ] Hilbert I)) : Set (State I) :=
  {rho | coefficientTraceHasSum (fun k => conjugateCoeff (P k) rho.coefficients) rho.coefficients}

/-- PDF p.21, Corollary 4(i): all pure states within individual blocks. -/
def blockPureStates {I K : Type} (P : K → (Hilbert I →L[ℂ] Hilbert I)) : Set (State I) :=
  {rho | rho ∈ pureStates I ∧ ∃ k, conjugateCoeff (P k) rho.coefficients = rho.coefficients}

/-- PDF pp.11,15: c-q/block measure-and-prepare form with normalized sigma_k,
correct ranks and trace-norm output convergence on the entire trace class. -/
def HasBlockCQForm {I E K : Type} (Psi : Matrix I I ℂ → Matrix E E ℂ)
    (P : K → (Hilbert I →L[ℂ] Hilbert I)) (m : ℕ∞) : Prop :=
  ∃ sigma : K → State E, (∀ k, operatorRank (boundedOperator (sigma k).coefficients) ≤ m) ∧
    ∀ X, IsTraceClass X → coefficientTraceHasSum
      (fun k => boundedTracePair X (P k) • (sigma k).coefficients) (Psi X)

/-- PDF pp.11–12,15: rowwise orthogonality and squared norms summing to one.
Zero vectors allow padding a smaller spectral decomposition to m labels. -/
def NormalizedOrthogonalRows {K M E : Type} (psi : K → M → Hilbert E) : Prop :=
  (∀ k, HasSum (fun p => ‖psi k p‖ ^ 2) 1) ∧
  ∀ k p t, p ≠ t → inner ℂ (psi k t) (psi k p) = 0

/-- PDF p.15(iv): exactly <psi_t^l|psi_p^k>, in H_A tensor H_m coordinates. -/
def blockNormalMap {I K M E : Type} (P : K → (Hilbert I →L[ℂ] Hilbert I))
    (psi : K → M → Hilbert E) (X : Matrix I I ℂ) : Matrix (I × M) (I × M) ℂ :=
  fun a b => ∑' k, ∑' l,
    operatorCoeff ((P k).comp ((boundedOperator X).comp (P l))) a.1 b.1 *
      inner ℂ (psi l b.2) (psi k a.2)

/-- PDF pp.11–12,15(iv): displayed CPTP normal form and both partial-isometry
identities. The condition is a conclusion, not an extra source hypothesis. -/
def HasBlockNormalForm {I J K : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (P : K → (Hilbert I →L[ℂ] Hilbert I)) (m : ℕ∞) : Prop :=
  ∃ (E : Type) (_ : Countable E) (_ : Nonempty E) (psi : K → BoundIndex m → Hilbert E),
    NormalizedOrthogonalRows psi ∧ IsTraceClassChannel (blockNormalMap P psi) ∧
    IsometricallyEquivalent Phi (blockNormalMap P psi)

/-- PDF pp.17–18: unitary equivalence on the entire output spaces. -/
def UnitarilyEquivalent {I J K : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (Theta : Matrix I I ℂ → Matrix K K ℂ) : Prop :=
  ∃ U : Hilbert K ≃ₗᵢ[ℂ] Hilbert J, ∀ X, IsTraceClass X →
    Phi X = conjugateCoeff U.toLinearIsometry.toContinuousLinearMap (Theta X)

/-- PDF pp.17–18: c_kl=<psi_l|psi_k>, retaining the source conjugation order. -/
def gramNormalMap {I K E : Type} (P : K → (Hilbert I →L[ℂ] Hilbert I))
    (psi : K → Hilbert E) (X : Matrix I I ℂ) : Matrix I I ℂ :=
  fun a b => ∑' k, ∑' l, inner ℂ (psi l) (psi k) *
    operatorCoeff ((P k).comp ((boundedOperator X).comp (P l))) a b

/-- PDF p.17: Gram form; the no-zero-entry clause is conditional on dual injectivity. -/
def HasGramNormalForm {I J K : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (P : K → (Hilbert I →L[ℂ] Hilbert I)) (nonzero : Prop) : Prop :=
  ∃ (E : Type) (_ : Countable E) (_ : Nonempty E) (psi : K → Hilbert E),
    (∀ k, ‖psi k‖ = 1) ∧ (nonzero → ∀ k l, inner ℂ (psi l) (psi k) ≠ 0) ∧
    IsTraceClassChannel (gramNormalMap P psi) ∧ UnitarilyEquivalent Phi (gramNormalMap P psi)

/-- PDF p.17: ker Phi*={0} on all bounded operators. -/
def DualInjective {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) : Prop :=
  ∀ B, channelDual Phi B = 0 → B = 0

/-- PDF p.17: the two advertised channel conditions are alternatives. -/
def SimplifiedRegime {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) : Prop :=
  DualInjective Phi ∨ (dimensionCount I = dimensionCount J ∧ dimensionCount I < ⊤)

/-- PDF pp.8,17: arbitrary strictly positive normalized weights. -/
def PositiveLaw {L : Type} (pi : L → ℝ) : Prop := (∀ i, 0 < pi i) ∧ HasSum pi 1

/-- Equation (9), PDF p.8: computed barycenter, not an arbitrary free parameter. -/
def vectorAverage {I L : Type} (pi : L → ℝ) (v : L → Hilbert I) : Matrix I I ℂ :=
  fun a b => ∑' i, (pi i : ℂ) * rankOne (v i) a b

/-- PDF p.8(9): inverse square root on its spectral domain, defined by its unique
least-norm preimage. Off-domain fallback is zero; theorems assert domain membership
through the defining equation, never as an additional input hypothesis. -/
def inverseRootImage {I : Type} (X : Matrix I I ℂ) (v : Hilbert I) : Hilbert I :=
  if h : ∃ u : Hilbert I, positiveSquareRoot (boundedOperator X) u = v ∧
      u ∈ (LinearMap.ker (positiveSquareRoot (boundedOperator X)).toLinearMap)ᗮ then h.choose else 0

/-- PDF p.8(9): sqrt(pi_i rho_bar^{-1})v_i, with inverse exponent -1/2. -/
def whitenedVector {I L : Type} (pi : L → ℝ) (v : L → Hilbert I) (i : L) : Hilbert I :=
  inverseRootImage (vectorAverage pi v) ((Real.sqrt (pi i) : ℂ) • v i)

/-- PDF p.8(8): computed frame and orthogonal spectral rows, both output series
in trace norm. The inverse equation explicitly excludes an off-domain fallback. -/
def HasWhitenedForm {I E L : Type} (Psi : Matrix I I ℂ → Matrix E E ℂ)
    (pi : L → ℝ) (v : L → Hilbert I) (m : ℕ∞) : Prop :=
  (∀ i, positiveSquareRoot (boundedOperator (vectorAverage pi v)) (whitenedVector pi v i) =
    (Real.sqrt (pi i) : ℂ) • v i) ∧ IsParsevalFrame (whitenedVector pi v) ∧
  ∃ psi : L → BoundIndex m → Hilbert E, NormalizedOrthogonalRows psi ∧
    ∃ sigma : L → Matrix E E ℂ,
      (∀ i, coefficientTraceHasSum (fun k => rankOne (psi i k)) (sigma i)) ∧
      ∀ X, IsTraceClass X → coefficientTraceHasSum (fun i => boundedTracePair X
        (boundedOperator (rankOne (whitenedVector pi v i))) • sigma i) (Psi X)

/-- PDF pp.16–17,25: ordered partial sums, allowing conditional basis expansions. -/
def orderedPartialSum {I : Type} {n : ℕ∞} (v : BoundIndex n → Hilbert I)
    (c : BoundIndex n → ℂ) (N : ℕ) : Hilbert I :=
  ∑ i ∈ Finset.range N, if h : (i : ℕ∞) < n then c ⟨i, h⟩ • v ⟨i, h⟩ else 0

/-- PDF pp.16–17,25: unique convergent-expansion basis; neither Hamel nor ONB. -/
def UniqueConvergentBasis {I : Type} {n : ℕ∞} (v : BoundIndex n → Hilbert I) : Prop :=
  ∀ x : Hilbert I, ∃! c : BoundIndex n → ℂ,
    Tendsto (fun N => orderedPartialSum v c N) atTop (nhds x)

/-- PDF pp.6–7: support projection on arbitrary completed countable coordinates.
The accepted Information100.P06 supportProjection returns a finite matrix and
cannot represent this domain. This coefficient adapter uses Mathlib's closed-range projection. -/
def coefficientSupportProjection {I : Type} (X : Matrix I I ℂ) : Hilbert I →L[ℂ] Hilbert I :=
  ((LinearMap.range (boundedOperator X).toLinearMap).topologicalClosure).starProjection

/-- PDF pp.6–7,23–24: the supported solution B of S_out B S_out =
Phi(S_in A S_in). It is unique and bounded for CPTP Phi and a reference state,
even when S_out has no bounded inverse. Off this domain the total fallback is zero.
No recovery property is assumed in this definition. -/
def petzSupportedDual {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (sigma : Matrix I I ℂ) (A : Hilbert I →L[ℂ] Hilbert I) : Hilbert J →L[ℂ] Hilbert J :=
  if h : ∃ B : Hilbert J →L[ℂ] Hilbert J,
      (coefficientSupportProjection (Phi sigma)).comp (B.comp (coefficientSupportProjection (Phi sigma))) = B ∧
      (positiveSquareRoot (boundedOperator (Phi sigma))).comp (B.comp (positiveSquareRoot (boundedOperator (Phi sigma)))) =
        boundedOperator (Phi (operatorCoeff ((positiveSquareRoot (boundedOperator sigma)).comp
          (A.comp (positiveSquareRoot (boundedOperator sigma)))))) then h.choose else 0

/-- PDF pp.6–7: explicit extension off output support; the predual prepares sigma
from the trace outside that support. This makes the total map unital on the dual. -/
def petzExtendedDual {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (sigma : Matrix I I ℂ) (A : Hilbert I →L[ℂ] Hilbert I) : Hilbert J →L[ℂ] Hilbert J :=
  petzSupportedDual Phi sigma A + boundedTracePair sigma A •
    (ContinuousLinearMap.id ℂ (Hilbert J) - coefficientSupportProjection (Phi sigma))

/-- PDF pp.6–7,23–24: computed predual, specified by every matrix-unit pairing. -/
def petzRecovery {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (sigma : Matrix I I ℂ) (X : Matrix J J ℂ) : Matrix I I ℂ :=
  fun i j => boundedTracePair X (petzExtendedDual Phi sigma (boundedOperator (Matrix.single j i (1 : ℂ))))

/-- PDF p.18: finite or countable discrete ensemble; zero weights are allowed. -/
structure DiscreteEnsemble (I : Type) where
  weight : ℕ → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  probability : HasSum weight 1
  state : ℕ → State I

/-- PDF p.18: the actual probability mass function of the normalized weights. -/
def discreteProbabilityLaw {I : Type} (e : DiscreteEnsemble I) : PMF ℕ := by
  have hsum : ∑' i, ENNReal.ofReal (e.weight i) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg e.nonneg e.probability.summable,
      e.probability.tsum_eq]
    simp
  exact ⟨fun i => ENNReal.ofReal (e.weight i), hsum ▸ ENNReal.summable.hasSum⟩

/-- PDF p.18: coefficient adapter to the accepted operator barycenter.
No independent average variable or new summation convention is introduced. -/
def discreteAverageCoefficients {I : Type} (e : DiscreteEnsemble I) : Matrix I I ℂ :=
  operatorCoeff (QAlgorithms.Papers.Independent.Renew46.P46.discreteAverage
    (fun i => boundedOperator (e.state i).coefficients) (discreteProbabilityLaw e))

/-- PDF pp.18–19: relative-entropy Holevo functional in nats, including infinity.
Zero weights times infinite relative entropy contribute zero. -/
def discreteHolevo {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (e : DiscreteEnsemble I) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (e.weight i) * extendedRelativeEntropyNats
    (Phi (e.state i).coefficients) (Phi (discreteAverageCoefficients e))

/-- PDF p.19: recovery family with zero-weight entries removed. -/
def activeStates {I : Type} (e : DiscreteEnsemble I) : Set (State I) :=
  {rho | ∃ i, 0 < e.weight i ∧ rho = e.state i}

/-- PDF pp.7,20,22: full rank means zero kernel, without a bounded inverse. -/
def FullRank {I : Type} (X : Matrix I I ℂ) : Prop :=
  ∀ x : Hilbert I, boundedOperator X x = 0 → x = 0

/-- PDF p.19: entropy gain, used only when both entropies are finite. -/
def finiteEntropyGain {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix I I ℂ) : ℝ :=
  (extendedEntropyNats (Phi X)).toReal - (extendedEntropyNats X).toReal

/-- PDF p.22(21): conditional entropy in nats on arbitrary countable coordinates;
discard the FIRST factor and retain B. The accepted Dependency50.P15 definition
is for finite matrices in bits, so it cannot represent this source domain. -/
def separableConditionalEntropyNats {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : ℝ :=
  (extendedEntropyNats X).toReal - (extendedEntropyNats (traceFirst X)).toReal

/-- PDF p.21: all four explicit clauses of Theorem 4 for the resolution P.
This predicate is a conclusion, never a premise substituting for the theorem. -/
def ResolutionClassification {I J E K : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (Psi : Matrix I I ℂ → Matrix E E ℂ) (P : K → (Hilbert I →L[ℂ] Hilbert I)) : Prop :=
  ReversibleOn Phi (blockPureStates P) ∧ ReversibleOn Phi (blockDiagonalStates P) ∧
    HasBlockCQForm Psi P (rankMultiplicity Phi 1) ∧ HasBlockNormalForm Phi P (rankMultiplicity Phi 1)

/-- PDF p.13(13): append a fixed normalized mixed state on a completed tensor. -/
def appendingMap {I K : Type} (sigma : State K) (X : Matrix I I ℂ) :
    Matrix (I × K) (I × K) ℂ := productCoeff X sigma.coefficients

/-- PDF p.21: strongly continuous unitary group action, irreducible on the whole
finite-dimensional Hilbert space, rather than just one commuting pair. -/
def IrreducibleUnitaryAction {I G : Type} [Group G] [TopologicalSpace G]
    (V : G → (Hilbert I ≃ₗᵢ[ℂ] Hilbert I)) : Prop :=
  (∀ x, V 1 x = x) ∧ (∀ g h x, V (g * h) x = V g (V h x)) ∧
  (∀ x, Continuous (fun g => V g x)) ∧
  ∀ M : Submodule ℂ (Hilbert I), (∀ g x, x ∈ M → V g x ∈ M) → M = ⊥ ∨ M = ⊤

/-! Sanity examples for the complete local definitions. -/

/-- Domain sanity: the inverse-square-root choice satisfies its equation whenever
that equation has a supported solution; no off-domain value is used here. -/
example {I : Type} (X : Matrix I I ℂ) (v : Hilbert I)
    (h : ∃ u : Hilbert I, positiveSquareRoot (boundedOperator X) u = v ∧
      u ∈ (LinearMap.ker (positiveSquareRoot (boundedOperator X)).toLinearMap)ᗮ) :
    positiveSquareRoot (boundedOperator X) (inverseRootImage X v) = v := by
  rw [inverseRootImage, dif_pos h]
  exact h.choose_spec.1

example : dimensionCount (Fin 0) = 0 := by simp [dimensionCount]

example : dimensionCount ℕ = ⊤ := by simp [dimensionCount]

example {I : Type} : componentSets (∅ : Set (State I)) = ∅ := by
  ext C
  simp [componentSets]

example {I : Type} : OrthogonallyNondecomposable (∅ : Set (State I)) := by
  intro T hT hnonempty
  obtain ⟨rho, hrho⟩ := hnonempty
  exact (hT hrho).elim

example {I : Type} {n : ℕ∞} (v : BoundIndex n → Hilbert I) (c : BoundIndex n → ℂ) :
    orderedPartialSum v c 0 = 0 := by simp [orderedPartialSum]

example {I : Type} (X : Matrix I I ℂ) (v : Hilbert I)
    (h : ¬ ∃ u : Hilbert I, positiveSquareRoot (boundedOperator X) u = v ∧
      u ∈ (LinearMap.ker (positiveSquareRoot (boundedOperator X)).toLinearMap)ᗮ) :
    inverseRootImage X v = 0 := by simp [inverseRootImage, h]

example {I J : Type} (Phi : Matrix I I ℂ → Matrix J J ℂ) (X : Matrix I I ℂ) :
    petzExtendedDual Phi X (0 : Hilbert I →L[ℂ] Hilbert I) =
      petzSupportedDual Phi X 0 := by
  simp [petzExtendedDual, boundedTracePair, operatorCoeff]

example {I K : Type} (sigma : State K) (X : Matrix I I ℂ) (a b : I × K) :
    appendingMap sigma X a b = X a.1 b.1 * sigma.coefficients a.2 b.2 := rfl

/-- Equation (12), PDF p.12: P tensor identity, on completed tensor coordinates. -/
def tensorIdentityEffect {I M : Type} (P : Hilbert I →L[ℂ] Hilbert I) :
    Hilbert (I × M) →L[ℂ] Hilbert (I × M) :=
  boundedOperator (fun a b => operatorCoeff P a.1 b.1 * (if a.2 = b.2 then 1 else 0))

example {I M : Type} (P : Hilbert I →L[ℂ] Hilbert I) :
    tensorIdentityEffect (M := M) P =
      boundedOperator (fun a b => operatorCoeff P a.1 b.1 * (if a.2 = b.2 then 1 else 0)) := rfl

end QAlgorithms.Papers.Independent.Gap48.P45


