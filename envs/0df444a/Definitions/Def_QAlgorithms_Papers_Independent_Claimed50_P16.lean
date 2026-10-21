-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16
-- name    : QAlgorithms_Papers_Independent_Claimed50_P16
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:44:01.767781+00:00
-- url     : https://prove2.me/theorems/b6cb8875-9539-4b0c-b38c-67ec9e5e32eb
-- title:
--   Definitions for The Schmidt number and partially entanglement breaking channels in infinite dimensions
-- statement:
--   The objects the formalized statements of *The Schmidt number and partially entanglement breaking channels in infinite dimensions* (arXiv:1110.4363) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tensorRankLE`: PDF p.5: finite Schmidt rank means a sum of k simple tensors in the completed tensor.
--   - `schmidtRank`: PDF p.5: pure Schmidt rank including infinity; representatives are normalized.
--   - `barycenterFiber`: PDF pp.4,13: Borel probability laws supported on A with the specified barycenter.
--   - `extremeFiber`: PDF pp.6,14: extremality within the fixed-barycenter fiber, not all probability laws.
--   - `continuousSchmidtNumber`: PDF p.5, (2): continuous Schmidt number. Empty extended infima equal infinity.
--   - `schmidtClass`: PDF pp.6–7: mixed Schmidt class, explicitly empty at k=0.
--   - `pureClass`: PDF p.7: pure class defined directly using rank.
--   - `stateHull`: PDF p.4: trace-norm closed convex hull in the ambient real operator space.
--   - `stateConvex`: PDF p.4: real affine convexity of density operators.
--   - `pureEnsemble`: PDF pp.4–5: pure ensemble. Zero weights allow finite ensembles; component rank consequences below explicitly require positive weight.
--   - `discreteSchmidtNumber`: PDF p.5, (1): countable-ensemble roof, ignoring zero-weight terms.
--   - `arrayRankLE`: PDF p.6: algebraic array rank equals operator rank for bounded operators. Finite operator rank does not imply finite pure Schmidt rank.
--   - `positiveArray`: PDF pp.7–9: positivity of every finite quadratic form, including reality; usable for infinite slice amplifications without assuming global trace class.
--   - `noFinitePurePart`: PDF p.7: absence of positive pure suboperators of finite Schmidt rank.
--   - `allEnsembleRanksInfinite`: PDF p.7: every positive-weight component in every countable pure ensemble.
--   - `edgeState`: PDF p.9: edge condition against all mixed states in S_(k-1), not only pure ones.
--   - `BoundedOp`: PDF p.4: genuine bounded operators on coordinate Hilbert spaces.
--   - `opCoeff`: PDF p.4: bounded-operator matrix coefficients in the specified basis.
--   - `traceClassConjugation`: PDF pp.6,12: V X V*, evaluated on trace-class inputs.
--   - `tracePair`: PDF p.9: real trace pairing of bounded W and trace-class X.
--   - `witness`: PDF p.9: bounded Hermitian witness detecting rho.
--   - `projectionApproximation`: PDF p.6: increasing finite-rank orthogonal projections converging strongly to identity.
--   - `localProjectionCompression`: PDF p.6: (P tensor Q) rho (P tensor Q).
--   - `compressionMass`: PDF p.6: mass of a positive trace-class local compression.
--   - `edgeDecomposition`: PDF p.8: edge decomposition, meaningful also at p=0 and p=1.
--   - `inKernel`: PDF p.9: kernel of a trace-class operator via its convergent coordinate action.
--   - `faithful`: PDF p.10: full rank means zero kernel, without a uniform inverse bound.
--   - `TraceMap`: PDF p.8: bounded complex-linear trace-class maps, canonically zero-extended outside trace class. Canonical extension prevents spurious unequal channels.
--   - `kPositive`: PDF p.8: k-positivity, without a trace-preservation condition.
--   - `completelyPositive`: PDF p.10: CP tests all finite ancillary dimensions.
--   - `CanonicalChannel`: PDF p.4: use the frozen infinite-dimensional channel type, choosing its unique zero extension outside trace class. This removes irrelevant raw-function choices so that the Choi correspondence is a homeomorphism of actual channels.
--   - `canonicalChannelAction`: PDF p.4: action of the canonical representative of a frozen channel.
--   - `classArray`: PDF p.10: Schmidt-class membership for a coefficient array includes normalization.
--   - `isPEB`: PDF p.10: every separable ancilla and every input state; no Kraus restriction.
--   - `pebConvex`: PDF p.10: real affine convexity relative to the set of channels.
--   - `cpComposition`: PDF p.10: complete positivity of L composed with Phi via finite amplifications.
--   - `supportedInput`: PDF p.11: slice columns in a closed input subspace characterize support in S tensor ancilla; finite-dimensionality of S is not required.
--   - `restrictionPEB`: PDF p.11: k-PEB restriction to the indicated Hilbert input subspace.
--   - `krausRepresentation`: PDF p.12, (5): countable Kraus representation; strong sum V*V=I and trace-norm sum on every trace-class input. Zero entries are permitted.
--   - `roof`: PDF p.13, (6): essential-supremum roof, used on the closed convex hull of A.
--   - `positiveTranslationConjugation`: PDF p.15: V_u phi(x)=phi(x+u). Reverse the parameter of the frozen negative-phase translation; this gives exactly the source's positive Fourier phase.
--   - `circleState`: PDF p.15, (9): specified normalized full-period correlated rotation twirl.
--   - `aeIndependent`: PDF p.17: independence modulo a.e. equality, without any integrability assumption.
--   - `omegaCoeff`: PDF p.18: Omega coefficients in H1 tensor (H2 tensor K), normalized by 1/sqrt(k).
--   - `shortTwirl`: PDF p.18, (15): short-interval twirl with normalization n/(2pi), for n>0.
--   - `pureStateFromRange`: PDF p.5: the frozen range of pure states and the frozen pure-state subtype describe the same normalized density, without choosing its vector phase.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, https://arxiv.org/abs/1110.4363v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

/-!
arXiv:1110.4363v3, Shirokov. Statements; compilation pending batch handoff.
Countable basis coordinates cover all separable complex Hilbert spaces and their
completed tensor products. P33 supplies normalized trace-class states, trace norm
and Borel barycenters. Compatible frozen interfaces are imported; distinct
definitions and canonical-channel adapters are local. Proposition 2 is deferred.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)
open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- PDF p.5: finite Schmidt rank means a sum of k simple tensors in the completed tensor. -/
def tensorRankLE {I J : Type} (k : ℕ) (u : Hilbert (I × J)) : Prop :=
  ∃ (a : Fin k → Hilbert I) (b : Fin k → Hilbert J),
    ∀ i j, u (i, j) = ∑ t, a t i * b t j

/-- PDF p.5: pure Schmidt rank including infinity; representatives are normalized. -/
def schmidtRank {I J : Type} (rho : PureState (I × J)) : ℝ≥0∞ :=
  ⨅ k : {k : ℕ // ∃ u : Hilbert (I × J),
    ‖u‖ = 1 ∧ rho.val.coefficients = rankOne u ∧ tensorRankLE k u}, (k.val : ℝ≥0∞)

/-- PDF pp.4,13: Borel probability laws supported on A with the specified barycenter. -/
def barycenterFiber {I : Type} (A : Set (State I)) (rho : State I) : Set (Measure A) :=
  {mu | IsProbabilityMeasure mu ∧
    IsBarycenter mu (fun x : A => x.val.coefficients) rho.coefficients}

/-- PDF pp.6,14: extremality within the fixed-barycenter fiber, not all probability laws. -/
def extremeFiber {I : Type} {A : Set (State I)} (rho : State I) (mu : Measure A) : Prop :=
  mu ∈ barycenterFiber A rho ∧ ∀ nu ∈ barycenterFiber A rho, ∀ xi ∈ barycenterFiber A rho,
    ∀ a : ℝ, 0 < a → a < 1 →
      mu = ENNReal.ofReal a • nu + ENNReal.ofReal (1 - a) • xi → nu = mu ∧ xi = mu

/-- PDF p.5, (2): continuous Schmidt number. Empty extended infima equal infinity. -/
def continuousSchmidtNumber {I J : Type} (rho : State (I × J)) : ℝ≥0∞ :=
  ⨅ mu : {mu : Measure (PureState (I × J)) //
    IsProbabilityMeasure mu ∧ IsBarycenter mu
      (fun x : PureState (I × J) => x.val.coefficients) rho.coefficients},
    essSup schmidtRank mu.val

/-- PDF pp.6–7: mixed Schmidt class, explicitly empty at k=0. -/
def schmidtClass (I J : Type) (k : ℕ) : Set (State (I × J)) :=
  {rho | 0 < k ∧ continuousSchmidtNumber rho ≤ (k : ℝ≥0∞)}

/-- PDF p.7: pure class defined directly using rank. -/
def pureClass (I J : Type) (k : ℕ) : Set (State (I × J)) :=
  {rho | ∃ h : ∃ u : Hilbert (I × J), ‖u‖ = 1 ∧ rho.coefficients = rankOne u,
    schmidtRank ⟨rho, h⟩ ≤ (k : ℝ≥0∞)}

/-- PDF p.4: trace-norm closed convex hull in the ambient real operator space. -/
def stateHull {I : Type} (A : Set (State I)) : Set (State I) :=
  {rho | rho.coefficients ∈ traceClosure (convexHull ℝ (State.coefficients '' A))}

/-- PDF p.4: real affine convexity of density operators. -/
def stateConvex {I : Type} (A : Set (State I)) : Prop :=
  Convex ℝ (State.coefficients '' A)

/-- PDF pp.4–5: pure ensemble. Zero weights allow finite ensembles; component
rank consequences below explicitly require positive weight. -/
def pureEnsemble {I : Type} (rho : State I) (w : ℕ → ℝ) (s : ℕ → PureState I) : Prop :=
  (∀ i, 0 ≤ w i) ∧ Summable w ∧ (∑' i, w i) = 1 ∧
    ∀ a b, rho.coefficients a b = ∑' i, (w i : ℂ) * (s i).val.coefficients a b

/-- PDF p.5, (1): countable-ensemble roof, ignoring zero-weight terms. -/
def discreteSchmidtNumber {I J : Type} (rho : State (I × J)) : ℝ≥0∞ :=
  ⨅ e : {e : (ℕ → ℝ) × (ℕ → PureState (I × J)) // pureEnsemble rho e.1 e.2},
    ⨆ i : {i : ℕ // 0 < e.val.1 i}, schmidtRank (e.val.2 i.val)

/-- PDF p.6: algebraic array rank equals operator rank for bounded operators.
Finite operator rank does not imply finite pure Schmidt rank. -/
def arrayRankLE {I J : Type} (k : ℕ) (X : Matrix J I ℂ) : Prop :=
  ∃ (a : Fin k → J → ℂ) (b : Fin k → I → ℂ),
    ∀ i j, X i j = ∑ t, a t i * b t j

/-- PDF pp.7–9: positivity of every finite quadratic form, including reality;
usable for infinite slice amplifications without assuming global trace class. -/
def positiveArray {I : Type} (X : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re

/-- PDF p.7: absence of positive pure suboperators of finite Schmidt rank. -/
def noFinitePurePart {I J : Type} (rho : State (I × J)) : Prop :=
  ∀ sigma : PureState (I × J), schmidtRank sigma < ⊤ →
    ∀ t : ℝ, 0 < t → ¬ positiveArray (rho.coefficients - (t : ℂ) • sigma.val.coefficients)

/-- PDF p.7: every positive-weight component in every countable pure ensemble. -/
def allEnsembleRanksInfinite {I J : Type} (rho : State (I × J)) : Prop :=
  ∀ w s, pureEnsemble rho w s → ∀ i, 0 < w i → schmidtRank (s i) = ⊤

/-- PDF p.9: edge condition against all mixed states in S_(k-1), not only pure ones. -/
def edgeState {I J : Type} (k : ℕ) (delta : State (I × J)) : Prop :=
  (k : ℝ≥0∞) ≤ continuousSchmidtNumber delta ∧
    ∀ sigma ∈ schmidtClass I J (k - 1), ∀ t : ℝ, 0 < t →
      ¬ positiveArray (delta.coefficients - (t : ℂ) • sigma.coefficients)

/-- PDF p.4: genuine bounded operators on coordinate Hilbert spaces. -/
abbrev BoundedOp (I J : Type) := Hilbert I →L[ℂ] Hilbert J

/-- PDF p.4: bounded-operator matrix coefficients in the specified basis. -/
def opCoeff {I J : Type} (T : BoundedOp I J) : Matrix J I ℂ :=
  fun i j => (T (lp.single 2 j (1 : ℂ))) i

/-- PDF pp.6,12: V X V*, evaluated on trace-class inputs. -/
def traceClassConjugation {I J : Type} (V : BoundedOp I J) (X : Matrix I I ℂ) : Matrix J J ℂ :=
  fun p q => ∑' i, ∑' j, opCoeff V p i * X i j * star (opCoeff V q j)

/-- PDF p.9: real trace pairing of bounded W and trace-class X. -/
def tracePair {I : Type} (W : BoundedOp I I) (X : Matrix I I ℂ) : ℝ :=
  (∑' i, ∑' j, opCoeff W i j * X j i).re

/-- PDF p.9: bounded Hermitian witness detecting rho. -/
def witness {I J : Type} (k : ℕ) (rho : State (I × J))
    (W : BoundedOp (I × J) (I × J)) : Prop :=
  W.adjoint = W ∧
    (∀ sigma ∈ schmidtClass I J (k - 1), 0 ≤ tracePair W sigma.coefficients) ∧
    tracePair W rho.coefficients < 0

/-- PDF p.6: increasing finite-rank orthogonal projections converging strongly to identity. -/
def projectionApproximation {I : Type} (P : ℕ → BoundedOp I I) : Prop :=
  (∀ n, (P n).adjoint = P n ∧ (P n).comp (P n) = P n ∧ ∃ k, arrayRankLE k (opCoeff (P n))) ∧
  (∀ n, (P (n + 1)).comp (P n) = P n) ∧
  ∀ v, Tendsto (fun n => P n v) atTop (nhds v)

/-- PDF p.6: (P tensor Q) rho (P tensor Q). -/
def localProjectionCompression {I J : Type} (P : BoundedOp I I) (Q : BoundedOp J J)
    (rho : State (I × J)) : Matrix (I × J) (I × J) ℂ :=
  fun p q => ∑' i : I × J, ∑' j : I × J,
    (opCoeff P p.1 i.1 * opCoeff Q p.2 i.2) * rho.coefficients i j *
      star (opCoeff P q.1 j.1 * opCoeff Q q.2 j.2)

/-- PDF p.6: mass of a positive trace-class local compression. -/
def compressionMass {I J : Type} (P : BoundedOp I I) (Q : BoundedOp J J)
    (rho : State (I × J)) : ℝ := ∑' i, (localProjectionCompression P Q rho i i).re

/-- PDF p.8: edge decomposition, meaningful also at p=0 and p=1. -/
def edgeDecomposition {I J : Type} (k : ℕ) (rho eta delta : State (I × J)) (p : ℝ) : Prop :=
  p ∈ Set.Icc 0 1 ∧ eta ∈ schmidtClass I J (k - 1) ∧ edgeState k delta ∧
    rho.coefficients = ((1 - p : ℝ) : ℂ) • eta.coefficients + (p : ℂ) • delta.coefficients

/-- PDF p.9: kernel of a trace-class operator via its convergent coordinate action. -/
def inKernel {I : Type} (X : Matrix I I ℂ) (v : Hilbert I) : Prop :=
  ∀ i, (∑' j, X i j * v j) = 0

/-- PDF p.10: full rank means zero kernel, without a uniform inverse bound. -/
def faithful {I : Type} (X : Matrix I I ℂ) : Prop :=
  ∀ v : Hilbert I, inKernel X v → v = 0

/-- PDF p.8: bounded complex-linear trace-class maps, canonically zero-extended
outside trace class. Canonical extension prevents spurious unequal channels. -/
structure TraceMap (I J : Type) where
  apply : Matrix I I ℂ → Matrix J J ℂ
  traceClass : ∀ X, IsTraceClass X → IsTraceClass (apply X)
  additive : ∀ X Y, IsTraceClass X → IsTraceClass Y → apply (X + Y) = apply X + apply Y
  homogeneous : ∀ (c : ℂ) X, IsTraceClass X → apply (c • X) = c • apply X
  bounded : ∃ M : ℝ≥0, ∀ X, IsTraceClass X → traceSize (apply X) ≤ (M : ℝ≥0∞) * traceSize X
  outside : ∀ X, ¬ IsTraceClass X → apply X = 0

/-- PDF p.8: k-positivity, without a trace-preservation condition. -/
def kPositive {I J : Type} (k : ℕ) (L : TraceMap I J) : Prop :=
  ∀ X : Matrix (I × Fin k) (I × Fin k) ℂ,
    IsTraceClass X → positiveArray X → positiveArray (tensorApply L.apply X)

/-- PDF p.10: CP tests all finite ancillary dimensions. -/
def completelyPositive {I J : Type} (L : TraceMap I J) : Prop := ∀ n, kPositive n L

/-- PDF p.4: use the frozen infinite-dimensional channel type, choosing its
unique zero extension outside trace class. This removes irrelevant raw-function
choices so that the Choi correspondence is a homeomorphism of actual channels. -/
abbrev CanonicalChannel (I J : Type) :=
  {Phi : QAlgorithms.Papers.Independent.Frontier18.P01.Channel I J //
    ∀ X, ¬ IsTraceClass X → Phi.val X = 0}

/-- PDF p.4: action of the canonical representative of a frozen channel. -/
def canonicalChannelAction {I J : Type} (Phi : CanonicalChannel I J) :
    Matrix I I ℂ → Matrix J J ℂ := Phi.val.val

/-- PDF p.10: Schmidt-class membership for a coefficient array includes normalization. -/
def classArray {I J : Type} (k : ℕ) (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ rho : State (I × J), rho.coefficients = X ∧ rho ∈ schmidtClass I J k

/-- PDF p.10: every separable ancilla and every input state; no Kraus restriction. -/
def isPEB {I J : Type} (k : ℕ) (Phi : CanonicalChannel I J) : Prop :=
  0 < k ∧ ∀ (A : Type) [Countable A] (rho : State (I × A)),
    classArray k (tensorApply (canonicalChannelAction Phi) rho.coefficients)

-- CanonicalChannel inherits the frozen pointwise trace-norm channel topology
-- through its subtype. No second channel topology is declared here.

/-- PDF p.10: real affine convexity relative to the set of channels. -/
def pebConvex (I J : Type) (k : ℕ) : Prop :=
  ∀ Phi Psi : CanonicalChannel I J, isPEB k Phi → isPEB k Psi →
    ∀ a : ℝ, a ∈ Set.Icc 0 1 → ∀ Xi : CanonicalChannel I J,
      (∀ X, IsTraceClass X → (canonicalChannelAction Xi) X = (a : ℂ) • (canonicalChannelAction Phi) X +
        ((1 - a : ℝ) : ℂ) • (canonicalChannelAction Psi) X) → isPEB k Xi

/-- PDF p.10: complete positivity of L composed with Phi via finite amplifications. -/
def cpComposition {I J : Type} (Phi : CanonicalChannel I J) (L : TraceMap J J) : Prop :=
  ∀ n (X : Matrix (I × Fin n) (I × Fin n) ℂ),
    IsTraceClass X → positiveArray X →
      positiveArray (tensorApply (fun Y => L.apply ((canonicalChannelAction Phi) Y)) X)

/-- PDF p.11: slice columns in a closed input subspace characterize support
in S tensor ancilla; finite-dimensionality of S is not required. -/
def supportedInput {I A : Type} (S : Submodule ℂ (Hilbert I)) (rho : State (I × A)) : Prop :=
  ∀ a j b, ∃ v : Hilbert I, v ∈ S ∧ ∀ i, v i = rho.coefficients (i, a) (j, b)

/-- PDF p.11: k-PEB restriction to the indicated Hilbert input subspace. -/
def restrictionPEB {I J : Type} (k : ℕ) (Phi : CanonicalChannel I J) (S : Submodule ℂ (Hilbert I)) : Prop :=
  ∀ (A : Type) [Countable A] (rho : State (I × A)), supportedInput S rho →
    classArray k (tensorApply (canonicalChannelAction Phi) rho.coefficients)

/-- PDF p.12, (5): countable Kraus representation; strong sum V*V=I and
trace-norm sum on every trace-class input. Zero entries are permitted. -/
def krausRepresentation {I J : Type} (Phi : CanonicalChannel I J) (V : ℕ → BoundedOp I J) : Prop :=
  (∀ v : Hilbert I, Tendsto (fun n => ∑ i ∈ Finset.range n,
    (V i).adjoint (V i v)) atTop (nhds v)) ∧
  ∀ X, IsTraceClass X → ∀ e : ℝ, 0 < e → ∃ N, ∀ n ≥ N,
    traceSize ((canonicalChannelAction Phi) X - ∑ i ∈ Finset.range n, traceClassConjugation (V i) X) < ENNReal.ofReal e

/-- PDF p.13, (6): essential-supremum roof, used on the closed convex hull of A. -/
def roof {I : Type} (A : Set (State I)) (f : A → ℝ≥0∞) (rho : State I) : ℝ≥0∞ :=
  ⨅ mu : {mu : Measure A // mu ∈ barycenterFiber A rho}, essSup f mu.val

/-- PDF p.15: V_u phi(x)=phi(x+u). Reverse the parameter of the frozen
negative-phase translation; this gives exactly the source's positive Fourier phase. -/
def positiveTranslationConjugation (x : ℝ) (X : Matrix ℤ ℤ ℂ) : Matrix ℤ ℤ ℂ :=
  QAlgorithms.Papers.Independent.Dependency50.P33.rotationCoeff (-x) X

/-- PDF p.15, (9): specified normalized full-period correlated rotation twirl. -/
def circleState (u v : Hilbert ℤ) : Matrix (ℤ × ℤ) (ℤ × ℤ) ℂ :=
  fun p q => ∫ x, productCoeff (positiveTranslationConjugation x (rankOne u)) (positiveTranslationConjugation x (rankOne v)) p q
    ∂QAlgorithms.Papers.Independent.Dependency50.P33.rotationMeasure

/-- PDF p.17: independence modulo a.e. equality, without any integrability assumption. -/
def aeIndependent {n : ℕ} (f : Fin n → ℝ → ℂ) (A : Set ℝ) : Prop :=
  ∀ c : Fin n → ℂ, (∀ᵐ x ∂volume.restrict A, (∑ i, c i * f i x) = 0) → c = 0

/-- PDF p.18: Omega coefficients in H1 tensor (H2 tensor K), normalized by 1/sqrt(k). -/
def omegaCoeff {k : ℕ} (u v : Fin k → Hilbert ℤ) : ℤ × (ℤ × Fin k) → ℂ :=
  fun p => ((Real.sqrt (k : ℝ))⁻¹ : ℂ) * u p.2.2 p.1 * v p.2.2 p.2.1

/-- PDF p.18, (15): short-interval twirl with normalization n/(2pi), for n>0. -/
def shortTwirl {k : ℕ} (u v : Fin k → Hilbert ℤ) (n : ℕ) :
    Matrix (ℤ × (ℤ × Fin k)) (ℤ × (ℤ × Fin k)) ℂ :=
  fun p q => ∫ x in (0 : ℝ)..(2 * Real.pi / n),
    ((n : ℝ) / (2 * Real.pi) : ℂ) *
    Complex.exp (Complex.I * (x : ℂ) *
      (((p.1 : ℂ) + (p.2.1 : ℂ)) - ((q.1 : ℂ) + (q.2.1 : ℂ)))) *
    omegaCoeff u v p * star (omegaCoeff u v q)

/-! Definitional sanity checks; source theorem proofs are outside this stage. -/

example {I J : Type} (u : Hilbert (I × J)) : tensorRankLE 0 u → ∀ p, u p = 0 := by
  rintro ⟨a, b, h⟩ ⟨i, j⟩
  simpa using h i j

example (I J : Type) : schmidtClass I J 0 = ∅ := by
  ext rho
  simp [schmidtClass]

example {I : Type} (A : Set (State I)) (rho : State I) (mu : Measure A)
    (h : extremeFiber rho mu) : mu ∈ barycenterFiber A rho := h.1

example {I : Type} (rho : State I) (w s) (h : pureEnsemble rho w s) :
    (∑' i, w i) = 1 := h.2.2.1

example (X : Matrix ℤ ℤ ℂ) : positiveTranslationConjugation 0 X = X := by
  funext i j
  simp [positiveTranslationConjugation,
    QAlgorithms.Papers.Independent.Dependency50.P33.rotationCoeff]

example (x : ℝ) (X : Matrix ℤ ℤ ℂ) (i : ℤ) : positiveTranslationConjugation x X i i = X i i := by
  simp [positiveTranslationConjugation,
    QAlgorithms.Papers.Independent.Dependency50.P33.rotationCoeff]

example {n : ℕ} (A : Set ℝ) (f : Fin n → ℝ → ℂ) (h : aeIndependent f A)
    (c : Fin n → ℂ) (hc : ∀ᵐ x ∂volume.restrict A, (∑ i, c i * f i x) = 0) : c = 0 := h c hc

example {I J : Type} (k : ℕ) (rho eta delta : State (I × J))
    (h : edgeDecomposition k rho eta delta 0) : rho.coefficients = eta.coefficients := by
  simpa using h.2.2.2

/-- Zero compressions have zero mass and cannot be normalized as states. -/
example {I J : Type} (Q : BoundedOp J J) (rho : State (I × J)) :
    localProjectionCompression (0 : BoundedOp I I) Q rho = 0 := by
  funext p q
  simp [localProjectionCompression, opCoeff]

example {I : Type} (X : Matrix I I ℂ) : tracePair (0 : BoundedOp I I) X = 0 := by
  simp [tracePair, opCoeff]

example {I : Type} : positiveArray (0 : Matrix I I ℂ) := by
  intro s z
  simp

example {I : Type} (v : Hilbert I) : inKernel (0 : Matrix I I ℂ) v := by
  intro i
  simp

/-- Footnote 4: the zero PEB class is empty even when the input is degenerate. -/
example {I J : Type} (Phi : CanonicalChannel I J) : ¬ isPEB 0 Phi := by
  simp [isPEB]

example {I J : Type} (k : ℕ) (rho eta delta : State (I × J))
    (h : edgeDecomposition k rho eta delta 1) : rho.coefficients = delta.coefficients := by
  simpa using h.2.2.2

/-- A positive translation phase on the first Fourier mode. -/
example (x : ℝ) (X : Matrix ℤ ℤ ℂ) :
    positiveTranslationConjugation x X 1 0 = Complex.exp (Complex.I * (x : ℂ)) * X 1 0 := by
  simp [positiveTranslationConjugation,
    QAlgorithms.Papers.Independent.Dependency50.P33.rotationCoeff]

/-- PDF p.5: the frozen range of pure states and the frozen pure-state
subtype describe the same normalized density, without choosing its vector phase. -/
def pureStateFromRange {I : Type} (rho : pureStates I) : PureState I :=
  ⟨rho.val, by
    obtain ⟨sigma, hsigma⟩ := rho.property
    exact hsigma ▸ sigma.property⟩

example {I : Type} (rho : pureStates I) : (pureStateFromRange rho).val = rho.val := rfl

example {I J : Type} (Phi : CanonicalChannel I J) (X : Matrix I I ℂ)
    (hX : ¬ IsTraceClass X) : canonicalChannelAction Phi X = 0 := Phi.property X hX

end QAlgorithms.Papers.Independent.Claimed50.P16


