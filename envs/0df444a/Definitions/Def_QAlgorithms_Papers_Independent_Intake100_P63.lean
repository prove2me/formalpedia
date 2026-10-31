-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63
-- name    : QAlgorithms_Papers_Independent_Intake100_P63
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:12:44.174156+00:00
-- url     : https://prove2.me/theorems/a483294f-67fb-4590-94eb-e9977eaf4b14
-- title:
--   Definitions for A Generalization of Quantum Stein's Lemma
-- statement:
--   The objects the formalized statements of *A Generalization of Quantum Stein's Lemma* (arXiv:0904.0281) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tensorBlocks`: PDF p.5 property 4: tensor two consecutive blocks in their actual registers.
--   - `discardPrefix`: PDF pp.3,13: trace out the first m copies, without renormalizing.
--   - `discardFirst`: PDF p.5: first-copy partial trace, with codomain indexed by n rather than n+1-1.
--   - `stateSetAxioms`: PDF p.5 properties 1--5. The first-copy trace together with all permutations is equivalent to every single-copy trace. M_0 is deliberately unconstrained.
--   - `setEntropy`: PDF p.4 Eq.(6): extended infimum, including infinity for empty alternatives.
--   - `regularizedSetEntropy`: PDF p.5 Eq.(10): positive-block infimum construction; its agreement with the limit and its finiteness are the conclusions of regularization_exists.
--   - `testingRate`: PDF p.5 Eqs.(12),(13): -log_2(0)=infinity. Positive n is imposed at uses. EReal preserves subtraction of eta, without truncation at zero.
--   - `SteinClauses`: PDF p.5 Eqs.(11)--(14): both clauses, with one effect sequence uniform over all alternatives, including all positive finite blocklengths.
--   - `maxBits`: PDF p.4 Eqs.(7),(8): max-relative entropy on normalized states. For such states any feasible exponent is nonnegative, so an ENNReal infimum of nonnegative exponents is exactly the source's real-exponent infimum.
--   - `traceNormSmoothMax`: PDF p.4 Eq.(9): closed balls of NORMALIZED states in the full trace norm.
--   - `SmoothFormula`: PDF p.6 Eq.(16): both inner asymptotic envelopes and the right-hand smoothing limits, without assuming an inner ordinary limit.
--   - `diagonalSmooth`: PDF p.10 Eq.(45): the entire nonnegative radius sequence is chosen before its limsup; zero radii and arbitrary decay rates are permitted.
--   - `thresholdProfile`: PDF p.7 Eq.(20): the actual optimization profile. Attainment is stated separately, rather than pretending a real infimum is automatically a minimum.
--   - `separableFamily`: PDF p.3 Eq.(3), p.6 Eq.(15): grouped-party fully separable alternatives. Each local state acts on ALL n copies of its party, allowing correlations among those copies. There is no restriction to a bipartition or to i.i.d. alternatives.
--   - `oneCopy`: PDF p.3: identify the one-copy function register with its original space.
--   - `MultipartiteEntangled`: PDF p.6: an entangled normalized multipartite state is outside Eq.(3).
--   - `CopySymmetric`: PDF pp.12--13: permutation symmetry of a vector. This is stronger than permutation invariance of its rank-one projector, as the source requires.
--   - `discardEnvironment`: PDF pp.12,18: trace every environmental factor, preserving paired-copy order.
--   - `AlmostPower`: PDF p.13 Eq.(67): normalized symmetric vectors in the complex span of at-most-r defect tensors. No entropy inequality is a field of this predicate.
--   - `MixedMarginal`: PDF pp.18,20: lambda_max(rho)<1, expressed on every eigenvalue.
--   - `Sublinear`: PDF pp.4,18: a natural-valued sequence is o(n), with positive-copy asymptotics.
--   - `normalizedCopySymmetrization`: PDF p.4 Eq.(4): normalized symmetrization; the zero-vector totalized value is zero. Active orthogonal-defect components have nonzero symmetrization.
--   - `tensorVectorFamily`: PDF p.18: arbitrary tensor of k local vectors, used to define the full tensor power of the orthogonal subspace, rather than only product defects.
--   - `OrthogonalDefects`: PDF pp.18,20: the k defective factors live in (theta-perp)^tensor k.
--   - `expansionComponent`: PDF pp.18,20: symmetrized k-defect component with exactly N sites.
--   - `Expansion`: PDF pp.18,20 Eqs.(103),(114): the original normalized expansion data. Zero-coefficient terms need no nonexistent normalized defect vector. The sum normalization and coefficient normalization are source assumptions.
--   - `cutoffVector`: PDF p.20 Eq.(114): retain EXACTLY the coefficients of modulus at least 1/n; Phi is unnormalized. n=0 is totalized but never used in finite-copy claims.
--   - `retainedCoefficientIndices`: PDF p.20: exact retainedCoefficientIndices finite index set, including equality at the cutoff.
--   - `cutoffReduction`: PDF p.20 Eq.(115): normalized cutoff reduction; the zero-cutoff off-domain value is zero. Normalization is required only eventually, when automatic.
--   - `closest`: PDF p.19 Eq.(107), p.20 before Eq.(122): choose an actual relative-entropy minimizer. Epsilon has a total off-domain value, and no optimality or tail bound is inserted as a hypothesis of the results using this construction.
--   - `regularizedAlternative`: PDF p.20 Eq.(122): the specified full-rank regularization of the minimizer.
--   - `Extendible`: PDF p.28: fixed-k extendibility, formulated as k equal B marginals. Averaging over B permutations gives the equivalent symmetric extension.
--   - `extendibleFamily`: PDF p.28: the same k is fixed before the copy number n; the A and B copies are each grouped into a local block when forming the extension.
--   - `pptStateFamily`: PDF p.28: PPT across grouped A:B blocks; NPPT means failure of PSD.
--   - `PartyReg`: PDF p.6 Eq.(18), p.29: finite local basis dimensions, one for each party.
--   - `localKraus`: PDF pp.6,29: rectangular local Kraus operator tensored with identities on all other parties. Equality of coordinate values implements their identity.
--   - `MultipartiteFiniteLOCC`: PDF pp.6,29: arbitrary finite adaptive deterministic LOCC tree. Rectangular complete instruments include local ancillas, preparation and disposal; the continuation can depend on the communicated outcome and every branch is summed. There is no entanglement assistance and no assumed closure or optimal attainment.
--   - `groupedCopies`: PDF p.6 Eq.(18): regroup each party's n copies as a local dimension d_j^n. The equivalence only changes coordinates and never transfers a quantum system.
--   - `conversionError`: PDF p.6 Eq.(18): infimal trace-norm error over actual finite LOCC protocols, without asserting that LOCC is closed or that an optimizer exists.
--   - `conversionCost`: PDF p.6 Eq.(18): INPUT copies per OUTPUT copy; empty feasible infima are infinity, so no convertibility assumption is needed.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, https://arxiv.org/abs/0904.0281v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

/-!
Brandao--Plenio, arXiv:0904.0281v3. All locators are PDF pages.
Finite nonzero Hilbert spaces are arbitrary finite basis types, not qubit registers.
Copy counts in rate constraints are strictly positive. Entropy and rates use bits;
the exponential in Lemma III.5 is natural. Trace norm is the full Schatten 1-norm.
Accepted frozen constructions are imported; distinct paper-local constructions are fully specified.
The source's permutation-conjugation typo is corrected to conjugation by the adjoint.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology
open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)
open QAlgorithms.Papers.Independent.Information100.P21 (Vec)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)
open QAlgorithms.Papers.Independent.Information100.P69 (permute)
open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5 property 4: tensor two consecutive blocks in their actual registers. -/
def tensorBlocks {I : Type*} {n m : ℕ} (A : Mat (Copies I n))
    (B : Mat (Copies I m)) : Mat (Copies I (n + m)) :=
  fun x y => A (fun i => x (Fin.castAdd m i)) (fun i => y (Fin.castAdd m i)) *
    B (fun i => x (Fin.natAdd n i)) (fun i => y (Fin.natAdd n i))

/-- PDF pp.3,13: trace out the first m copies, without renormalizing. -/
def discardPrefix {I : Type} [Fintype I] {n : ℕ}
    (m : ℕ) (h : m ≤ n) (X : Mat (Copies I n)) : Mat (Copies I (n - m)) :=
  fun x y => ∑ z : Copies I m, X (joinCopies h z x) (joinCopies h z y)

/-- PDF p.5: first-copy partial trace, with codomain indexed by n rather than n+1-1. -/
def discardFirst {I : Type*} [Fintype I] {n : ℕ}
    (X : Mat (Copies I (n + 1))) : Mat (Copies I n) :=
  fun x y => ∑ a, X (Fin.cons a x) (Fin.cons a y)

/-- PDF p.5 properties 1--5. The first-copy trace together with all permutations
is equivalent to every single-copy trace. M_0 is deliberately unconstrained. -/
def stateSetAxioms {I : Type*} [Fintype I] [DecidableEq I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) : Prop :=
  (∀ n, 0 < n → IsClosed (M n) ∧ Convex ℝ (M n) ∧
    ∀ X ∈ M n, IsDensityMatrix X) ∧
  (∃ sigma : Mat I, IsDensityMatrix sigma ∧ LinearMap.ker sigma.mulVecLin = ⊥ ∧
    ∀ n, 0 < n → piKron n sigma ∈ M n) ∧
  (∀ n, 0 < n → ∀ X ∈ M (n + 1), discardFirst X ∈ M n) ∧
  (∀ n m, 0 < n → 0 < m → ∀ X ∈ M n, ∀ Y ∈ M m,
    tensorBlocks X Y ∈ M (n + m)) ∧
  (∀ n, 0 < n → ∀ X ∈ M n, ∀ p, permute p X ∈ M n)

/-- PDF p.4 Eq.(6): extended infimum, including infinity for empty alternatives. -/
def setEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (M : Set (Mat I)) (rho : Mat I) : ℝ≥0∞ :=
  ⨅ sigma : M, relativeBits rho sigma.val

/-- PDF p.5 Eq.(10): positive-block infimum construction; its agreement with
the limit and its finiteness are the conclusions of regularization_exists. -/
def regularizedSetEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (rho : Mat I) : ℝ≥0∞ :=
  ⨅ n : {n : ℕ // 0 < n}, setEntropy (M n.val) (piKron n.val rho) / (n.val : ℝ≥0∞)

/-- PDF p.5 Eqs.(12),(13): -log_2(0)=infinity. Positive n is imposed at uses.
EReal preserves subtraction of eta, without truncation at zero. -/
def testingRate (n : ℕ) (p : ℝ) : EReal :=
  if p = 0 then ⊤ else ((-Real.logb 2 p / (n : ℝ) : ℝ) : EReal)

/-- PDF p.5 Eqs.(11)--(14): both clauses, with one effect sequence uniform over
all alternatives, including all positive finite blocklengths. -/
def SteinClauses {I : Type*} [Fintype I] [DecidableEq I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (rho : Mat I) : Prop :=
  (∀ eta : ℝ, 0 < eta → ∃ A : (n : ℕ) → Mat (Copies I n),
    (∀ n, 0 < n → IsEffect (A n)) ∧
    Tendsto (fun n => effectProb (1 - A n) (piKron n rho)) atTop (𝓝 0) ∧
    ∀ n, 0 < n → ∀ omega ∈ M n,
      (regularizedSetEntropy M rho : EReal) ≤ testingRate n (effectProb (A n) omega) + (eta : EReal)) ∧
  (∀ (eta : ℝ) (A : (n : ℕ) → Mat (Copies I n)), 0 < eta →
    (∀ n, 0 < n → IsEffect (A n)) →
    (∀ n, 0 < n → ∀ omega ∈ M n,
      (regularizedSetEntropy M rho : EReal) ≤ testingRate n (effectProb (A n) omega) - (eta : EReal)) →
    Tendsto (fun n => effectProb (1 - A n) (piKron n rho)) atTop (𝓝 1))

/-- PDF p.4 Eqs.(7),(8): max-relative entropy on normalized states.
For such states any feasible exponent is nonnegative, so an ENNReal infimum
of nonnegative exponents is exactly the source's real-exponent infimum. -/
def maxBits {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : ℝ≥0∞ :=
  sInf {v : ℝ≥0∞ | ∃ s : ℝ, 0 ≤ s ∧ v = ENNReal.ofReal s ∧
    ((((2 : ℝ) ^ s : ℝ) : ℂ) • sigma - rho).PosSemidef}

/-- PDF p.4 Eq.(9): closed balls of NORMALIZED states in the full trace norm. -/
def traceNormSmoothMax {I : Type*} [Fintype I] [DecidableEq I]
    (M : Set (Mat I)) (rho : Mat I) (eps : ℝ) : ℝ≥0∞ :=
  ⨅ tau : {tau : Mat I // IsDensityMatrix tau ∧ traceNorm (rho - tau) ≤ eps},
    ⨅ sigma : M, maxBits tau.val sigma.val

/-- PDF p.6 Eq.(16): both inner asymptotic envelopes and the right-hand
smoothing limits, without assuming an inner ordinary limit. -/
def SmoothFormula {I : Type*} [Fintype I] [DecidableEq I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (rho : Mat I) : Prop :=
  Tendsto (fun eps => liminf
    (fun n => traceNormSmoothMax (M n) (piKron n rho) eps / (n : ℝ≥0∞)) atTop)
    (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (regularizedSetEntropy M rho)) ∧
  Tendsto (fun eps => limsup
    (fun n => traceNormSmoothMax (M n) (piKron n rho) eps / (n : ℝ≥0∞)) atTop)
    (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (regularizedSetEntropy M rho))

/-- PDF p.10 Eq.(45): the entire nonnegative radius sequence is chosen before
its limsup; zero radii and arbitrary decay rates are permitted. -/
def diagonalSmooth {I : Type*} [Fintype I] [DecidableEq I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (rho : Mat I) : ℝ≥0∞ :=
  ⨅ eps : {eps : ℕ → ℝ // (∀ n, 0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0)},
    limsup (fun n => traceNormSmoothMax (M n) (piKron n rho) (eps.val n) / (n : ℝ≥0∞)) atTop

/-- PDF p.7 Eq.(20): the actual optimization profile. Attainment is stated
separately, rather than pretending a real infimum is automatically a minimum. -/
def thresholdProfile {I : Type*} [Fintype I] [DecidableEq I]
    (M : (n : ℕ) → Set (Mat (Copies I n))) (rho : Mat I) (y : ℝ) (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ omega ∈ M n,
    v = (positivePart (piKron n rho - (((2 : ℝ) ^ (y * n) : ℝ) : ℂ) • omega)).trace.re}

/-- PDF p.3 Eq.(3), p.6 Eq.(15): grouped-party fully separable alternatives.
Each local state acts on ALL n copies of its party, allowing correlations
among those copies. There is no restriction to a bipartition or to i.i.d. alternatives. -/
def separableFamily {P : Type*} [Fintype P] (d : P → ℕ) (n : ℕ) :
    Set (Mat (Copies ((j : P) → Fin (d j)) n)) :=
  {X | IsDensityMatrix X ∧ ∃ q : ℕ, ∃ w : Fin q → ℝ,
    ∃ tau : (a : Fin q) → (j : P) → Mat (Copies (Fin (d j)) n),
    (∀ a, 0 ≤ w a) ∧ (∑ a, w a) = 1 ∧ (∀ a j, IsDensityMatrix (tau a j)) ∧
    X = ∑ a, (w a : ℂ) • (fun x y => ∏ j, tau a j (fun i => x i j) (fun i => y i j))}

/-- PDF p.3: identify the one-copy function register with its original space. -/
def oneCopy {I : Type*} (rho : Mat I) : Mat (Copies I 1) :=
  fun x y => rho (x 0) (y 0)

/-- PDF p.6: an entangled normalized multipartite state is outside Eq.(3). -/
def MultipartiteEntangled {P : Type*} [Fintype P] (d : P → ℕ)
    (rho : Mat ((j : P) → Fin (d j))) : Prop :=
  IsDensityMatrix rho ∧ oneCopy rho ∉ separableFamily d 1

/-- PDF pp.12--13: permutation symmetry of a vector. This is stronger than
permutation invariance of its rank-one projector, as the source requires. -/
def CopySymmetric {I : Type*} {n : ℕ} (v : Vec (Copies I n)) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (x : Copies I n), v (x ∘ p) = v x

/-- PDF pp.12,18: trace every environmental factor, preserving paired-copy order. -/
def discardEnvironment {I : Type*} [Fintype I] {n : ℕ}
    (X : Mat (Copies (I × I) n)) : Mat (Copies I n) :=
  fun x y => ∑ z : Copies I n,
    X (fun i => (x i, z i)) (fun i => (y i, z i))

/-- PDF p.13 Eq.(67): normalized symmetric vectors in the complex span of
at-most-r defect tensors. No entropy inequality is a field of this predicate. -/
def AlmostPower {I : Type} [Fintype I] (theta : Vec I) (n r : ℕ)
    (psi : Vec (Copies I n)) : Prop :=
  r ≤ n ∧ IsState theta ∧ IsState psi ∧ CopySymmetric psi ∧
  psi ∈ Submodule.span ℂ {v | ∃ (S : Finset (Fin n)) (chi : (S → I) → ℂ),
    S.card ≤ r ∧ v = defectTensor theta S chi}

/-- PDF pp.18,20: lambda_max(rho)<1, expressed on every eigenvalue. -/
def MixedMarginal {I : Type*} [Fintype I] [DecidableEq I] (theta : Vec (I × I)) : Prop :=
  ∀ k : Fin (Fintype.card I), ascEigenvalues (traceRight (pureDensity theta)) k < 1

/-- PDF pp.4,18: a natural-valued sequence is o(n), with positive-copy asymptotics. -/
def Sublinear (a : ℕ → ℕ) : Prop :=
  Tendsto (fun n => (a n : ℝ) / (n : ℝ)) atTop (𝓝 0)

/-- PDF p.4 Eq.(4): normalized symmetrization; the zero-vector totalized value
is zero. Active orthogonal-defect components have nonzero symmetrization. -/
def normalizedCopySymmetrization {I : Type*} [Fintype I] {n : ℕ}
    (v : Vec (Copies I n)) : Vec (Copies I n) :=
  let z : Vec (Copies I n) := ∑ p : Equiv.Perm (Fin n),
    WithLp.toLp 2 (fun x => v (x ∘ p))
  (‖z‖ : ℂ)⁻¹ • z

/-- PDF p.18: arbitrary tensor of k local vectors, used to define the full
tensor power of the orthogonal subspace, rather than only product defects. -/
def tensorVectorFamily {I : Type*} {k : ℕ} (v : Fin k → Vec I) : Vec (Copies I k) :=
  WithLp.toLp 2 fun x => ∏ j, v j (x j)

/-- PDF pp.18,20: the k defective factors live in (theta-perp)^tensor k. -/
def OrthogonalDefects {I : Type*} [Fintype I] (theta : Vec I) (k : ℕ)
    (eta : Vec (Copies I k)) : Prop :=
  eta ∈ Submodule.span ℂ {v | ∃ w : Fin k → Vec I,
    (∀ j, inner ℂ theta (w j) = 0) ∧ v = tensorVectorFamily w}

/-- PDF pp.18,20: symmetrized k-defect component with exactly N sites. -/
def expansionComponent {I : Type*} [Fintype I] (theta : Vec I)
    (N k : ℕ) (hk : k ≤ N) (eta : Vec (Copies I k)) : Vec (Copies I N) :=
  normalizedCopySymmetrization (WithLp.toLp 2 fun x =>
    eta (fun i => x ⟨i.val, by omega⟩) *
    ∏ i : Fin (N - k), theta (x ⟨k + i.val, by omega⟩))

/-- PDF pp.18,20 Eqs.(103),(114): the original normalized expansion data.
Zero-coefficient terms need no nonexistent normalized defect vector. The
sum normalization and coefficient normalization are source assumptions. -/
structure Expansion {I : Type*} [Fintype I] (theta : Vec I) (N r : ℕ) where
  range : r ≤ N
  beta : Fin (r + 1) → ℂ
  eta : (k : Fin (r + 1)) → Vec (Copies I k.val)
  coefficients : (∑ k, Complex.normSq (beta k)) = 1
  defects : ∀ k, beta k ≠ 0 → IsState (eta k) ∧ CopySymmetric (eta k) ∧
    OrthogonalDefects theta k.val (eta k)
  normalized : IsState (∑ k, beta k • expansionComponent theta N k.val
    (by have := k.isLt; omega) (eta k))

/-- PDF p.20 Eq.(114): retain EXACTLY the coefficients of modulus at least 1/n;
Phi is unnormalized. n=0 is totalized but never used in finite-copy claims. -/
def cutoffVector {I : Type*} [Fintype I] {theta : Vec I} {N r : ℕ}
    (D : Expansion theta N r) (n : ℕ) : Vec (Copies I N) :=
  ∑ k, if (n : ℝ)⁻¹ ≤ ‖D.beta k‖ then
    D.beta k • expansionComponent theta N k.val (by have := k.isLt; have := D.range; omega) (D.eta k)
  else 0

/-- PDF p.20: exact retainedCoefficientIndices finite index set, including equality at the cutoff. -/
def retainedCoefficientIndices {I : Type*} [Fintype I] {theta : Vec I} {N r : ℕ}
    (D : Expansion theta N r) (n : ℕ) : Finset (Fin (r + 1)) :=
  Finset.univ.filter fun k => (n : ℝ)⁻¹ ≤ ‖D.beta k‖

/-- PDF p.20 Eq.(115): normalized cutoff reduction; the zero-cutoff off-domain
value is zero. Normalization is required only eventually, when automatic. -/
def cutoffReduction {I : Type} [Fintype I] {theta : Vec (I × I)} {N r : ℕ}
    (D : Expansion theta N r) (n : ℕ) : Mat (Copies I (N - r)) :=
  let phi := cutoffVector D n
  let psi := (‖phi‖ : ℂ)⁻¹ • phi
  discardPrefix r D.range (discardEnvironment (pureDensity psi))

/-- PDF p.19 Eq.(107), p.20 before Eq.(122): choose an actual relative-entropy
minimizer. Epsilon has a total off-domain value, and no optimality or tail
bound is inserted as a hypothesis of the results using this construction. -/
def closest {I : Type*} [Fintype I] [DecidableEq I]
    (M : Set (Mat I)) (rho : Mat I) : Mat I :=
  Classical.epsilon fun omega => omega ∈ M ∧ relativeBits rho omega = setEntropy M rho

/-- PDF p.20 Eq.(122): the specified full-rank regularization of the minimizer. -/
def regularizedAlternative {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : Set (Mat (Copies I k))) (pi : Mat (Copies I k)) (sigma : Mat I) (tau : ℝ) :
    Mat (Copies I k) :=
  ((1 / (1 + tau) : ℝ) : ℂ) • closest M pi +
    ((tau / (1 + tau) : ℝ) : ℂ) • piKron k sigma

/-- PDF p.28: fixed-k extendibility, formulated as k equal B marginals.
Averaging over B permutations gives the equivalent symmetric extension. -/
def Extendible {A B : Type*} [Fintype A] [Fintype B] (k : ℕ)
    (rho : Mat (A × B)) : Prop :=
  IsDensityMatrix rho ∧ ∃ ext : Mat (A × (Fin k → B)), IsDensityMatrix ext ∧
    ∀ j : Fin k, ∀ a a' b b', rho (a,b) (a',b') =
      ∑ z : ({i : Fin k // i ≠ j} → B),
        ext (a, fun i => if h : i = j then b else z ⟨i,h⟩)
          (a', fun i => if h : i = j then b' else z ⟨i,h⟩)

/-- PDF p.28: the same k is fixed before the copy number n; the A and B
copies are each grouped into a local block when forming the extension. -/
def extendibleFamily {A B : Type*} [Fintype A] [Fintype B] (k n : ℕ) :
    Set (Mat (Copies (A × B) n)) :=
  {X | Extendible (A := Copies A n) (B := Copies B n) k
    (fun (x y : Copies A n × Copies B n) =>
      X (fun i => (x.1 i,x.2 i)) (fun i => (y.1 i,y.2 i)))}

/-- PDF p.28: PPT across grouped A:B blocks; NPPT means failure of PSD. -/
def pptStateFamily {A B : Type*} [Fintype A] [Fintype B] (n : ℕ) :
    Set (Mat (Copies (A × B) n)) :=
  {X | IsDensityMatrix X ∧
    Matrix.PosSemidef (fun x y : Copies (A × B) n =>
      X (fun i => ((x i).1,(y i).2)) (fun i => ((y i).1,(x i).2)))}

/-- PDF p.6 Eq.(18), p.29: finite local basis dimensions, one for each party. -/
abbrev PartyReg {P : Type*} (d : P → ℕ) := (j : P) → Fin (d j)

/-- PDF pp.6,29: rectangular local Kraus operator tensored with identities on
all other parties. Equality of coordinate values implements their identity. -/
def localKraus {P : Type*} [Fintype P] [DecidableEq P] (d : P → ℕ)
    (j : P) (h : ℕ) (K : Matrix (Fin h) (Fin (d j)) ℂ) :
    Matrix (PartyReg (Function.update d j h)) (PartyReg d) ℂ :=
  fun y x => K ⟨(y j).val, by simpa using (y j).isLt⟩ (x j) *
    ∏ i ∈ Finset.univ.erase j, if (y i).val = (x i).val then 1 else 0

/-- PDF pp.6,29: arbitrary finite adaptive deterministic LOCC tree.
Rectangular complete instruments include local ancillas, preparation and disposal;
the continuation can depend on the communicated outcome and every branch is summed.
There is no entanglement assistance and no assumed closure or optimal attainment. -/
inductive MultipartiteFiniteLOCC {P : Type} [Fintype P] [DecidableEq P] :
    {d e : P → ℕ} → (Mat (PartyReg d) → Mat (PartyReg e)) → Prop
  | identity (d : P → ℕ) : MultipartiteFiniteLOCC (fun X : Mat (PartyReg d) => X)
  | step {d e : P → ℕ} (j : P) (h k : ℕ)
      (K : Fin k → Matrix (Fin h) (Fin (d j)) ℂ)
      (complete : (∑ a, (K a)ᴴ * K a) = 1)
      (next : Fin k → (Mat (PartyReg (Function.update d j h)) → Mat (PartyReg e)))
      (valid : ∀ a, MultipartiteFiniteLOCC (next a)) :
      MultipartiteFiniteLOCC (fun X : Mat (PartyReg d) =>
        ∑ a, next a (localKraus d j h (K a) * X * (localKraus d j h (K a))ᴴ))

/-- PDF p.6 Eq.(18): regroup each party's n copies as a local dimension d_j^n.
The equivalence only changes coordinates and never transfers a quantum system. -/
def groupedCopies {P : Type*} [Fintype P] (d : P → ℕ) (n : ℕ)
    (rho : Mat (PartyReg d)) : Mat (PartyReg (fun j => d j ^ n)) :=
  fun x y => piKron n rho
    (fun t j => (finFunctionFinEquiv.symm (x j)) t)
    (fun t j => (finFunctionFinEquiv.symm (y j)) t)

/-- PDF p.6 Eq.(18): infimal trace-norm error over actual finite LOCC protocols,
without asserting that LOCC is closed or that an optimizer exists. -/
def conversionError {P : Type} [Fintype P] [DecidableEq P] (d : P → ℕ)
    (rho sigma : Mat (PartyReg d)) (k n : ℕ) : ℝ≥0∞ :=
  ⨅ L : {L : Mat (PartyReg (fun j => d j ^ k)) → Mat (PartyReg (fun j => d j ^ n)) //
    MultipartiteFiniteLOCC L}, ENNReal.ofReal (traceNorm (L.val (groupedCopies d k rho) - groupedCopies d n sigma))

/-- PDF p.6 Eq.(18): INPUT copies per OUTPUT copy; empty feasible infima are
infinity, so no convertibility assumption is needed. -/
def conversionCost {P : Type} [Fintype P] [DecidableEq P] (d : P → ℕ)
    (rho sigma : Mat (PartyReg d)) : ℝ≥0∞ :=
  ⨅ k : {k : ℕ → ℕ // Tendsto (fun n => conversionError d rho sigma (k n) n) atTop (𝓝 0)},
    limsup (fun n => (k.val n : ℝ≥0∞) / (n : ℝ≥0∞)) atTop

/-! Sanity checks pin the totalized edges and the physical constructions. -/

example : testingRate 1 0 = ⊤ := by simp [testingRate]

example : testingRate 1 1 = 0 := by simp [testingRate]

example {I : Type*} (X : Mat I) (x y : Copies I 0) : piKron 0 X x y = 1 := by
  simp [piKron]

example {I : Type*} (rho : Mat I) (x y : Copies I 1) :
    oneCopy rho x y = rho (x 0) (y 0) := rfl

example {I : Type*} [Fintype I] [DecidableEq I] :
    setEntropy (∅ : Set (Mat I)) 0 = ⊤ := by simp [setEntropy]

example {P : Type} [Fintype P] [DecidableEq P] (d : P → ℕ) :
    MultipartiteFiniteLOCC (fun X : Mat (PartyReg d) => X) := MultipartiteFiniteLOCC.identity d

example {I : Type*} [Fintype I] [DecidableEq I] :
    (positivePart (0 : Mat I)).trace.re = 0 := by simp [positivePart, cfc_zero]

example {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Mat I)
    (h : IsDensityMatrix rho ∧ IsDensityMatrix sigma)
    (hs : ¬ LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin) :
    relativeBits rho sigma = ⊤ := by
  simp [relativeBits, h, QuantumLoss.umegakiEntropy, hs, ENNReal.div_eq_top]

end QAlgorithms.Papers.Independent.Intake100.P63


