-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
-- name    : QAlgorithms_Papers_Independent_Claimed50_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T18:29:13.62643+00:00
-- url     : https://prove2.me/theorems/9274d9cb-a436-4538-a3f8-122155be65c5
-- title:
--   Definitions for Quantum conditional mutual information and approximate Markov chains
-- statement:
--   The objects the formalized statements of *Quantum conditional mutual information and approximate Markov chains* (arXiv:1410.0664) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `generalizedTraceDistance`: Eq.17, PDF p.5: includes the absolute trace correction.
--   - `normalizedRelativeEntropyBits`: Eq.16, PDF p.5: normalized relative entropy in bits; infinity on support failure. The accepted unnormalized entropy in nats is divided by tr(X) ln(2). The zero-first-argument convention is zero. Lemma 2.3 excludes it eventually.
--   - `copyPermutationInvariant`: Invariance under all permutations, PDF pp.9,13.
--   - `GroupInvariant`: Same permutation on both groups of copies, PDF p.12.
--   - `Contractive`: Norm at most one via W†W <= identity; W need not be positive (PDF p.13).
--   - `TNI`: Completely positive, trace non-increasing map (PDF pp.6,22).
--   - `copyPermutationCovariant`: Separate input/output permutation actions (PDF p.12).
--   - `liftFirst`: Explicit omitted identity on the second factor (PDF p.13 fn.6).
--   - `DiagonalIn`: Diagonal in the ON basis given by the columns of a unitary matrix, PDF p.14.
--   - `dimensionParameter`: Eq.88 dimension parameter, PDF p.13.
--   - `fidelityFactor`: Eq.88 factor (n+1)^(-d²), PDF pp.13–14.
--   - `Extensions`: Extensions are PSD, not necessarily normalized (PDF p.12).
--   - `extensionMeasurable`: Coordinate Borel sigma algebra on fixed-marginal extensions (PDF p.12). This is the pullback of the finite complex matrix-entry coordinates.
--   - `channelMeasurable`: Matrix-unit coordinate measurable structure for channels (PDF p.12).
--   - `meanChannel`: Mean tensor channel, evaluated on every operator, including entangled inputs (PDF p.12). The theorem explicitly supplies coordinate integrability.
--   - `cmi`: Finite conditional mutual information in bits, PDF p.1.
--   - `Markov`: Markov-chain property, Eq.1 (PDF p.1), with identity on A.
--   - `qcq`: Eq.11 qcq input in a specified orthonormal basis of B (PDF p.3).
--   - `qcqRecovered`: Eq.13 explicitly reconstructed qcq state (PDF p.3).
--   - `rotatedPetzRecovery`: Support-inverse Petz map with specified rotations, PDF pp.15,19.
--   - `completedPetz`: Computed CP deficit completion, PDF p.19. If the two deficits have zero trace, use the product marginal state to complete outside the support as well. Otherwise the completion state is their tensor product divided by their common trace squared.
--   - `negLogBits`: Negative log in bits, with +infinity at zero probability (PDF p.19 fn.11).
--   - `normalizedTestingEntropyBits`: Eq.142, PDF p.19, on the positive epsilon domain needed below.
--   - `maxEntropy`: Eq.143, PDF p.19: equivalent infimum of finite domination logarithms. Empty domination domain has value +infinity; epsilon=0 is permitted.
--   - `entropyWindowMass`: Spectral mass in the closed entropy window of Eq.42, PDF pp.7–8. Repeated eigenvalues are counted with multiplicity, equivalently taking the trace of the spectral projector times the tensor-power state. This is not the accepted classical strong-typicality mass Dependency50.P48.typicalMass.
--   - `vectorOuterProduct`: Unnormalized rank-one operator, PDF pp.21,23.
--   - `UnnormalizedPurifies`: A purification has the specified marginal; no normalization is imposed when the marginal is an arbitrary nonnegative operator, PDF p.21. Frontier18.P01.Purifies instead takes a normalized PureState; it cannot represent the arbitrary-trace vectors required here.
--   - `testingValue`: Primal value in Eq.142 before taking the negative logarithm, PDF p.19.
--   - `dualTestingValue`: Dual value in Eq.146 for positive epsilon, PDF pp.19–20. Taking the supremum of nonnegative parts leaves the supremum unchanged: mu=0 is feasible and has value zero.
--   - `endpointTestingValue`: Continuous right endpoint of the increasing primal value, footnote 9, PDF p.19. For positive epsilon this is exactly the original optimization. The definition does not replace any asserted limit by a liminf.
--   - `endpointDualValue`: Continuous endpoint of the dual value of Eq.146, PDF pp.19–20.
--   - `endpointTestingEntropyBits`: Testing entropy including the continuous epsilon=0 endpoint (p.19 fn.9). The Definition A.1 domain is enforced below. At rho=0 the positive-epsilon primal is infeasible, so its value is infinity and its entropy is minus infinity.
--   - `prefixMarginal`: Actual prefix marginal for heterogeneous systems, chain rule, PDF p.1. Rows and columns agree on all discarded systems; all such diagonal entries are summed. The retained prefix uses the subtype of indices less than k.
--   - `traceMiddle`: Marginal on A,C, tracing out the middle conditioning register, Eq.205, p.26.
--   - `squashedEntanglement`: Squashed entanglement, Eq.205, PDF p.26, in the finite-system setting. All finite ancillary dimensions occur in the infimum, with no fixed dimension cap. The marginal condition implies trace one; the density predicate makes it explicit.
--   - `extensionMarginal`: One A,C_i marginal of a k-extension, p.4 fn.4 and PDF pp.27–28. Summing over full strings with the i-th coordinate fixed counts each discarded configuration once, with no factor of dim C.
--   - `KExtendible`: k-extendibility on C: a density extension has the same A,C_i marginal for every i. Symmetry may be obtained by averaging and is not an extra premise (PDF p.4 fn.4, pp.27–28).
--   - `separableDistance`: Distance to the finite-dimensional separable density states, Eq.217, p.28. On density inputs this infimum is over a nonempty set bounded in [0,1].
--   - `antisymmetricState`: Normalized two-party totally antisymmetric state, PDF p.28, d>=2. Its antisymmetric projector is (identity-swap)/2, with rank d(d-1)/2.
--   - `spechtBell`: Eq.196, PDF p.25, in paired conjugate Specht coordinates. The second Schur basis is the conjugate of the first, so the canonical Bell vector is invariant even when the library's orthonormal bases are complex.
--   - `pairedSchurSynthesis`: Eq.193 synthesis in compatible Schur-Weyl coordinates, PDF pp.25–26. The inverse of the D transform is its adjoint; the E transform is its complex conjugate. These are computed transforms, not parameters assumed to decompose symmetric vectors. The Specht factor is fixed before the input vector.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, https://arxiv.org/abs/1410.0664v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

/-! Fawzi–Renner, arXiv:1410.0664v3. Local interfaces below are finite dimensional.
Separable-space claims are explicitly deferred, without finite replacements. -/
noncomputable section
open Filter MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)
open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Eq.17, PDF p.5: includes the absolute trace correction. -/
def generalizedTraceDistance {I : Type*} [Fintype I] [DecidableEq I] (X Y : Op I) : ℝ :=
  traceDistance X Y + |(X-Y).trace.re| / 2

/-- Eq.16, PDF p.5: normalized relative entropy in bits; infinity on support failure.
The accepted unnormalized entropy in nats is divided by tr(X) ln(2).
The zero-first-argument convention is zero. Lemma 2.3 excludes it eventually. -/
def normalizedRelativeEntropyBits {I : Type*} [Fintype I] [DecidableEq I] (X Y : Op I) : EReal :=
  if X = 0 then 0 else
    QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy X Y *
      (((X.trace.re * Real.log 2)⁻¹ : ℝ) : EReal)

/-- Invariance under all permutations, PDF pp.9,13. -/
def copyPermutationInvariant {I : Type*} {n : ℕ} (X : Op (Fin n → I)) : Prop :=
  ∀ p : Equiv.Perm (Fin n), permute p X = X

/-- Same permutation on both groups of copies, PDF p.12. -/
def GroupInvariant {D E : Type*} {n : ℕ}
    (X : Op ((Fin n → D) × (Fin n → E))) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) x y,
    X (x.1 ∘ p, x.2 ∘ p) (y.1 ∘ p, y.2 ∘ p) = X x y

/-- Norm at most one via W†W <= identity; W need not be positive (PDF p.13). -/
def Contractive {I : Type*} [Fintype I] [DecidableEq I] (W : Op I) : Prop :=
  OperatorLE (Wᴴ * W) 1

/-- Completely positive, trace non-increasing map (PDF pp.6,22). -/
def TNI {I J : Type*} [Fintype I] [Fintype J] (W : Superop I J) : Prop :=
  CP W ∧ ∀ X : Op I, X.PosSemidef → (W X).trace.re ≤ X.trace.re

/-- Separate input/output permutation actions (PDF p.12). -/
def copyPermutationCovariant {D E : Type*} {n : ℕ} (W : Superop (Fin n → D) (Fin n → E)) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) X, W (permute p X) = permute p (W X)

/-- Explicit omitted identity on the second factor (PDF p.13 fn.6). -/
def liftFirst {R S : Type*} [DecidableEq S] (W : Op R) : Op (R × S) :=
  Matrix.kronecker W 1

/-- Diagonal in the ON basis given by the columns of a unitary matrix, PDF p.14. -/
def DiagonalIn {I : Type*} [Fintype I] (B X : Op I) : Prop :=
  ∀ i j, i ≠ j → (Bᴴ * X * B) i j = 0

/-- Eq.88 dimension parameter, PDF p.13. -/
def dimensionParameter (R S : Type*) [Fintype R] [Fintype S] : ℕ :=
  Fintype.card R * Fintype.card S ^ 2

/-- Eq.88 factor (n+1)^(-d²), PDF pp.13–14. -/
def fidelityFactor (n d : ℕ) : ℝ := ((n : ℝ)+1) ^ (-(d^2 : ℝ))

/-- Extensions are PSD, not necessarily normalized (PDF p.12). -/
abbrev Extensions {D E : Type*} [Fintype E] [Fintype D] (sigma : Op D) :=
  {X : Op (D × E) // X.PosSemidef ∧ traceRight X = sigma}

/-- Coordinate Borel sigma algebra on fixed-marginal extensions (PDF p.12).
This is the pullback of the finite complex matrix-entry coordinates. -/
def extensionMeasurable {D E : Type*} [Fintype D] [Fintype E] (sigma : Op D) :
    MeasurableSpace (Extensions (E := E) sigma) :=
  MeasurableSpace.comap
    (fun Z : Extensions (E := E) sigma =>
      fun q : (D × E) × (D × E) => Z.val q.1 q.2) inferInstance

/-- Coordinate measurability of extensions, including zero marginal (PDF p.12). -/
example {D E : Type*} [Fintype D] [Fintype E] (sigma : Op D) :
    Measurable[extensionMeasurable (E := E) sigma]
      (fun Z : Extensions (E := E) sigma =>
        fun q : (D × E) × (D × E) => Z.val q.1 q.2) :=
  comap_measurable _

/-- Matrix-unit coordinate measurable structure for channels (PDF p.12). -/
def channelMeasurable (D E : Type*) [Fintype D] [Fintype E] [DecidableEq D] :
    MeasurableSpace {W : Superop D E // IsChannel W} :=
  MeasurableSpace.comap
    (fun W : {W : Superop D E // IsChannel W} =>
      fun q : D × D × E × E => W.val (Matrix.single q.1 q.2.1 1) q.2.2.1 q.2.2.2)
    inferInstance

/-- Mean tensor channel, evaluated on every operator, including entangled inputs
(PDF p.12). The theorem explicitly supplies coordinate integrability. -/
def meanChannel {D E : Type*} [Fintype D] [Fintype E] [DecidableEq D]
    (mu : @Measure {W : Superop D E // IsChannel W} (channelMeasurable D E)) (n : ℕ) :
    Superop (Fin n → D) (Fin n → E) := by
  letI := channelMeasurable D E
  exact fun X y z => ∫ W, piSuperop (fun _ : Fin n => W.val) X y z ∂mu

/-- Finite conditional mutual information in bits, PDF p.1. -/
def cmi {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (X : Op (A × (B × C))) : ℝ :=
  vnEntropy (marginalAB X) + vnEntropy (traceLeft X) -
    vnEntropy (traceRight (traceLeft X)) - vnEntropy X

/-- Markov-chain property, Eq.1 (PDF p.1), with identity on A. -/
def Markov {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] [DecidableEq B]
    (X : Op (A × (B × C))) : Prop :=
  ∃ T : Superop B (B × C), IsChannel T ∧ idTensorSuperop T (marginalAB X) = X

/-- Eq.11 qcq input in a specified orthonormal basis of B (PDF p.3). -/
def qcq {A B C : Type*} [Fintype B] (basis : Op B) (p : B → ℝ)
    (rho : B → Op (A × C)) : Op (A × (B × C)) :=
  fun x y => ∑ b, (p b : ℂ) * basis x.2.1 b * conj (basis y.2.1 b) *
    rho b (x.1,x.2.2) (y.1,y.2.2)

/-- Eq.13 explicitly reconstructed qcq state (PDF p.3). -/
def qcqRecovered {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (basis : Op B) (p : B → ℝ) (rho : B → Op (A × C)) : Op (A × (B × C)) :=
  fun x y => ∑ b, (p b : ℂ) * basis x.2.1 b * conj (basis y.2.1 b) *
    traceRight (rho b) x.1 y.1 * traceLeft (rho b) x.2.2 y.2.2

/-- Support-inverse Petz map with specified rotations, PDF pp.15,19. -/
def rotatedPetzRecovery {B C : Type*} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (rhoBC : Op (B × C)) (U : Op B) (V : Op (B × C)) : Superop B (B × C) :=
  let S := cfc Real.sqrt rhoBC
  let R := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (traceRight rhoBC)
  fun X => V * S * Matrix.kronecker (R * U * X * Uᴴ * R) 1 * S * Vᴴ

/-- Computed CP deficit completion, PDF p.19. If the two deficits have zero trace,
use the product marginal state to complete outside the support as well. Otherwise
the completion state is their tensor product divided by their common trace squared. -/
def completedPetz {B C : Type*} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (rhoBC : Op (B × C)) (U : Op B) (V : Op (B × C)) : Superop B (B × C) :=
  let P := rotatedPetzRecovery rhoBC U V
  let rhoB := traceRight rhoBC
  let Y := P rhoB
  let t := (rhoB - traceRight Y).trace.re
  let tau := if t = 0 then Matrix.kronecker rhoB (traceLeft rhoBC) else
    (((t^2)⁻¹ : ℝ) : ℂ) • Matrix.kronecker (rhoB-traceRight Y) (traceLeft rhoBC-traceLeft Y)
  fun X => P X + (X.trace - (P X).trace) • tau

/-- Negative log in bits, with +infinity at zero probability (PDF p.19 fn.11). -/
def negLogBits (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊤ else if x = ⊤ then ⊥ else ((-Real.logb 2 x.toReal : ℝ) : EReal)

/-- Eq.142, PDF p.19, on the positive epsilon domain needed below. -/
def normalizedTestingEntropyBits {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : ℝ) (rho sigma : Op I) : EReal :=
  negLogBits (sInf {v : ℝ≥0∞ | ∃ Q : Op I, IsEffect Q ∧
    epsilon ≤ (Q*rho).trace.re ∧ v = ENNReal.ofReal ((Q*sigma).trace.re / epsilon)})

/-- Eq.143, PDF p.19: equivalent infimum of finite domination logarithms.
Empty domination domain has value +infinity; epsilon=0 is permitted. -/
def maxEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : ℝ) (rho sigma : Op I) : EReal :=
  sInf {v : EReal | ∃ (lam : ℝ) (bar : Op I), 0 < lam ∧ bar.PosSemidef ∧
    bar.trace.re ≤ 1 ∧ 1-rootFidelity bar rho^2 ≤ epsilon^2 ∧
    OperatorLE bar ((lam : ℂ) • sigma) ∧ v = ((Real.logb 2 lam : ℝ) : EReal)}

/-! Concrete sanity checks (no theorem proofs are supplied in this stage). -/
example {I : Type*} [Fintype I] [DecidableEq I] : Contractive (0 : Op I) := by
  simpa [Contractive, OperatorLE] using (Matrix.PosSemidef.one : (1 : Op I).PosSemidef)

example {I J : Type*} [Fintype I] [Fintype J] : CP (0 : Superop I J) := by
  refine ⟨0, (fun _ => 0), ?_⟩
  intro X
  simp [krausApply]

example {I J : Type*} [Fintype I] [Fintype J] : TNI (0 : Superop I J) := by
  constructor
  · refine ⟨0, (fun _ => 0), ?_⟩
    intro X
    simp [krausApply]
  · intro X hX
    simpa using (Complex.nonneg_iff.mp hX.trace_nonneg).1

example {I : Type*} [Fintype I] (B : Op I) : DiagonalIn B 0 := by
  simp [DiagonalIn]

example : dimensionParameter Unit Unit = 1 := by simp [dimensionParameter]

example (d : ℕ) : fidelityFactor 0 d = 1 := by simp [fidelityFactor]

example {R S : Type*} [DecidableEq S] : liftFirst (0 : Op R) = (0 : Op (R × S)) := by
  ext x y
  simp [liftFirst, Matrix.kronecker]

example {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} :
    copyPermutationInvariant (0 : Op (Fin n → I)) := by
  intro p
  rfl

example {D E : Type*} {n : ℕ} :
    @GroupInvariant D E n (0 : Op ((Fin n → D) × (Fin n → E))) := by
  unfold GroupInvariant
  intro p x y
  rfl

example {D E : Type*} {n : ℕ} :
    @copyPermutationCovariant D E n (0 : Superop (Fin n → D) (Fin n → E)) := by
  unfold copyPermutationCovariant
  intro p X
  rfl

example {A B C : Type*} [Fintype C] : marginalAB (0 : Op (A × (B × C))) = 0 := by
  ext x y
  simp [marginalAB]

example {A B C : Type*} [Fintype B] (basis : Op B) (rho : B → Op (A × C)) :
    qcq basis (fun _ => 0) rho = 0 := by
  ext x y
  simp [qcq]

example {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (basis : Op B) (rho : B → Op (A × C)) : qcqRecovered basis (fun _ => 0) rho = 0 := by
  ext x y
  simp [qcqRecovered]

example {B C : Type*} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (U : Op B) (V : Op (B × C)) (X : Op B) : rotatedPetzRecovery 0 U V X = 0 := by
  simp [rotatedPetzRecovery, cfc_zero]

example {B C : Type*} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]
    (U : Op B) (V : Op (B × C)) (X : Op B) : completedPetz 0 U V X = 0 := by
  ext x y
  simp [completedPetz, rotatedPetzRecovery, cfc_zero, traceRight, traceLeft,
    Matrix.kronecker, Matrix.mul_apply]

example {I : Type*} [Fintype I] [DecidableEq I] (X : Op I) : generalizedTraceDistance X X = 0 := by
  simp [generalizedTraceDistance, traceDistance, traceNorm, cfc_zero]

example {I : Type*} [Fintype I] [DecidableEq I] (Y : Op I) : normalizedRelativeEntropyBits 0 Y = 0 := by
  simp [normalizedRelativeEntropyBits]

example {I : Type*} (X : Op I) (x y : Fin 0 → I) : matrixPower X 0 x y = 1 := by
  simp [matrixPower]

example {D E : Type*} (X : Op (D × E))
    (x y : (Fin 0 → D) × (Fin 0 → E)) : groupedPower X 0 x y = 1 := by
  simp [groupedPower]

example {I : Type*} [Fintype I] [DecidableEq I] (X : Op I) : OperatorLE X X := by
  simpa [OperatorLE] using (Matrix.PosSemidef.zero : (0 : Op I).PosSemidef)

example {I : Type*} {n : ℕ} (X : Op (Fin n → I)) : permute (Equiv.refl _) X = X := rfl

example : negLogBits 0 = ⊤ := by simp [negLogBits]

example : negLogBits 1 = 0 := by simp [negLogBits]

example {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] : cmi (0 : Op (A × (B × C))) = 0 := by
  have hab : marginalAB (0 : Op (A × (B × C))) = 0 := by
    ext x y
    simp [marginalAB]
  have hbc : traceLeft (0 : Op (A × (B × C))) = 0 := by
    ext x y
    simp [traceLeft]
  have hb : traceRight (0 : Op (B × C)) = 0 := by
    ext x y
    simp [traceRight]
  simp only [cmi, hab, hbc, hb]
  simp [vnEntropy, cfc_zero]

/-- Spectral mass in the closed entropy window of Eq.42, PDF pp.7–8.
Repeated eigenvalues are counted with multiplicity, equivalently taking the trace
of the spectral projector times the tensor-power state. This is not the
accepted classical strong-typicality mass Dependency50.P48.typicalMass. -/
def entropyWindowMass {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Op I) (n : ℕ) (delta : ℝ) : ℝ :=
  ∑ i : Fin (Fintype.card (Fin n → I)),
    let s := ascEigenvalues (matrixPower rho n) i
    if (2 : ℝ) ^ (-(n : ℝ) * (vnEntropy rho + delta)) ≤ s ∧
      s ≤ (2 : ℝ) ^ (-(n : ℝ) * (vnEntropy rho - delta)) then s else 0

/-- Unnormalized rank-one operator, PDF pp.21,23. -/
def vectorOuterProduct {I : Type*} (psi : I → ℂ) : Op I :=
  pureDensity (WithLp.toLp 2 psi)

/-- A purification has the specified marginal; no normalization is imposed
when the marginal is an arbitrary nonnegative operator, PDF p.21.
Frontier18.P01.Purifies instead takes a normalized PureState; it cannot
represent the arbitrary-trace vectors required here. -/
def UnnormalizedPurifies {D R : Type*} [Fintype R] (psi : D × R → ℂ) (rho : Op D) : Prop :=
  traceRight (vectorOuterProduct psi) = rho

/-- Primal value in Eq.142 before taking the negative logarithm, PDF p.19. -/
def testingValue {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : ℝ) (rho sigma : Op I) : ℝ≥0∞ :=
  sInf {v : ℝ≥0∞ | ∃ Q : Op I, IsEffect Q ∧
    epsilon ≤ (Q*rho).trace.re ∧ v = ENNReal.ofReal ((Q*sigma).trace.re / epsilon)}

/-- Dual value in Eq.146 for positive epsilon, PDF pp.19–20.
Taking the supremum of nonnegative parts leaves the supremum unchanged: mu=0
is feasible and has value zero. -/
def dualTestingValue {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : ℝ) (rho sigma : Op I) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ (mu : ℝ) (Y : Op I), 0 ≤ mu ∧ Y.PosSemidef ∧
    OperatorLE ((mu : ℂ) • (rho-Y)) sigma ∧
    v = ENNReal.ofReal (mu * (1-Y.trace.re/epsilon))}

/-- Continuous right endpoint of the increasing primal value, footnote 9,
PDF p.19. For positive epsilon this is exactly the original optimization.
The definition does not replace any asserted limit by a liminf. -/
def endpointTestingValue {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : ℝ) (rho sigma : Op I) : ℝ≥0∞ :=
  if epsilon = 0 then sInf {v : ℝ≥0∞ | ∃ e : ℝ, 0 < e ∧ v = testingValue e rho sigma}
  else testingValue epsilon rho sigma

/-- Continuous endpoint of the dual value of Eq.146, PDF pp.19–20. -/
def endpointDualValue {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : ℝ) (rho sigma : Op I) : ℝ≥0∞ :=
  if epsilon = 0 then sInf {v : ℝ≥0∞ | ∃ e : ℝ, 0 < e ∧ v = dualTestingValue e rho sigma}
  else dualTestingValue epsilon rho sigma

/-- Testing entropy including the continuous epsilon=0 endpoint (p.19 fn.9).
The Definition A.1 domain is enforced below. At rho=0 the positive-epsilon
primal is infeasible, so its value is infinity and its entropy is minus infinity. -/
def endpointTestingEntropyBits {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon : ℝ) (rho sigma : Op I) : EReal :=
  negLogBits (endpointTestingValue epsilon rho sigma)

/-- Actual prefix marginal for heterogeneous systems, chain rule, PDF p.1.
Rows and columns agree on all discarded systems; all such diagonal entries
are summed. The retained prefix uses the subtype of indices less than k. -/
def prefixMarginal {n : ℕ} {H : Fin n → Type*} {B C : Type*}
    [∀ i, Fintype (H i)]
    (rho : Op (((i : Fin n) → H i) × (B × C))) (k : ℕ) :
    Op (((i : {j : Fin n // j.val < k}) → H i.val) × (B × C)) :=
  fun a b => ∑ x : (i : Fin n) → H i, ∑ y : (i : Fin n) → H i,
    if (∀ (i : Fin n) (h : i.val < k), x i = a.1 ⟨i,h⟩ ∧ y i = b.1 ⟨i,h⟩) ∧
      (∀ i : Fin n, k ≤ i.val → x i = y i)
    then rho (x,a.2) (y,b.2) else 0

/-- Marginal on A,C, tracing out the middle conditioning register, Eq.205, p.26. -/
def traceMiddle {A E C : Type*} [Fintype E]
    (rho : Op (A × (E × C))) : Op (A × C) :=
  fun x y => ∑ e, rho (x.1,(e,x.2)) (y.1,(e,y.2))

/-- Squashed entanglement, Eq.205, PDF p.26, in the finite-system setting.
All finite ancillary dimensions occur in the infimum, with no fixed dimension cap.
The marginal condition implies trace one; the density predicate makes it explicit. -/
def squashedEntanglement {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (rho : Op (A × C)) : ℝ :=
  sInf {v : ℝ | ∃ (m : ℕ), 0 < m ∧ ∃ X : Op (A × (Fin m × C)),
    IsDensityMatrix X ∧ traceMiddle X = rho ∧ v = cmi X / 2}

/-- One A,C_i marginal of a k-extension, p.4 fn.4 and PDF pp.27–28.
Summing over full strings with the i-th coordinate fixed counts each discarded
configuration once, with no factor of dim C. -/
def extensionMarginal {A C : Type*} [Fintype C] {k : ℕ}
    (X : Op (A × (Fin k → C))) (i : Fin k) : Op (A × C) :=
  fun x y => ∑ z : Fin k → C,
    if z i = x.2 then X (x.1,z) (y.1,Function.update z i y.2) else 0

/-- k-extendibility on C: a density extension has the same A,C_i marginal
for every i. Symmetry may be obtained by averaging and is not an extra premise
(PDF p.4 fn.4, pp.27–28). -/
def KExtendible {A C : Type*} [Fintype A] [Fintype C]
    (k : ℕ) (rho : Op (A × C)) : Prop :=
  ∃ X : Op (A × (Fin k → C)), IsDensityMatrix X ∧
    ∀ i : Fin k, extensionMarginal X i = rho

/-- Distance to the finite-dimensional separable density states, Eq.217, p.28.
On density inputs this infimum is over a nonempty set bounded in [0,1]. -/
def separableDistance {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (rho : Op (A × C)) : ℝ :=
  sInf {v : ℝ | ∃ sigma : Op (A × C),
    QAlgorithms.Entanglement.IsSeparableDensity sigma ∧
    v = generalizedTraceDistance rho sigma}

/-- Normalized two-party totally antisymmetric state, PDF p.28, d>=2.
Its antisymmetric projector is (identity-swap)/2, with rank d(d-1)/2. -/
def antisymmetricState (d : ℕ) : Op (Fin d × Fin d) :=
  Matrix.of fun x y =>
    (((((d : ℝ) * ((d : ℝ) - 1))⁻¹ : ℝ) : ℂ)) *
      ((if x = y then (1 : ℂ) else 0) -
        (if x.1 = y.2 ∧ x.2 = y.1 then (1 : ℂ) else 0))

/-- Zero vectors purify the zero operator, including unnormalized inputs. -/
example {D R : Type*} [Fintype R] : UnnormalizedPurifies (fun _ : D × R => 0) (0 : Op D) := by
  ext x y
  simp [UnnormalizedPurifies, vectorOuterProduct, pureDensity, traceRight]

example {I : Type*} : vectorOuterProduct (fun _ : I => 0) = 0 := by
  ext x y
  simp [vectorOuterProduct, pureDensity]

/-- At positive epsilon the endpoint adapter is precisely Eq.142. -/
example {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Op I)
    (e : ℝ) (he : e ≠ 0) :
    endpointTestingEntropyBits e rho sigma = normalizedTestingEntropyBits e rho sigma := by
  simp [endpointTestingEntropyBits, endpointTestingValue, he, testingValue,
    normalizedTestingEntropyBits]

example {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Op I)
    (e : ℝ) (he : e ≠ 0) : endpointDualValue e rho sigma = dualTestingValue e rho sigma := by
  simp [endpointDualValue, he]

/-- Marginalizing zero does not introduce a multiplicity or normalization term. -/
example {n : ℕ} {H : Fin n → Type*} {B C : Type*} [∀ i, Fintype (H i)] (k : ℕ) :
    prefixMarginal (0 : Op (((i : Fin n) → H i) × (B × C))) k = 0 := by
  ext a b
  simp [prefixMarginal]

example {A E C : Type*} [Fintype E] : traceMiddle (0 : Op (A × (E × C))) = 0 := by
  ext x y
  simp [traceMiddle]

example {A C : Type*} [Fintype C] {k : ℕ} (i : Fin k) :
    extensionMarginal (0 : Op (A × (Fin k → C))) i = 0 := by
  ext x y
  simp [extensionMarginal]

/-- The antisymmetric projection has zero weight on repeated basis letters. -/
example (d : ℕ) (i : Fin d) : antisymmetricState d (i,i) (i,i) = 0 := by
  simp [antisymmetricState, Matrix.one_apply]

/-- Eq.196, PDF p.25, in paired conjugate Specht coordinates.
The second Schur basis is the conjugate of the first, so the canonical Bell
vector is invariant even when the library's orthonormal bases are complex. -/
def spechtBell {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :
    (Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)) ×
      Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda))) → ℂ :=
  fun x => if x.1 = x.2 then
    ((Real.sqrt (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda) : ℝ))⁻¹ : ℂ) else 0

/-- Eq.193 synthesis in compatible Schur-Weyl coordinates, PDF pp.25–26.
The inverse of the D transform is its adjoint; the E transform is its complex
conjugate. These are computed transforms, not parameters assumed to decompose
symmetric vectors. The Specht factor is fixed before the input vector. -/
def pairedSchurSynthesis (d n : ℕ)
    (phi : (lambda : QAlgorithms.Schur.Partition d n) →
      (Fin (Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda)) ×
        Fin (Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda))) → ℂ) :
    ((Fin n → Fin d) × (Fin n → Fin d)) → ℂ :=
  fun x => ∑ lambda : QAlgorithms.Schur.Partition d n,
    ∑ a : Fin (Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda)),
    ∑ b : Fin (Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda)),
    ∑ r : Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)),
    ∑ s : Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)),
      conj (QAlgorithms.Schur.decomposition d n ⟨lambda,(r,a)⟩ x.1) *
        QAlgorithms.Schur.decomposition d n ⟨lambda,(s,b)⟩ x.2 *
        phi lambda (a,b) * spechtBell lambda (r,s)

example {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (r s : Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda))) (h : r ≠ s) :
    spechtBell lambda (r,s) = 0 := by simp [spechtBell, h]

example (d n : ℕ) : pairedSchurSynthesis d n (fun _ _ => 0) = 0 := by
  funext x
  simp [pairedSchurSynthesis]

end QAlgorithms.Papers.Independent.Claimed50.P12


