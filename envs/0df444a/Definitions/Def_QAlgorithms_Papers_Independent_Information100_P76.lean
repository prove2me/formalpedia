-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76
-- name    : QAlgorithms_Papers_Independent_Information100_P76
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:56:23.489882+00:00
-- url     : https://prove2.me/theorems/832d773f-45fd-4a5e-abf4-caf94843258b
-- title:
--   Definitions for Bath dimension and initial entropy for closed repeated use of a quantum channel
-- statement:
--   The objects the formalized statements of *Bath dimension and initial entropy for closed repeated use of a quantum channel* (arXiv:2609.18267) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Op`: PDF pp.3–4: finite square operators, with dimension an actual natural number.
--   - `maximallyMixed`: PDF pp.3–4: normalized maximally mixed state; used only at positive dimensions.
--   - `halfDistance`: PDF p.3: half trace distance, distinct from operator norm.
--   - `canonicalPurification`: PDF p.4: the normalized canonical input purification has coefficients `(sqrt rho)_(s,i)` in reference-system order, so its reference marginal is `rho` transposed.
--   - `chi`: PDF p.4, Definition 1.3: reference-output state chi.
--   - `exchangeCost`: PDF pp.3–4: maximum entropy exchange. The reference-output state and a pure Stinespring environment have the same nonzero spectrum. The supremum is a maximum for a CPTP map in positive finite dimension.
--   - `qzMarginal`: PDF p.4: QZ marginal of a QAZ operator, in the order `(Q,A),Z`.
--   - `extensionObjective`: PDF p.4, (1.2): conditional entropy S(QA|Z), with no auxiliary dimension penalty.
--   - `extensionValues`: PDF p.4, (1.2): exact QZ independence and approximate QA marginal. All states are normalized; `z` ranges over all positive finite dimensions, without a size bound.
--   - `smoothedCost`: PDF p.4: smoothed extension infimum. For a full-rank density and CPTP map, its feasible set is nonempty and bounded below, including at zero error.
--   - `exactInputCost`: PDF p.4: exact fixed-input extension infimum, independently of the smoothing limit.
--   - `intrinsicCost`: PDF p.4: monotonicity makes the positive-error limit the supremum over positive errors. This supremum is taken at fixed rho, before the full-rank input supremum.
--   - `Collision`: PDF p.4, Definition 1.4: one active-only square unitary and its actual initializer. No operated purifier is present; every allocated bath dimension is in R.
--   - `collisionOutput`: PDF p.4: the actual joint output of a collision, with an independent bath input.
--   - `collisionChannel`: PDF p.4: system channel of the collision.
--   - `bathChannel`: PDF p.4: active bath channel, excluding any inert purifier.
--   - `gainFunction`: PDF p.4: input-dependent bath entropy gain.
--   - `collisionGain`: PDF p.4: maximum bath entropy gain over normalized inputs.
--   - `channelDistance`: PDF p.4: half diamond distance between channels, as its equivalent supremum over all finite reference-entangled density inputs. No reference size is fixed in this definition.
--   - `exactCollisionCost`: PDF p.4: intrinsic exact collision gain; the exact set is nonempty by square unitary completion of a finite pure Stinespring dilation.
--   - `approximateCollisionCost`: PDF p.6: infimum of uniform gains at positive channel tolerance.
--   - `choi`: PDF pp.4,7: normalized trace-one Choi operator.
--   - `samePositiveSpectrum`: PDF pp.7–8: equality of the positive spectra, including multiplicities; extra zero eigenvalues in the larger allocated bath are allowed.
--   - `choiSupportContained`: PDF p.8: support containment for PSD Choi operators, expressed by reverse kernel containment so that no inverse on the target kernel occurs.
--   - `repairModulus`: PDF p.8: bath-dimension-independent conditional entropy modulus, in bits.
--   - `dilationPurification`: PDF p.4: Stinespring purification built from a normalized Kraus family.
--   - `channelExtension`: PDF pp.4,9: channel E to Z applied to the fixed pure QAE dilation.
--   - `referenceLeakage`: PDF p.4: quantum mutual information I(Q;Z).
--   - `privacyFunnel`: PDF pp.4,9: zero-leakage quantum privacy funnel, X=E,Y=Q,R=A,W=Z. The objective is I(QA;Z); the subscript q in the paper means quantum.
--   - `generalizedDampingKraus`: PDF p.13: generalized amplitude damping in computational order. Reuse the frozen ordinary amplitude-damping family with weights sqrt(p), sqrt(1-p) and reversed basis in the second branch. For 0 <= nu,p <= 1 these are precisely the four source operators.
--   - `dampingChannel`: PDF p.13: generalized amplitude damping channel.
--   - `WeightedTracial`: PDF p.15: finite weighted-tracial dilation, with zero-probability sectors allowed. Each block is an actual finite collision with a uniformly mixed bath.
--   - `weightedChannel`: PDF p.15: channel implemented by sector-preserving weighted direct sum.
--   - `inWeightedTracialClosure`: PDF p.15: approximation closure of finite weighted-tracial dilations.
--   - `inSingleTracialClosure`: PDF p.15: approximation closure with one maximally mixed matrix bath.
--   - `gramMap`: PDF p.7: the Gram map L(E_ab)=A_a^* A_b.
--   - `gramSpace`: PDF p.7: D is the complex span of the Kraus Gram products.
--   - `amplify`: PDF p.7: amplification of a linear right inverse on the system matrix factor.
--   - `spanMap`: PDF p.7: rectangular maps with system coefficients in the prescribed Kraus span.
--   - `swapMatrix`: PDF p.20: swap on two copies of a finite register.
--   - `twoCopyAverage`: PDF p.20: uniform second-moment channel of a finite unitary ensemble.
--   - `isExactTwoDesign`: PDF p.20: exact uniform unitary two-design, expressed by the full two-copy Haar moment identity. In dimension one this moment is the identity, avoiding division by D^2-1. All norms in the matrix lemmas use Mathlib's Euclidean L2 operator norm scope.
--   - `decoupledOutput`: PDF p.20: trace out G from a CH operator in C=M tensor G order.
--   - `retainedSeedOutput`: PDF p.20: joint state with the physical independent uniform classical label retained. This cq construction initializes Z independently of CH jointly.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, https://arxiv.org/abs/2609.18267v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent2_P01

/-!
Statements from Douglas, arXiv:2609.18267v1. The closed causal implementation results
are deferred in this unit's GAPS.json; none is replaced by a numerical resource assignment.
All definitions below belong only to this paper. Compilation is pending batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open Filter

/-- PDF pp.3–4: finite square operators, with dimension an actual natural number. -/
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- PDF pp.3–4: normalized maximally mixed state; used only at positive dimensions. -/
def maximallyMixed (d : ℕ) : Op d := (1 / (d : ℂ)) • 1

/-- PDF p.3: half trace distance, distinct from operator norm. -/
def halfDistance {A : Type*} [Fintype A] [DecidableEq A]
    (X Y : Matrix A A ℂ) : ℝ := traceNorm (X - Y) / 2

/-- PDF p.4: the normalized canonical input purification has coefficients
`(sqrt rho)_(s,i)` in reference-system order, so its reference marginal is `rho` transposed. -/
def canonicalPurification {q : ℕ} (rho : Op q) :
    EuclideanSpace ℂ (Fin q × Fin q) :=
  WithLp.toLp 2 fun p => (cfc Real.sqrt rho) p.2 p.1

/-- PDF p.4, Definition 1.3: reference-output state chi. -/
def chi {q : ℕ} (Phi : Superop (Fin q) (Fin q)) (rho : Op q) :=
  idTensorSuperop (R := Fin q) Phi (pureDensity (canonicalPurification rho))

/-- PDF pp.3–4: maximum entropy exchange. The reference-output state and a pure
Stinespring environment have the same nonzero spectrum. The supremum is a maximum
for a CPTP map in positive finite dimension. -/
def exchangeCost {q : ℕ} (Phi : Superop (Fin q) (Fin q)) : ℝ :=
  sSup {v | ∃ rho : Op q, IsDensityMatrix rho ∧ v = vnEntropy (chi Phi rho)}

/-- PDF p.4: QZ marginal of a QAZ operator, in the order `(Q,A),Z`. -/
def qzMarginal {q z : ℕ}
    (sigma : Matrix ((Fin q × Fin q) × Fin z) ((Fin q × Fin q) × Fin z) ℂ) :
    Matrix (Fin q × Fin z) (Fin q × Fin z) ℂ :=
  fun p p' => ∑ a, sigma ((p.1, a), p.2) ((p'.1, a), p'.2)

/-- PDF p.4, (1.2): conditional entropy S(QA|Z), with no auxiliary dimension penalty. -/
def extensionObjective {q z : ℕ}
    (sigma : Matrix ((Fin q × Fin q) × Fin z) ((Fin q × Fin q) × Fin z) ℂ) : ℝ :=
  vnEntropy sigma - vnEntropy (traceLeft sigma)

/-- PDF p.4, (1.2): exact QZ independence and approximate QA marginal. All states
are normalized; `z` ranges over all positive finite dimensions, without a size bound. -/
def extensionValues {q : ℕ} (Phi : Superop (Fin q) (Fin q)) (rho : Op q)
    (epsilon : ℝ) : Set ℝ :=
  {v | ∃ z : ℕ, 0 < z ∧ ∃ sigma :
      Matrix ((Fin q × Fin q) × Fin z) ((Fin q × Fin q) × Fin z) ℂ,
    IsDensityMatrix sigma ∧
    qzMarginal sigma = Matrix.kronecker rho.transpose (traceLeft sigma) ∧
    halfDistance (traceRight sigma) (chi Phi rho) ≤ epsilon ∧
    v = extensionObjective sigma}

/-- PDF p.4: smoothed extension infimum. For a full-rank density and CPTP map,
its feasible set is nonempty and bounded below, including at zero error. -/
def smoothedCost {q : ℕ} (Phi : Superop (Fin q) (Fin q)) (rho : Op q)
    (epsilon : ℝ) : ℝ := sInf (extensionValues Phi rho epsilon)

/-- PDF p.4: exact fixed-input extension infimum, independently of the smoothing limit. -/
def exactInputCost {q : ℕ} (Phi : Superop (Fin q) (Fin q)) (rho : Op q) : ℝ :=
  sInf (extensionValues Phi rho 0)

/-- PDF p.4: monotonicity makes the positive-error limit the supremum over positive
errors. This supremum is taken at fixed rho, before the full-rank input supremum. -/
def intrinsicCost {q : ℕ} (Phi : Superop (Fin q) (Fin q)) : ℝ :=
  sSup {v | ∃ rho : Op q, IsDensityMatrix rho ∧ rho.PosDef ∧
    v = sSup {w | ∃ epsilon : ℝ, 0 < epsilon ∧ w = smoothedCost Phi rho epsilon}}

/-- PDF p.4, Definition 1.4: one active-only square unitary and its actual initializer.
No operated purifier is present; every allocated bath dimension is in R. -/
structure Collision (q : ℕ) where
  R : ℕ
  positiveDimension : 0 < R
  tau : Op R
  normalized : IsDensityMatrix tau
  U : Matrix.unitaryGroup (Fin q × Fin R) ℂ

/-- PDF p.4: the actual joint output of a collision, with an independent bath input. -/
def collisionOutput {q : ℕ} (C : Collision q) (rho : Op q) :=
  (C.U : Matrix (Fin q × Fin C.R) (Fin q × Fin C.R) ℂ) *
    Matrix.kronecker rho C.tau *
    (C.U : Matrix (Fin q × Fin C.R) (Fin q × Fin C.R) ℂ)ᴴ

/-- PDF p.4: system channel of the collision. -/
def collisionChannel {q : ℕ} (C : Collision q) : Superop (Fin q) (Fin q) :=
  fun rho => traceRight (collisionOutput C rho)

/-- PDF p.4: active bath channel, excluding any inert purifier. -/
def bathChannel {q : ℕ} (C : Collision q) : Superop (Fin q) (Fin C.R) :=
  fun rho => traceLeft (collisionOutput C rho)

/-- PDF p.4: input-dependent bath entropy gain. -/
def gainFunction {q : ℕ} (C : Collision q) (rho : Op q) : ℝ :=
  vnEntropy (bathChannel C rho) - vnEntropy C.tau

/-- PDF p.4: maximum bath entropy gain over normalized inputs. -/
def collisionGain {q : ℕ} (C : Collision q) : ℝ :=
  sSup {v | ∃ rho : Op q, IsDensityMatrix rho ∧ v = gainFunction C rho}

/-- PDF p.4: half diamond distance between channels, as its equivalent supremum over
all finite reference-entangled density inputs. No reference size is fixed in this definition. -/
def channelDistance {q : ℕ} (Psi Phi : Superop (Fin q) (Fin q)) : ℝ :=
  sSup {v | ∃ d : ℕ, 0 < d ∧
    ∃ rho : Matrix (Fin d × Fin q) (Fin d × Fin q) ℂ, IsDensityMatrix rho ∧
      v = halfDistance (idTensorSuperop (R := Fin d) Psi rho)
        (idTensorSuperop (R := Fin d) Phi rho)}

/-- PDF p.4: intrinsic exact collision gain; the exact set is nonempty by square
unitary completion of a finite pure Stinespring dilation. -/
def exactCollisionCost {q : ℕ} (Phi : Superop (Fin q) (Fin q)) : ℝ :=
  sInf {v | ∃ C : Collision q, collisionChannel C = Phi ∧ v = collisionGain C}

/-- PDF p.6: infimum of uniform gains at positive channel tolerance. -/
def approximateCollisionCost {q : ℕ} (Phi : Superop (Fin q) (Fin q)) (eta : ℝ) : ℝ :=
  sInf {v | ∃ C : Collision q, channelDistance (collisionChannel C) Phi ≤ eta ∧
    v = collisionGain C}

/-- PDF pp.4,7: normalized trace-one Choi operator. -/
def choi {q : ℕ} (Phi : Superop (Fin q) (Fin q)) := chi Phi (maximallyMixed q)

/-- PDF pp.7–8: equality of the positive spectra, including multiplicities; extra
zero eigenvalues in the larger allocated bath are allowed. -/
def samePositiveSpectrum {a b : ℕ} (X : Op a) (Y : Op b) : Prop :=
  ∀ x : ℝ, 0 < x →
    (Finset.univ.filter fun i => ascEigenvalues X i = x).card =
      (Finset.univ.filter fun j => ascEigenvalues Y j = x).card

/-- PDF p.8: support containment for PSD Choi operators, expressed by reverse
kernel containment so that no inverse on the target kernel occurs. -/
def choiSupportContained {q : ℕ} (Psi Phi : Superop (Fin q) (Fin q)) : Prop :=
  ∀ v : (Fin q × Fin q) → ℂ, (choi Phi).mulVec v = 0 → (choi Psi).mulVec v = 0

/-- PDF p.8: bath-dimension-independent conditional entropy modulus, in bits. -/
def repairModulus (q : ℕ) (epsilon : ℝ) : ℝ :=
  4 * epsilon * Real.logb 2 q + (1 + epsilon) * binEntropy2 (epsilon / (1 + epsilon))

/-- PDF p.4: Stinespring purification built from a normalized Kraus family. -/
def dilationPurification {q k : ℕ} (A : Fin k → Op q) (rho : Op q) :
    EuclideanSpace ℂ ((Fin q × Fin q) × Fin k) :=
  WithLp.toLp 2 fun p => ∑ s, A p.2 p.1.2 s * (cfc Real.sqrt rho) s p.1.1

/-- PDF pp.4,9: channel E to Z applied to the fixed pure QAE dilation. -/
def channelExtension {q k z : ℕ} (A : Fin k → Op q) (rho : Op q)
    (Lambda : Superop (Fin k) (Fin z)) :=
  idTensorSuperop (R := Fin q × Fin q) Lambda (pureDensity (dilationPurification A rho))

/-- PDF p.4: quantum mutual information I(Q;Z). -/
def referenceLeakage {q z : ℕ}
    (sigma : Matrix ((Fin q × Fin q) × Fin z) ((Fin q × Fin q) × Fin z) ℂ) : ℝ :=
  let X := qzMarginal sigma
  vnEntropy (traceRight X) + vnEntropy (traceLeft X) - vnEntropy X

/-- PDF pp.4,9: zero-leakage quantum privacy funnel, X=E,Y=Q,R=A,W=Z.
The objective is I(QA;Z); the subscript q in the paper means quantum. -/
def privacyFunnel {q k : ℕ} (A : Fin k → Op q) (rho : Op q) : ℝ :=
  sSup {v | ∃ z : ℕ, 0 < z ∧ ∃ Lambda : Superop (Fin k) (Fin z),
    IsChannel Lambda ∧ referenceLeakage (channelExtension A rho Lambda) = 0 ∧
    v = vnEntropy (traceRight (channelExtension A rho Lambda)) -
      extensionObjective (channelExtension A rho Lambda)}

/-- PDF p.13: generalized amplitude damping in computational order. Reuse the frozen
ordinary amplitude-damping family with weights sqrt(p), sqrt(1-p) and reversed basis
in the second branch. For 0 <= nu,p <= 1 these are precisely the four source operators. -/
def generalizedDampingKraus (nu p : ℝ) : Fin 4 → Op 2 :=
  let lower : Bool → Op 2 := fun b =>
    (QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus nu b).submatrix
      (fun i : Fin 2 => decide (i = 1)) (fun i : Fin 2 => decide (i = 1))
  let upper : Bool → Op 2 := fun b =>
    (QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus nu b).submatrix
      (fun i : Fin 2 => decide (i = 0)) (fun i : Fin 2 => decide (i = 0))
  ![(Real.sqrt p : ℂ) • lower false,
    (Real.sqrt p : ℂ) • lower true,
    (Real.sqrt (1 - p) : ℂ) • upper false,
    (Real.sqrt (1 - p) : ℂ) • upper true]

/-- PDF p.13: generalized amplitude damping channel. -/
def dampingChannel (nu p : ℝ) : Superop (Fin 2) (Fin 2) :=
  krausApply (generalizedDampingKraus nu p)

/-- PDF p.15: finite weighted-tracial dilation, with zero-probability sectors allowed.
Each block is an actual finite collision with a uniformly mixed bath. -/
structure WeightedTracial (q : ℕ) where
  sectors : ℕ
  nonemptySectors : 0 < sectors
  weights : Fin sectors → ℝ
  nonnegativeWeights : ∀ j, 0 ≤ weights j
  totalWeight : ∑ j, weights j = 1
  block : Fin sectors → Collision q
  tracial : ∀ j, (block j).tau = maximallyMixed (block j).R

/-- PDF p.15: channel implemented by sector-preserving weighted direct sum. -/
def weightedChannel {q : ℕ} (W : WeightedTracial q) : Superop (Fin q) (Fin q) :=
  fun rho => ∑ j, (W.weights j : ℂ) • collisionChannel (W.block j) rho

/-- PDF p.15: approximation closure of finite weighted-tracial dilations. -/
def inWeightedTracialClosure {q : ℕ} (Phi : Superop (Fin q) (Fin q)) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ W : WeightedTracial q,
    channelDistance (weightedChannel W) Phi ≤ epsilon

/-- PDF p.15: approximation closure with one maximally mixed matrix bath. -/
def inSingleTracialClosure {q : ℕ} (Phi : Superop (Fin q) (Fin q)) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ C : Collision q,
    C.tau = maximallyMixed C.R ∧ channelDistance (collisionChannel C) Phi ≤ epsilon

/-- Scalar maximally mixed initializer is the unique scalar density operator. -/
example : maximallyMixed 1 = (1 : Op 1) := by
  simp [maximallyMixed]

/-- Identity service retains the entire canonical purification, not only its marginals. -/
example {q : ℕ} (rho : Op q) :
    chi (fun X => X) rho = pureDensity (canonicalPurification rho) := by
  ext p p'
  rfl

/-- The QZ trace sums over A and does not trace out the reference. -/
example {q z : ℕ} (sigma : Matrix ((Fin q × Fin q) × Fin z)
    ((Fin q × Fin q) × Fin z) ℂ) (i j : Fin q) (b c : Fin z) :
    qzMarginal sigma (i, b) (j, c) = ∑ a, sigma ((i, a), b) ((j, a), c) := rfl

/-- The active bath gain subtracts the actual initial entropy. -/
example {q : ℕ} (C : Collision q) (rho : Op q) :
    gainFunction C rho + vnEntropy C.tau = vnEntropy (bathChannel C rho) := by
  simp [gainFunction]

/-- At zero damping the lowering Kraus operator is zero, including parameter endpoints. -/
example (p : ℝ) : generalizedDampingKraus 0 p 1 = 0 := by
  ext i j
  simp [generalizedDampingKraus,
    QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, Matrix.submatrix]

/-- PDF p.7: the Gram map L(E_ab)=A_a^* A_b. -/
def gramMap {q k : ℕ} (A : Fin k → Op q) (E : Op k) : Op q :=
  ∑ a, ∑ b, E a b • ((A a)ᴴ * A b)

/-- PDF p.7: D is the complex span of the Kraus Gram products. -/
def gramSpace {q k : ℕ} (A : Fin k → Op q) : Submodule ℂ (Op q) :=
  Submodule.span ℂ (Set.range fun ab : Fin k × Fin k => (A ab.1)ᴴ * A ab.2)

/-- PDF p.7: amplification of a linear right inverse on the system matrix factor. -/
def amplify {q k d : ℕ} (R : Op q →ₗ[ℂ] Op k)
    (X : Matrix (Fin q × Fin d) (Fin q × Fin d) ℂ) :
    Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ :=
  fun a b => R (fun i j => X (i, a.2) (j, b.2)) a.1 b.1

/-- PDF p.7: rectangular maps with system coefficients in the prescribed Kraus span. -/
def spanMap {q k : ℕ} {I O : Type*} (A : Fin k → Op q)
    (B : Fin k → Matrix O I ℂ) : Matrix (Fin q × O) (Fin q × I) ℂ :=
  ∑ a, Matrix.kronecker (A a) (B a)

/-- PDF p.20: swap on two copies of a finite register. -/
def swapMatrix {I : Type*} [DecidableEq I] : Matrix (I × I) (I × I) ℂ :=
  fun a b => if a.1 = b.2 ∧ a.2 = b.1 then 1 else 0

/-- PDF p.20: uniform second-moment channel of a finite unitary ensemble. -/
def twoCopyAverage {I : Type*} [Fintype I] [DecidableEq I] {J : ℕ}
    (V : Fin J → Matrix.unitaryGroup I ℂ) (X : Matrix (I × I) (I × I) ℂ) :=
  (1 / (J : ℂ)) • ∑ j,
    let U := Matrix.kronecker (V j : Matrix I I ℂ) (V j : Matrix I I ℂ)
    U * X * Uᴴ

/-- PDF p.20: exact uniform unitary two-design, expressed by the full two-copy Haar
moment identity. In dimension one this moment is the identity, avoiding division by D^2-1.
All norms in the matrix lemmas use Mathlib's Euclidean L2 operator norm scope. -/
def isExactTwoDesign {I : Type*} [Fintype I] [DecidableEq I] {J : ℕ}
    (V : Fin J → Matrix.unitaryGroup I ℂ) : Prop :=
  ∀ X : Matrix (I × I) (I × I) ℂ,
    twoCopyAverage V X =
      if Fintype.card I = 1 then X else
        let D : ℂ := Fintype.card I
        ((D * X.trace - (swapMatrix * X).trace) / (D * (D ^ 2 - 1))) • 1 +
          ((D * (swapMatrix * X).trace - X.trace) / (D * (D ^ 2 - 1))) • swapMatrix

/-- PDF p.20: trace out G from a CH operator in C=M tensor G order. -/
def decoupledOutput {m g h : ℕ}
    (rho : Matrix ((Fin m × Fin g) × Fin h) ((Fin m × Fin g) × Fin h) ℂ)
    (V : Matrix.unitaryGroup (Fin m × Fin g) ℂ) :
    Matrix (Fin m × Fin h) (Fin m × Fin h) ℂ :=
  let U := Matrix.kronecker (V : Matrix (Fin m × Fin g) (Fin m × Fin g) ℂ)
    (1 : Op h)
  let X := U * rho * Uᴴ;
  fun a b => ∑ j, X ((a.1, j), a.2) ((b.1, j), b.2)

/-- PDF p.20: joint state with the physical independent uniform classical label retained.
This cq construction initializes Z independently of CH jointly. -/
def retainedSeedOutput {m g h J : ℕ}
    (rho : Matrix ((Fin m × Fin g) × Fin h) ((Fin m × Fin g) × Fin h) ℂ)
    (V : Fin J → Matrix.unitaryGroup (Fin m × Fin g) ℂ) :
    Matrix (Fin J × (Fin m × Fin h)) (Fin J × (Fin m × Fin h)) ℂ :=
  fun a b => if a.1 = b.1 then
    (1 / (J : ℂ)) * decoupledOutput rho (V a.1) a.2 b.2 else 0

/-- The swap matrix exchanges two distinct basis labels. -/
example : (swapMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (0, 1) (1, 0) = 1 := by
  simp [swapMatrix]

/-- The retained seed is classical: off-diagonal label blocks vanish exactly. -/
example {m g h J : ℕ}
    (rho : Matrix ((Fin m × Fin g) × Fin h) ((Fin m × Fin g) × Fin h) ℂ)
    (V : Fin J → Matrix.unitaryGroup (Fin m × Fin g) ℂ)
    (a b : Fin J) (hab : a ≠ b) (x y : Fin m × Fin h) :
    retainedSeedOutput rho V (a, x) (b, y) = 0 := by
  simp [retainedSeedOutput, hab]

end QAlgorithms.Papers.Independent.Information100.P76


