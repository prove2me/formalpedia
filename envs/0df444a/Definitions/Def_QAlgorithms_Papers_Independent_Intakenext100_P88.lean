-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P88
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:23:20.147201+00:00
-- url     : https://prove2.me/theorems/e810b85e-33a4-4ad0-a45a-9d2db5a24f69
-- title:
--   Definitions for Representation Learning via Quantum Neural Tangent Kernels
-- statement:
--   The objects the formalized statements of *Representation Learning via Quantum Neural Tangent Kernels* (arXiv:2111.04225) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ansatz`: PDF pp.2,19 Eqs.(1),(54): fixed unitary gates and Hermitian generators.
--   - `writtenProd`: PDF p.2 Eq.(1): increasing written order; the rightmost factor acts first. The frozen `orderedProd` has the opposite convention and is not used.
--   - `qntkFactor`: PDF p.2 Eq.(1): W_l exp(+i theta_l X_l).
--   - `qntkCircuit`: PDF p.2 Eq.(1): the actual ordered circuit.
--   - `circuitPrefix`: PDF p.3 Eq.(6): circuitPrefix excluding layer l.
--   - `circuitSuffix`: PDF p.3 Eq.(6): circuitSuffix excluding layer l.
--   - `coordinateDerivative`: PDF p.23: coordinate derivative with respect to a real trainable angle.
--   - `second`: PDF p.25: mixed derivative of the actual output, not a free tensor.
--   - `ExpectationNetwork`: PDF p.5 Eq.(23): normalized feature states and Hermitian observables.
--   - `expectationOutput`: PDF p.5 Eq.(23): real expectation, with first-slot-conjugate inner product.
--   - `expectationKernel`: PDF p.23 Eq.(90): the full real expectation-value QNTK.
--   - `scaledOutput`: PDF pp.3,24: absorb theta-star into W and rescale by delta.
--   - `jet`: PDF p.26 Eq.(111): linear jet at the expansion point.
--   - `expectationHessian`: PDF p.26 Eq.(111): mixed quadratic jet at the expansion point.
--   - `frozenKernel`: PDF p.24 Eq.(97): frozen Gram kernel with delta-squared scaling.
--   - `quadraticOutput`: PDF p.25 Eq.(105): retained quadratic Taylor polynomial, including 1/2.
--   - `deltaKernel`: PDF p.26 Eq.(114): cubic cross terms of the Taylor-jet Gram matrix.
--   - `thetaCoefficient`: PDF p.3 Eq.(5), p.19 Eq.(59): imaginary commutator expectation.
--   - `gCoefficient`: PDF p.7 Eq.(40), SM p.26 Eq.(109), corrected to match Eq.(126). Printed: nested interval conjugations include an extra W_l conjugation even for k=l. Changed: use the suffix-conjugated generators Y_l=S_l^dagger X_l S_l and A=U(0)^dagger O U(0), with the larger index in the outer commutator. Why: differentiating the original ordered circuit gives this coefficient; for one layer W=H, X=Z, O=Z and phi=|+>, the printed coefficient is -4 whereas -z''(0)=4. This body contains only matrices and inner products, not the derivative it evaluates.
--   - `metaKernel`: PDF p.7 Eq.(45): derivative definition of the meta-kernel.
--   - `l2Action`: Euclidean L2 action, used in every norm estimate.
--   - `frozenResidual`: PDF pp.24,30 Eqs.(98),(152): frozen residual recurrence before it is solved.
--   - `retainedResidual`: PDF pp.26-27,33: retain degree zero and one in an auxiliary kernel perturbation K+sD. This coefficient recurrence omits higher delta orders and does not describe exact nonlinear GD.
--   - `prediction`: PDF p.25 Eq.(102): unsolved general-data prediction recurrence.
--   - `logRate`: PDF p.6 Eq.(32): norm of -log(I-step K), through its convergent power series. This is the paper's norm-log statistic, not the slowest-eigenmode convergence rate.
--   - `AmplitudeModel`: PDF p.28 Eq.(128): normalized amplitude model.
--   - `basisAmplitude`: PDF p.28 Eq.(128): all computational-basis output coordinates.
--   - `doubledAmplitude`: PDF p.29 Eq.(138): false denotes z, true denotes conjugate z.
--   - `amplitudeKernel`: PDF p.29 Eq.(135): all four blocks of the complex Gram matrix.
--   - `amplitudeJet`: PDF pp.30-32: linear jet directly from the original circuit.
--   - `amplitudeHessian`: PDF pp.31-32: mixed quadratic jet, including equal layer indices.
--   - `frozenAmplitudeKernel`: PDF p.30 Eq.(150): frozen doubled kernel with rescaled angles.
--   - `deltaAmplitudeKernel`: PDF p.32 Eqs.(167)-(169): cubic cross terms computed from the actual jets. The inconsistent G^(1), G^(2) shorthands are not used.
--   - `quadraticAmplitude`: PDF p.31 Eq.(161): quadratic amplitude polynomial using correct circuit derivatives.
--   - `QuantumLayer`: PDF p.36 Eqs.(190),(195): incoming quantum ensemble with normalized feature states. Observables are independent over the reals, so m is the dimension of their real span.
--   - `incomingQuantumOutput`: PDF p.36: the actual incoming quantum expectation.
--   - `HybridLayer`: PDF p.36 Eqs.(193)-(194): centered Gaussian coordinates, jointly independent of incoming outputs. Finite fourth moments prevent default nonintegrable integrals.
--   - `preactivation`: PDF p.36 Eq.(193): affine preactivation, before any nonlinear activation.
--   - `connectedFour`: PDF p.37 Eq.(197): subtract all three disconnected Wick pairings.
--   - `productCovariance`: PDF p.38 Eq.(201): covariance of products, subtracting only one paired product.
--   - `kd`: PDF p.37 Eq.(200): Kronecker delta for classical output coordinates.
--   - `fourContraction`: PDF p.37 Eq.(200): three paired-product covariance contractions.
--   - `OptimizationModel`: PDF p.2 Eq.(2): the scalar optimization target is the known minimum eigenvalue.
--   - `linearOutput`: PDF p.24: the first Taylor polynomial in rescaled angles.
--   - `trainingIndex`: PDF p.5: training indices are precisely the finite training data times observables.
--   - `trainingKernel`: PDF pp.6,25: restrict the frozen kernel to training indices before taking any inverse.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, https://arxiv.org/abs/2111.04225v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

/-! Statements for arXiv:2111.04225v3. Page numbers are PDF pages.
Dynamics mean frozen/retained coefficient dynamics, not exact nonlinear GD.
Incompatible source packages are recorded in HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder
open MeasureTheory ProbabilityTheory Filter

/-- PDF pp.2,19 Eqs.(1),(54): fixed unitary gates and Hermitian generators. -/
structure Ansatz (h L : ℕ) where
  dim_pos : 0 < h
  W : Fin L → Matrix.unitaryGroup (Fin h) ℂ
  X : Fin L → Matrix (Fin h) (Fin h) ℂ
  hermitian : ∀ l, (X l).IsHermitian

/-- PDF p.2 Eq.(1): increasing written order; the rightmost factor acts first.
The frozen `orderedProd` has the opposite convention and is not used. -/
def writtenProd {h L : ℕ} (F : Fin L → Matrix (Fin h) (Fin h) ℂ) :=
  (List.ofFn F).prod

/-- PDF p.2 Eq.(1): W_l exp(+i theta_l X_l). -/
def qntkFactor {h L : ℕ} (c : Ansatz h L) (theta : Fin L → ℝ) (l : Fin L) :=
  (c.W l : Matrix (Fin h) (Fin h) ℂ) *
    NormedSpace.exp (((theta l : ℂ) * Complex.I) • c.X l)

/-- PDF p.2 Eq.(1): the actual ordered circuit. -/
def qntkCircuit {h L : ℕ} (c : Ansatz h L) (theta : Fin L → ℝ) :=
  writtenProd (qntkFactor c theta)

/-- PDF p.3 Eq.(6): circuitPrefix excluding layer l. -/
def circuitPrefix {h L : ℕ} (c : Ansatz h L) (theta : Fin L → ℝ) (l : Fin L) :=
  writtenProd (fun k => if k < l then qntkFactor c theta k else 1)

/-- PDF p.3 Eq.(6): circuitSuffix excluding layer l. -/
def circuitSuffix {h L : ℕ} (c : Ansatz h L) (theta : Fin L → ℝ) (l : Fin L) :=
  writtenProd (fun k => if l < k then qntkFactor c theta k else 1)

/-- PDF p.23: coordinate derivative with respect to a real trainable angle. -/
def coordinateDerivative {L : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin L → ℝ) → E) (theta : Fin L → ℝ) (l : Fin L) : E :=
  deriv (fun s : ℝ => f (Function.update theta l s)) (theta l)

/-- PDF p.25: mixed derivative of the actual output, not a free tensor. -/
def second {L : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin L → ℝ) → E) (theta : Fin L → ℝ) (k l : Fin L) : E :=
  coordinateDerivative (fun u => coordinateDerivative f u l) theta k

/-- PDF p.5 Eq.(23): normalized feature states and Hermitian observables. -/
structure ExpectationNetwork (D I : Type*) (h L : ℕ) where
  ansatz : Ansatz h L
  phi : D → EuclideanSpace ℂ (Fin h)
  normalized : ∀ x, QAlgorithms.IsState (phi x)
  observable : I → Matrix (Fin h) (Fin h) ℂ
  hermitian : ∀ i, (observable i).IsHermitian

/-- PDF p.5 Eq.(23): real expectation, with first-slot-conjugate inner product. -/
def expectationOutput {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (theta : Fin L → ℝ) (a : D × I) : ℝ :=
  (inner ℂ (QAlgorithms.act (qntkCircuit M.ansatz theta) (M.phi a.1))
    (QAlgorithms.act (M.observable a.2)
      (QAlgorithms.act (qntkCircuit M.ansatz theta) (M.phi a.1)))).re

/-- PDF p.23 Eq.(90): the full real expectation-value QNTK. -/
def expectationKernel {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (theta : Fin L → ℝ) (a b : D × I) : ℝ :=
  ∑ l, coordinateDerivative (fun u => expectationOutput M u a) theta l * coordinateDerivative (fun u => expectationOutput M u b) theta l

/-- PDF pp.3,24: absorb theta-star into W and rescale by delta. -/
def scaledOutput {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (v : Fin L → ℝ) (a : D × I) : ℝ :=
  expectationOutput M (fun l => delta * v l) a

/-- PDF p.26 Eq.(111): linear jet at the expansion point. -/
def jet {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (a : D × I) (l : Fin L) : ℝ :=
  coordinateDerivative (fun v => scaledOutput M delta v a) 0 l

/-- PDF p.26 Eq.(111): mixed quadratic jet at the expansion point. -/
def expectationHessian {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (a : D × I) (k l : Fin L) : ℝ :=
  second (fun v => scaledOutput M delta v a) 0 k l

/-- PDF p.24 Eq.(97): frozen Gram kernel with delta-squared scaling. -/
def frozenKernel {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (a b : D × I) : ℝ :=
  ∑ l, jet M delta a l * jet M delta b l

/-- PDF p.25 Eq.(105): retained quadratic Taylor polynomial, including 1/2. -/
def quadraticOutput {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (v : Fin L → ℝ) (a : D × I) : ℝ :=
  expectationOutput M 0 a + (∑ l, jet M delta a l * v l) +
    (1 / 2 : ℝ) * ∑ k, ∑ l, expectationHessian M delta a k l * v k * v l

/-- PDF p.26 Eq.(114): cubic cross terms of the Taylor-jet Gram matrix. -/
def deltaKernel {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (v : Fin L → ℝ) (a b : D × I) : ℝ :=
  ∑ l, (jet M delta a l * (∑ k, expectationHessian M delta b k l * v k) +
    (∑ k, expectationHessian M delta a k l * v k) * jet M delta b l)

/-- PDF p.3 Eq.(5), p.19 Eq.(59): imaginary commutator expectation. -/
def thetaCoefficient {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (theta : Fin L → ℝ) (a : D × I) (l : Fin L) : ℂ :=
  let P := circuitPrefix M.ansatz theta l
  let S := circuitSuffix M.ansatz theta l
  let F := qntkFactor M.ansatz theta l
  let A := F.conjTranspose * P.conjTranspose * M.observable a.2 * P * F
  inner ℂ (M.phi a.1)
    (QAlgorithms.act (S.conjTranspose * (M.ansatz.X l * A - A * M.ansatz.X l) * S)
      (M.phi a.1))

/-- PDF p.7 Eq.(40), SM p.26 Eq.(109), corrected to match Eq.(126).
Printed: nested interval conjugations include an extra W_l conjugation even for k=l.
Changed: use the suffix-conjugated generators Y_l=S_l^dagger X_l S_l and
A=U(0)^dagger O U(0), with the larger index in the outer commutator.
Why: differentiating the original ordered circuit gives this coefficient; for one layer
W=H, X=Z, O=Z and phi=|+>, the printed coefficient is -4 whereas -z''(0)=4.
This body contains only matrices and inner products, not the derivative it evaluates. -/
def gCoefficient {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (a : D × I) (k l : Fin L) : ℂ :=
  let U := qntkCircuit M.ansatz 0
  let A := U.conjTranspose * M.observable a.2 * U
  let Sk := circuitSuffix M.ansatz 0 k
  let Sl := circuitSuffix M.ansatz 0 l
  let Yk := Sk.conjTranspose * M.ansatz.X k * Sk
  let Yl := Sl.conjTranspose * M.ansatz.X l * Sl
  let C := if k ≤ l then
      Yl * (Yk * A - A * Yk) - (Yk * A - A * Yk) * Yl
    else
      Yk * (Yl * A - A * Yl) - (Yl * A - A * Yl) * Yk
  inner ℂ (M.phi a.1) (QAlgorithms.act C (M.phi a.1))

/-- PDF p.7 Eq.(45): derivative definition of the meta-kernel. -/
def metaKernel {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (a b c : D × I) : ℝ :=
  ∑ k, ∑ l, expectationHessian M delta a k l * jet M delta b k * jet M delta c l

/-- Euclidean L2 action, used in every norm estimate. -/
def l2Action {𝕜 T : Type*} [RCLike 𝕜] [Fintype T]
    (A : Matrix T T 𝕜) (v : EuclideanSpace 𝕜 T) : EuclideanSpace 𝕜 T :=
  WithLp.toLp 2 (A.mulVec (WithLp.ofLp v))

/-- PDF pp.24,30 Eqs.(98),(152): frozen residual recurrence before it is solved. -/
def frozenResidual {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
    (K : Matrix T T 𝕜) (step : ℝ) (e : EuclideanSpace 𝕜 T) : ℕ → EuclideanSpace 𝕜 T
  | 0 => e
  | t + 1 => l2Action (1 - step • K) (frozenResidual K step e t)

/-- PDF pp.26-27,33: retain degree zero and one in an auxiliary kernel perturbation K+sD.
This coefficient recurrence omits higher delta orders and does not describe exact nonlinear GD. -/
def retainedResidual {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
    (K D : Matrix T T 𝕜) (step : ℝ) (e : EuclideanSpace 𝕜 T) :
    ℕ → EuclideanSpace 𝕜 T × EuclideanSpace 𝕜 T
  | 0 => (e, 0)
  | t + 1 =>
    let prev := retainedResidual K D step e t
    (l2Action (1 - step • K) prev.1,
      l2Action (1 - step • K) prev.2 - step • l2Action D prev.1)

/-- PDF p.25 Eq.(102): unsolved general-data prediction recurrence. -/
def prediction {D T : Type*} [Fintype T] [DecidableEq T]
    (K : D → D → ℝ) (embed : T → D) (step : ℝ) (z : D → ℝ)
    (e : EuclideanSpace ℝ T) : ℕ → D → ℝ
  | 0 => z
  | t + 1 => fun a => prediction K embed step z e t a -
      step * ∑ b, K a (embed b) * frozenResidual (fun i j => K (embed i) (embed j)) step e t b

/-- PDF p.6 Eq.(32): norm of -log(I-step K), through its convergent power series.
This is the paper's norm-log statistic, not the slowest-eigenmode convergence rate. -/
def logRate {T : Type*} [Fintype T] [DecidableEq T] (K : Matrix T T ℝ) (step : ℝ) : ℝ :=
  QAlgorithms.specNorm (∑' n : ℕ, (1 / ((n : ℝ) + 1)) • ((step • K) ^ (n + 1)))

/-- PDF p.28 Eq.(128): normalized amplitude model. -/
structure AmplitudeModel (D : Type*) (h L : ℕ) where
  ansatz : Ansatz h L
  phi : D → EuclideanSpace ℂ (Fin h)
  normalized : ∀ x, QAlgorithms.IsState (phi x)

/-- PDF p.28 Eq.(128): all computational-basis output coordinates. -/
def basisAmplitude {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (theta : Fin L → ℝ) (a : D × Fin h) : ℂ :=
  QAlgorithms.act (qntkCircuit M.ansatz theta) (M.phi a.1) a.2

/-- PDF p.29 Eq.(138): false denotes z, true denotes conjugate z. -/
def doubledAmplitude {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (theta : Fin L → ℝ) (a : D × Bool × Fin h) : ℂ :=
  if a.2.1 then star (basisAmplitude M theta (a.1, a.2.2))
  else basisAmplitude M theta (a.1, a.2.2)

/-- PDF p.29 Eq.(135): all four blocks of the complex Gram matrix. -/
def amplitudeKernel {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (theta : Fin L → ℝ) (a b : D × Bool × Fin h) : ℂ :=
  ∑ l, coordinateDerivative (fun u => doubledAmplitude M u a) theta l *
    star (coordinateDerivative (fun u => doubledAmplitude M u b) theta l)

/-- PDF pp.30-32: linear jet directly from the original circuit. -/
def amplitudeJet {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (delta : ℝ) (a : D × Bool × Fin h) (l : Fin L) : ℂ :=
  coordinateDerivative (fun v => doubledAmplitude M (fun k => delta * v k) a) 0 l

/-- PDF pp.31-32: mixed quadratic jet, including equal layer indices. -/
def amplitudeHessian {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (delta : ℝ) (a : D × Bool × Fin h) (k l : Fin L) : ℂ :=
  second (fun v => doubledAmplitude M (fun j => delta * v j) a) 0 k l

/-- PDF p.30 Eq.(150): frozen doubled kernel with rescaled angles. -/
def frozenAmplitudeKernel {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (delta : ℝ) (a b : D × Bool × Fin h) : ℂ :=
  ∑ l, amplitudeJet M delta a l * star (amplitudeJet M delta b l)

/-- PDF p.32 Eqs.(167)-(169): cubic cross terms computed from the actual jets.
The inconsistent G^(1), G^(2) shorthands are not used. -/
def deltaAmplitudeKernel {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (delta : ℝ) (v : Fin L → ℝ) (a b : D × Bool × Fin h) : ℂ :=
  ∑ l, (amplitudeJet M delta a l *
      star (∑ k, (v k : ℂ) * amplitudeHessian M delta b k l) +
    (∑ k, (v k : ℂ) * amplitudeHessian M delta a k l) * star (amplitudeJet M delta b l))

/-- PDF p.31 Eq.(161): quadratic amplitude polynomial using correct circuit derivatives. -/
def quadraticAmplitude {D : Type*} {h L : ℕ} (M : AmplitudeModel D h L)
    (delta : ℝ) (v : Fin L → ℝ) (a : D × Bool × Fin h) : ℂ :=
  doubledAmplitude M 0 a + (∑ l, amplitudeJet M delta a l * (v l : ℂ)) +
    (1 / 2 : ℂ) * ∑ k, ∑ l, amplitudeHessian M delta a k l * (v k : ℂ) * (v l : ℂ)

/-- PDF p.36 Eqs.(190),(195): incoming quantum ensemble with normalized feature states.
Observables are independent over the reals, so m is the dimension of their real span. -/
structure QuantumLayer (Ω D : Type*) (h L m : ℕ) where
  ansatz : Ω → Ansatz h L
  theta : Ω → Fin L → ℝ
  phi : Ω → D → EuclideanSpace ℂ (Fin h)
  normalized : ∀ w a, QAlgorithms.IsState (phi w a)
  observable : Ω → Fin m → Matrix (Fin h) (Fin h) ℂ
  hermitian : ∀ w j, (observable w j).IsHermitian
  independent : ∀ w, LinearIndependent ℝ (observable w)

/-- PDF p.36: the actual incoming quantum expectation. -/
def incomingQuantumOutput {Ω D : Type*} {h L m : ℕ} (q : QuantumLayer Ω D h L m)
    (a : D) (j : Fin m) (w : Ω) : ℝ :=
  (inner ℂ (QAlgorithms.act (qntkCircuit (q.ansatz w) (q.theta w)) (q.phi w a))
    (QAlgorithms.act (q.observable w j)
      (QAlgorithms.act (qntkCircuit (q.ansatz w) (q.theta w)) (q.phi w a)))).re

/-- PDF p.36 Eqs.(193)-(194): centered Gaussian coordinates, jointly independent of
incoming outputs. Finite fourth moments prevent default nonintegrable integrals. -/
structure HybridLayer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D R : Type*) [Fintype R] (h L m : ℕ) (CW CB : ℝ≥0) where
  width_pos : 0 < m
  quantum : QuantumLayer Ω D h L m
  noise : (R × Fin m) ⊕ R → Ω → ℝ
  measurable_noise : ∀ i, Measurable (noise i)
  gaussian : ∀ i, Measure.map (noise i) μ = gaussianReal 0
    (match i with | Sum.inl _ => CW / (m : ℝ≥0) | Sum.inr _ => CB)
  independent_noise : iIndepFun noise μ
  independent_quantum : IndepFun
    (fun w => fun i => noise i w)
    (fun w => fun a => fun j => incomingQuantumOutput quantum a j w) μ
  measurable_quantum : ∀ a j, Measurable (incomingQuantumOutput quantum a j)
  fourth_moment : ∀ a j, MemLp (incomingQuantumOutput quantum a j) 4 μ

/-- PDF p.36 Eq.(193): affine preactivation, before any nonlinear activation. -/
def preactivation {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] {μ : Measure Ω}
    {h L m : ℕ} {CW CB : ℝ≥0} (S : HybridLayer μ D R h L m CW CB)
    (a : D) (r : R) (w : Ω) : ℝ :=
  (∑ j, S.noise (Sum.inl (r, j)) w * incomingQuantumOutput S.quantum a j w) +
    S.noise (Sum.inr r) w

/-- PDF p.37 Eq.(197): subtract all three disconnected Wick pairings. -/
def connectedFour {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f1 f2 f3 f4 : Ω → ℝ) : ℝ :=
  (∫ w, f1 w * f2 w * f3 w * f4 w ∂μ) -
    (∫ w, f1 w * f2 w ∂μ) * (∫ w, f3 w * f4 w ∂μ) -
    (∫ w, f1 w * f3 w ∂μ) * (∫ w, f2 w * f4 w ∂μ) -
    (∫ w, f1 w * f4 w ∂μ) * (∫ w, f2 w * f3 w ∂μ)

/-- PDF p.38 Eq.(201): covariance of products, subtracting only one paired product. -/
def productCovariance {Ω D : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {h L m : ℕ} (q : QuantumLayer Ω D h L m)
    (a b c d : D) (j k : Fin m) : ℝ :=
  (∫ w, incomingQuantumOutput q a j w * incomingQuantumOutput q b j w *
    incomingQuantumOutput q c k w * incomingQuantumOutput q d k w ∂μ) -
  (∫ w, incomingQuantumOutput q a j w * incomingQuantumOutput q b j w ∂μ) *
    (∫ w, incomingQuantumOutput q c k w * incomingQuantumOutput q d k w ∂μ)

/-- PDF p.37 Eq.(200): Kronecker delta for classical output coordinates. -/
def kd {R : Type*} [DecidableEq R] (r s : R) : ℝ := if r = s then 1 else 0

/-- PDF p.37 Eq.(200): three paired-product covariance contractions. -/
def fourContraction {Ω D R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
    {μ : Measure Ω} {h L m : ℕ} {CW CB : ℝ≥0}
    (S : HybridLayer μ D R h L m CW CB) (a b c d : D) (r s t u : R) : ℝ :=
  ((CW : ℝ) / (m : ℝ)) ^ 2 *
    (kd r s * kd t u * (∑ j, ∑ k, productCovariance μ S.quantum a b c d j k) +
     kd r t * kd s u * (∑ j, ∑ k, productCovariance μ S.quantum a c b d j k) +
     kd r u * kd s t * (∑ j, ∑ k, productCovariance μ S.quantum a d b c j k))

/-! Sanity checks for the local constructions, with no admitted proofs. -/

example {h : ℕ} (F : Fin 0 → Matrix (Fin h) (Fin h) ℂ) : writtenProd F = 1 := by
  simp [writtenProd]

example {h : ℕ} (F : Fin 2 → Matrix (Fin h) (Fin h) ℂ) :
    writtenProd F = F 0 * F 1 := by
  simp [writtenProd, List.ofFn_succ]

example {𝕜 T : Type*} [RCLike 𝕜] [Fintype T] [DecidableEq T]
    (K D : Matrix T T 𝕜) (s : ℝ) (e : EuclideanSpace 𝕜 T) :
    retainedResidual K D s e 0 = (e, 0) := rfl

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    connectedFour μ (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) = 0 := by
  simp [connectedFour]

/-- PDF p.2 Eq.(2): the scalar optimization target is the known minimum eigenvalue. -/
structure OptimizationModel (h L : ℕ) where
  model : ExpectationNetwork Unit Unit h L
  minimum : ℝ
  minimum_eigenvalue :
    (∃ v : EuclideanSpace ℂ (Fin h), QAlgorithms.IsState v ∧
      QAlgorithms.act (model.observable ()) v = (minimum : ℂ) • v) ∧
    ∀ v : EuclideanSpace ℂ (Fin h), QAlgorithms.IsState v →
      minimum ≤ (inner ℂ v (QAlgorithms.act (model.observable ()) v)).re

/-- PDF p.24: the first Taylor polynomial in rescaled angles. -/
def linearOutput {D I : Type*} {h L : ℕ} (M : ExpectationNetwork D I h L)
    (delta : ℝ) (v : Fin L → ℝ) (a : D × I) : ℝ :=
  expectationOutput M 0 a + ∑ l, jet M delta a l * v l

/-- PDF p.5: training indices are precisely the finite training data times observables. -/
def trainingIndex {D T I : Type*} (embed : T ↪ D) (a : T × I) : D × I :=
  (embed a.1, a.2)

/-- PDF pp.6,25: restrict the frozen kernel to training indices before taking any inverse. -/
def trainingKernel {D T I : Type*} {h L : ℕ}
    (M : ExpectationNetwork D I h L) (delta : ℝ) (embed : T ↪ D) :
    Matrix (T × I) (T × I) ℝ :=
  fun a b => frozenKernel M delta (trainingIndex embed a) (trainingIndex embed b)

end QAlgorithms.Papers.Independent.Intakenext100.P88

end


