-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44
-- name    : QAlgorithms_Papers_Independent_Claimed50_P44
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:05:35.276373+00:00
-- url     : https://prove2.me/theorems/f24e82b3-67cb-44e4-91e8-1f093452bf63
-- title:
--   Definitions for Improving fidelity of continuous-variable teleportation via local operations
-- statement:
--   The objects the formalized statements of *Improving fidelity of continuous-variable teleportation via local operations* (arXiv:quant-ph/0202102) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mode`
--   - `PairMode`
--   - `QuadratureMatrix`
--   - `JointMat`
--   - `PhasePoint`
--   - `modeSymplecticForm`: PDF p.4, Eq.(27), in the order (x,p).
--   - `reflect`: PDF p.2, Eq.(12).
--   - `InputOrProcess`: D=0 is a formal process objective, never a zero-covariance input state.
--   - `resourceCov`: Resource order (x_A,p_A,x_B,p_B), PDF p.2, Eq.(7).
--   - `PhysicalResource`: Physical two-mode uncertainty condition, PDF p.2, Eqs.(6)-(7). The accepted predicate uses V-i Omega; complex conjugation makes this identical to V+i Omega for these real matrices. No positivity is added.
--   - `GaussianCP`: PDF pp.3-4, Eqs.(25)-(27): deterministic, trace-preserving Gaussian map. Singular noise, including G=0 for symplectic maps, is included. An affine output displacement is supplied separately to the Wigner function.
--   - `Symplectic`: Source's one-mode symplectic unitary action on covariance matrices.
--   - `gaussianWigner`: Fourier transform of exp(-q V q^T/4), PDF p.2, Eqs.(4)-(8). Used only in dimensions 2 and 4, with a physical covariance.
--   - `joinPhasePoints`: Join Alice and Bob coordinates in the paper's order.
--   - `resourceWigner`: Centered Alice, arbitrary Bob mean; zero mean is the source's resource.
--   - `phaseIntegral`: Integrate one optical phase plane with its ordinary dx dp measure.
--   - `bellBranch`: PDF p.2: unnormalized conditional Bob Wigner function, with measured X_+=u and P_-=v. The factor 2 is the Jacobian for x_A=sqrt(2)u-x_in and p_A=p_in-sqrt(2)v. Input/resource independence is encoded by their product. This is the ideal balanced-beam-splitter homodyne instrument in the positive Gaussian Wigner representation.
--   - `bellOutcomeDensity`: Probability density of a Bell outcome; no postselection.
--   - `conditionalBobWigner`: Normalized conditional state on positive-density outcomes. Its value at zero-density outcomes has no operational weight.
--   - `bellOutput`: PDF p.2: feedforward adds sqrt(2)(X_+,P_-) to Bob. Average every unnormalized outcome branch; the input quadrature gain is exactly one.
--   - `bellAverageFidelity`: PDF p.2, Eq.(9): ordinary pure-input overlap after the Bell instrument and outcome-dependent displacement, averaged over all outcomes. This is not defined by a determinant.
--   - `teleportKernel`: PDF p.2, Eqs.(1)-(3), in original resource coordinates: noise=(x_A+x_B,p_B-p_A). The transformed-coordinate factor 1/4 has been absorbed by the inverse change of variables.
--   - `processScore`: PDF p.3, Eq.(18): finite renormalization, not a probability or a normalized ideal EPR vector.
--   - `noiseBase`: PDF pp.2,4, Eqs.(11),(34); correlations have PLUS signs.
--   - `bobCov`: PDF p.4, Eq.(29), Bob preprocessing before the Bell measurement.
--   - `reducedDet`: PDF p.4, Eq.(40), after minimizing over CP noises at fixed S.
--   - `standardCov`: PDF p.4, Eq.(41).
--   - `firstBaseVariance`: PDF p.5, Eq.(43).
--   - `secondBaseVariance`: PDF p.5, Eq.(43).
--   - `diagonalObjective`: PDF p.5, Eq.(44), square root of the optimized determinant.
--   - `DiagonalStationary`: Vanishing coordinate derivatives, never a claim of global optimality.
--   - `boundaryPolynomial`: PDF p.5, Eq.(48), after multiplying the derivative by x^3/2. The polynomial is allowed to be identically zero.
--   - `Noises`: Order: g_A,11, g_A,22, g_B,11, g_B,22.
--   - `FeasibleNoises`: PDF p.5, Eqs.(26),(49)-(52), inequalities rather than divided densities.
--   - `rawTwoDet`: The raw determinant underlying (53), including zero-noise cases.
--   - `twoNoiseValue`: PDF p.5, Eq.(55): the optimal value, possibly only an infimum.
--   - `DiagonalStrategy`: Independent diagonal local maps, with no preprocessing communication.
--   - `ValidStrategy`: Source's local CP constraints, including zero gains.
--   - `strategyCov`: PDF p.5, Eq.(51).
--   - `ThreeAlternatives`: Alice-only, Bob-only, or replacement of both modes by vacuum.
--   - `strategyScore`: Operational process score for a diagonal two-sided strategy.
--   - `strategyValues`: Full and three-alternative achievable score sets for a fixed resource.
--   - `exampleA`: PDF p.6, Eq.(60), b0=1/2 in the plotted example.
--   - `exampleB`: Bob's added classical covariance noise.
--   - `exampleC`: Positive magnitude of the cross correlation.
--   - `exampleResource`: PDF p.6, Eq.(60), signs c1=-sinh(2r), c2=+sinh(2r).
--   - `squeezingThreshold`: PDF pp.6-7: threshold with b0 fixed to 1/2.
--   - `dampingGain`: PDF pp.6-7, Eq.(61): amplitude transmittance, including the endpoints.
--   - `dampingNoise`: Vacuum-environment attenuation noise; G=0 at transmittance one.
--   - `exampleOutput`: Bob-preprocessed resource, allowing any affine Bob displacement.
--   - `exampleOptimalNoise`: Exact optimized scalar noise; F=2/(2+noise), process score=2/noise.
--   - `dampingStrategy`: The Bob-only damping strategy inside the diagonal two-sided class.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, https://arxiv.org/abs/quant-ph/0202102v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

/-!
Fiurasek, arXiv:quant-ph/0202102v3. Gaussian states are represented by their
normalized Wigner functions, with vacuum covariance I and hbar = 1. The Bell
instrument below is defined before the determinant formula. All integrals use
Lebesgue measure. General non-Gaussian separability is deferred, not truncated.
-/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

abbrev Mode := Fin 2

abbrev PairMode := Mode ⊕ Mode

abbrev QuadratureMatrix := Matrix Mode Mode ℝ

abbrev JointMat := Matrix PairMode PairMode ℝ

abbrev PhasePoint := Mode → ℝ

/-- PDF p.4, Eq.(27), in the order (x,p). -/
def modeSymplecticForm : QuadratureMatrix := !![0, 1; -1, 0]

/-- PDF p.2, Eq.(12). -/
def reflect : QuadratureMatrix := !![1, 0; 0, -1]

/-- D=0 is a formal process objective, never a zero-covariance input state. -/
def InputOrProcess (D : QuadratureMatrix) : Prop := pureCovariance D modeSymplecticForm ∨ D = 0

/-- Resource order (x_A,p_A,x_B,p_B), PDF p.2, Eq.(7). -/
def resourceCov (A B C : QuadratureMatrix) : JointMat := Matrix.fromBlocks A C C.transpose B

/-- Physical two-mode uncertainty condition, PDF p.2, Eqs.(6)-(7).
The accepted predicate uses V-i Omega; complex conjugation makes this
identical to V+i Omega for these real matrices. No positivity is added. -/
def PhysicalResource (V : JointMat) : Prop :=
  physicalCovariance V (Matrix.fromBlocks modeSymplecticForm 0 0 modeSymplecticForm)

/-- PDF pp.3-4, Eqs.(25)-(27): deterministic, trace-preserving Gaussian map.
Singular noise, including G=0 for symplectic maps, is included. An affine
output displacement is supplied separately to the Wigner function. -/
def GaussianCP (S G : QuadratureMatrix) : Prop :=
  G.transpose = G ∧
    (complexify G + Complex.I • complexify (modeSymplecticForm - S * modeSymplecticForm * S.transpose)).PosSemidef

/-- Source's one-mode symplectic unitary action on covariance matrices. -/
def Symplectic (S : QuadratureMatrix) : Prop := S * modeSymplecticForm * S.transpose = modeSymplecticForm

/-- Fourier transform of exp(-q V q^T/4), PDF p.2, Eqs.(4)-(8).
Used only in dimensions 2 and 4, with a physical covariance. -/
def gaussianWigner {I : Type*} [Fintype I] [DecidableEq I]
    (V : Matrix I I ℝ) (mean z : I → ℝ) : ℝ :=
  Real.exp (-quadratic V⁻¹ (z - mean)) /
    (Real.pi ^ (Fintype.card I / 2) * Real.sqrt V.det)

/-- Join Alice and Bob coordinates in the paper's order. -/
def joinPhasePoints (a b : PhasePoint) : PairMode → ℝ := Sum.elim a b

/-- Centered Alice, arbitrary Bob mean; zero mean is the source's resource. -/
def resourceWigner (V : JointMat) (bobMean : PhasePoint) (a b : PhasePoint) : ℝ :=
  gaussianWigner V (joinPhasePoints 0 bobMean) (joinPhasePoints a b)

/-- Integrate one optical phase plane with its ordinary dx dp measure. -/
def phaseIntegral (f : PhasePoint → ℝ) : ℝ :=
  ∫ x : ℝ, ∫ p : ℝ, f ![x, p]

/-- PDF p.2: unnormalized conditional Bob Wigner function, with measured
X_+=u and P_-=v. The factor 2 is the Jacobian for
x_A=sqrt(2)u-x_in and p_A=p_in-sqrt(2)v. Input/resource independence is
encoded by their product. This is the ideal balanced-beam-splitter homodyne
instrument in the positive Gaussian Wigner representation. -/
def bellBranch (input : PhasePoint → ℝ) (resource : PhasePoint → PhasePoint → ℝ)
    (outcome bob : PhasePoint) : ℝ :=
  2 * phaseIntegral (fun z => input z *
    resource ![Real.sqrt 2 * outcome 0 - z 0,
      z 1 - Real.sqrt 2 * outcome 1] bob)

/-- Probability density of a Bell outcome; no postselection. -/
def bellOutcomeDensity (input : PhasePoint → ℝ) (resource : PhasePoint → PhasePoint → ℝ)
    (outcome : PhasePoint) : ℝ :=
  phaseIntegral (bellBranch input resource outcome)

/-- Normalized conditional state on positive-density outcomes. Its value at
zero-density outcomes has no operational weight. -/
def conditionalBobWigner (input : PhasePoint → ℝ) (resource : PhasePoint → PhasePoint → ℝ)
    (outcome bob : PhasePoint) : ℝ :=
  bellBranch input resource outcome bob / bellOutcomeDensity input resource outcome

/-- PDF p.2: feedforward adds sqrt(2)(X_+,P_-) to Bob. Average every
unnormalized outcome branch; the input quadrature gain is exactly one. -/
def bellOutput (input : PhasePoint → ℝ) (resource : PhasePoint → PhasePoint → ℝ) (z : PhasePoint) : ℝ :=
  phaseIntegral (fun outcome => bellBranch input resource outcome
    ![z 0 - Real.sqrt 2 * outcome 0, z 1 - Real.sqrt 2 * outcome 1])

/-- PDF p.2, Eq.(9): ordinary pure-input overlap after the Bell instrument
and outcome-dependent displacement, averaged over all outcomes. This is not
defined by a determinant. -/
def bellAverageFidelity (D : QuadratureMatrix) (mean : PhasePoint) (resource : PhasePoint → PhasePoint → ℝ) : ℝ :=
  let input := gaussianWigner D mean
  2 * Real.pi * phaseIntegral (fun z => input z * bellOutput input resource z)

/-- PDF p.2, Eqs.(1)-(3), in original resource coordinates:
noise=(x_A+x_B,p_B-p_A). The transformed-coordinate factor 1/4 has been
absorbed by the inverse change of variables. -/
def teleportKernel (resource : PhasePoint → PhasePoint → ℝ) (noise : PhasePoint) : ℝ :=
  phaseIntegral (fun a => resource a ![noise 0 - a 0, noise 1 + a 1])

/-- PDF p.3, Eq.(18): finite renormalization, not a probability or a
normalized ideal EPR vector. -/
def processScore (resource : PhasePoint → PhasePoint → ℝ) : ℝ :=
  2 * Real.pi * teleportKernel resource 0

/-- PDF pp.2,4, Eqs.(11),(34); correlations have PLUS signs. -/
def noiseBase (D A B C S : QuadratureMatrix) : QuadratureMatrix :=
  2 • D + reflect * A * reflect.transpose + reflect * C * S.transpose +
    S * C.transpose * reflect.transpose + S * B * S.transpose

/-- PDF p.4, Eq.(29), Bob preprocessing before the Bell measurement. -/
def bobCov (A B C S G : QuadratureMatrix) : JointMat :=
  resourceCov A (S * B * S.transpose + G) (C * S.transpose)

/-- PDF p.4, Eq.(40), after minimizing over CP noises at fixed S. -/
def reducedDet (D A B C S : QuadratureMatrix) : ℝ :=
  (|1 - S.det| + Real.sqrt (noiseBase D A B C S).det) ^ 2

/-- PDF p.4, Eq.(41). -/
def standardCov (a b c1 c2 : ℝ) : JointMat :=
  resourceCov (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix)) !![c1, 0; 0, c2]

/-- PDF p.5, Eq.(43). -/
def firstBaseVariance (a b c1 d1 x : ℝ) : ℝ := 2 * d1 + a + 2 * c1 * x + b * x ^ 2

/-- PDF p.5, Eq.(43). -/
def secondBaseVariance (a b c2 d2 y : ℝ) : ℝ := 2 * d2 + a - 2 * c2 * y + b * y ^ 2

/-- PDF p.5, Eq.(44), square root of the optimized determinant. -/
def diagonalObjective (a b c1 c2 d1 d2 x y : ℝ) : ℝ :=
  |1 - x * y| + Real.sqrt (firstBaseVariance a b c1 d1 x * secondBaseVariance a b c2 d2 y)

/-- Vanishing coordinate derivatives, never a claim of global optimality. -/
def DiagonalStationary (a b c1 c2 d1 d2 x y : ℝ) : Prop :=
  HasDerivAt (fun z => diagonalObjective a b c1 c2 d1 d2 z y) 0 x ∧
  HasDerivAt (fun z => diagonalObjective a b c1 c2 d1 d2 x z) 0 y

/-- PDF p.5, Eq.(48), after multiplying the derivative by x^3/2.
The polynomial is allowed to be identically zero. -/
def boundaryPolynomial (a b c1 c2 d1 d2 x : ℝ) : ℝ :=
  b * (2 * d2 + a) * x ^ 4 + (c1 * (2 * d2 + a) - b * c2) * x ^ 3 +
    ((2 * d1 + a) * c2 - b * c1) * x - (2 * d1 + a) * b

/-- Order: g_A,11, g_A,22, g_B,11, g_B,22. -/
abbrev Noises := Fin 4 → ℝ

/-- PDF p.5, Eqs.(26),(49)-(52), inequalities rather than divided densities. -/
def FeasibleNoises (u v x y : ℝ) (g : Noises) : Prop :=
  (∀ i, 0 ≤ g i) ∧ (1 - u * v) ^ 2 ≤ g 0 * g 1 ∧
    (1 - x * y) ^ 2 ≤ g 2 * g 3

/-- The raw determinant underlying (53), including zero-noise cases. -/
def rawTwoDet (al be : ℝ) (g : Noises) : ℝ :=
  (al + g 0 + g 2) * (be + g 1 + g 3)

/-- PDF p.5, Eq.(55): the optimal value, possibly only an infimum. -/
def twoNoiseValue (al be u v x y : ℝ) : ℝ :=
  (|1 - u * v| + |1 - x * y| + Real.sqrt (al * be)) ^ 2

/-- Independent diagonal local maps, with no preprocessing communication. -/
structure DiagonalStrategy where
  u : ℝ
  v : ℝ
  x : ℝ
  y : ℝ
  g : Noises

/-- Source's local CP constraints, including zero gains. -/
def ValidStrategy (s : DiagonalStrategy) : Prop := FeasibleNoises s.u s.v s.x s.y s.g

/-- PDF p.5, Eq.(51). -/
def strategyCov (V : JointMat) (s : DiagonalStrategy) : JointMat :=
  let S := Matrix.fromBlocks (!![s.u, 0; 0, s.v] : QuadratureMatrix) 0 0
    (!![s.x, 0; 0, s.y] : QuadratureMatrix)
  let G := Matrix.fromBlocks (!![s.g 0, 0; 0, s.g 1] : QuadratureMatrix) 0 0
    (!![s.g 2, 0; 0, s.g 3] : QuadratureMatrix)
  S * V * S.transpose + G

/-- Alice-only, Bob-only, or replacement of both modes by vacuum. -/
def ThreeAlternatives (s : DiagonalStrategy) : Prop :=
  (s.x = 1 ∧ s.y = 1 ∧ s.g 2 = 0 ∧ s.g 3 = 0) ∨
  (s.u = 1 ∧ s.v = 1 ∧ s.g 0 = 0 ∧ s.g 1 = 0) ∨
  (s.u = 0 ∧ s.v = 0 ∧ s.x = 0 ∧ s.y = 0 ∧ s.g = ![1, 1, 1, 1])

/-- Operational process score for a diagonal two-sided strategy. -/
def strategyScore (V : JointMat) (s : DiagonalStrategy) : ℝ :=
  processScore (resourceWigner (strategyCov V s) 0)

/-- Full and three-alternative achievable score sets for a fixed resource. -/
def strategyValues (V : JointMat) (restricted : Bool) : Set ℝ :=
  {z | ∃ s : DiagonalStrategy, ValidStrategy s ∧
    (restricted = true → ThreeAlternatives s) ∧ strategyScore V s = z}

/-- PDF p.6, Eq.(60), b0=1/2 in the plotted example. -/
def exampleA (r : ℝ) : ℝ := Real.cosh (2 * r)

/-- Bob's added classical covariance noise. -/
def exampleB (r : ℝ) : ℝ := exampleA r + 1 / 2

/-- Positive magnitude of the cross correlation. -/
def exampleC (r : ℝ) : ℝ := Real.sinh (2 * r)

/-- PDF p.6, Eq.(60), signs c1=-sinh(2r), c2=+sinh(2r). -/
def exampleResource (r : ℝ) : JointMat :=
  standardCov (exampleA r) (exampleB r) (-exampleC r) (exampleC r)

/-- PDF pp.6-7: threshold with b0 fixed to 1/2. -/
def squeezingThreshold : ℝ := -Real.log (1 / 2) / 2

/-- PDF pp.6-7, Eq.(61): amplitude transmittance, including the endpoints. -/
def dampingGain (r : ℝ) : ℝ :=
  if r ≤ squeezingThreshold then exampleC r / (exampleB r - 1) else 1

/-- Vacuum-environment attenuation noise; G=0 at transmittance one. -/
def dampingNoise (r : ℝ) : QuadratureMatrix := (1 - dampingGain r ^ 2) • (1 : QuadratureMatrix)

/-- Bob-preprocessed resource, allowing any affine Bob displacement. -/
def exampleOutput (r : ℝ) (S G : QuadratureMatrix) (d : PhasePoint) : PhasePoint → PhasePoint → ℝ :=
  resourceWigner (bobCov (exampleA r • (1 : QuadratureMatrix)) (exampleB r • (1 : QuadratureMatrix))
    (!![-exampleC r, 0; 0, exampleC r]) S G) d

/-- Exact optimized scalar noise; F=2/(2+noise), process score=2/noise. -/
def exampleOptimalNoise (r : ℝ) : ℝ :=
  if r ≤ squeezingThreshold then
    exampleA r + 1 - exampleC r ^ 2 / (exampleB r - 1)
  else 1 / 2 + 2 * Real.exp (-2 * r)

/-- The Bob-only damping strategy inside the diagonal two-sided class. -/
def dampingStrategy (r : ℝ) : DiagonalStrategy :=
  ⟨1, 1, dampingGain r, dampingGain r,
    ![0, 0, 1 - dampingGain r ^ 2, 1 - dampingGain r ^ 2]⟩

/-! Sanity examples pinning coordinates, feedforward signs, and zero-noise domains. -/

example : modeSymplecticForm 0 1 = 1 := rfl

example : reflect 1 1 = -1 := rfl

example (A B C : QuadratureMatrix) : resourceCov A B C (Sum.inl 0) (Sum.inr 1) = C 0 1 := rfl

example (W : PhasePoint → PhasePoint → ℝ) :
    teleportKernel W 0 = phaseIntegral (fun a => W a ![-a 0, a 1]) := by
  simp [teleportKernel]

example : rawTwoDet 0 0 ![1, 1, 1, 1] = 4 := by
  change (0 + 1 + 1 : ℝ) * (0 + 1 + 1) = 4
  norm_num

example : (0 : QuadratureMatrix).transpose = 0 := by simp

end QAlgorithms.Papers.Independent.Claimed50.P44


