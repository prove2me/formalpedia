-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49
-- name    : QAlgorithms_Papers_Independent_Claimed50_P49
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:59:45.975028+00:00
-- url     : https://prove2.me/theorems/7fa5b3c5-b84e-4c2e-86d8-5f3851171e0c
-- title:
--   Definitions for One-mode Bosonic Gaussian channels: a full weak-degradability classification
-- statement:
--   The objects the formalized statements of *One-mode Bosonic Gaussian channels: a full weak-degradability classification* (arXiv:quant-ph/0609013) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RealMatrix`
--   - `FockMap`
--   - `JointUnitary`
--   - `sourceWeyl`: Section 2.1, PDF p.6: V(z)=exp(i(Qx+Py)), [Q,P]=i.
--   - `traceClassObservablePair`: Section 2.1, PDF p.6: trace-class/bounded pairing, not a finite trace.
--   - `sourceCharacteristic`: Equation (2.3), PDF p.6, for arbitrary input densities. Coordinate adapter to the accepted bounded-operator characteristic function. The matrix input is always an actual density in the source statements.
--   - `GaussianData`: Equations (2.4)-(2.5), PDF pp.6-7, including first moments.
--   - `GaussianAdmissible`: Section 2.1, PDF p.7: symmetry, positivity, and the one-mode CP inequality.
--   - `gaussianTransform`: Equation (2.5), PDF p.7, acting on a characteristic function.
--   - `IsGaussianChannel`: Gaussian CPTP maps on all trace class; the formula holds for every density.
--   - `composeData`: Equation (2.6), PDF p.7: first g1, then g2 in the Schrodinger picture.
--   - `CanonicalClass`: Table 1, PDF p.9: six canonical types.
--   - `sigmaThree`: Third real Pauli matrix, Table 1, PDF p.9.
--   - `canonicalData`: Fixed source axes, Table 1, PDF p.9.
--   - `ValidSourceCanonical`: Table 1, PDF p.9: B2 includes zero noise; k is amplitude, not intensity.
--   - `classOf`: Table 1, PDF pp.9-10: rank tests specialized to two real dimensions.
--   - `compositionClasses`: Equation (2.18), PDF p.11, row=second map. D-D includes corrected B2 branch.
--   - `couplingBlock`: Equation (2.11), PDF p.8: m11,m21 are the upper blocks.
--   - `jointSymplecticMatrix`: Equations (2.1),(2.10), PDF pp.6,8: full symplectic form.
--   - `ImplementsJointGaussian`: Bounded Weyl version of (2.10), with U-adjoint on the left, PDF p.8. No products of unbounded Q/P operators on an unspecified domain are used.
--   - `IsThermal`: Equation (2.9), PDF p.7: finite nonnegative thermal parameter, including vacuum.
--   - `environmentNumber`: Section 2.4, PDF p.12: B1 uses vacuum, all other canonical dilations use N0.
--   - `appendixCouplingMatrix`: Appendix A, PDF p.20: explicit full matrices; k is amplitude kappa. B2 is excluded from every theorem using this definition.
--   - `complementData`: Table 2, PDF p.14: actual environmental coordinates from Appendix A. For A2 the B1 noise scale is N+1/2 and is normalized only by a squeeze.
--   - `AntiRegion`: Section 3.2, PDF pp.16-17: regimes where the explicit reverse recovery applies.
--   - `WeakRegion`: Section 3.2, PDF pp.16-17: equality belongs to both regimes.
--   - `antiRecoveryData`: Section 3.2, PDF pp.16-17: anti-degrading maps, with identity at k^2=1/2.
--   - `weakRecoveryData`: Section 3.2, PDF p.17: printed amplifier I and (r^2-1) are corrected here to sigma3 and (r^2+1), forced by (2.6) and Table 2. Independent moderation of this source correction is required. At k^2=1/2 the attenuator map is identity.
--   - `nearB2Data`: Sections 2.3,2.5, PDF pp.11,14: class-C approximation with fixed noise.
--   - `displacementNoise`: Equation (2.22), PDF p.13: real two-dimensional Lebesgue law. At zero noise use a Dirac mass; division by zero never defines the endpoint.
--   - `randomDisplacement`: Equation (2.22), PDF p.13: coefficient integral of the trace-class barycenter. The theorem supplies integrability for all densities, not a default-zero integral.
--   - `TrueComplementary`: Section 1, PDF p.4: two legs of one PURE isometry, with different outputs.
--   - `HasAntiRepresentation`: Section 1, PDF p.4: anti-degradable in SOME physical representation. This never asserts recovery from every fixed mixed weak complement.
--   - `PurifiedImplementation`: Section 1, PDF p.3: coefficients of U tensor identity acting on rho's input ket tensored with an actual purification vector, not an arbitrary channel.
--   - `BoundedOp`
--   - `observableCoeff`: Section 1, PDF p.5: coefficients of a genuinely bounded observable.
--   - `BlockPositive`: Complete positivity test on bounded couplingBlock operators, Section 1, PDF p.5.
--   - `IsBoundedCPUnital`: Section 1, PDF p.5: complex linear, CP, unital Heisenberg map. Normality is additionally guaranteed by its trace-class predual below.
--   - `TraceDual`: Equation (1.6), PDF p.5: bounded-observable duality on every density.
--   - `ddPhotonNumber`: Equations (4.1)-(4.2), PDF p.18; used only when k1*k2 != 1.
--   - `ccPhotonNumber`: Equations (4.4)-(4.5), PDF p.19; used only when k1*k2 != 1.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, https://arxiv.org/abs/quant-ph/0609013v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

/-!
Caruso, Giovannetti and Holevo, arXiv:quant-ph/0609013v2.
Full Fock space, unrestricted trace-class CPTP channels, no energy cutoff.
Accepted P33/P39/P14 supply nuclear trace class, actual Fock displacement
coefficients, physical output legs, and operational quantum capacity.
The local coordinate conversion is V(x,y)=D((-y+ix)/sqrt(2)).
Only source theorems are admitted. Compilation is pending batch handoff.
-/

noncomputable section

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P14
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

abbrev RealMatrix := Matrix (Fin 2) (Fin 2) ℝ

abbrev FockMap := Operation ℕ ℕ

abbrev JointUnitary := Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ)

/-- Section 2.1, PDF p.6: V(z)=exp(i(Qx+Py)), [Q,P]=i. -/
def sourceWeyl (z : (Fin 2 → ℝ)) : Matrix ℕ ℕ ℂ :=
  displacementMatrix ⟨-z 1 / Real.sqrt 2, z 0 / Real.sqrt 2⟩

/-- Section 2.1, PDF p.6: trace-class/bounded pairing, not a finite trace. -/
def traceClassObservablePair {I : Type} (X B : Matrix I I ℂ) : ℂ :=
  ∑' i, ∑' j, X i j * B j i

/-- Equation (2.3), PDF p.6, for arbitrary input densities.
Coordinate adapter to the accepted bounded-operator characteristic function.
The matrix input is always an actual density in the source statements. -/
def sourceCharacteristic (X : Matrix ℕ ℕ ℂ) (z : (Fin 2 → ℝ)) : ℂ :=
  QAlgorithms.Papers.Independent.Dependency50.P39.characteristic
    (QAlgorithms.Papers.Independent.Dependency50.P39.operatorOfMatrix X)
    ⟨-z 1 / Real.sqrt 2, z 0 / Real.sqrt 2⟩

/-- Equations (2.4)-(2.5), PDF pp.6-7, including first moments. -/
structure GaussianData where
  K : RealMatrix
  alpha : RealMatrix
  displacement : (Fin 2 → ℝ)

/-- Section 2.1, PDF p.7: symmetry, positivity, and the one-mode CP inequality. -/
def GaussianAdmissible (g : GaussianData) : Prop :=
  g.alpha.transpose = g.alpha ∧ (∀ z, 0 ≤ quadratic g.alpha z) ∧
    ((g.K.det - 1) / 2) ^ 2 ≤ g.alpha.det

/-- Equation (2.5), PDF p.7, acting on a characteristic function. -/
def gaussianTransform (g : GaussianData) (phi : (Fin 2 → ℝ) → ℂ) (z : (Fin 2 → ℝ)) : ℂ :=
  phi (g.K.mulVec z) * Complex.exp
    (((-quadratic g.alpha z / 2 : ℝ) : ℂ) +
      Complex.I * ((∑ i, g.displacement i * z i : ℝ) : ℂ))

/-- Gaussian CPTP maps on all trace class; the formula holds for every density. -/
def IsGaussianChannel (E : FockMap) (g : GaussianData) : Prop :=
  IsTraceClassChannel E ∧ GaussianAdmissible g ∧
    ∀ (rho : State ℕ) z,
      sourceCharacteristic (E rho.coefficients) z =
        gaussianTransform g (sourceCharacteristic rho.coefficients) z

/-- Equation (2.6), PDF p.7: first g1, then g2 in the Schrodinger picture. -/
def composeData (g1 g2 : GaussianData) : GaussianData :=
  ⟨g1.K * g2.K, g2.K.transpose * g1.alpha * g2.K + g2.alpha,
    g2.K.transpose.mulVec g1.displacement + g2.displacement⟩

/-- Table 1, PDF p.9: six canonical types. -/
inductive CanonicalClass where
  | A1 | A2 | B1 | B2 | C | D
  deriving DecidableEq

/-- Third real Pauli matrix, Table 1, PDF p.9. -/
def sigmaThree : RealMatrix := !![1, 0; 0, -1]

/-- Fixed source axes, Table 1, PDF p.9. -/
def canonicalData (c : CanonicalClass) (k N : ℝ) : GaussianData :=
  match c with
  | .A1 => ⟨0, (N + 1 / 2) • 1, 0⟩
  | .A2 => ⟨!![1, 0; 0, 0], (N + 1 / 2) • 1, 0⟩
  | .B1 => ⟨1, !![0, 0; 0, 1 / 2], 0⟩
  | .B2 => ⟨1, N • 1, 0⟩
  | .C => ⟨k • 1, (|k ^ 2 - 1| * (N + 1 / 2)) • 1, 0⟩
  | .D => ⟨k • sigmaThree, ((k ^ 2 + 1) * (N + 1 / 2)) • 1, 0⟩

/-- Table 1, PDF p.9: B2 includes zero noise; k is amplitude, not intensity. -/
def ValidSourceCanonical (c : CanonicalClass) (k N : ℝ) : Prop :=
  0 ≤ N ∧ QAlgorithms.Papers.Independent.Frontier30.P07.ValidCanonical
    (match c with
    | .A1 => .a1 N
    | .A2 => .a2 N
    | .B1 => .b1
    | .B2 => .b2 N
    | .C => .c k N
    | .D => .d k N)

/-- Table 1, PDF pp.9-10: rank tests specialized to two real dimensions. -/
def classOf (g : GaussianData) : CanonicalClass :=
  if g.K.det = 0 then (if g.K = 0 then .A1 else .A2)
  else if g.K.det = 1 then
    (if g.alpha ≠ 0 ∧ g.alpha.det = 0 then .B1 else .B2)
  else if g.K.det < 0 then .D else .C

/-- Equation (2.18), PDF p.11, row=second map. D-D includes corrected B2 branch. -/
def compositionClasses (second first : CanonicalClass) : Set CanonicalClass :=
  match second, first with
  | .A1, _ => {.A1}
  | .A2, .A1 => {.A1}
  | .A2, _ => {.A2}
  | _, .A1 => {.A1}
  | _, .A2 => {.A2}
  | .B1, .B1 => {.B1}
  | .B1, .B2 => {.B1, .B2}
  | .B2, .B1 => {.B1, .B2}
  | .B2, .B2 => {.B2}
  | .C, .C => {.B2, .C}
  | .D, .D => {.B2, .C}
  | .D, _ => {.D}
  | _, .D => {.D}
  | _, _ => {.C}

/-- Equation (2.11), PDF p.8: m11,m21 are the upper blocks. -/
def couplingBlock (M : Matrix (Fin 4) (Fin 4) ℝ) (r s : Fin 2) : RealMatrix :=
  M.submatrix (fun i => ⟨2 * r.val + i.val, by omega⟩)
    (fun j => ⟨2 * s.val + j.val, by omega⟩)

/-- Equations (2.1),(2.10), PDF pp.6,8: full symplectic form. -/
def jointSymplecticMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- Bounded Weyl version of (2.10), with U-adjoint on the left, PDF p.8.
No products of unbounded Q/P operators on an unspecified domain are used. -/
def ImplementsJointGaussian (U : JointUnitary) (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  M.transpose * jointSymplecticMatrix * M = jointSymplecticMatrix ∧
    ∀ z w : (Fin 2 → ℝ),
      boundedUnitaryConjugation U.symm (productCoeff (sourceWeyl z) (sourceWeyl w)) =
        productCoeff
          (sourceWeyl ((couplingBlock M 0 0).mulVec z + (couplingBlock M 0 1).mulVec w))
          (sourceWeyl ((couplingBlock M 1 0).mulVec z + (couplingBlock M 1 1).mulVec w))

/-- Equation (2.9), PDF p.7: finite nonnegative thermal parameter, including vacuum. -/
def IsThermal (sigma : Matrix ℕ ℕ ℂ) (N : ℝ) : Prop :=
  0 ≤ N ∧ IsDensity sigma ∧ ∀ z : (Fin 2 → ℝ),
    sourceCharacteristic sigma z = Complex.exp
      (((-(N + 1 / 2) * (∑ i, z i ^ 2) / 2 : ℝ) : ℂ))

/-- Section 2.4, PDF p.12: B1 uses vacuum, all other canonical dilations use N0. -/
def environmentNumber (c : CanonicalClass) (N : ℝ) : ℝ :=
  if c = .B1 then 0 else N

/-- Appendix A, PDF p.20: explicit full matrices; k is amplitude kappa.
B2 is excluded from every theorem using this definition. -/
def appendixCouplingMatrix (c : CanonicalClass) (k : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  match c with
  | .A1 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  | .A2 => !![1, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, -1]
  | .B1 => !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 1, 0, -1]
  | .B2 => 1
  | .C => if k < 1 then
      let r := Real.sqrt (1 - k ^ 2)
      !![k, 0, r, 0; 0, k, 0, r; r, 0, -k, 0; 0, r, 0, -k]
    else
      let r := Real.sqrt (k ^ 2 - 1)
      !![k, 0, r, 0; 0, k, 0, -r; r, 0, k, 0; 0, -r, 0, k]
  | .D =>
      let r := Real.sqrt (k ^ 2 + 1)
      !![k, 0, r, 0; 0, -k, 0, r; r, 0, k, 0; 0, r, 0, -k]

/-- Table 2, PDF p.14: actual environmental coordinates from Appendix A.
For A2 the B1 noise scale is N+1/2 and is normalized only by a squeeze. -/
def complementData (c : CanonicalClass) (k N : ℝ) : GaussianData :=
  match c with
  | .A1 => ⟨1, 0, 0⟩
  | .A2 => ⟨1, !![0, 0; 0, N + 1 / 2], 0⟩
  | .B1 => canonicalData .A2 0 0
  | .B2 => ⟨0, 0, 0⟩
  | .C => if k < 1 then
      ⟨Real.sqrt (1 - k ^ 2) • 1, (k ^ 2 * (N + 1 / 2)) • 1, 0⟩
    else
      ⟨Real.sqrt (k ^ 2 - 1) • sigmaThree, (k ^ 2 * (N + 1 / 2)) • 1, 0⟩
  | .D => ⟨Real.sqrt (k ^ 2 + 1) • 1, (k ^ 2 * (N + 1 / 2)) • 1, 0⟩

/-- Section 3.2, PDF pp.16-17: regimes where the explicit reverse recovery applies. -/
def AntiRegion (c : CanonicalClass) (k : ℝ) : Prop :=
  c = .A1 ∨ c = .A2 ∨ c = .D ∨ (c = .C ∧ k ^ 2 ≤ 1 / 2)

/-- Section 3.2, PDF pp.16-17: equality belongs to both regimes. -/
def WeakRegion (c : CanonicalClass) (k : ℝ) : Prop :=
  c = .B1 ∨ (c = .C ∧ 1 / 2 ≤ k ^ 2)

/-- Section 3.2, PDF pp.16-17: anti-degrading maps, with identity at k^2=1/2. -/
def antiRecoveryData (c : CanonicalClass) (k N : ℝ) : GaussianData :=
  match c with
  | .A1 => canonicalData .A1 k N
  | .A2 => canonicalData .A2 k N
  | .D => canonicalData .D (k / Real.sqrt (k ^ 2 + 1)) N
  | _ =>
      let r := k / Real.sqrt (1 - k ^ 2)
      ⟨r • 1, ((1 - r ^ 2) * (N + 1 / 2)) • 1, 0⟩

/-- Section 3.2, PDF p.17: printed amplifier I and (r^2-1) are corrected
here to sigma3 and (r^2+1), forced by (2.6) and Table 2. Independent moderation
of this source correction is required. At k^2=1/2 the attenuator map is identity. -/
def weakRecoveryData (c : CanonicalClass) (k N : ℝ) : GaussianData :=
  if c = .B1 then complementData .B1 k N
  else if k < 1 then
    let r := Real.sqrt (1 - k ^ 2) / k
    ⟨r • 1, ((1 - r ^ 2) * (N + 1 / 2)) • 1, 0⟩
  else canonicalData .D (Real.sqrt (k ^ 2 - 1) / k) N

/-- Sections 2.3,2.5, PDF pp.11,14: class-C approximation with fixed noise. -/
def nearB2Data (N k : ℝ) : GaussianData :=
  ⟨k • 1, N • 1, 0⟩

/-- Equation (2.22), PDF p.13: real two-dimensional Lebesgue law.
At zero noise use a Dirac mass; division by zero never defines the endpoint. -/
def displacementNoise (N : ℝ) : Measure (ℝ × ℝ) :=
  if N = 0 then Measure.dirac (0, 0)
  else volume.withDensity (fun z => ENNReal.ofReal
    ((2 * Real.pi * N)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (2 * N))))

/-- Equation (2.22), PDF p.13: coefficient integral of the trace-class barycenter.
The theorem supplies integrability for all densities, not a default-zero integral. -/
def randomDisplacement (N : ℝ) : FockMap :=
  fun X i j => ∫ z : ℝ × ℝ,
    conjugateKernel (sourceWeyl ![z.1, z.2]) X i j ∂displacementNoise N

/-- Section 1, PDF p.4: two legs of one PURE isometry, with different outputs. -/
def TrueComplementary {I J K : Type} (E : Operation I J) (F : Operation I K) : Prop :=
  IsTraceClassChannel E ∧ IsTraceClassChannel F ∧
    ∃ V : Hilbert I →ₗᵢ[ℂ] Hilbert (J × K),
      (∀ rho : State I,
        partialRight (conjugateKernel (isometryCoeff V) rho.coefficients) = E rho.coefficients) ∧
      (∀ rho : State I,
        partialLeft (conjugateKernel (isometryCoeff V) rho.coefficients) = F rho.coefficients)

/-- Section 1, PDF p.4: anti-degradable in SOME physical representation.
This never asserts recovery from every fixed mixed weak complement. -/
def HasAntiRepresentation {I : Type} (E : Operation I I) : Prop :=
  ∃ (J : Type) (U : Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J)) (sigma : State J),
    (∀ rho : State I, dilationReceiver U sigma.coefficients rho.coefficients = E rho.coefficients) ∧
    AntiDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)

/-- Section 1, PDF p.3: coefficients of U tensor identity acting on rho's
input ket tensored with an actual purification vector, not an arbitrary channel. -/
def PurifiedImplementation {I J : Type}
    (U : Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J)) (v : Hilbert (J × ℕ))
    (V : Hilbert I →ₗᵢ[ℂ] Hilbert (I × (J × ℕ))) : Prop :=
  ∀ a i j c,
    V (lp.single 2 a 1) (i, (j, c)) =
      ∑' b, unitaryCoeff U (i, j) (a, b) * v (b, c)

abbrev BoundedOp (I : Type) := Hilbert I →L[ℂ] Hilbert I

/-- Section 1, PDF p.5: coefficients of a genuinely bounded observable. -/
def observableCoeff {I : Type} (T : BoundedOp I) : Matrix I I ℂ :=
  fun i j => T (lp.single 2 j 1) i

/-- Complete positivity test on bounded couplingBlock operators, Section 1, PDF p.5. -/
def BlockPositive {I : Type} {n : ℕ} (A : Fin n → Fin n → BoundedOp I) : Prop :=
  ∀ v : Fin n → Hilbert I,
    (∑ i, ∑ j, inner (𝕜 := ℂ) (v i) (A i j (v j))).im = 0 ∧
    0 ≤ (∑ i, ∑ j, inner (𝕜 := ℂ) (v i) (A i j (v j))).re

/-- Section 1, PDF p.5: complex linear, CP, unital Heisenberg map.
Normality is additionally guaranteed by its trace-class predual below. -/
def IsBoundedCPUnital {I J : Type} (H : BoundedOp J → BoundedOp I) : Prop :=
  (∀ A B, H (A + B) = H A + H B) ∧
  (∀ (c : ℂ) A, H (c • A) = c • H A) ∧
  H (ContinuousLinearMap.id ℂ (Hilbert J)) = ContinuousLinearMap.id ℂ (Hilbert I) ∧
  ∀ (n : ℕ) (A : Fin n → Fin n → BoundedOp J),
    BlockPositive A → BlockPositive (fun i j => H (A i j))

/-- Equation (1.6), PDF p.5: bounded-observable duality on every density. -/
def TraceDual {I J : Type} (E : Operation I J) (H : BoundedOp J → BoundedOp I) : Prop :=
  ∀ (rho : State I) T,
    traceClassObservablePair (E rho.coefficients) (observableCoeff T) =
      traceClassObservablePair rho.coefficients (observableCoeff (H T))

/-- Equations (4.1)-(4.2), PDF p.18; used only when k1*k2 != 1. -/
def ddPhotonNumber (k1 k2 N1 N2 : ℝ) : ℝ :=
  ((k2 ^ 2 + 1) * N2 + k2 ^ 2 * (k1 ^ 2 + 1) * N1) /
      |k1 ^ 2 * k2 ^ 2 - 1| +
    (1 / 2) * ((k1 ^ 2 * k2 ^ 2 + 2 * k2 ^ 2 + 1) /
      |k1 ^ 2 * k2 ^ 2 - 1| - 1)

/-- Equations (4.4)-(4.5), PDF p.19; used only when k1*k2 != 1. -/
def ccPhotonNumber (k1 k2 N1 N2 : ℝ) : ℝ :=
  (|k2 ^ 2 - 1| * N2 + k2 ^ 2 * |k1 ^ 2 - 1| * N1) /
      |k1 ^ 2 * k2 ^ 2 - 1| +
    (1 / 2) * ((k2 ^ 2 * |k1 ^ 2 - 1| + |k2 ^ 2 - 1|) /
      |k1 ^ 2 * k2 ^ 2 - 1| - 1)

/-! Sanity examples pin definitions, never prove the source results. -/

example : (canonicalData .B2 0 0).alpha = 0 := by
  simp [canonicalData]

example : (canonicalData .B1 0 0).alpha 0 0 = 0 := rfl

example : (canonicalData .A2 0 0).K 1 1 = 0 := rfl

example : sourceWeyl ![0, 0] = displacementMatrix 0 := by
  have hz : (⟨-(0 : ℝ) / Real.sqrt 2, (0 : ℝ) / Real.sqrt 2⟩ : ℂ) = 0 := by
    apply Complex.ext <;> simp
  change displacementMatrix
    (⟨-(0 : ℝ) / Real.sqrt 2, (0 : ℝ) / Real.sqrt 2⟩ : ℂ) = displacementMatrix 0
  exact congrArg displacementMatrix hz

example (X : Matrix ℕ ℕ ℂ) (z : Fin 2 → ℝ) :
    sourceCharacteristic X z =
      QAlgorithms.Papers.Independent.Dependency50.P39.characteristic
        (QAlgorithms.Papers.Independent.Dependency50.P39.operatorOfMatrix X)
        ⟨-z 1 / Real.sqrt 2, z 0 / Real.sqrt 2⟩ := rfl

example : ValidSourceCanonical .B2 0 0 := by
  simp [ValidSourceCanonical,
    QAlgorithms.Papers.Independent.Frontier30.P07.ValidCanonical]

example (g1 g2 : GaussianData) : (composeData g1 g2).K = g1.K * g2.K := rfl

example : displacementNoise 0 = Measure.dirac (0, 0) := by
  simp [displacementNoise]

example : environmentNumber .B1 5 = 0 := by
  simp [environmentNumber]

example : (appendixCouplingMatrix .A1 0) 0 2 = 1 := rfl

example : (complementData .A1 0 0).alpha = 0 := rfl

example : (complementData .A2 0 3).K = 1 := rfl

example : (weakRecoveryData .B1 0 0).K = (canonicalData .A2 0 0).K := by
  simp [weakRecoveryData, complementData]

example : CanonicalClass.B2 ∈ compositionClasses .D .D := by
  simp [compositionClasses]

example (N k : ℝ) : (nearB2Data N k).alpha = N • 1 := rfl

end QAlgorithms.Papers.Independent.Claimed50.P49


