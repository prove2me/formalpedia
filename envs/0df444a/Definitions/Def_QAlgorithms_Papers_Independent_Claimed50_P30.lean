-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
-- name    : QAlgorithms_Papers_Independent_Claimed50_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:17:30.858016+00:00
-- url     : https://prove2.me/theorems/46fa6a51-c0a5-4527-bed2-2213de34a2d9
-- title:
--   Definitions for Computable bounds for the discrimination of Gaussian states
-- statement:
--   The objects the formalized statements of *Computable bounds for the discrimination of Gaussian states* (arXiv:0806.1625) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ModeHilbert`: Completed n-mode number space, PDF pp.1--2; no photon cutoff.
--   - `ModeOperator`: Bounded operators on the completed oscillator space, PDF p.2.
--   - `Quadrature`: Interleaved coordinates (q_1,p_1,...,q_n,p_n), PDF p.1, (1).
--   - `PhaseVector`: Real phase space in interleaved coordinates, PDF p.2, (3).
--   - `numberBasis`: The canonical complete number basis; Mathlib's l2 coordinate isometry.
--   - `numberKet`: The number ket in the completed space, PDF p.2, (17).
--   - `trace`: The accepted basis-independent trace specialized to the complete number basis. Only trace-class operators are used in source targets; summability is explicit.
--   - `TraceSummable`: Absolute convergence guard for the displayed basis trace.
--   - `IsModeDensity`: Positive trace-class density, PDF p.2, (4),(16). Positivity includes self-adjointness, and the trace is one, excluding the zero operator.
--   - `canonicalOmega`: Omega = direct sum [[0,1],[-1,0]], PDF p.2, (2).
--   - `dot`: The real dot product in the source's quadrature order.
--   - `PhysicalCovariance`: The physical, real, symmetric, strictly positive covariance domain, including V+i Omega >=0, PDF p.2, (9),(13).
--   - `Symplectic`: Symplecticity with the source's transpose convention, PDF p.2, (10).
--   - `repeatedDiagonal`: Repeated 2n-dimensional diagonal: every symplectic eigenvalue occurs twice.
--   - `displacementArgument`: Convert D(xi)=exp(i(q xi_q+p xi_p)) to D(z)=exp(z a*-conj(z)a). For q=a+a*, p=i(a*-a), one has z=-xi_p+i xi_q.
--   - `FockWeylSystem`: The actual standard oscillator Weyl system, fixed by ALL its Fock entries. The finite product is the n-mode tensor product of the accepted displacement coefficients. Unitary bounded operators avoid exponentiating unbounded q,p. These are coordinate/CCR data, not any Gaussian trace or power identity.
--   - `modeWeylTrace`: chi(xi)=Tr(rho D(xi)), with exactly the source ordering, PDF p.2, (4).
--   - `GaussianMoments`: A genuine Gaussian density with physical first and second moments, PDF p.2, (6)--(9). All modeWeylTrace pairings are absolutely convergent. This does not assume the power-state or overlap formulas being proved.
--   - `GaussianState`: Gaussian state data are attached to an actual density, not just a covariance.
--   - `thermalWeight`: Single-mode thermal occupation weights, PDF p.2, (17), valid for nu>=1. In particular nu=1 is the vacuum and uses 0^0=1 at j=0.
--   - `thermalProductWeight`: Independent normal-mode thermal weights on all number strings.
--   - `thermalTerm`: A single term of the full thermal density series, PDF p.2, (16)--(17).
--   - `thermalTensorDensity`: The actual thermal tensor density as a series of bounded rank-one operators. No cutoff is imposed. On physical spectra the nuclear series is summable; the source targets explicitly conclude summability, preventing a default tsum.
--   - `unitaryConjugation`: Bounded unitary conjugation, source (15)--(16).
--   - `normalDensity`: The independently constructed normal-mode density of (16).
--   - `NormalModes`: Physical Williamson normal modes, PDF p.2, (10)--(17). The unitary implements x -> Sx+u by U*D(xi)U=exp(i u^T xi)D(S^T xi). The only state equality assumed is the source's ORIGINAL normal decomposition; no identity about rho^p, rho(p), or a Gaussian overlap is a field.
--   - `phiPlus`: Phi_p^+, PDF p.2, (18); physical arguments satisfy x>=1,p>0.
--   - `phiMinus`: Phi_p^-, PDF p.2, (18); strictly positive on the physical domain.
--   - `spectralG`: G_p, PDF p.2, (19). Endpoint p=0 is never used.
--   - `spectralLambda`: Lambda_p, PDF p.2, (20). Pure modes x=1 are included.
--   - `positiveOperatorPower`: Genuine bounded-operator positive spectral power, not a formula in moment data. This differs from the accepted P48.densityPower, which is an IID tensor power.
--   - `powerState`: Independently constructed normalized power candidate (23), not rho^p/Tr(rho^p).
--   - `powerCovariance`: Physical covariance of the independent power state, PDF p.3, (32).
--   - `chernoffTrace`: Actual operator Chernoff trace (45), independent of the formula in Theorem 2.
--   - `halfInfPower`: A prior factor 1/2 OUTSIDE the Nth power of the interior infimum. The infimum is in the complete nonnegative extended reals: no empty/unbounded real-infimum default. Interior functions in source targets are nonnegative and finite; their infima are finite by evaluation at s=1/2.
--   - `quantumChernoff`: Equal-prior N-copy quantum Chernoff bound, PDF p.4, (44)--(45). N counts independent copies, whereas n always counts modes.
--   - `spectralPsi`: Psi_p(x,y), PDF p.5, (62); only 0<p<1 and positive n are used.
--   - `minkowskiFunction`: M_s=4^n times the inverse nth power of the ENTIRE sum, PDF p.5, (61).
--   - `minkowskiBound`: The N-copy Minkowski bound (60).
--   - `spectralGamma`: Gamma_p(x)=[(x+1)^(2p)-(x-1)^(2p)]^(-1/2), PDF p.6, (74). Written as reciprocal positive square root to pin the exponent.
--   - `youngFunction`: Y_s, PDF p.6, (73),(79). Formula (78)'s product scope is not copied.
--   - `youngBound`: The N-copy Young bound (72).
--   - `operatorSquaredFidelity`: The squared Uhlmann fidelity, PDF p.4, (50), as an actual operator trace. Used only for the thermal densities in the worked example.
--   - `fidelityLower`: F_- of (49), with squared fidelity as its argument.
--   - `fidelityUpper`: F_+ of (49), with squared fidelity as its argument.
-- source:
--   Computable bounds for the discrimination of Gaussian states, arXiv:0806.1625v2, https://arxiv.org/abs/0806.1625v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

/-!
# Computable bounds for the discrimination of Gaussian states

arXiv:0806.1625v2, PDF pp.1--7. The oscillator space is the completed l2
space of all number strings. The Weyl system is pinned by the actual Fock
coefficients, with D(xi)=exp(i x^T xi), hbar=2, and vacuum covariance I.
Only the six source results are admitted. All local definitions have bodies.
Covariance and quadratic are imported exact accepted interfaces. Other local
names distinguish full n-mode spectral/CCR objects from incompatible frozen
one-mode, finite-matrix, tensor-power or graph-phase namesakes.
The endpoint convention for every infimum is the open interval (0,1),
equivalent to adjoining one-sided limits. No value of G_0 or Lambda_0 is used.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- Mathlib supplies this C-star functional calculus as a theorem, not a global instance.
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P30

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass IsPositive operatorTrace)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P04 (Covariance)
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- Completed n-mode number space, PDF pp.1--2; no photon cutoff. -/
abbrev ModeHilbert (n : ℕ) := QAlgorithms.RealRegisters.Hilbert (Fin n → ℕ)

/-- Bounded operators on the completed oscillator space, PDF p.2. -/
abbrev ModeOperator (n : ℕ) := ModeHilbert n →L[ℂ] ModeHilbert n

/-- Interleaved coordinates (q_1,p_1,...,q_n,p_n), PDF p.1, (1). -/
abbrev Quadrature (n : ℕ) := Fin n × Fin 2

/-- Real phase space in interleaved coordinates, PDF p.2, (3). -/
abbrev PhaseVector (n : ℕ) := Quadrature n → ℝ

/-- The canonical complete number basis; Mathlib's l2 coordinate isometry. -/
def numberBasis (n : ℕ) : HilbertBasis (Fin n → ℕ) ℂ (ModeHilbert n) :=
  ⟨LinearIsometryEquiv.refl ℂ (ModeHilbert n)⟩

/-- The number ket in the completed space, PDF p.2, (17). -/
def numberKet {n : ℕ} (j : Fin n → ℕ) : ModeHilbert n := numberBasis n j

/-- The accepted basis-independent trace specialized to the complete number basis.
Only trace-class operators are used in source targets; summability is explicit. -/
def trace {n : ℕ} (T : ModeOperator n) : ℂ := operatorTrace (numberBasis n) T

/-- Absolute convergence guard for the displayed basis trace. -/
def TraceSummable {n : ℕ} (T : ModeOperator n) : Prop :=
  Summable (fun j : Fin n → ℕ => inner ℂ (numberKet j) (T (numberKet j)))

/-- Positive trace-class density, PDF p.2, (4),(16). Positivity includes
self-adjointness, and the trace is one, excluding the zero operator. -/
def IsModeDensity {n : ℕ} (rho : ModeOperator n) : Prop :=
  IsTraceClass rho ∧ IsPositive rho ∧ TraceSummable rho ∧ trace rho = 1

/-- Omega = direct sum [[0,1],[-1,0]], PDF p.2, (2). -/
def canonicalOmega (n : ℕ) : Covariance n :=
  fun i j => if i.1 = j.1 then
    (if i.2 = 0 ∧ j.2 = 1 then 1 else if i.2 = 1 ∧ j.2 = 0 then -1 else 0)
    else 0

/-- The real dot product in the source's quadrature order. -/
def dot {n : ℕ} (x y : PhaseVector n) : ℝ := ∑ i, x i * y i

/-- The physical, real, symmetric, strictly positive covariance domain,
including V+i Omega >=0, PDF p.2, (9),(13). -/
def PhysicalCovariance {n : ℕ} (V : Covariance n) : Prop :=
  V.transpose = V ∧ V.PosDef ∧
    Matrix.PosSemidef (fun i j => (V i j : ℂ) + Complex.I * (canonicalOmega n i j : ℂ))

/-- Symplecticity with the source's transpose convention, PDF p.2, (10). -/
def Symplectic {n : ℕ} (S : Covariance n) : Prop :=
  S * canonicalOmega n * S.transpose = canonicalOmega n

/-- Repeated 2n-dimensional diagonal: every symplectic eigenvalue occurs twice. -/
def repeatedDiagonal {n : ℕ} (nu : Fin n → ℝ) : Covariance n :=
  Matrix.diagonal (fun i => nu i.1)

/-- Convert D(xi)=exp(i(q xi_q+p xi_p)) to D(z)=exp(z a*-conj(z)a).
For q=a+a*, p=i(a*-a), one has z=-xi_p+i xi_q. -/
def displacementArgument {n : ℕ} (xi : PhaseVector n) (k : Fin n) : ℂ :=
  -(xi (k, 1) : ℂ) + Complex.I * (xi (k, 0) : ℂ)

/-- The actual standard oscillator Weyl system, fixed by ALL its Fock entries.
The finite product is the n-mode tensor product of the accepted displacement
coefficients. Unitary bounded operators avoid exponentiating unbounded q,p.
These are coordinate/CCR data, not any Gaussian trace or power identity. -/
structure FockWeylSystem (n : ℕ) where
  operator : PhaseVector n → ModeOperator n
  unitary : ∀ xi, operator xi ∈ unitary (ModeOperator n)
  coefficients : ∀ (xi : PhaseVector n) (i j : Fin n → ℕ),
    operator xi (numberKet j) i =
      ∏ k, displacementMatrix (displacementArgument xi k) (i k) (j k)

/-- chi(xi)=Tr(rho D(xi)), with exactly the source ordering, PDF p.2, (4). -/
def modeWeylTrace {n : ℕ} (W : FockWeylSystem n) (rho : ModeOperator n) (xi : PhaseVector n) : ℂ :=
  trace (rho.comp (W.operator xi))

/-- A genuine Gaussian density with physical first and second moments,
PDF p.2, (6)--(9). All modeWeylTrace pairings are absolutely convergent.
This does not assume the power-state or overlap formulas being proved. -/
def GaussianMoments {n : ℕ} (W : FockWeylSystem n) (rho : ModeOperator n)
    (u : PhaseVector n) (V : Covariance n) : Prop :=
  IsModeDensity rho ∧ PhysicalCovariance V ∧
    ∀ xi, TraceSummable (rho.comp (W.operator xi)) ∧
      modeWeylTrace W rho xi =
        Complex.exp (((-quadratic V xi / 2 : ℝ) : ℂ) + Complex.I * (dot u xi : ℂ))

/-- Gaussian state data are attached to an actual density, not just a covariance. -/
structure GaussianState (n : ℕ) (W : FockWeylSystem n) where
  rho : ModeOperator n
  mean : PhaseVector n
  covariance : Covariance n
  gaussian : GaussianMoments W rho mean covariance

/-- Single-mode thermal occupation weights, PDF p.2, (17), valid for nu>=1.
In particular nu=1 is the vacuum and uses 0^0=1 at j=0. -/
def thermalWeight (nu : ℝ) (j : ℕ) : ℝ :=
  2 / (nu + 1) * ((nu - 1) / (nu + 1)) ^ j

/-- Independent normal-mode thermal weights on all number strings. -/
def thermalProductWeight {n : ℕ} (nu : Fin n → ℝ) (j : Fin n → ℕ) : ℝ :=
  ∏ k, thermalWeight (nu k) (j k)

/-- A single term of the full thermal density series, PDF p.2, (16)--(17). -/
def thermalTerm {n : ℕ} (nu : Fin n → ℝ) (j : Fin n → ℕ) : ModeOperator n :=
  (thermalProductWeight nu j : ℂ) • InnerProductSpace.rankOne ℂ (numberKet j) (numberKet j)

/-- The actual thermal tensor density as a series of bounded rank-one operators.
No cutoff is imposed. On physical spectra the nuclear series is summable;
the source targets explicitly conclude summability, preventing a default tsum. -/
def thermalTensorDensity {n : ℕ} (nu : Fin n → ℝ) : ModeOperator n := ∑' j, thermalTerm nu j

/-- Bounded unitary conjugation, source (15)--(16). -/
def unitaryConjugation {n : ℕ} (U : ModeHilbert n ≃ₗᵢ[ℂ] ModeHilbert n) (T : ModeOperator n) : ModeOperator n :=
  U.toLinearIsometry.toContinuousLinearMap.comp
    (T.comp U.symm.toLinearIsometry.toContinuousLinearMap)

/-- The independently constructed normal-mode density of (16). -/
def normalDensity {n : ℕ} (U : ModeHilbert n ≃ₗᵢ[ℂ] ModeHilbert n)
    (nu : Fin n → ℝ) : ModeOperator n := unitaryConjugation U (thermalTensorDensity nu)

/-- Physical Williamson normal modes, PDF p.2, (10)--(17).
The unitary implements x -> Sx+u by U*D(xi)U=exp(i u^T xi)D(S^T xi).
The only state equality assumed is the source's ORIGINAL normal decomposition;
no identity about rho^p, rho(p), or a Gaussian overlap is a field. -/
structure NormalModes {n : ℕ} {W : FockWeylSystem n} (A : GaussianState n W) where
  spectrum : Fin n → ℝ
  spectrum_ge_one : ∀ k, 1 ≤ spectrum k
  symplecticMatrix : Covariance n
  symplectic : Symplectic symplecticMatrix
  covariance_eq : A.covariance =
    symplecticMatrix * repeatedDiagonal spectrum * symplecticMatrix.transpose
  gaussianUnitary : ModeHilbert n ≃ₗᵢ[ℂ] ModeHilbert n
  implements : ∀ xi, unitaryConjugation gaussianUnitary.symm (W.operator xi) =
    Complex.exp (Complex.I * (dot A.mean xi : ℂ)) •
      W.operator (symplecticMatrix.transpose.mulVec xi)
  normal_eq : A.rho = normalDensity gaussianUnitary spectrum

/-- Phi_p^+, PDF p.2, (18); physical arguments satisfy x>=1,p>0. -/
def phiPlus (p x : ℝ) : ℝ := Real.rpow (x + 1) p + Real.rpow (x - 1) p

/-- Phi_p^-, PDF p.2, (18); strictly positive on the physical domain. -/
def phiMinus (p x : ℝ) : ℝ := Real.rpow (x + 1) p - Real.rpow (x - 1) p

/-- G_p, PDF p.2, (19). Endpoint p=0 is never used. -/
def spectralG (p x : ℝ) : ℝ := Real.rpow 2 p / phiMinus p x

/-- Lambda_p, PDF p.2, (20). Pure modes x=1 are included. -/
def spectralLambda (p x : ℝ) : ℝ := phiPlus p x / phiMinus p x

/-- Genuine bounded-operator positive spectral power, not a formula in moment data.
This differs from the accepted P48.densityPower, which is an IID tensor power. -/
def positiveOperatorPower {n : ℕ} (rho : ModeOperator n) (p : ℝ) : ModeOperator n := by
  letI : ContinuousFunctionalCalculus ℂ (ModeOperator n) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus (A := ModeOperator n)
  letI : ContinuousFunctionalCalculus ℝ (ModeOperator n) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus (A := ModeOperator n)
  exact CFC.rpow rho p

/-- Independently constructed normalized power candidate (23), not rho^p/Tr(rho^p). -/
def powerState {n : ℕ} {W : FockWeylSystem n} {A : GaussianState n W}
    (D : NormalModes A) (p : ℝ) : ModeOperator n :=
  normalDensity D.gaussianUnitary (fun k => spectralLambda p (D.spectrum k))

/-- Physical covariance of the independent power state, PDF p.3, (32). -/
def powerCovariance {n : ℕ} {W : FockWeylSystem n} {A : GaussianState n W}
    (D : NormalModes A) (p : ℝ) : Covariance n :=
  D.symplecticMatrix * repeatedDiagonal (fun k => spectralLambda p (D.spectrum k)) *
    D.symplecticMatrix.transpose

/-- Actual operator Chernoff trace (45), independent of the formula in Theorem 2. -/
def chernoffTrace {n : ℕ} (rhoA rhoB : ModeOperator n) (s : ℝ) : ℝ :=
  (trace ((positiveOperatorPower rhoA s).comp (positiveOperatorPower rhoB (1 - s)))).re

/-- A prior factor 1/2 OUTSIDE the Nth power of the interior infimum.
The infimum is in the complete nonnegative extended reals: no empty/unbounded
real-infimum default. Interior functions in source targets are nonnegative and
finite; their infima are finite by evaluation at s=1/2. -/
def halfInfPower (f : ℝ → ℝ) (N : ℕ) : ℝ≥0∞ :=
  (⨅ s : Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (f s)) ^ N / 2

/-- Equal-prior N-copy quantum Chernoff bound, PDF p.4, (44)--(45).
N counts independent copies, whereas n always counts modes. -/
def quantumChernoff {n : ℕ} (rhoA rhoB : ModeOperator n) (N : ℕ) : ℝ≥0∞ :=
  halfInfPower (chernoffTrace rhoA rhoB) N

/-- Psi_p(x,y), PDF p.5, (62); only 0<p<1 and positive n are used. -/
def spectralPsi (n : ℕ) (p x y : ℝ) : ℝ :=
  Real.rpow (phiPlus p x * phiMinus (1 - p) y) (1 / (n : ℝ))

/-- M_s=4^n times the inverse nth power of the ENTIRE sum, PDF p.5, (61). -/
def minkowskiFunction {n : ℕ} (alpha beta : Fin n → ℝ) (s : ℝ) : ℝ :=
  (4 : ℝ) ^ n /
    ((∏ k, spectralPsi n s (alpha k) (beta k)) +
      (∏ k, spectralPsi n (1 - s) (beta k) (alpha k))) ^ n

/-- The N-copy Minkowski bound (60). -/
def minkowskiBound {n : ℕ} (alpha beta : Fin n → ℝ) (N : ℕ) : ℝ≥0∞ :=
  halfInfPower (minkowskiFunction alpha beta) N

/-- Gamma_p(x)=[(x+1)^(2p)-(x-1)^(2p)]^(-1/2), PDF p.6, (74).
Written as reciprocal positive square root to pin the exponent. -/
def spectralGamma (p x : ℝ) : ℝ :=
  (Real.sqrt (Real.rpow (x + 1) (2 * p) - Real.rpow (x - 1) (2 * p)))⁻¹

/-- Y_s, PDF p.6, (73),(79). Formula (78)'s product scope is not copied. -/
def youngFunction {n : ℕ} (alpha beta : Fin n → ℝ) (s : ℝ) : ℝ :=
  (2 : ℝ) ^ n * ∏ k, spectralGamma s (alpha k) * spectralGamma (1 - s) (beta k)

/-- The N-copy Young bound (72). -/
def youngBound {n : ℕ} (alpha beta : Fin n → ℝ) (N : ℕ) : ℝ≥0∞ :=
  halfInfPower (youngFunction alpha beta) N

/-- The squared Uhlmann fidelity, PDF p.4, (50), as an actual operator trace.
Used only for the thermal densities in the worked example. -/
def operatorSquaredFidelity {n : ℕ} (rhoA rhoB : ModeOperator n) : ℝ :=
  (trace (positiveOperatorPower
    ((positiveOperatorPower rhoA (1 / 2)).comp (rhoB.comp (positiveOperatorPower rhoA (1 / 2))))
    (1 / 2))).re ^ 2

/-- F_- of (49), with squared fidelity as its argument. -/
def fidelityLower (F : ℝ) : ℝ := (1 - Real.sqrt (1 - F)) / 2

/-- F_+ of (49), with squared fidelity as its argument. -/
def fidelityUpper (F : ℝ) : ℝ := Real.sqrt F / 2

/-! Definition sanity checks. These do not prove the six source results. -/

example : canonicalOmega 1 (0, 0) (0, 1) = 1 := by norm_num [canonicalOmega]

example : canonicalOmega 1 (0, 1) (0, 0) = -1 := by norm_num [canonicalOmega]

example (n : ℕ) (nu : Fin n → ℝ) (k : Fin n) (b : Fin 2) :
    repeatedDiagonal nu (k, b) (k, b) = nu k := by simp [repeatedDiagonal]

example (j : ℕ) : thermalWeight 1 j = (0 : ℝ) ^ j := by norm_num [thermalWeight]

example {n : ℕ} (j : Fin n → ℕ) : numberKet j = lp.single 2 j 1 := by
  rw [numberKet, ← HilbertBasis.repr_symm_single]
  rfl

example (n : ℕ) : displacementArgument (0 : PhaseVector n) = 0 := by
  funext k
  simp [displacementArgument]

example : spectralG 1 1 = 1 := by norm_num [spectralG, phiMinus]

example : spectralLambda 1 1 = 1 := by norm_num [spectralLambda, phiPlus, phiMinus]

example : fidelityLower 1 = 1 / 2 ∧ fidelityUpper 1 = 1 / 2 := by
  norm_num [fidelityLower, fidelityUpper]

example : halfInfPower (fun _ => 1) 1 = (1 / 2 : ℝ≥0∞) := by
  have hi : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  letI := hi
  simp [halfInfPower]

end QAlgorithms.Papers.Independent.Claimed50.P30


