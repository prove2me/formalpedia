-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P23
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:27:07.513639+00:00
-- url     : https://prove2.me/theorems/d343d444-2949-4039-a76c-216da507b2e3
-- title:
--   Definitions for Entanglement entropy of two disjoint intervals in conformal field theory
-- statement:
--   The objects the formalized statements of *Entanglement entropy of two disjoint intervals in conformal field theory* (arXiv:0905.2069) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `hypergeometricTerm`: Coefficient of the defining Gauss series F_y(x), source p.4, Eq.(10). The two denominator factorials are (1)_j and j!, respectively.
--   - `hypergeometricF`: The actual Gauss series 2F1(y,1-y;1;x), not a freely chosen function. Only its convergence domain 0 < x < 1 is used below; source p.4, Eq.(10).
--   - `hypergeometricRatio`: Source p.4, Eq.(10). End parameters y=0,1 are never used in period sums.
--   - `complexHypergeometricTerm`: Complex-parameter Gauss series coefficient for the vertical integral (79), p.17. The argument x remains real and in (0,1).
--   - `complexHypergeometricF`: Actual Gauss power series in its unit-disc convergence domain, with complex parameter z, for Eq.(79), source p.17.
--   - `negativeDerivativeIntegrand`: Parametrization z=i t of the negative-derivative integral (79), p.17. The factor dz/i is dt. Complex.log uses the principal branch, continued from F_z(0)=1. The single totalized value at t=0 does not affect the integral.
--   - `negativeReplicaDerivative`: The explicit d(x) integral in (79), with the minus-derivative convention of (78). No interpolation of the integer replica data is assumed or claimed.
--   - `negativeDerivativePolynomial`: The finite polynomial displayed in (D.8), p.30, through order eleven. The large final coefficients and the negative order-ten sign are retained.
--   - `cosineMatrix`: The source's C_{k/n}, with d coordinates numbered 1,...,d; p.11, Eq.(48).
--   - `periodKernel`: Imaginary-part period kernel, summing k=1,...,n-1; pp.11--12, (50),(56). The coordinate difference is unchanged by numbering coordinates from zero.
--   - `gammaMatrix`: Imaginary part of Gamma of (9); the n=1 matrix has empty index type.
--   - `dualGammaMatrix`: Imaginary part of the dual matrix in (56), source p.12.
--   - `thetaTerm`: A term of Theta(0|i G), source p.4, Eq.(11).
--   - `theta0`: Exact lattice sum for a purely imaginary period matrix, source p.4, Eq.(11). Summability on all period matrices used is asserted in the results, not assumed.
--   - `replicaFactor`: Explicit theta quotient in Eq.(8), pp.3--4. This is an analytic function constructed from the lattice sums, not a definition of a CFT density matrix.
--   - `selfDualContinuation`: The identically constant self-dual continuation explicitly selected by the source on p.4. This does not choose a continuation at other radii.
--   - `betaProduct`: Beta product over precisely the nonzero replica frequencies, p.27, Eq.(B.6).
--   - `hypergeometricProduct`: Hypergeometric product of Eq.(61), source p.13.
--   - `imaginaryMatrix`: Complex matrix whose imaginary part is G.
--   - `fourierMatrix`: Normalized positive-sign Fourier matrix, source p.11, Eq.(53). Both row and column indices in the exponential are the source's 1,...,n.
--   - `fullPeriod`: Imaginary part of Omega or its dual, source pp.11--12.
--   - `periodEigenvalue`: The last eigenvalue is zero by definition; beta_1 is never evaluated and multiplied by sin(pi). Source p.11, Eq.(52) and its zero-mode paragraph.
--   - `specialA`: The particular A=2 Uhat^dagger H Uhat in Appendix B, p.27. This real cosine sum is its real value; H_kk=sin(pi k/n).
--   - `jacobiTheta2`: Jacobi theta_2(i t), p.13, Eq.(64), with t>0 in its uses.
--   - `jacobiTheta3`: Jacobi theta_3(i t), source p.13.
--   - `jacobiTheta4`: Jacobi theta_4(i t), source p.13. Integer parity supplies (-1)^m.
--   - `thetaTriple`: The three-term bracket in (64); the overall factor 1/2 is not included.
--   - `windingEnergy`: The integer nearest-neighbor form in Eq.(68), source pp.14--15. The adjacent-pair sum contains exactly n-2 terms.
--   - `windingBlock`: Contiguous block of length ell, starting at a, with one constant sign; source p.15, following Eq.(68). Admissible starts are Fin(n-ell).
--   - `windingFourier`: Fourier form on the left of Eq.(68), source p.14.
--   - `windingConstant`: The source's f_y=2 gamma_E+psi(y)+psi(1-y), p.14. Gamma and its logarithmic derivative are the actual Mathlib functions.
--   - `replicaP`: The coefficient P_n(alpha), source p.19, Eq.(83).
--   - `windingCoefficient`: Leading winding coefficient in (72), with the full base 2n sin(...).
--   - `halfDIntegrand`: Entire combined integrand of Eq.(D.5), source p.30; none of its divergent pieces is separately integrated.
--   - `halfDContinuation`: The explicit positive-real-n continuation at x=1/2, p.30, Eq.(D.5).
--   - `halfDNegativeIntegrand`: Combined derivative integrand in (D.6), source p.30.
--   - `halfPIntegrand`: Source p.31, Eq.(D.12), combined before integration.
--   - `halfPContinuation`: Explicit real-n function of (D.12), source p.31.
--   - `halfPDerivativeIntegrand`: Derivative integrand of (D.13), source p.31.
--   - `unitPContinuation`: Polynomial continuation of (D.9), source p.31.
--   - `zeroPContinuation`: Auxiliary alpha=0 endpoint continuation, source p.31; no eta=0 theory.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, https://arxiv.org/abs/0905.2069v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

/-!
Explicit mathematical identities from Calabrese--Cardy--Tonni, arXiv:0905.2069v2.
Real matrices below are the imaginary parts of the source's purely imaginary
period matrices. Thus `theta0 G` is exactly the source's Theta(0 | i G).
No identification with a constructed CFT marginal is asserted in this module.
The missing physical interface and source ambiguities are recorded in HARD.md.
-/

noncomputable section

open scoped BigOperators Topology
open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Coefficient of the defining Gauss series F_y(x), source p.4, Eq.(10).
The two denominator factorials are (1)_j and j!, respectively. -/
def hypergeometricTerm (y x : ℝ) (j : ℕ) : ℝ :=
  (∏ a ∈ Finset.range j, (y + (a : ℝ)) * (1 - y + (a : ℝ))) /
    ((Nat.factorial j : ℝ) ^ 2) * x ^ j

/-- The actual Gauss series 2F1(y,1-y;1;x), not a freely chosen function.
Only its convergence domain 0 < x < 1 is used below; source p.4, Eq.(10). -/
def hypergeometricF (y x : ℝ) : ℝ :=
  ∑' j : ℕ, hypergeometricTerm y x j

/-- Source p.4, Eq.(10). End parameters y=0,1 are never used in period sums. -/
def hypergeometricRatio (y x : ℝ) : ℝ := hypergeometricF y (1 - x) / hypergeometricF y x

/-- Complex-parameter Gauss series coefficient for the vertical integral
(79), p.17. The argument x remains real and in (0,1). -/
def complexHypergeometricTerm (z : ℂ) (x : ℝ) (j : ℕ) : ℂ :=
  (∏ a ∈ Finset.range j, (z + (a : ℂ)) * (1 - z + (a : ℂ))) /
    ((Nat.factorial j : ℂ) ^ 2) * (x : ℂ) ^ j

/-- Actual Gauss power series in its unit-disc convergence domain, with
complex parameter z, for Eq.(79), source p.17. -/
def complexHypergeometricF (z : ℂ) (x : ℝ) : ℂ :=
  ∑' j : ℕ, complexHypergeometricTerm z x j

/-- Parametrization z=i t of the negative-derivative integral (79), p.17.
The factor dz/i is dt. Complex.log uses the principal branch, continued from
F_z(0)=1. The single totalized value at t=0 does not affect the integral. -/
def negativeDerivativeIntegrand (x t : ℝ) : ℝ :=
  (-( (Real.pi : ℂ) * (t : ℂ) * Complex.I /
    Complex.sin ((Real.pi : ℂ) * (t : ℂ) * Complex.I) ^ 2 *
      Complex.log (complexHypergeometricF ((t : ℂ) * Complex.I) x))).re

/-- The explicit d(x) integral in (79), with the minus-derivative convention
of (78). No interpolation of the integer replica data is assumed or claimed. -/
def negativeReplicaDerivative (x : ℝ) : ℝ :=
  ∫ t : ℝ, negativeDerivativeIntegrand x t

/-- The finite polynomial displayed in (D.8), p.30, through order eleven.
The large final coefficients and the negative order-ten sign are retained. -/
def negativeDerivativePolynomial (x : ℝ) : ℝ :=
  x / 3 + (2 / 15 : ℝ) * x ^ 2 + (26 / 315 : ℝ) * x ^ 3 +
  (2 / 35 : ℝ) * x ^ 4 + (52 / 1155 : ℝ) * x ^ 5 +
  (302 / 9009 : ℝ) * x ^ 6 + (76 / 2145 : ℝ) * x ^ 7 +
  (398 / 255255 : ℝ) * x ^ 8 + (327128 / 2297295 : ℝ) * x ^ 9 -
  (18047684 / 24249225 : ℝ) * x ^ 10 + (31378136 / 5311735 : ℝ) * x ^ 11

/-- The source's C_{k/n}, with d coordinates numbered 1,...,d; p.11, Eq.(48). -/
def cosineMatrix (n k d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun r s => Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ) *
    ((r.val : ℝ) - (s.val : ℝ)))

/-- Imaginary-part period kernel, summing k=1,...,n-1; pp.11--12, (50),(56).
The coordinate difference is unchanged by numbering coordinates from zero. -/
def periodKernel (n d : ℕ) (w : ℕ → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun r s => 2 / (n : ℝ) * ∑ k : Fin (n - 1),
    Real.sin (Real.pi * ((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) *
      w (k.val + 1) * cosineMatrix n (k.val + 1) d r s

/-- Imaginary part of Gamma of (9); the n=1 matrix has empty index type. -/
def gammaMatrix (n : ℕ) (x : ℝ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  periodKernel n (n - 1) (fun k => hypergeometricRatio ((k : ℝ) / (n : ℝ)) x)

/-- Imaginary part of the dual matrix in (56), source p.12. -/
def dualGammaMatrix (n : ℕ) (x : ℝ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  periodKernel n (n - 1) (fun k => (hypergeometricRatio ((k : ℝ) / (n : ℝ)) x)⁻¹)

/-- A term of Theta(0|i G), source p.4, Eq.(11). -/
def thetaTerm {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℤ) : ℝ :=
  Real.exp (-Real.pi * QAlgorithms.Papers.Independent.Information100.P37.quadratic G (fun r => (m r : ℝ)))

/-- Exact lattice sum for a purely imaginary period matrix, source p.4, Eq.(11).
Summability on all period matrices used is asserted in the results, not assumed. -/
def theta0 {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑' m : Fin d → ℤ, thetaTerm G m

/-- Explicit theta quotient in Eq.(8), pp.3--4. This is an analytic function
constructed from the lattice sums, not a definition of a CFT density matrix. -/
def replicaFactor (n : ℕ) (eta x : ℝ) : ℝ :=
  theta0 (eta • gammaMatrix n x) * theta0 (eta⁻¹ • gammaMatrix n x) /
    theta0 (gammaMatrix n x) ^ 2

/-- The identically constant self-dual continuation explicitly selected by
the source on p.4. This does not choose a continuation at other radii. -/
def selfDualContinuation (_n : ℝ) : ℝ := 1

/-- Beta product over precisely the nonzero replica frequencies, p.27, Eq.(B.6). -/
def betaProduct (n : ℕ) (x : ℝ) : ℝ :=
  ∏ k : Fin (n - 1), hypergeometricRatio (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) x

/-- Hypergeometric product of Eq.(61), source p.13. -/
def hypergeometricProduct (n : ℕ) (x : ℝ) : ℝ :=
  ∏ k : Fin (n - 1), hypergeometricF (((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) x

/-- Complex matrix whose imaginary part is G. -/
def imaginaryMatrix {d : ℕ} (G : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℂ := fun r s => (G r s : ℂ) * Complex.I

/-- Normalized positive-sign Fourier matrix, source p.11, Eq.(53).
Both row and column indices in the exponential are the source's 1,...,n. -/
def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun q r => Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    (((q.val + 1 : ℕ) : ℂ) * ((r.val + 1 : ℕ) : ℂ)) / (n : ℂ)) /
      (Real.sqrt (n : ℝ) : ℂ)

/-- Imaginary part of Omega or its dual, source pp.11--12. -/
def fullPeriod (n : ℕ) (eta x : ℝ) (dual : Bool) : Matrix (Fin n) (Fin n) ℝ :=
  eta • periodKernel n n (fun k =>
    if dual then (hypergeometricRatio ((k : ℝ) / (n : ℝ)) x)⁻¹
    else hypergeometricRatio ((k : ℝ) / (n : ℝ)) x)

/-- The last eigenvalue is zero by definition; beta_1 is never evaluated and
multiplied by sin(pi). Source p.11, Eq.(52) and its zero-mode paragraph. -/
def periodEigenvalue (n : ℕ) (eta x : ℝ) (dual : Bool) (q : Fin n) : ℂ :=
  if q.val + 1 = n then 0 else
    ((2 * eta * Real.sin (Real.pi * ((q.val + 1 : ℕ) : ℝ) / (n : ℝ)) *
      (if dual then (hypergeometricRatio (((q.val + 1 : ℕ) : ℝ) / (n : ℝ)) x)⁻¹
       else hypergeometricRatio (((q.val + 1 : ℕ) : ℝ) / (n : ℝ)) x) : ℝ) : ℂ) * Complex.I

/-- The particular A=2 Uhat^dagger H Uhat in Appendix B, p.27.
This real cosine sum is its real value; H_kk=sin(pi k/n). -/
def specialA (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ :=
  periodKernel n (n - 1) (fun _ => 1)

/-- Jacobi theta_2(i t), p.13, Eq.(64), with t>0 in its uses. -/
def jacobiTheta2 (t : ℝ) : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * t * ((m : ℝ) + 1 / 2) ^ 2)

/-- Jacobi theta_3(i t), source p.13. -/
def jacobiTheta3 (t : ℝ) : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * t * (m : ℝ) ^ 2)

/-- Jacobi theta_4(i t), source p.13. Integer parity supplies (-1)^m. -/
def jacobiTheta4 (t : ℝ) : ℝ :=
  ∑' m : ℤ, (-1 : ℝ) ^ m * Real.exp (-Real.pi * t * (m : ℝ) ^ 2)

/-- The three-term bracket in (64); the overall factor 1/2 is not included. -/
def thetaTriple (t : ℝ) : ℝ :=
  jacobiTheta2 t ^ 2 * jacobiTheta2 (t / 3) ^ 2 +
  jacobiTheta3 t ^ 2 * jacobiTheta3 (t / 3) ^ 2 +
  jacobiTheta4 t ^ 2 * jacobiTheta4 (t / 3) ^ 2

/-- The integer nearest-neighbor form in Eq.(68), source pp.14--15.
The adjacent-pair sum contains exactly n-2 terms. -/
def windingEnergy (n : ℕ) (m : Fin (n - 1) → ℤ) : ℤ :=
  (∑ j, m j ^ 2) - ∑ j : Fin (n - 2),
    (∑ r : Fin (n - 1), if r.val = j.val then m r else 0) *
    (∑ s : Fin (n - 1), if s.val = j.val + 1 then m s else 0)

/-- Contiguous block of length ell, starting at a, with one constant sign;
source p.15, following Eq.(68). Admissible starts are Fin(n-ell). -/
def windingBlock (n ell a : ℕ) (positive : Bool) : Fin (n - 1) → ℤ :=
  fun j => if a ≤ j.val ∧ j.val < a + ell then (if positive then 1 else -1) else 0

/-- Fourier form on the left of Eq.(68), source p.14. -/
def windingFourier (n : ℕ) (m : Fin (n - 1) → ℤ) : ℝ :=
  2 / (n : ℝ) * ∑ k : Fin (n - 1),
    Real.sin (Real.pi * ((k.val + 1 : ℕ) : ℝ) / (n : ℝ)) ^ 2 *
      QAlgorithms.Papers.Independent.Information100.P37.quadratic (cosineMatrix n (k.val + 1) (n - 1)) (fun j => (m j : ℝ))

/-- The source's f_y=2 gamma_E+psi(y)+psi(1-y), p.14.
Gamma and its logarithmic derivative are the actual Mathlib functions. -/
def windingConstant (y : ℝ) : ℝ :=
  2 * Real.eulerMascheroniConstant + logDeriv Real.Gamma y + logDeriv Real.Gamma (1 - y)

/-- The coefficient P_n(alpha), source p.19, Eq.(83). -/
def replicaP (n : ℕ) (alpha : ℝ) : ℝ :=
  ∑ l : Fin (n - 1),
    let y : ℝ := ((l.val + 1 : ℕ) : ℝ) / (n : ℝ)
    y / (Real.sin (Real.pi * y)) ^ (2 * alpha)

/-- Leading winding coefficient in (72), with the full base 2n sin(...). -/
def windingCoefficient (n : ℕ) (alpha : ℝ) : ℝ :=
  ∑ l : Fin (n - 1), 2 * ((n : ℝ) - ((l.val + 1 : ℕ) : ℝ)) /
    (2 * (n : ℝ) * Real.sin (Real.pi * ((l.val + 1 : ℕ) : ℝ) / (n : ℝ))) ^ (2 * alpha)

/-- Entire combined integrand of Eq.(D.5), source p.30; none of its divergent
pieces is separately integrated. -/
def halfDIntegrand (n t : ℝ) : ℝ :=
  Real.exp (-t) / t *
    (Real.exp t * (Real.exp (t / 2) - 1 - n * (Real.exp (t / (2 * n)) - 1)) /
      ((Real.exp t - 1) * (Real.exp (t / (2 * n)) - 1)) + (1 - n) / 4)

/-- The explicit positive-real-n continuation at x=1/2, p.30, Eq.(D.5). -/
def halfDContinuation (n : ℝ) : ℝ :=
  (n - 1) / 2 * Real.log Real.pi - 2 * ∫ t in Ioi (0 : ℝ), halfDIntegrand n t

/-- Combined derivative integrand in (D.6), source p.30. -/
def halfDNegativeIntegrand (t : ℝ) : ℝ :=
  Real.exp (-t) / (2 * t) *
    ((Real.exp (3 * t / 2) * (2 * t - 5) + 5 * Real.exp t + Real.exp (t / 2) - 1) /
      ((Real.exp t - 1) * (Real.exp (t / 2) - 1)))

/-- Source p.31, Eq.(D.12), combined before integration. -/
def halfPIntegrand (n t : ℝ) : ℝ :=
  Real.cosh t / Real.sinh t * (Real.sinh (n * t) / Real.cosh (n * t)) - 1

/-- Explicit real-n function of (D.12), source p.31. -/
def halfPContinuation (n : ℝ) : ℝ :=
  n / Real.pi * ∫ t in Ioi (0 : ℝ), halfPIntegrand n t

/-- Derivative integrand of (D.13), source p.31. -/
def halfPDerivativeIntegrand (t : ℝ) : ℝ := t / (Real.sinh t * Real.cosh t)

/-- Polynomial continuation of (D.9), source p.31. -/
def unitPContinuation (n : ℝ) : ℝ := (n ^ 2 - 1) / 6

/-- Auxiliary alpha=0 endpoint continuation, source p.31; no eta=0 theory. -/
def zeroPContinuation (n : ℝ) : ℝ := (n - 1) / 2

example (y x : ℝ) : hypergeometricTerm y x 0 = 1 := by
  simp [hypergeometricTerm]

example (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ) : QAlgorithms.Papers.Independent.Information100.P37.quadratic G 0 = 0 := by
  simp [QAlgorithms.Papers.Independent.Information100.P37.quadratic]

example (alpha : ℝ) : replicaP 1 alpha = 0 := by
  simp [replicaP]

example : windingBlock 2 1 0 true = fun _ => 1 := by
  funext j
  have hj : j.val = 0 := by omega
  simp [windingBlock, hj]

example (eta x : ℝ) : periodEigenvalue 2 eta x false ⟨1, by decide⟩ = 0 := by
  simp [periodEigenvalue]

example (x : ℝ) : hypergeometricProduct 1 x = 1 := by
  simp [hypergeometricProduct]

example (t : ℝ) : halfDIntegrand 1 t = 0 := by
  simp [halfDIntegrand]

example : halfDContinuation 1 = 0 := by
  simp [halfDContinuation, halfDIntegrand]

example : negativeDerivativePolynomial 0 = 0 := by
  norm_num [negativeDerivativePolynomial]

end QAlgorithms.Papers.Independent.Intakenext100.P23


