-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
-- name    : QAlgorithms_Papers_Independent_Dependency50_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:08:48.990986+00:00
-- url     : https://prove2.me/theorems/22daec77-f742-465c-8a94-06372f308fd4
-- title:
--   Definitions for Universal recovery maps and approximate sufficiency of quantum relative entropy
-- statement:
--   The objects the formalized statements of *Universal recovery maps and approximate sufficiency of quantum relative entropy* (arXiv:1509.07127) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `alphaDensity`: Equation (28), PDF p.8: the left Hirschman probability density.
--   - `betaDensity`: Equation (28), PDF p.8: the right Hirschman probability density.
--   - `betaZero`: Equations (19),(30), PDF pp.5,8: parentheses include the added one.
--   - `extendedLog`: Natural logarithm extended by log(0)=-infinity; used only for nonnegative inputs. PDF pp.5,8. The negative-input branch is immaterial to all declarations below.
--   - `fidelityPenalty`: The penalty -2 log(f), PDF p.6, including +infinity at zero fidelity.
--   - `upperLogIntegral`: Signed extended integral, PDF p.8, Eq.(27). For its use below the positive part has finite integral, by boundedness of G and integrability of the two kernels. The negative part may have infinite integral; no Bochner default is used.
--   - `singularValues`: Singular values with multiplicity from the positive Gram matrix, PDF p.7, Eq.(22).
--   - `interpolationExponent`: Equation (26), PDF p.8; reciprocal infinity is zero and reciprocal zero is infinity.
--   - `IsSupported`: Support containment, Eq.(16), PDF p.5; kernels reverse inclusion.
--   - `relativeEntropy`: Finite-dimensional Umegaki relative entropy, Eq.(2), PDF p.2. References need not have trace one, so the finite value can be negative; support failure gives +infinity. The expression x log x is zero at zero. Used only on positive semidefinite arguments.
--   - `marginalAB`: AB marginal of a tripartite state ordered as A x (B x C), PDF p.16.
--   - `conditionalMutualInfo`: Conditional mutual information H(AB)+H(BC)-H(ABC)-H(B), PDF pp.3,16.
--   - `spectralFunction`: Finite spectral functional calculus with complex values, PDF p.2, Eq.(5), and p.5, Eq.(18). The zero branch on non-Hermitian matrices is unused.
--   - `imaginaryScalar`: The support-zero scalar imaginary power, PDF p.5, Eq.(18). In particular the zeroth power is the support projector, not the full identity.
--   - `imaginaryPower`: Imaginary powers act only on spectral support, PDF pp.2,5.
--   - `channelAdjoint`: Hilbert-Schmidt adjoint via matrix units, PDF p.2, footnote 2. For the linear maps used below this is the unique trace-dual adjoint.
--   - `petz`: Petz map with Moore-Penrose inverse square roots, Eq.(5), PDF p.2. This full-space extension kills the orthogonal complement of supp(N(sigma)).
--   - `rotatedPetz`: Rotated Petz map, Eq.(18), PDF p.5; the outer sign is negative.
--   - `recovery`: Explicit universal recovery map, Eq.(21), PDF p.6: beta_0 averages R^(t/2). Entrywise integration is weak integration in finite dimension. For positive sigma and a finite-dimensional channel (also the partial traces below), every entry is integrable: rotations are bounded, Petz is linear, and beta_0 is a probability density. No state is an argument selecting this map.
--   - `cqOperator`: The block-diagonal cq operator sum_x nu(x)|x><x| tensor X_x, PDF pp.17-18, Eqs.(103),(109); the blocks need not have trace one.
-- source:
--   Universal recovery maps and approximate sufficiency of quantum relative entropy, arXiv:1509.07127v3, https://arxiv.org/abs/1509.07127v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P21

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the named interfaces from the pinned accepted paper library.
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- Equation (28), PDF p.8: the left Hirschman probability density. -/
def alphaDensity (theta t : ℝ) : ℝ :=
  Real.sin (Real.pi * theta) /
    (2 * (1 - theta) * (Real.cosh (Real.pi * t) - Real.cos (Real.pi * theta)))

/-- Equation (28), PDF p.8: the right Hirschman probability density. -/
def betaDensity (theta t : ℝ) : ℝ :=
  Real.sin (Real.pi * theta) /
    (2 * theta * (Real.cosh (Real.pi * t) + Real.cos (Real.pi * theta)))

/-- Equations (19),(30), PDF pp.5,8: parentheses include the added one. -/
def betaZero (t : ℝ) : ℝ := Real.pi / (2 * (Real.cosh (Real.pi * t) + 1))

/-- Natural logarithm extended by log(0)=-infinity; used only for nonnegative inputs.
PDF pp.5,8. The negative-input branch is immaterial to all declarations below. -/
def extendedLog (x : ℝ) : EReal := if x ≤ 0 then ⊥ else (Real.log x : EReal)

/-- The penalty -2 log(f), PDF p.6, including +infinity at zero fidelity. -/
def fidelityPenalty (f : ℝ) : EReal := -(2 * extendedLog f)

/-- Signed extended integral, PDF p.8, Eq.(27). For its use below the positive part
has finite integral, by boundedness of G and integrability of the two kernels.
The negative part may have infinite integral; no Bochner default is used. -/
def upperLogIntegral (f : ℝ → EReal) : EReal :=
  ((∫⁻ t, (f t).toENNReal) : EReal) - ((∫⁻ t, (-f t).toENNReal) : EReal)

/-- Singular values with multiplicity from the positive Gram matrix, PDF p.7, Eq.(22). -/
def singularValues {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) :
    Fin (Fintype.card I) → ℝ :=
  fun j => Real.sqrt (ascEigenvalues (Xᴴ * X) j)

/-- Equation (26), PDF p.8; reciprocal infinity is zero and reciprocal zero is infinity. -/
def interpolationExponent (theta : ℝ) (p0 p1 : ℝ≥0∞) : ℝ≥0∞ :=
  (ENNReal.ofReal ((1 - theta) * (p0⁻¹).toReal + theta * (p1⁻¹).toReal))⁻¹

/-- Support containment, Eq.(16), PDF p.5; kernels reverse inclusion. -/
def IsSupported {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : Prop :=
  LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin

/-- Finite-dimensional Umegaki relative entropy, Eq.(2), PDF p.2. References need
not have trace one, so the finite value can be negative; support failure gives +infinity.
The expression x log x is zero at zero. Used only on positive semidefinite arguments. -/
def relativeEntropy {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Mat I) : EReal :=
  if IsSupported rho sigma then
    ((cfc (fun x : ℝ => x * Real.log x) rho - rho * cfc Real.log sigma).trace.re : EReal)
  else ⊤

/-- AB marginal of a tripartite state ordered as A x (B x C), PDF p.16. -/
def marginalAB {I J K : Type*} [Fintype K] (rho : Mat (I × (J × K))) : Mat (I × J) :=
  fun i j => ∑ k, rho (i.1, (i.2, k)) (j.1, (j.2, k))

/-- Conditional mutual information H(AB)+H(BC)-H(ABC)-H(B), PDF pp.3,16. -/
def conditionalMutualInfo {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] (rho : Mat (I × (J × K))) : ℝ :=
  entropy (marginalAB rho) + entropy (traceLeft rho) - entropy rho -
    entropy (traceRight (traceLeft rho))

/-- Finite spectral functional calculus with complex values, PDF p.2, Eq.(5),
and p.5, Eq.(18). The zero branch on non-Hermitian matrices is unused. -/
def spectralFunction {I : Type*} [Fintype I] [DecidableEq I]
    (f : ℝ → ℂ) (X : Mat I) : Mat I :=
  if h : X.IsHermitian then
    let U : Mat I := h.eigenvectorUnitary
    U * Matrix.diagonal (fun j => f (h.eigenvalues j)) * Uᴴ
  else 0

/-- The support-zero scalar imaginary power, PDF p.5, Eq.(18).
In particular the zeroth power is the support projector, not the full identity. -/
def imaginaryScalar (t x : ℝ) : ℂ :=
  if x = 0 then 0 else Complex.exp ((t * Real.log x : ℝ) * Complex.I)

/-- Imaginary powers act only on spectral support, PDF pp.2,5. -/
def imaginaryPower {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) (t : ℝ) : Mat I :=
  spectralFunction (imaginaryScalar t) X

/-- Hilbert-Schmidt adjoint via matrix units, PDF p.2, footnote 2.
For the linear maps used below this is the unique trace-dual adjoint. -/
def channelAdjoint {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (N : Superop I J) (X : Mat J) : Mat I :=
  fun i j => ∑ k, ∑ l, conj (N (Matrix.single i j 1) k l) * X k l

/-- Petz map with Moore-Penrose inverse square roots, Eq.(5), PDF p.2.
This full-space extension kills the orthogonal complement of supp(N(sigma)). -/
def petz {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (sigma : Mat I) (N : Superop I J) (X : Mat J) : Mat I :=
  let S := cfc Real.sqrt sigma
  let T := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (N sigma)
  S * channelAdjoint N (T * X * T) * S

/-- Rotated Petz map, Eq.(18), PDF p.5; the outer sign is negative. -/
def rotatedPetz {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (sigma : Mat I) (N : Superop I J) (t : ℝ) (X : Mat J) : Mat I :=
  imaginaryPower sigma (-t) *
    petz sigma N (imaginaryPower (N sigma) t * X * imaginaryPower (N sigma) (-t)) *
    imaginaryPower sigma t

/-- Explicit universal recovery map, Eq.(21), PDF p.6: beta_0 averages R^(t/2).
Entrywise integration is weak integration in finite dimension. For positive sigma
and a finite-dimensional channel (also the partial traces below), every entry is
integrable: rotations are bounded, Petz is linear, and beta_0 is a probability density.
No state is an argument selecting this map. -/
def recovery {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (sigma : Mat I) (N : Superop I J) : Superop J I :=
  fun X i j => ∫ t : ℝ, (betaZero t : ℂ) * rotatedPetz sigma N (t / 2) X i j

/-- The block-diagonal cq operator sum_x nu(x)|x><x| tensor X_x,
PDF pp.17-18, Eqs.(103),(109); the blocks need not have trace one. -/
def cqOperator {X I : Type*} [DecidableEq X] (nu : X → ℝ) (blocks : X → Mat I) : Mat (X × I) :=
  fun a b => if a.1 = b.1 then (nu a.1 : ℂ) * blocks a.1 a.2 b.2 else 0

/-! Sanity checks on the new interfaces; theorem proofs are intentionally omitted. -/

example : betaZero 0 = Real.pi / 4 := by
  norm_num [betaZero, Real.cosh_zero]

example : alphaDensity (1/2) 0 = 1 ∧ betaDensity (1/2) 0 = 1 := by
  norm_num [alphaDensity, betaDensity, Real.sin_pi_div_two, Real.cos_pi_div_two,
    show Real.pi * (1 / 2) = Real.pi / 2 by ring]

example : extendedLog 0 = ⊥ ∧ extendedLog 1 = 0 := by
  simp [extendedLog]

example (theta : ℝ) : interpolationExponent theta ⊤ ⊤ = ⊤ := by
  simp [interpolationExponent]

example (t : ℝ) : imaginaryScalar t 0 = 0 ∧ imaginaryScalar t 1 = 1 := by
  simp [imaginaryScalar]

example {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) :
    spectralFunction (fun _ => 0) X = 0 := by
  unfold spectralFunction
  split <;> simp

example {I : Type*} [Fintype I] [DecidableEq I] (rho : Mat I)
    (h : ¬ IsSupported rho 0) : relativeEntropy rho 0 = ⊤ := by
  simp [relativeEntropy, h]

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] (X : Mat J) :
    channelAdjoint (fun _ : Mat I => (0 : Mat J)) X = 0 := by
  ext i j
  simp [channelAdjoint]

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) (X : Mat J) : petz 0 N X = 0 := by
  simp [petz, cfc_zero]

example {I : Type*} (X : Mat I) :
    (fun i j => cqOperator (fun _ : Unit => (1 : ℝ)) (fun _ => X) ((), i) ((), j)) = X := by
  funext i j
  simp [cqOperator]

example : upperLogIntegral (fun _ => 0) = 0 := by
  simp [upperLogIntegral, EReal.toENNReal_zero]

example {I : Type*} [Fintype I] [DecidableEq I] : entropy (0 : Mat I) = 0 := by
  simp [entropy, cfc_zero]

example {I : Type*} (X : Mat I) :
    traceRight (fun a b : I × Unit => X a.1 b.1) = X := by
  funext i j
  simp [traceRight]

end QAlgorithms.Papers.Independent.Dependency50.P21


