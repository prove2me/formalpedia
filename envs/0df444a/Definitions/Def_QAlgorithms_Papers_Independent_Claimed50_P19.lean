-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
-- name    : QAlgorithms_Papers_Independent_Claimed50_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:16:21.223256+00:00
-- url     : https://prove2.me/theorems/7de3696f-1b38-4fc0-b7ba-cc6412253195
-- title:
--   Definitions for Quantum versus classical correlations in Gaussian states
-- statement:
--   The objects that formalizations building on *Quantum versus classical correlations in Gaussian states* (arXiv:1003.4979) are stated in. Every numbered result of this paper itself was deferred, so it has no mission of its own; its definitions are published for the papers that import them.
--
--   - `Cov`: PDF p.2: interleaved real phase-space matrices, distinct from density operators.
--   - `FockIndex`: PDF pp.1–2: full oscillator basis, with no photon-number cutoff.
--   - `DensityKernel`: PDF pp.1–2: operator coefficients on the completed multimode Fock space. Density normalization and trace class are supplied by the accepted IsDensity.
--   - `PhysicalCovariance`: PDF p.2: finite positive covariance in the vacuum-I uncertainty convention. Accepted P08 uses hbar=2 with half anticommutators; the numerical matrix condition is identical to this paper's hbar=1 with full anticommutators.
--   - `productWeyl`: PDF p.2: independent-mode Weyl displacement coefficients on the full Fock space. Only finite products of the accepted one-mode displacement coefficients occur.
--   - `weylArgument`: PDF p.2: D(z(v))=exp(i sum_j(v_x x_j+v_p p_j)), since z_j=(-v_p+i v_x)/sqrt(2) when [x,p]=i.
--   - `multimodeWeylTrace`: PDF p.2: the trace pairing Tr(rho W(v)); the row sum precedes the trace sum. Use only on the explicitly summable domain in GaussianWithCovariance.
--   - `CharacteristicSummable`: PDF p.2: convergence of the actual trace pairing, excluding default-zero tsums.
--   - `covarianceCharacteristicValue`: PDF pp.1–2: first moments m and full anticommutator covariance V give exp(-v^T V v/4+i m^T v). In particular V=I gives the vacuum characteristic.
--   - `FiniteMeanEnergy`: PDF p.5, Appendix A: finite actual mean photon number; adding the finite zero-point energy does not change finiteness. Applied only to positive densities.
--   - `GaussianWithCovariance`: PDF pp.1–2,5: a specified covariance of THIS normalized oscillator density, with arbitrary first moments, finite energy and genuine convergent Weyl traces. This is a predicate with a complete body, not a covariance tuple called a state. Existence and covariance/entropy/measurement identifications remain unstated.
--   - `vacuumKernel`: PDF p.2: actual zero-occupation vacuum coefficients, not a finite truncation.
--   - `modeCovarianceBlock`: PDF p.2: the source's one-mode matrix block, also for inter-party correlations.
--   - `standardFormCovariance`: PDF p.2, Eq.(2): a standard-form phase-space matrix, without a state claim.
--   - `xlogx`: PDF pp.1–2: the scalar entropy summand, with explicit 0 log 0=0.
--   - `f`: PDF p.2: scalar f(x), used at x≥1. This is NOT an independently defined von Neumann entropy functional on arbitrary oscillator density operators.
--   - `phaseSpaceRotation`: PDF p.2: the printed rotation has positive upper-right sine.
--   - `squeezedSeedCovariance`: PDF p.2: pure-seed covariance expression, to be used only for lambda>0. It is not a density operator or an ideal homodyne seed at lambda=0.
--   - `schurExpression`: PDF p.2, cited background [16]: algebraic Schur expression. Identification with the covariance of an actual measurement-conditioned density is deferred. For physical input and seed covariances beta+G is positive definite.
--   - `determinantExpression`: PDF p.2: the displayed scalar expression, without asserting the deferred conditional-density identity. Positive lambda and physical b prevent zero denominators.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Papers.Independent.Claimed50.P19

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

/-!
Adesso–Datta, arXiv:1003.4979v2: definition groundwork only.
Every planned source-result theorem is explicitly deferred in HARD.md/GAPS.json.
A covariance-only prototype was removed: it did not establish the plan's actual
oscillator-density, conditional-state and independent entropy identifications.
No matrix surrogate for operational discord, separability or EoF is retained.
The definitions below connect specified finite-mode covariances to actual
normalized trace-class densities through their product-Weyl characteristics.
They do not assert existence, Gaussian entropy identities, POVM normalization,
conditional-state identities, or any of the paper's optimization results.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P19

/-! The five descriptive names below distinguish genuinely different objects from
same-short-name accepted declarations. P39.characteristic takes a one-mode bounded
operator; P10.gaussianCharacteristic is an operator-valued observable;
P32.standard is channel robustness; the accepted block declarations are channel
or complex basis blocks; EquatorialQSP.rotation is a two-angle complex qubit gate.
None is an interchangeable definition of this paper's multimode coefficient
trace, scalar state characteristic, real covariance block, standard-form CM or
one-angle real rotation. Existing accepted imports remain unchanged.
-/

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex quantumCovariance)

/-- PDF p.2: interleaved real phase-space matrices, distinct from density operators. -/
abbrev Cov (n : ℕ) := Matrix (QuadratureIndex n) (QuadratureIndex n) ℝ

/-- PDF pp.1–2: full oscillator basis, with no photon-number cutoff. -/
abbrev FockIndex (n : ℕ) := Fin n → ℕ

/-- PDF pp.1–2: operator coefficients on the completed multimode Fock space.
Density normalization and trace class are supplied by the accepted IsDensity. -/
abbrev DensityKernel (n : ℕ) := Matrix (FockIndex n) (FockIndex n) ℂ

/-- PDF p.2: finite positive covariance in the vacuum-I uncertainty convention.
Accepted P08 uses hbar=2 with half anticommutators; the numerical matrix condition
is identical to this paper's hbar=1 with full anticommutators. -/
def PhysicalCovariance {n : ℕ} (V : Cov n) : Prop :=
  V.PosDef ∧ quantumCovariance V

/-- PDF p.2: independent-mode Weyl displacement coefficients on the full Fock space.
Only finite products of the accepted one-mode displacement coefficients occur. -/
def productWeyl {n : ℕ} (z : Fin n → ℂ) : DensityKernel n :=
  fun i j => ∏ k, displacementMatrix (z k) (i k) (j k)

/-- PDF p.2: D(z(v))=exp(i sum_j(v_x x_j+v_p p_j)), since
z_j=(-v_p+i v_x)/sqrt(2) when [x,p]=i. -/
def weylArgument {n : ℕ} (v : QuadratureIndex n → ℝ) : Fin n → ℂ :=
  fun j => (-(v (j, 1) : ℂ) + Complex.I * (v (j, 0) : ℂ)) /
    (Real.sqrt 2 : ℂ)

/-- PDF p.2: the trace pairing Tr(rho W(v)); the row sum precedes the trace sum.
Use only on the explicitly summable domain in GaussianWithCovariance. -/
def multimodeWeylTrace {n : ℕ} (rho : DensityKernel n)
    (v : QuadratureIndex n → ℝ) : ℂ :=
  ∑' i, ∑' j, rho i j * productWeyl (weylArgument v) j i

/-- PDF p.2: convergence of the actual trace pairing, excluding default-zero tsums. -/
def CharacteristicSummable {n : ℕ} (rho : DensityKernel n)
    (v : QuadratureIndex n → ℝ) : Prop :=
  (∀ i, Summable (fun j => rho i j * productWeyl (weylArgument v) j i)) ∧
  Summable (fun i => ∑' j, rho i j * productWeyl (weylArgument v) j i)

/-- PDF pp.1–2: first moments m and full anticommutator covariance V give
exp(-v^T V v/4+i m^T v). In particular V=I gives the vacuum characteristic. -/
def covarianceCharacteristicValue {n : ℕ} (V : Cov n)
    (m v : QuadratureIndex n → ℝ) : ℂ :=
  Complex.exp
    (((-(∑ i, ∑ j, v i * V i j * v j) / 4 : ℝ) : ℂ) +
      Complex.I * ((∑ i, m i * v i : ℝ) : ℂ))

/-- PDF p.5, Appendix A: finite actual mean photon number; adding the finite
zero-point energy does not change finiteness. Applied only to positive densities. -/
def FiniteMeanEnergy {n : ℕ} (rho : DensityKernel n) : Prop :=
  Summable (fun i : FockIndex n => (∑ j, (i j : ℝ)) * (rho i i).re)

/-- PDF pp.1–2,5: a specified covariance of THIS normalized oscillator density,
with arbitrary first moments, finite energy and genuine convergent Weyl traces.
This is a predicate with a complete body, not a covariance tuple called a state.
Existence and covariance/entropy/measurement identifications remain unstated. -/
def GaussianWithCovariance {n : ℕ} (rho : DensityKernel n) (V : Cov n) : Prop :=
  IsDensity rho ∧ PhysicalCovariance V ∧ FiniteMeanEnergy rho ∧
    ∃ m : QuadratureIndex n → ℝ, ∀ v,
      CharacteristicSummable rho v ∧ multimodeWeylTrace rho v = covarianceCharacteristicValue V m v

/-- PDF p.2: actual zero-occupation vacuum coefficients, not a finite truncation. -/
def vacuumKernel (n : ℕ) : DensityKernel n :=
  fun i j => if i = (fun _ => 0) ∧ j = (fun _ => 0) then 1 else 0

/-- PDF p.2: the source's one-mode matrix block, also for inter-party correlations. -/
def modeCovarianceBlock {n : ℕ} (V : Cov n) (i j : Fin n) : Matrix (Fin 2) (Fin 2) ℝ :=
  V.submatrix (fun k => (i, k)) (fun k => (j, k))

/-- PDF p.2, Eq.(2): a standard-form phase-space matrix, without a state claim. -/
def standardFormCovariance (a b c d : ℝ) : Cov 2 :=
  fun i j =>
    if i.1 = j.1 then (if i.2 = j.2 then (if i.1 = 0 then a else b) else 0)
    else if i.2 = j.2 then (if i.2 = 0 then c else d) else 0

/-- PDF pp.1–2: the scalar entropy summand, with explicit 0 log 0=0. -/
def xlogx (x : ℝ) : ℝ := if x = 0 then 0 else x * Real.log x

/-- PDF p.2: scalar f(x), used at x≥1. This is NOT an independently defined
von Neumann entropy functional on arbitrary oscillator density operators. -/
def f (x : ℝ) : ℝ := xlogx ((x + 1) / 2) - xlogx ((x - 1) / 2)

/-- PDF p.2: the printed rotation has positive upper-right sine. -/
def phaseSpaceRotation (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos theta, Real.sin theta; -Real.sin theta, Real.cos theta]

/-- PDF p.2: pure-seed covariance expression, to be used only for lambda>0.
It is not a density operator or an ideal homodyne seed at lambda=0. -/
def squeezedSeedCovariance (lambda theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  phaseSpaceRotation theta * Matrix.diagonal ![lambda, 1 / lambda] * (phaseSpaceRotation theta).transpose

/-- PDF p.2, cited background [16]: algebraic Schur expression. Identification
with the covariance of an actual measurement-conditioned density is deferred.
For physical input and seed covariances beta+G is positive definite. -/
def schurExpression (V : Cov 2) (G : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  modeCovarianceBlock V 0 0 - modeCovarianceBlock V 0 1 *
    (modeCovarianceBlock V 1 1 + G)⁻¹ * (modeCovarianceBlock V 0 1).transpose

/-- PDF p.2: the displayed scalar expression, without asserting the deferred
conditional-density identity. Positive lambda and physical b prevent zero denominators. -/
def determinantExpression (a b c d lambda theta : ℝ) : ℝ :=
  (2 * a ^ 2 * (b + lambda) * (1 + b * lambda) -
    a * (c ^ 2 + d ^ 2) * (2 * b * lambda + lambda ^ 2 + 1) +
    a * (c ^ 2 - d ^ 2) * (lambda ^ 2 - 1) * Real.cos (2 * theta) +
    2 * c ^ 2 * d ^ 2 * lambda) / (2 * (b + lambda) * (1 + b * lambda))

/-! Sanity tests for the complete definitions; none claims a deferred source result. -/

example {n : ℕ} (V : Cov n) (m : QuadratureIndex n → ℝ) :
    covarianceCharacteristicValue V m 0 = 1 := by simp [covarianceCharacteristicValue]

example {n : ℕ} (z : ℂ) (zs : Fin n → ℂ) (i j : ℕ)
    (tailI tailJ : FockIndex n) :
    productWeyl (Fin.cons z zs) (Fin.cons i tailI) (Fin.cons j tailJ) =
      displacementMatrix z i j * productWeyl zs tailI tailJ := by
  simp [productWeyl, Fin.prod_univ_succ]

example (n : ℕ) : vacuumKernel n (fun _ => 0) (fun _ => 0) = 1 := by
  simp [vacuumKernel]

example (z : ℂ) : productWeyl (fun _ : Fin 1 => z)
    (fun _ => 0) (fun _ => 0) = (Real.exp (-Complex.normSq z / 2) : ℂ) := by
  simp [productWeyl, Fin.prod_univ_succ, displacementMatrix]

example : f 1 = 0 := by norm_num [f, xlogx]

example (a b c d : ℝ) : standardFormCovariance a b c d ((0 : Fin 2), (0 : Fin 2)) (1, 0) = c := by
  norm_num [standardFormCovariance]

example (a b c d : ℝ) : standardFormCovariance a b c d ((0 : Fin 2), (1 : Fin 2)) (1, 1) = d := by
  norm_num [standardFormCovariance]

example : phaseSpaceRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [phaseSpaceRotation]

end QAlgorithms.Papers.Independent.Claimed50.P19


