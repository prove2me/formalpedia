-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41
-- name    : QAlgorithms_Papers_Independent_Gap48_P41
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:25:57.449095+00:00
-- url     : https://prove2.me/theorems/34673be8-f705-4187-b161-7ebaea2b01aa
-- title:
--   Definitions for Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing
-- statement:
--   The objects the formalized statements of *Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing* (arXiv:quant-ph/9906090) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `blockDifference`: PDF p.3, (4): the specific comparison operator on n identical copies.
--   - `nonnegativeProjection`: PDF p.3: projection onto NONNEGATIVE eigenvalues, including the whole kernel. Only Hermitian arguments are used; at B=0 the value is I.
--   - `petzPsi`: PDF p.3, (8): Petz power-product logarithmic moment, distinct from the sandwiched moment in Dependency50.P28. On nested-support density pairs the trace is strictly positive for all real s, so Real.log never sees zero.
--   - `petzPhi`: PDF p.3, (7): the accepted compact Legendre transform specialized to [0,1]. On the stated density/support domain its supremum is a finite attained maximum.
--   - `petzG`: PDF pp.5--6, (15): the compact perspective objective, in nats.
--   - `petzExponent`: PDF p.5, (15): the paper's bound, with orders restricted to s in [0,1]. Nonempty compactness and continuity on the stated domain ensure finiteness; Theorem 3 explicitly supplies maximum attainment.
--   - `crossing`: PDF pp.5--6: the crossing parameter is CONSTRUCTED from rho, sigma, r, not supplied as a variable satisfying the desired crossing equation.
--   - `betaValues`: PDF p.2: all feasible type-II values, over arbitrary effects.
--   - `betaStar`: PDF p.2: optimal type-II error. For density inputs and eps in [0,1], the feasible set contains I, is compact, and has values in [0,1]. The Stein theorem asserts attainment explicitly. Off-domain empty/unbounded real infima have Lean's default value zero and are not used by any statement.
--   - `quantumValues`: PDF p.8, (22): extended objective values over ALL feasible density matrices. Feasibility makes the subtracted divergence finite. The first may be +infinity.
--   - `quantumMinimum`: PDF p.8, (22): extended infimum; minimum attainment is part of the result. For r>D, rho itself is a finite feasible candidate; no trial state is discarded merely for having infinite divergence to rho.
--   - `classicalPsi`: PDF pp.7--8: zero-preserving classical power-product log moment. On valid laws with nested supports it is a finite real analytic function.
--   - `tilt`: PDF p.8, Appendix: the constructed exponential tilt. Zero p coordinates stay zero; no full-support hypothesis is imposed. Validity is concluded below.
--   - `tiltedLogLikelihood`: PDF p.8, Appendix: eta(s), the tilted log-likelihood expectation. Zero p mass contributes zero; support inclusion guards positive p coordinates.
--   - `classicalG`: PDF p.7, (21): the classical perspective expression, used only for s>=0.
--   - `classicalValues`: PDF p.7, (20): ALL feasible laws, retaining infinite KL values to p. The KL value to q is finite by the real-rate feasibility constraint.
--   - `classicalMinimum`: PDF p.7, (20): extended variational infimum; theorems assert attainment.
--   - `classicalDualValues`: PDF p.7, (21): values on the noncompact parameter domain. An extended set avoids any bounded-real-supremum default. Attainment is asserted only in the explicit finite-positive-tilt regime from the Appendix.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, https://arxiv.org/abs/quant-ph/9906090v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-! Ogawa--Nagaoka, arXiv:quant-ph/9906090v1. Finite-dimensional states,
natural logarithms, arbitrary effects, and support-restricted powers.
The printed zero-error Stein endpoint and strict-curvature calculation are
corrected explicitly below. The ambiguous combined log-Euclidean assertion
on PDF p.8 is deferred in HARD.md. Compilation is pending batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P41

open scoped Matrix ComplexOrder BigOperators
open Filter QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)
open QAlgorithms.Papers.Independent.Dependency50.P28
  (tr SupportLE relativeEntropy scalarPower classicalD typeI accept TestSequence
    scaled logNonnegativeExtended)
open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF p.3, (4): the specific comparison operator on n identical copies. -/
def blockDifference (rho sigma : Mat I) (n : ℕ) (lambda : ℝ) : Mat (Fin n → I) :=
  copies n rho - (Real.exp ((n : ℝ) * lambda) : ℂ) • copies n sigma

/-- PDF p.3: projection onto NONNEGATIVE eigenvalues, including the whole kernel.
Only Hermitian arguments are used; at B=0 the value is I. -/
def nonnegativeProjection (B : Mat I) : Mat I := 1 - positiveProjection (-B)

/-- PDF p.3, (8): Petz power-product logarithmic moment, distinct from the
sandwiched moment in Dependency50.P28. On nested-support density pairs the
trace is strictly positive for all real s, so Real.log never sees zero. -/
def petzPsi (rho sigma : Mat I) (s : ℝ) : ℝ :=
  Real.log (tr (supportPower rho (1 + s) * supportPower sigma (-s)))

/-- PDF p.3, (7): the accepted compact Legendre transform specialized to [0,1].
On the stated density/support domain its supremum is a finite attained maximum. -/
abbrev petzPhi (rho sigma : Mat I) (lambda : ℝ) : ℝ :=
  legendre 0 1 (petzPsi rho sigma) lambda

/-- PDF pp.5--6, (15): the compact perspective objective, in nats. -/
def petzG (rho sigma : Mat I) (r s : ℝ) : ℝ :=
  s / (1 + s) * r - petzPsi rho sigma s / (1 + s)

/-- PDF p.5, (15): the paper's bound, with orders restricted to s in [0,1].
Nonempty compactness and continuity on the stated domain ensure finiteness;
Theorem 3 explicitly supplies maximum attainment. -/
def petzExponent (rho sigma : Mat I) (r : ℝ) : ℝ :=
  sSup (petzG rho sigma r '' Set.Icc 0 1)

/-- PDF pp.5--6: the crossing parameter is CONSTRUCTED from rho, sigma, r,
not supplied as a variable satisfying the desired crossing equation. -/
def crossing (rho sigma : Mat I) (r : ℝ) : ℝ := r - petzExponent rho sigma r

/-- PDF p.2: all feasible type-II values, over arbitrary effects. -/
def betaValues (rho sigma : Mat I) (n : ℕ) (eps : ℝ) : Set ℝ :=
  {v | ∃ A : Mat (Fin n → I), IsEffect A ∧ typeI rho n A ≤ eps ∧
    v = accept sigma n A}

/-- PDF p.2: optimal type-II error. For density inputs and eps in [0,1], the
feasible set contains I, is compact, and has values in [0,1]. The Stein theorem
asserts attainment explicitly. Off-domain empty/unbounded real infima have
Lean's default value zero and are not used by any statement. -/
def betaStar (rho sigma : Mat I) (n : ℕ) (eps : ℝ) : ℝ :=
  sInf (betaValues rho sigma n eps)

/-- PDF p.8, (22): extended objective values over ALL feasible density matrices.
Feasibility makes the subtracted divergence finite. The first may be +infinity. -/
def quantumValues (rho sigma : Mat I) (r : ℝ) : Set EReal :=
  {v | ∃ theta : Mat I, IsDensityMatrix theta ∧ relativeEntropy theta sigma ≤ (r : EReal) ∧
    v = relativeEntropy theta rho + (r : EReal) - relativeEntropy theta sigma}

/-- PDF p.8, (22): extended infimum; minimum attainment is part of the result.
For r>D, rho itself is a finite feasible candidate; no trial state is discarded
merely for having infinite divergence to rho. -/
def quantumMinimum (rho sigma : Mat I) (r : ℝ) : EReal :=
  sInf (quantumValues rho sigma r)

/-- PDF p.3 tie check: equal hypotheses at lambda=0 have comparison operator zero. -/
example (rho : Mat I) (n : ℕ) : blockDifference rho rho n 0 = 0 := by
  simp [blockDifference]

/-- PDF p.3 tie check: the constructed projector includes the zero eigenspace. -/
example : nonnegativeProjection (0 : Mat I) = 1 := by
  simp [nonnegativeProjection,
    QAlgorithms.Papers.Independent.Information100.P07.positiveProjection,
    QAlgorithms.Papers.Independent.Information100.P07.positivePart, cfc_zero,
    QAlgorithms.Papers.Independent.Information100.P07.support,
    QAlgorithms.Papers.Independent.Information100.P07.projection,
    QAlgorithms.Papers.Independent.Information100.P07.operatorRange,
    Submodule.starProjection_bot]

/-- PDF p.3: the one-dimensional identical state has a zero moment at every order. -/
example (s : ℝ) : petzPsi (1 : Mat (Fin 1)) 1 s = 0 := by
  simp [petzPsi, supportPower, tr, cfc_one]

/-- PDF p.5: the compact perspective at its left endpoint is zero in the one-state case. -/
example (r : ℝ) : petzG (1 : Mat (Fin 1)) 1 r 0 = 0 := by
  simp [petzG, petzPsi, supportPower, tr, cfc_one]

/-- PDF p.8: the null density is a feasible variational candidate when its divergence fits. -/
example (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (r : ℝ)
    (hr : relativeEntropy rho sigma ≤ (r : EReal)) :
    relativeEntropy rho rho + (r : EReal) - relativeEntropy rho sigma ∈
      quantumValues rho sigma r := by
  exact ⟨rho, hrho, hr, rfl⟩

/-- PDF p.2: the zero effect has zero success probability, with extended log -infinity. -/
example (rho : Mat I) (n : ℕ) : logNonnegativeExtended (accept rho n 0) = ⊥ := by
  simp [accept, tr, logNonnegativeExtended]

variable {X : Type} [Fintype X]

/-- PDF pp.7--8: zero-preserving classical power-product log moment.
On valid laws with nested supports it is a finite real analytic function. -/
def classicalPsi (p q : X → ℝ) (s : ℝ) : ℝ :=
  Real.log (∑ x, scalarPower (p x) (1 + s) * scalarPower (q x) (-s))

/-- PDF p.8, Appendix: the constructed exponential tilt. Zero p coordinates
stay zero; no full-support hypothesis is imposed. Validity is concluded below. -/
def tilt (p q : X → ℝ) (s : ℝ) : X → ℝ :=
  fun x => Real.exp (-classicalPsi p q s) *
    scalarPower (p x) (1 + s) * scalarPower (q x) (-s)

/-- PDF p.8, Appendix: eta(s), the tilted log-likelihood expectation.
Zero p mass contributes zero; support inclusion guards positive p coordinates. -/
def tiltedLogLikelihood (p q : X → ℝ) (s : ℝ) : ℝ :=
  ∑ x, if 0 < p x then tilt p q s x * Real.log (p x / q x) else 0

/-- PDF p.7, (21): the classical perspective expression, used only for s>=0. -/
def classicalG (p q : X → ℝ) (r s : ℝ) : ℝ :=
  s / (1 + s) * r - classicalPsi p q s / (1 + s)

/-- PDF p.7, (20): ALL feasible laws, retaining infinite KL values to p.
The KL value to q is finite by the real-rate feasibility constraint. -/
def classicalValues (p q : X → ℝ) (r : ℝ) : Set EReal :=
  {v | ∃ phat : X → ℝ, IsLaw phat ∧ classicalD (.finite 1 (by norm_num)) phat q ≤ (r : EReal) ∧
    v = classicalD (.finite 1 (by norm_num)) phat p + (r : EReal) - classicalD (.finite 1 (by norm_num)) phat q}

/-- PDF p.7, (20): extended variational infimum; theorems assert attainment. -/
def classicalMinimum (p q : X → ℝ) (r : ℝ) : EReal :=
  sInf (classicalValues p q r)

/-- PDF p.7, (21): values on the noncompact parameter domain.
An extended set avoids any bounded-real-supremum default. Attainment is asserted
only in the explicit finite-positive-tilt regime from the Appendix. -/
def classicalDualValues (p q : X → ℝ) (r : ℝ) : Set EReal :=
  {v | ∃ s : ℝ, 0 ≤ s ∧ v = (classicalG p q r s : EReal)}

/-- PDF p.7: one-point probability law is allowed. -/
example : IsLaw (fun _ : Fin 1 => (1 : ℝ)) := by simp [IsLaw]

/-- PDF p.8: the one-point moment and its tilted law are normalized at every order. -/
example (s : ℝ) : classicalPsi (fun _ : Fin 1 => 1) (fun _ => 1) s = 0 ∧
    tilt (fun _ : Fin 1 => 1) (fun _ => 1) s = (fun _ => 1) := by
  constructor
  · simp [classicalPsi, scalarPower]
  · funext x
    simp [tilt, classicalPsi, scalarPower]

/-- PDF pp.7--9: equal one-point laws have zero KL divergence. -/
example : classicalD (.finite 1 (by norm_num)) (fun _ : Fin 1 => 1) (fun _ => 1) = 0 := by
  simp [classicalD]

/-- PDF p.8: the one-point log-likelihood expectation is zero. -/
example (s : ℝ) : tiltedLogLikelihood (fun _ : Fin 1 => 1) (fun _ => 1) s = 0 := by
  simp [tiltedLogLikelihood]

/-- PDF p.7: the original law is a feasible variational candidate when its divergence fits. -/
example (p q : X → ℝ) (hp : IsLaw p) (r : ℝ)
    (hr : classicalD (.finite 1 (by norm_num)) p q ≤ (r : EReal)) :
    classicalD (.finite 1 (by norm_num)) p p + (r : EReal) - classicalD (.finite 1 (by norm_num)) p q ∈ classicalValues p q r := by
  exact ⟨p, hp, hr, rfl⟩

end QAlgorithms.Papers.Independent.Gap48.P41


