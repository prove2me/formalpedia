-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P04
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P04
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T03:50:44.765765+00:00
-- url     : https://prove2.me/theorems/1e79dee0-4008-4b8b-aa90-2573c0bca37d
-- title:
--   Definitions for The Converse Part of The Theorem for Quantum Hoeffding Bound
-- statement:
--   The objects the formalized statements of *The Converse Part of The Theorem for Quantum Hoeffding Bound* (arXiv:quant-ph/0611289) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DensitySpectrum`: PDF p.3, (12): complete eigenbasis of the given density, including its kernel. No countability, faithfulness or finite-dimensionality is imposed.
--   - `spectralP`: PDF p.3, (13): constructed Nussbaum--Szkola p weights.
--   - `spectralQ`: PDF p.3, (13): constructed Nussbaum--Szkola q weights. Completeness and trace normalization imply that each of p and q has total mass one.
--   - `lowerMass`: PDF p.4, (18),(21): p mass on the non-strict multiplicative event, including ties. Nonnegative sums retain infinity rather than defaulting to zero.
--   - `upperMass`: PDF p.4, (18),(22): q mass on the strict complementary event. No likelihood division or logarithm at a zero atom is used.
--   - `iidOperator`: PDF pp.1,4: (k+1)-copy operator in the complete tensor basis, realized as an ACTUAL bounded operator by the accepted boundedOperator. For bounded A, these coefficients always have a unique bounded realization A tensor ... tensor A, with norm at most norm(A)^(k+1). Thus reconstruction's off-domain zero branch cannot be reached. The coordinate Hilbert space is the completed tensor power.
--   - `iidLaw`: PDF p.4: (k+1) independent classical copies. For spectral probability weights these finite product laws also have mass one.
--   - `logRate`: PDF p.1, (1): natural log rate with positive denominator k+1. Zero probability is sent to minus infinity by ENNReal.log.
--   - `hoeffdingB`: PDF p.1, (1): supremum over all effect sequences and EXISTING extended alpha-rate limits, with the non-strict beta limsup constraint. No total limit selector or liminf replaces the limit. The zero-effect sequence is feasible for r>0 and gives exponent zero; unbounded exponents retain plus infinity.
--   - `logMoment`: PDF pp.2,7, (5),(31): extended natural log moment. Interior zero overlap, possible for orthogonal supports, has value minus infinity. Reuses imported traceAcceptance for the fractional-power product, with ordinary A^0=I. On states and 0<=s<=1 Schatten Holder ensures traceability and a trace in [0,1].
-- source:
--   The Converse Part of The Theorem for Quantum Hoeffding Bound, arXiv:quant-ph/0611289v1, https://arxiv.org/abs/quant-ph/0611289v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18

/-!
# Nagaoka, quant-ph/0611289v1

Five nondeferred nodes on arbitrary complete complex Hilbert spaces.
Citations use PDF pages. The independent-paper override authorizes imports
from the pinned accepted library. Twenty other nodes, including the
endpoint-defective Theorem 1, are recorded in HARD.md and GAPS.json.
Tensor blocks use complete l2(I^(k+1)) coordinates of the completed tensor
power. B retains the EXISTING extended alpha-rate limit from (1).
Type-I errors and Petz traces use imported traceAcceptance directly;
no local alpha or petzOverlap definition is declared.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

open Filter
open scoped ENNReal NNReal BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P04

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State operatorTrace relativeEntropy)
open QAlgorithms.Papers.Independent.Support50.P20
  (Effect traceAcceptance IsHilbertCPTP BlockHilbert blockBasis)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- PDF p.3, (12): complete eigenbasis of the given density, including its
kernel. No countability, faithfulness or finite-dimensionality is imposed. -/
structure DensitySpectrum {I : Type*} {b : HilbertBasis I ℂ H}
    (rho : State b) (J : Type*) where
  basis : HilbertBasis J ℂ H
  eigenvalue : J → ℝ≥0
  eigenvector : ∀ j, rho.val.val (basis j) = (eigenvalue j : ℂ) • basis j

/-- PDF p.3, (13): constructed Nussbaum--Szkola p weights. -/
def spectralP {I J L : Type*} {b : HilbertBasis I ℂ H}
    {rho sigma : State b} (x : DensitySpectrum rho J) (y : DensitySpectrum sigma L)
    (w : J × L) : ℝ≥0∞ :=
  (x.eigenvalue w.1 : ℝ≥0∞) *
    ENNReal.ofReal (Complex.normSq (inner ℂ (x.basis w.1) (y.basis w.2)))

/-- PDF p.3, (13): constructed Nussbaum--Szkola q weights. Completeness and
trace normalization imply that each of p and q has total mass one. -/
def spectralQ {I J L : Type*} {b : HilbertBasis I ℂ H}
    {rho sigma : State b} (x : DensitySpectrum rho J) (y : DensitySpectrum sigma L)
    (w : J × L) : ℝ≥0∞ :=
  (y.eigenvalue w.2 : ℝ≥0∞) *
    ENNReal.ofReal (Complex.normSq (inner ℂ (x.basis w.1) (y.basis w.2)))

/-- PDF p.4, (18),(21): p mass on the non-strict multiplicative event,
including ties. Nonnegative sums retain infinity rather than defaulting to zero. -/
def lowerMass {Omega : Type*} (p q : Omega → ℝ≥0∞) (delta : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' w, if p w ≤ delta * q w then p w else 0

/-- PDF p.4, (18),(22): q mass on the strict complementary event.
No likelihood division or logarithm at a zero atom is used. -/
def upperMass {Omega : Type*} (p q : Omega → ℝ≥0∞) (delta : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' w, if delta * q w < p w then q w else 0

/-- PDF pp.1,4: (k+1)-copy operator in the complete tensor basis, realized
as an ACTUAL bounded operator by the accepted boundedOperator. For bounded A,
these coefficients always have a unique bounded realization A tensor ... tensor A,
with norm at most norm(A)^(k+1). Thus reconstruction's off-domain zero branch
cannot be reached. The coordinate Hilbert space is the completed tensor power. -/
def iidOperator {I : Type} (b : HilbertBasis I ℂ H)
    (A : H →L[ℂ] H) (k : ℕ) : BlockHilbert I k →L[ℂ] BlockHilbert I k :=
  boundedOperator (fun u v : Fin (k + 1) → I =>
    ∏ t, inner ℂ (b (u t)) (A (b (v t))))

/-- PDF p.4: (k+1) independent classical copies. For spectral probability
weights these finite product laws also have mass one. -/
def iidLaw {Omega : Type*} (p : Omega → ℝ≥0∞) (k : ℕ)
    (w : Fin (k + 1) → Omega) : ℝ≥0∞ :=
  ∏ t, p (w t)

/-- PDF p.1, (1): natural log rate with positive denominator k+1.
Zero probability is sent to minus infinity by ENNReal.log. -/
def logRate (p : ℕ → ℝ≥0∞) (k : ℕ) : EReal :=
  (((k + 1 : ℕ) : ℝ)⁻¹ : EReal) * ENNReal.log (p k)

/-- PDF p.1, (1): supremum over all effect sequences and EXISTING extended
alpha-rate limits, with the non-strict beta limsup constraint. No total limit
selector or liminf replaces the limit. The zero-effect sequence is feasible
for r>0 and gives exponent zero; unbounded exponents retain plus infinity. -/
def hoeffdingB {I : Type} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (r : ℝ) : EReal :=
  sSup {z | ∃ (T : (k : ℕ) → Effect (BlockHilbert I k)) (l : EReal),
    Tendsto (logRate (fun k => ENNReal.ofReal
      (1 - traceAcceptance (blockBasis I k) (T k).val (iidOperator b rho k)))) atTop (nhds l) ∧
    Filter.limsup (logRate (fun k => ENNReal.ofReal
      (traceAcceptance (blockBasis I k) (T k).val (iidOperator b sigma k)))) atTop ≤
        -(r : EReal) ∧ z = -l}

/-- PDF pp.2,7, (5),(31): extended natural log moment. Interior zero overlap,
possible for orthogonal supports, has value minus infinity. Reuses imported
traceAcceptance for the fractional-power product, with ordinary A^0=I.
On states and 0<=s<=1 Schatten Holder ensures traceability and a trace in [0,1]. -/
def logMoment {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : H →L[ℂ] H) (s : ℝ) : EReal :=
  ENNReal.log (ENNReal.ofReal
    (traceAcceptance b (CFC.rpow rho (1 - s)) (CFC.rpow sigma s)))

/-- Sanity: the zero test has type-I error one. -/
example {I : Type*} (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H) :
    1 - traceAcceptance b 0 rho = 1 := by
  simp [traceAcceptance, operatorTrace]

/-- Sanity: zero first law contributes zero mass at any threshold. -/
example {Omega : Type*} (q : Omega → ℝ≥0∞) (delta : ℝ≥0∞) :
    lowerMass (fun _ => 0) q delta = 0 := by
  simp [lowerMass]

/-- Sanity: the strict second event excludes ties. -/
example {Omega : Type*} (p : Omega → ℝ≥0∞) : upperMass p p 1 = 0 := by
  simp [upperMass]

/-- Sanity: a product of unit coordinate weights remains unit. -/
example {Omega : Type*} (k : ℕ) (w : Fin (k + 1) → Omega) :
    iidLaw (fun _ => 1) k w = 1 := by
  simp [iidLaw]

/-- Sanity: the zero probability rate is minus infinity at one copy. -/
example : logRate (fun _ => 0) 0 = ⊥ := by
  simp [logRate]

/-- Sanity: extended logarithms preserve zero overlap. -/
example : ENNReal.log (0 : ℝ≥0∞) = ⊥ := by simp

end QAlgorithms.Papers.Independent.Intakethird100.P04


