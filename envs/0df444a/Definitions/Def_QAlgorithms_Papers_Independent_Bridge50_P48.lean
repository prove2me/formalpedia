-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P48
-- name    : QAlgorithms_Papers_Independent_Bridge50_P48
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:55:05.254911+00:00
-- url     : https://prove2.me/theorems/699f233d-50f3-48c0-bd95-5c189189314f
-- title:
--   Definitions for Monotonicity of a relative Rényi entropy
-- statement:
--   The objects the formalized statements of *Monotonicity of a relative Rényi entropy* (arXiv:1306.5358) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `hilbertPositiveTrace`: PDF p.1: adapter to the frozen extended positive trace in Claimed50.P46. A chosen Hilbert basis indexed by a subset of H fits QuantumData's single universe. Positive extended trace is basis independent; the supplied basis b is retained in the interface for compatibility with the finite trace formulas. Zero auxiliary inputs only package H; the operator being traced is A.
--   - `hilbertSandwichedTrace`: PDF pp.1--2, Proposition 3: the unnormalized sandwiched spectral trace. For alpha<1 its two powers have positive exponents on the theorem's domain. For alpha>1, R is the reduced positive solution of rho = sigma^((alpha-1)/(2 alpha)) R sigma^((alpha-1)/(2 alpha)). The kernel condition makes R unique. The infimum of an empty set is infinity. A divergent positive trace also remains infinity. The zero numerator is zero. Orders <=0 and order one are outside the claims made about this definition.
--   - `positivePairs`: PDF p.2, Proposition 3: both operators are non-negative, including zero.
--   - `traceSlice`: PDF p.2: the fixed-trace quantum-operation domain. Both operators are positive trace class; the first has trace t, without a normalization t=1.
--   - `jointConcaveOn`: PDF p.2: joint concavity, using the same real mixing weight for both operators. ENNReal arithmetic is used only on nonnegative quantities. At lambda=0 or 1 its convention 0*infinity=0 gives exactly the endpoint value.
--   - `jointConvexOn`: PDF p.2: joint convexity, with the same audited nonnegative endpoint convention as jointConcaveOn. No subtraction of infinite quantities occurs.
--   - `scaledExponential`: PDF p.2, consequence after Proposition 3: exp((alpha-1)D_alpha)=Q_alpha/t. For t>0 this retains zero below one and infinity above one on orthogonal pairs.
--   - `divergenceExponential`: PDF p.2, second consequence after Proposition 3: exp(D_alpha). Used only for alpha>1 and t>0, so its scalar power is positive and t is finite. This defines the exponential directly, without totalizing an extended logarithm.
--   - `ennrealNaturalLog`: PDF p.1: natural logarithm on nonnegative extended arguments. The finite branch reuses Dependency50.P21.extendedLog; its real input cannot represent infinity, so the top branch is supplied before converting toReal.
--   - `normalizedRelativeEntropy`: PDF p.1, alpha=1: remove the finite trace correction from the accepted extended generalized relative entropy, then divide by Tr rho. The accepted finite-compression formula includes Tr(sigma-rho); hence both finite scalar corrections below are essential for unnormalized operators. The domain of the theorems has positive finite Tr rho and trace-class sigma.
--   - `maxSandwichNorm`: PDF p.1, alpha=infinity: the extended norm of the relative sandwich is its positive order gauge, inf{c>0 : rho<=c sigma}. An empty set gives infinity. No division by the trace of rho belongs to this endpoint.
--   - `traceNormalizedHilbertRenyi`: PDF p.1: the full trace-normalized sandwiched divergence in nats. The order parameter includes infinity. At one the extended Umegaki formula is used; at infinity the logarithm of the order gauge has no trace divisor. For finite orders different from one the divisor is inside the logarithm. Only alpha>=1/2 and positive trace-class pairs with Tr rho>0 are used below.
--   - `entropyJointConvexOn`: PDF p.2, Theorem 2: Jensen inequality for entropy itself. On the positive finite-trace slice the divergence is real or +infinity, never -infinity. Thus the weights 0 and 1 also recover the exact endpoint values.
-- source:
--   Monotonicity of a relative Rényi entropy, arXiv:1306.5358v3, https://arxiv.org/abs/1306.5358v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

/-!
Frank--Lieb, arXiv:1306.5358v3. Page numbers are PDF pages.
Theorems 1--2, Proposition 3 and its two exponential consequences are stated below.
Lemmas 4--5 and Remark 6 are explicitly deferred in HARD.md and GAPS.json.

For orders above one, the spectral trace is constructed through the unique
positive bounded reduced sandwich, when it exists. This is the specialization
z = alpha of Mosonyi, arXiv:2107.08036v5, Lemma III.1, Remark III.3 and
Definition III.9 (PDF pp.4--8). If no such bounded operator exists, or its
positive spectral trace diverges, the value is infinity. Thus negative powers
are never evaluated by the bounded continuous functional calculus.
Compilation is pending the batch handoff.
-/

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P48

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass operatorTrace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.1: adapter to the frozen extended positive trace in Claimed50.P46.
A chosen Hilbert basis indexed by a subset of H fits QuantumData's single
universe. Positive extended trace is basis independent; the supplied basis b
is retained in the interface for compatibility with the finite trace formulas.
Zero auxiliary inputs only package H; the operator being traced is A. -/
def hilbertPositiveTrace {I : Type*} (_b : HilbertBasis I ℂ H) (A : H →L[ℂ] H) : ℝ≥0∞ :=
  let w : Set H := (exists_hilbertBasis ℂ H).choose
  let e : HilbertBasis w ℂ H := (exists_hilbertBasis ℂ H).choose_spec.choose
  QAlgorithms.Papers.Independent.Claimed50.P46.positiveTrace
    { H := H, J := w, basis := e, rho := 0, sigma := 0,
      rho_positive := by simp [IsPositive], sigma_positive := by simp [IsPositive] } A

example {I : Type*} (b : HilbertBasis I ℂ H) : hilbertPositiveTrace b 0 = 0 := by
  simp [hilbertPositiveTrace, QAlgorithms.Papers.Independent.Claimed50.P46.positiveTrace]

/-- PDF pp.1--2, Proposition 3: the unnormalized sandwiched spectral trace.
For alpha<1 its two powers have positive exponents on the theorem's domain.
For alpha>1, R is the reduced positive solution of
rho = sigma^((alpha-1)/(2 alpha)) R sigma^((alpha-1)/(2 alpha)).
The kernel condition makes R unique. The infimum of an empty set is infinity.
A divergent positive trace also remains infinity. The zero numerator is zero.
Orders <=0 and order one are outside the claims made about this definition. -/
def hilbertSandwichedTrace {I : Type*} (b : HilbertBasis I ℂ H) (alpha : ℝ)
    (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) : ℝ≥0∞ :=
  if pair.1 = 0 then 0
  else if alpha < 1 then
    let S := cfc (fun x : ℝ => Real.rpow x ((1 - alpha) / (2 * alpha))) pair.2
    hilbertPositiveTrace b (cfc (fun x : ℝ => Real.rpow x alpha) (S * pair.1 * S))
  else
    let S := cfc (fun x : ℝ => Real.rpow x ((alpha - 1) / (2 * alpha))) pair.2
    sInf {v : ℝ≥0∞ | ∃ R : H →L[ℂ] H,
      IsPositive R ∧ S * R * S = pair.1 ∧
      (∀ x, pair.2 x = 0 → R x = 0) ∧
      v = hilbertPositiveTrace b (cfc (fun x : ℝ => Real.rpow x alpha) R)}

example {I : Type*} (b : HilbertBasis I ℂ H) (alpha : ℝ) (sigma : H →L[ℂ] H) :
    hilbertSandwichedTrace b alpha (0, sigma) = 0 := by
  simp [hilbertSandwichedTrace]

/-- PDF p.2, Proposition 3: both operators are non-negative, including zero. -/
def positivePairs : Set ((H →L[ℂ] H) × (H →L[ℂ] H)) :=
  {pair | IsPositive pair.1 ∧ IsPositive pair.2}

example : (0, 0) ∈ positivePairs (H := H) := by
  simp [positivePairs, IsPositive]

/-- PDF p.2: the fixed-trace quantum-operation domain. Both operators are
positive trace class; the first has trace t, without a normalization t=1. -/
def traceSlice {I : Type*} (b : HilbertBasis I ℂ H) (t : ℝ) :
    Set ((H →L[ℂ] H) × (H →L[ℂ] H)) :=
  {pair | pair ∈ positivePairs ∧ IsTraceClass pair.1 ∧ IsTraceClass pair.2 ∧
    (operatorTrace b pair.1).re = t}

/-- PDF p.2: joint concavity, using the same real mixing weight for both
operators. ENNReal arithmetic is used only on nonnegative quantities.
At lambda=0 or 1 its convention 0*infinity=0 gives exactly the endpoint value. -/
def jointConcaveOn (domain : Set ((H →L[ℂ] H) × (H →L[ℂ] H)))
    (f : ((H →L[ℂ] H) × (H →L[ℂ] H)) → ℝ≥0∞) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
    ENNReal.ofReal lambda * f x + ENNReal.ofReal (1 - lambda) * f y ≤
      f (lambda • x + (1 - lambda) • y)

/-- PDF p.2: joint convexity, with the same audited nonnegative endpoint
convention as jointConcaveOn. No subtraction of infinite quantities occurs. -/
def jointConvexOn (domain : Set ((H →L[ℂ] H) × (H →L[ℂ] H)))
    (f : ((H →L[ℂ] H) × (H →L[ℂ] H)) → ℝ≥0∞) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
    f (lambda • x + (1 - lambda) • y) ≤
      ENNReal.ofReal lambda * f x + ENNReal.ofReal (1 - lambda) * f y

example (domain : Set ((H →L[ℂ] H) × (H →L[ℂ] H))) :
    jointConcaveOn domain (fun _ => 0) ∧ jointConvexOn domain (fun _ => 0) := by
  simp [jointConcaveOn, jointConvexOn]

/-- PDF p.2, consequence after Proposition 3: exp((alpha-1)D_alpha)=Q_alpha/t.
For t>0 this retains zero below one and infinity above one on orthogonal pairs. -/
def scaledExponential {I : Type*} (b : HilbertBasis I ℂ H) (t alpha : ℝ)
    (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) : ℝ≥0∞ :=
  hilbertSandwichedTrace b alpha pair / ENNReal.ofReal t

example {I : Type*} (b : HilbertBasis I ℂ H) (t alpha : ℝ) (sigma : H →L[ℂ] H) :
    scaledExponential b t alpha (0, sigma) = 0 := by
  simp [scaledExponential, hilbertSandwichedTrace]

/-- PDF p.2, second consequence after Proposition 3: exp(D_alpha).
Used only for alpha>1 and t>0, so its scalar power is positive and t is finite.
This defines the exponential directly, without totalizing an extended logarithm. -/
def divergenceExponential {I : Type*} (b : HilbertBasis I ℂ H) (t alpha : ℝ)
    (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) : ℝ≥0∞ :=
  (scaledExponential b t alpha pair) ^ (1 / (alpha - 1) : ℝ)

example {I : Type*} (b : HilbertBasis I ℂ H) (t : ℝ)
    (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) :
    divergenceExponential b t 2 pair = scaledExponential b t 2 pair := by
  unfold divergenceExponential
  have hexponent : (1 / ((2 : ℝ) - 1)) = 1 := by norm_num
  rw [hexponent, ENNReal.rpow_one]

/-- PDF p.1: natural logarithm on nonnegative extended arguments.
The finite branch reuses Dependency50.P21.extendedLog; its real input cannot
represent infinity, so the top branch is supplied before converting toReal. -/
def ennrealNaturalLog (x : ℝ≥0∞) : EReal :=
  if x = ⊤ then ⊤ else
    QAlgorithms.Papers.Independent.Dependency50.P21.extendedLog x.toReal

example : ennrealNaturalLog 0 = ⊥ ∧ ennrealNaturalLog ⊤ = ⊤ := by
  simp [ennrealNaturalLog, QAlgorithms.Papers.Independent.Dependency50.P21.extendedLog]

/-- PDF p.1, alpha=1: remove the finite trace correction from the accepted
extended generalized relative entropy, then divide by Tr rho.
The accepted finite-compression formula includes Tr(sigma-rho); hence both
finite scalar corrections below are essential for unnormalized operators.
The domain of the theorems has positive finite Tr rho and trace-class sigma. -/
def normalizedRelativeEntropy {I : Type*} (b : HilbertBasis I ℂ H)
    (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) : EReal :=
  if h : IsTraceClass pair.1 ∧ IsTraceClass pair.2 then
    let d := QAlgorithms.Papers.Independent.Dependency50.P13.relativeEntropy
      ⟨pair.1, h.1⟩ ⟨pair.2, h.2⟩
    let e : EReal := if d = ⊤ then ⊤ else (d.toReal : EReal)
    ((((operatorTrace b pair.1).re)⁻¹ : ℝ) : EReal) *
      (e - ((operatorTrace b pair.2).re : EReal) + ((operatorTrace b pair.1).re : EReal))
  else ⊤

/-- PDF p.1, alpha=infinity: the extended norm of the relative sandwich
is its positive order gauge, inf{c>0 : rho<=c sigma}. An empty set gives
infinity. No division by the trace of rho belongs to this endpoint. -/
def maxSandwichNorm (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) : ℝ≥0∞ :=
  sInf {v : ℝ≥0∞ | ∃ c : ℝ, 0 < c ∧
    IsPositive ((c : ℂ) • pair.2 - pair.1) ∧ v = ENNReal.ofReal c}

/-- PDF p.1: the full trace-normalized sandwiched divergence in nats.
The order parameter includes infinity. At one the extended Umegaki formula
is used; at infinity the logarithm of the order gauge has no trace divisor.
For finite orders different from one the divisor is inside the logarithm.
Only alpha>=1/2 and positive trace-class pairs with Tr rho>0 are used below. -/
def traceNormalizedHilbertRenyi {I : Type*} (b : HilbertBasis I ℂ H) (alpha : ℝ≥0∞)
    (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) : EReal :=
  if alpha = ⊤ then ennrealNaturalLog (maxSandwichNorm pair)
  else if alpha = 1 then normalizedRelativeEntropy b pair
  else (((alpha.toReal - 1)⁻¹ : ℝ) : EReal) *
    ennrealNaturalLog (scaledExponential b (operatorTrace b pair.1).re alpha.toReal pair)

example {I : Type*} (b : HilbertBasis I ℂ H)
    (pair : (H →L[ℂ] H) × (H →L[ℂ] H)) :
    traceNormalizedHilbertRenyi b 1 pair = normalizedRelativeEntropy b pair ∧
    traceNormalizedHilbertRenyi b ⊤ pair = ennrealNaturalLog (maxSandwichNorm pair) := by
  simp [traceNormalizedHilbertRenyi]

/-- PDF p.2, Theorem 2: Jensen inequality for entropy itself. On the positive
finite-trace slice the divergence is real or +infinity, never -infinity.
Thus the weights 0 and 1 also recover the exact endpoint values. -/
def entropyJointConvexOn (domain : Set ((H →L[ℂ] H) × (H →L[ℂ] H)))
    (f : ((H →L[ℂ] H) × (H →L[ℂ] H)) → EReal) : Prop :=
  ∀ x ∈ domain, ∀ y ∈ domain, ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
    f (lambda • x + (1 - lambda) • y) ≤
      (lambda : EReal) * f x + ((1 - lambda : ℝ) : EReal) * f y

example (domain : Set ((H →L[ℂ] H) × (H →L[ℂ] H))) :
    entropyJointConvexOn domain (fun _ => 0) := by
  simp [entropyJointConvexOn]

end QAlgorithms.Papers.Independent.Bridge50.P48


