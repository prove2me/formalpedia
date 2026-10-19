-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
-- name    : QAlgorithms_Papers_Independent_Frontier18_P08
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:53:15.364977+00:00
-- url     : https://prove2.me/theorems/fbf255dd-00e9-4ce8-b5a1-c4a63f8a4907
-- title:
--   Definitions for Measures of quantum correlations in infinite-dimensional systems
-- statement:
--   The objects the formalized statements of *Measures of quantum correlations in infinite-dimensional systems* (arXiv:1506.06377) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `partialTraceSecond`: Partial trace over the second completed Hilbert factor, PDF pp.6--7. On nuclear trace-class inputs these scalar series converge absolutely. The unrestricted array formula is only used on trace-class inputs below.
--   - `partialTraceFirst`: Partial trace over the first completed Hilbert factor, PDF pp.6,46. No finite-dimensional assumption is made on the discarded factor.
--   - `TraceNormConverges`: Trace-norm convergence, PDF p.6 and Remark 1, pp.7--8. The nuclear norm is extended nonnegative; it is never converted to a real. The arguments in the statements are genuine trace-class coefficient arrays.
--   - `PositiveCoefficients`: Positivity of an operator in countable orthonormal coordinates, PDF p.6. This is the quadratic-form clause of accepted P33.IsDensity, without its normalization. Nuclearity below ensures extension to a bounded operator.
--   - `PositiveTraceClass`: Full positive trace-class cone T_+, PDF p.6, including zero and arbitrary finite trace. Absolute summability of the diagonal is included explicitly; it is automatic for the nuclear operators represented here.
--   - `operatorTrace`: Trace of a trace-class operator, PDF p.6. All uses below carry nuclearity; the positive-cone predicate also explicitly carries diagonal summability.
--   - `OperatorBelow`: Loewner order on trace-class operators, PDF p.46. The argument operators are trace class; positivity is tested on every finite quadratic form.
--   - `IsQuantumOperation`: A complex-linear completely positive trace-nonincreasing map on ALL trace class inputs, PDF p.6. Every finite matrix amplification is positive on every positive trace-class input, including entangled inputs. Arrays outside trace class are irrelevant; no Kraus-rank restriction or trace preservation is added.
--   - `StronglyConverges`: Strong convergence of operations, §8.2, PDF pp.40--41: pointwise trace norm convergence on every input state. No diamond-norm requirement is imposed.
--   - `HasFullSupport`: Full support of a state, Lemma 7, PDF p.46: trivial kernel on l². The scalar row series is convergent for these trace-class inputs. This does not require a bounded inverse or a uniform positive lower eigenvalue.
--   - `conditionalEntropyNats`: Original finite-dimensional conditional entropy (30), PDF p.18, in nats. The frozen vnEntropy is in bits, so multiplication by log 2 converts to nats. It is not used as a definition of the infinite-dimensional extension (31).
-- source:
--   Measures of quantum correlations in infinite-dimensional systems, arXiv:1506.06377v2, https://arxiv.org/abs/1506.06377v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

/-!
# Measures of quantum correlations in infinite-dimensional systems

Source: M. E. Shirokov, arXiv:1506.06377v2.
The countable-basis nuclear trace-class domain is the pinned accepted P33 domain.
Partial traces sum over the full discarded basis. No finite support restriction
is placed on Lemmas 1 or 7. Other nodes without completed spectral-entropy and
faithful-extension interfaces are explicitly deferred in HARD.md and GAPS.json.
Only the finite-dimensional bounds (15)--(16) use the frozen matrix entropy,
converted from bits to nats by multiplication by Real.log 2.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P08

open QAlgorithms
open QAlgorithms.RealRegisters (Hilbert)

namespace Accepted

export QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsTraceClass NuclearExpansion traceSize tensorApply)

end Accepted

/-- Partial trace over the second completed Hilbert factor, PDF pp.6--7.
On nuclear trace-class inputs these scalar series converge absolutely. The
unrestricted array formula is only used on trace-class inputs below. -/
def partialTraceSecond {I J : Type} (X : Matrix (I × J) (I × J) ℂ) :
    Matrix I I ℂ := fun i j => ∑' a : J, X (i, a) (j, a)

/-- Partial trace over the first completed Hilbert factor, PDF pp.6,46.
No finite-dimensional assumption is made on the discarded factor. -/
def partialTraceFirst {I J : Type} (X : Matrix (I × J) (I × J) ℂ) :
    Matrix J J ℂ := fun i j => ∑' a : I, X (a, i) (a, j)

/-- Trace-norm convergence, PDF p.6 and Remark 1, pp.7--8.
The nuclear norm is extended nonnegative; it is never converted to a real.
The arguments in the statements are genuine trace-class coefficient arrays. -/
def TraceNormConverges {I : Type} (X : ℕ → Matrix I I ℂ)
    (X0 : Matrix I I ℂ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ k ≥ N,
    Accepted.traceSize (X k - X0) < ENNReal.ofReal epsilon

/-- Positivity of an operator in countable orthonormal coordinates, PDF p.6.
This is the quadratic-form clause of accepted P33.IsDensity, without its
normalization. Nuclearity below ensures extension to a bounded operator. -/
def PositiveCoefficients {I : Type} (X : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * X i j * z j).re

/-- Full positive trace-class cone T_+, PDF p.6, including zero and arbitrary
finite trace. Absolute summability of the diagonal is included explicitly;
it is automatic for the nuclear operators represented here. -/
def PositiveTraceClass {I : Type} (X : Matrix I I ℂ) : Prop :=
  Accepted.IsTraceClass X ∧ PositiveCoefficients X ∧
    Summable (fun i => (X i i).re)

/-- Trace of a trace-class operator, PDF p.6. All uses below carry nuclearity;
the positive-cone predicate also explicitly carries diagonal summability. -/
def operatorTrace {I : Type} (X : Matrix I I ℂ) : ℝ := ∑' i, (X i i).re

/-- Loewner order on trace-class operators, PDF p.46. The argument operators
are trace class; positivity is tested on every finite quadratic form. -/
def OperatorBelow {I : Type} (X Y : Matrix I I ℂ) : Prop :=
  PositiveCoefficients (Y - X)

/-- A complex-linear completely positive trace-nonincreasing map on ALL trace
class inputs, PDF p.6. Every finite matrix amplification is positive on every
positive trace-class input, including entangled inputs. Arrays outside trace
class are irrelevant; no Kraus-rank restriction or trace preservation is added. -/
def IsQuantumOperation {I J : Type}
    (Phi : Matrix I I ℂ → Matrix J J ℂ) : Prop :=
  (∀ X, Accepted.IsTraceClass X → Accepted.IsTraceClass (Phi X)) ∧
  (∀ X Y, Accepted.IsTraceClass X → Accepted.IsTraceClass Y →
    Phi (X + Y) = Phi X + Phi Y) ∧
  (∀ (c : ℂ) X, Accepted.IsTraceClass X → Phi (c • X) = c • Phi X) ∧
  (∀ (n : ℕ) (X : Matrix (I × Fin n) (I × Fin n) ℂ),
    PositiveTraceClass X → PositiveTraceClass (Accepted.tensorApply Phi X)) ∧
  (∀ X, PositiveTraceClass X → operatorTrace (Phi X) ≤ operatorTrace X)

/-- Strong convergence of operations, §8.2, PDF pp.40--41: pointwise trace
norm convergence on every input state. No diamond-norm requirement is imposed. -/
def StronglyConverges {I J : Type}
    (Phi : ℕ → (Matrix I I ℂ → Matrix J J ℂ))
    (Phi0 : Matrix I I ℂ → Matrix J J ℂ) : Prop :=
  ∀ rho : Accepted.State I,
    TraceNormConverges (fun k => Phi k rho.coefficients) (Phi0 rho.coefficients)

/-- Full support of a state, Lemma 7, PDF p.46: trivial kernel on l².
The scalar row series is convergent for these trace-class inputs. This does
not require a bounded inverse or a uniform positive lower eigenvalue. -/
def HasFullSupport {I : Type} (rho : Accepted.State I) : Prop :=
  ∀ u : Hilbert I,
    (∀ i, (∑' j : I, rho.coefficients i j * u j) = 0) → u = 0

/-- Original finite-dimensional conditional entropy (30), PDF p.18, in nats.
The frozen vnEntropy is in bits, so multiplication by log 2 converts to nats.
It is not used as a definition of the infinite-dimensional extension (31). -/
def conditionalEntropyNats {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) : ℝ :=
  Real.log 2 * vnEntropy rho - Real.log 2 * vnEntropy (traceLeft rho)

/-! Sanity examples for the new interfaces. -/

example {I J : Type} : partialTraceSecond (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  funext i j
  simp [partialTraceSecond]

example {I J : Type} : partialTraceFirst (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  funext i j
  simp [partialTraceFirst]

example {I : Type} (X : Matrix (I × Unit) (I × Unit) ℂ) (i j : I) :
    partialTraceSecond X i j = X (i, ()) (j, ()) := by
  simp [partialTraceSecond]

example {I : Type} (rho : Accepted.State I) :
    PositiveTraceClass rho.coefficients :=
  ⟨rho.density.1, rho.density.2.1, rho.density.2.2.1⟩

example {I : Type} (rho : Accepted.State I) : operatorTrace rho.coefficients = 1 :=
  rho.density.2.2.2

example {I : Type} (X : Matrix I I ℂ) : OperatorBelow X X := by
  intro s z
  simp [PositiveCoefficients]

example {I : Type} (rho : Accepted.State I) (h : HasFullSupport rho)
    (u : Hilbert I) (hu : ∀ i, (∑' j, rho.coefficients i j * u j) = 0) : u = 0 := h u hu

example {I : Type*} [Fintype I] [DecidableEq I] :
    Real.log 2 * vnEntropy (0 : Matrix I I ℂ) = 0 := by
  simp [vnEntropy, cfc_zero]

example : Real.log 2 * vnEntropy (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [vnEntropy, cfc_one]

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    conditionalEntropyNats (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
  have hTrace : traceLeft (0 : Matrix (I × J) (I × J) ℂ) = 0 := by
    ext b bprime
    simp [traceLeft]
  simp [conditionalEntropyNats, hTrace, vnEntropy, cfc_zero]

end QAlgorithms.Papers.Independent.Frontier18.P08


