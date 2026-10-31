-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P35
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:11:18.639659+00:00
-- url     : https://prove2.me/theorems/28bddd5d-931f-42bb-90f1-5895cc2f877f
-- title:
--   Definitions for Bounded functional calculi for unbounded operators
-- statement:
--   The objects the formalized statements of *Bounded functional calculi for unbounded operators* (arXiv:2202.03143) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AnalyticSymbol`
--   - `hp`: The open right half-plane (source p.4).
--   - `closedHp`: The closed right half-plane (source p.4).
--   - `openSectorDomain`: The source's open sector, including its special angle-zero convention (p.4).
--   - `point`: Cartesian parametrization of the right half-plane.
--   - `positiveVolume`: Lebesgue measure on the positive alpha axis. Endpoints have measure zero.
--   - `Hol`: Holomorphicity on the actual symbol domain.
--   - `supSize`: Supremum in an extended lattice, never a default real supremum.
--   - `HInfinity`: A bounded holomorphic symbol on its native domain.
--   - `limitValue`: A guarded limit selector. Its fallback is never asserted to be a limit.
--   - `infinityValue`: The canonical infinity value selected along the positive real axis.
--   - `zeroValue`: The canonical zero value selected along the positive real axis.
--   - `extension`: Continuous boundary extension, when it exists; interior values are unchanged.
--   - `infinityWithin`: Norm infinity filter restricted to a native symbol domain.
--   - `SectorialLimits`: Both sectorial limits, with the same values for every strict subsector (p.20).
--   - `bSemi`: Besov seminorm, equation (3.1), without a boundedness hypothesis (p.6).
--   - `BesovClass`: The space B as it is defined before Proposition 3.1.
--   - `bSize`: Full Besov norm (p.7), in an extended lattice off its natural domain.
--   - `BZero`: The ideal B0, with vanishing canonical infinity value (p.7).
--   - `wSize`: Mixed W norm uses an essential, rather than pointwise, supremum (3.3).
--   - `MixedDerivativeClass`: Measurable representatives of W. All W assertions below are a.e. invariant.
--   - `AbsoluteDouble`: Absolute convergence of a double scalar integral, including measurability.
--   - `qKernel`: The reflected resolvent kernel from (3.5), p.8.
--   - `besovPrimitive`: Q is computed from its scalar integral; B0 membership is not assumed.
--   - `eSemi`: The derivative dual seminorm from p.11.
--   - `DerivativeDualClass`: The holomorphic space E.
--   - `besovPairing`: The bilinear (not sesquilinear) partial duality (3.9).
--   - `LaplaceRep`: A positive finite control measure and an integrable complex density represent an arbitrary finite complex measure; no positivity of the density is imposed.
--   - `LM`: The full finite-complex-measure Laplace class LM (p.5).
--   - `hpSize`: HP norm: infimum of total variations over representations. The empty infimum is infinity, so non-LM symbols cannot have a spurious zero norm.
--   - `vSize`: Extended mixed weighted norm (4.3); alpha is positive in this integral.
--   - `WeightedDerivativeClass`: Measurable representatives of V_s.
--   - `D`: D_s imposes only the source's holomorphic derivative-integrability condition.
--   - `dSemi`: The D_s seminorm and norm (pp.18--20).
--   - `dSize`: The full D_s norm retains its infinity term separately from the seminorm.
--   - `DUnion`: D_infinity is a union, not a boundedness condition.
--   - `DBounded`: Bounded subalgebra D_s^infinity.
--   - `dBoundedSize`: Its stronger norm (p.20).
--   - `powerPull`: Principal complex powers on native sectors.
--   - `qsKernel`: Kernel in (4.6); the power is on the entire denominator.
--   - `Qs`: The explicit Q_s integral.
--   - `hardySize`: Radial Hardy H1 norm, summing both rays as in (4.8).
--   - `HardySobolevClass`: H_psi membership is independent of any boundary extension theorem.
--   - `hSize`: Full Hardy-Sobolev norm (p.21).
--   - `NormConverges`: A norm-convergent sequence in a domain-relative symbol space.
--   - `NormCauchy`: The Cauchy condition, with no assumed normed-space instance.
--   - `BanachSymbols`: Banach-space properties stated extensionally on the native domain.
--   - `BanachAlgebraSymbols`: A unital Banach algebra of symbols, modulo equality on its domain.
--   - `NormClosure`: Relative norm closure; the ambient space is supplied separately.
--   - `CompactClosure`: Uniform approximation on each compact subset, the compact-open topology.
--   - `CompactConverges`: Uniform convergence on compact sets for a sequence.
--   - `NotSeparableSymbols`: Nonseparability in the norm topology, expressed using every countable family.
--   - `Vanishes`: Source C0 on the closed half-plane, using canonical boundary values.
--   - `resolventSymbol`: Resolvent symbols (p.5).
--   - `ResolventSpan`: Finite sums of resolvents, compared only on the indicated domain.
--   - `localDerivative`: Localized derivative integral in Lemma 3.5.
--   - `BConvergence`: Exactly the three sequence assumptions of Lemma 3.5; no limit membership.
--   - `arccot`: The holomorphic arccot branch (3.2).
--   - `arccotZero`: The continuous right-half-plane arccot value at zero is pi/2.
--   - `sinhQuotient`: Continuous value of sinh(zt)/t at t=0 (Example 3.3).
--   - `scalarCayley`: Cayley symbol.
--   - `phiSymbol`: The regularized inverse-exponential symbol preceding Proposition 3.19.
--   - `betaValue`: Euler's beta integral on its positive-parameter domain.
--   - `boundaryAverage`: The boundary average (4.11), defined through continuous native traces.
--   - `DenseClosedGraphOperator`: Closed densely defined complex-linear operators, represented by their actual single-valued graph. No semigroup or dense-range hypothesis is built in (p.4).
--   - `InverseAt`: A bounded two-sided inverse of z+A, on the actual graph domain.
--   - `plusResolvent`: A concrete resolvent selector, with an irrelevant fallback off the resolvent set.
--   - `operatorSpectrum`: Spectrum of A, with the sign appropriate to the z+A resolvent.
--   - `SectorialAtAngle`: Sectoriality of angle theta uses the CLOSED sector and all larger angles.
--   - `SectorialBelow`: The strict pi/2-minus class.
--   - `mSize`: M_A with its genuine extended supremum (2.2).
--   - `gsfSlice`: Scalar GSF integral for the square resolvent.
--   - `GSF`: Exactly the pointwise GSF assumptions (3.12), without adding a supplied uniform GSF constant or semigroup as a hypothesis.
--   - `gammaSize`: Least uniform GSF constant as an extended supremum over the two unit balls. The factor 2/pi is NOT part of gamma_A in (3.14).
--   - `weakKernel`: Integrand of the actual weak operator formula (3.15).
--   - `weakBValue`: The scalar formula is fixed before any operator is asserted to exist.
--   - `RealizesB`: Representation in X, as opposed to a merely bidual-valued weak formula.
--   - `bOperator`: Canonical value of (3.15) when it is represented by a bounded X-valued operator; existence is a conclusion of Theorem 3.13.
--   - `AlgebraMapOn`: Algebra homomorphism on native-domain symbols, with domain extensionality.
--   - `BoundedMapOn`: Boundedness on a source symbol space, with a uniform constant.
--   - `BCalculus`: A B-calculus as defined on p.4, with its resolvent normalization.
--   - `C0SemigroupData`: Bounded C0-semigroup data, reusing the accepted predicate (source pp.4--5). The subtype only packages its time map with that predicate; it adds no axioms.
--   - `Generates`: Generator graph with the paper's negative-generator convention.
--   - `HPCompatible`: Exact HP agreement for every finite COMPLEX measure, using a positive control measure and a complex density as above.
--   - `HilbertNorm`: Hilbert structure for the SAME complex normed-space structure as the operators. Equality of the inherited NormedSpace also fixes complex scalars.
--   - `HilbertGenerator`: The bounded Hilbert-semigroup regime, without imposing it on Banach clauses.
--   - `besovOperatorIntegrand`: Operator-norm integrand of Theorem 4.1.
--   - `AbsoluteOperatorDouble`: Absolute convergence in operator norm, rather than only weak convergence.
--   - `TransposeEigen`: The eigenfunctional condition for the BANACH transpose: no conjugation.
--   - `operatorCayley`: The concrete Cayley transform I-2(1+A)^(-1).
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, https://arxiv.org/abs/2202.03143v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07

/-!
Batty--Gomilko--Tomilov, arXiv:2202.03143v1.
All symbol predicates and comparisons are relative to the displayed open domain.
Extended nonnegative norms retain divergence. Values selected by `limitValue`
are used only when the corresponding existence assertion is established by a
stated result; no existence or regularity conclusion is assumed in a definition.
-/

noncomputable section

open Complex MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

abbrev AnalyticSymbol := ℂ → ℂ

/-- The open right half-plane (source p.4). -/
def hp : Set ℂ := {z | 0 < z.re}

/-- The closed right half-plane (source p.4). -/
def closedHp : Set ℂ := {z | 0 ≤ z.re}

/-- The source's open sector, including its special angle-zero convention (p.4). -/
def openSectorDomain (psi : ℝ) : Set ℂ :=
  if psi = 0 then {z | z.im = 0 ∧ 0 < z.re}
  else {z | z ≠ 0 ∧ |Complex.arg z| < psi}

/-- Cartesian parametrization of the right half-plane. -/
def point (a b : ℝ) : ℂ := (a : ℂ) + Complex.I * (b : ℂ)

/-- Lebesgue measure on the positive alpha axis. Endpoints have measure zero. -/
def positiveVolume : Measure ℝ := volume.restrict (Ioi 0)

/-- Holomorphicity on the actual symbol domain. -/
def Hol (S : Set ℂ) (f : AnalyticSymbol) : Prop := DifferentiableOn ℂ f S

/-- Supremum in an extended lattice, never a default real supremum. -/
def supSize (S : Set ℂ) (f : AnalyticSymbol) : ℝ≥0∞ :=
  ⨆ z : S, ENNReal.ofReal ‖f z‖

/-- A bounded holomorphic symbol on its native domain. -/
def HInfinity (S : Set ℂ) (f : AnalyticSymbol) : Prop := Hol S f ∧ supSize S f < ⊤

/-- A guarded limit selector. Its fallback is never asserted to be a limit. -/
def limitValue {D : Type*} (F : Filter D) (f : D → ℂ) : ℂ :=
  if h : ∃ c, Tendsto f F (𝓝 c) then Classical.choose h else 0

/-- The canonical infinity value selected along the positive real axis. -/
def infinityValue (f : AnalyticSymbol) : ℂ :=
  limitValue atTop (fun t : ℝ => f (t : ℂ))

/-- The canonical zero value selected along the positive real axis. -/
def zeroValue (f : AnalyticSymbol) : ℂ :=
  limitValue (𝓝[>] (0 : ℝ)) (fun t : ℝ => f (t : ℂ))

/-- Continuous boundary extension, when it exists; interior values are unchanged. -/
def extension (S : Set ℂ) (f : AnalyticSymbol) (z : ℂ) : ℂ :=
  if z ∈ S then f z else limitValue (𝓝[S] z) f

/-- Norm infinity filter restricted to a native symbol domain. -/
def infinityWithin (S : Set ℂ) : Filter ℂ :=
  Filter.comap (fun z : ℂ => ‖z‖) atTop ⊓ Filter.principal S

/-- Both sectorial limits, with the same values for every strict subsector (p.20). -/
def SectorialLimits (f : AnalyticSymbol) : Prop :=
  ∀ psi : ℝ, 0 < psi → psi < Real.pi / 2 →
    Tendsto f (𝓝[openSectorDomain psi] 0) (𝓝 (zeroValue f)) ∧
    Tendsto f (infinityWithin (openSectorDomain psi)) (𝓝 (infinityValue f))

/-- Besov seminorm, equation (3.1), without a boundedness hypothesis (p.6). -/
def bSemi (f : AnalyticSymbol) : ℝ≥0∞ :=
  ∫⁻ a, (⨆ b : ℝ, ENNReal.ofReal ‖deriv f (point a b)‖) ∂positiveVolume

/-- The space B as it is defined before Proposition 3.1. -/
def BesovClass (f : AnalyticSymbol) : Prop := Hol hp f ∧ bSemi f < ⊤

/-- Full Besov norm (p.7), in an extended lattice off its natural domain. -/
def bSize (f : AnalyticSymbol) : ℝ≥0∞ := supSize hp f + bSemi f

/-- The ideal B0, with vanishing canonical infinity value (p.7). -/
def BZero (f : AnalyticSymbol) : Prop := BesovClass f ∧ infinityValue f = 0

/-- Mixed W norm uses an essential, rather than pointwise, supremum (3.3). -/
def wSize (g : AnalyticSymbol) : ℝ≥0∞ :=
  ∫⁻ a, essSup (fun b : ℝ => ENNReal.ofReal ‖g (point a b)‖)
    volume ∂positiveVolume

/-- Measurable representatives of W. All W assertions below are a.e. invariant. -/
def MixedDerivativeClass (g : AnalyticSymbol) : Prop :=
  AEStronglyMeasurable (fun p : ℝ × ℝ => g (point p.1 p.2))
    (positiveVolume.prod volume) ∧ wSize g < ⊤

/-- Absolute convergence of a double scalar integral, including measurability. -/
def AbsoluteDouble (F : ℝ → ℝ → ℂ) : Prop :=
  AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
    (positiveVolume.prod volume) ∧
  (∫⁻ a, ∫⁻ b, ENNReal.ofReal ‖F a b‖ ∂volume ∂positiveVolume) < ⊤

/-- The reflected resolvent kernel from (3.5), p.8. -/
def qKernel (g : AnalyticSymbol) (z : ℂ) (a b : ℝ) : ℂ :=
  (a : ℂ) * g (point a b) / (point a (-b) + z) ^ 2

/-- Q is computed from its scalar integral; B0 membership is not assumed. -/
def besovPrimitive (g : AnalyticSymbol) (z : ℂ) : ℂ :=
  (-2 / (Real.pi : ℂ)) * ∫ a, ∫ b, qKernel g z a b ∂volume ∂positiveVolume

/-- The derivative dual seminorm from p.11. -/
def eSemi (g : AnalyticSymbol) : ℝ≥0∞ :=
  ⨆ a : {a : ℝ // 0 < a}, ENNReal.ofReal a.1 *
    ∫⁻ b, ENNReal.ofReal ‖deriv g (point a.1 b)‖ ∂volume

/-- The holomorphic space E. -/
def DerivativeDualClass (g : AnalyticSymbol) : Prop := Hol hp g ∧ eSemi g < ⊤

/-- The bilinear (not sesquilinear) partial duality (3.9). -/
def besovPairing (g f : AnalyticSymbol) : ℂ :=
  ∫ a, (a : ℂ) * ∫ b, deriv g (point a (-b)) * deriv f (point a b)
    ∂volume ∂positiveVolume

/-- A positive finite control measure and an integrable complex density represent
an arbitrary finite complex measure; no positivity of the density is imposed. -/
def LaplaceRep (mu : Measure ℝ) (w : ℝ → ℂ) (f : AnalyticSymbol) : Prop :=
  IsFiniteMeasure mu ∧ mu (Iio 0) = 0 ∧ Integrable w mu ∧
    EqOn f (fun z => ∫ t, Complex.exp (-z * (t : ℂ)) * w t ∂mu) hp

/-- The full finite-complex-measure Laplace class LM (p.5). -/
def LM (f : AnalyticSymbol) : Prop := ∃ mu w, LaplaceRep mu w f

/-- HP norm: infimum of total variations over representations. The empty
infimum is infinity, so non-LM symbols cannot have a spurious zero norm. -/
def hpSize (f : AnalyticSymbol) : ℝ≥0∞ :=
  sInf {v | ∃ mu w, LaplaceRep mu w f ∧ v = ∫⁻ t, ENNReal.ofReal ‖w t‖ ∂mu}

/-- Extended mixed weighted norm (4.3); alpha is positive in this integral. -/
def vSize (s : ℝ) (g : AnalyticSymbol) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ b, ENNReal.ofReal
    (Real.rpow a s / Real.rpow (a ^ 2 + b ^ 2) ((s + 1) / 2)) *
      ENNReal.ofReal ‖g (point a b)‖ ∂volume ∂positiveVolume

/-- Measurable representatives of V_s. -/
def WeightedDerivativeClass (s : ℝ) (g : AnalyticSymbol) : Prop :=
  AEStronglyMeasurable (fun p : ℝ × ℝ => g (point p.1 p.2))
    (positiveVolume.prod volume) ∧ vSize s g < ⊤

/-- D_s imposes only the source's holomorphic derivative-integrability condition. -/
def D (s : ℝ) (f : AnalyticSymbol) : Prop := Hol hp f ∧ WeightedDerivativeClass s (deriv f)

/-- The D_s seminorm and norm (pp.18--20). -/
def dSemi (s : ℝ) (f : AnalyticSymbol) : ℝ≥0∞ := vSize s (deriv f)

/-- The full D_s norm retains its infinity term separately from the seminorm. -/
def dSize (s : ℝ) (f : AnalyticSymbol) : ℝ≥0∞ :=
  ENNReal.ofReal ‖infinityValue f‖ + dSemi s f

/-- D_infinity is a union, not a boundedness condition. -/
def DUnion (f : AnalyticSymbol) : Prop := ∃ s : ℝ, -1 < s ∧ D s f

/-- Bounded subalgebra D_s^infinity. -/
def DBounded (s : ℝ) (f : AnalyticSymbol) : Prop := D s f ∧ HInfinity hp f

/-- Its stronger norm (p.20). -/
def dBoundedSize (s : ℝ) (f : AnalyticSymbol) : ℝ≥0∞ := supSize hp f + dSemi s f

/-- Principal complex powers on native sectors. -/
def powerPull (r : ℝ) (f : AnalyticSymbol) (z : ℂ) : ℂ := f (z ^ (r : ℂ))

/-- Kernel in (4.6); the power is on the entire denominator. -/
def qsKernel (s : ℝ) (g : AnalyticSymbol) (z : ℂ) (a b : ℝ) : ℂ :=
  (Real.rpow a s : ℂ) * g (point a b) /
    (point a (-b) + z) ^ ((s + 1 : ℝ) : ℂ)

/-- The explicit Q_s integral. -/
def Qs (s : ℝ) (g : AnalyticSymbol) (z : ℂ) : ℂ :=
  (-(Real.rpow 2 s) / Real.pi : ℝ) *
    ∫ a, ∫ b, qsKernel s g z a b ∂volume ∂positiveVolume

/-- Radial Hardy H1 norm, summing both rays as in (4.8). -/
def hardySize (psi : ℝ) (g : AnalyticSymbol) : ℝ≥0∞ :=
  ⨆ phi : {phi : ℝ // |phi| < psi},
    ∫⁻ t, ENNReal.ofReal ‖g ((t : ℂ) * Complex.exp (Complex.I * phi.1))‖ +
      ENNReal.ofReal ‖g ((t : ℂ) * Complex.exp (-Complex.I * phi.1))‖
      ∂positiveVolume

/-- H_psi membership is independent of any boundary extension theorem. -/
def HardySobolevClass (psi : ℝ) (f : AnalyticSymbol) : Prop :=
  Hol (openSectorDomain psi) f ∧ hardySize psi (deriv f) < ⊤

/-- Full Hardy-Sobolev norm (p.21). -/
def hSize (psi : ℝ) (f : AnalyticSymbol) : ℝ≥0∞ :=
  supSize (openSectorDomain psi) f + hardySize psi (deriv f)

/-- A norm-convergent sequence in a domain-relative symbol space. -/
def NormConverges (N : AnalyticSymbol → ℝ≥0∞) (fs : ℕ → AnalyticSymbol) (f : AnalyticSymbol) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ k, ∀ n ≥ k, N (fs n - f) < ENNReal.ofReal eps

/-- The Cauchy condition, with no assumed normed-space instance. -/
def NormCauchy (N : AnalyticSymbol → ℝ≥0∞) (fs : ℕ → AnalyticSymbol) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ k, ∀ n ≥ k, ∀ m ≥ k,
    N (fs n - fs m) < ENNReal.ofReal eps

/-- Banach-space properties stated extensionally on the native domain. -/
def BanachSymbols (S : Set ℂ) (A : AnalyticSymbol → Prop) (N : AnalyticSymbol → ℝ≥0∞) : Prop :=
  A 0 ∧ (∀ f, A f → N f < ⊤ ∧ (N f = 0 ↔ EqOn f 0 S)) ∧
  (∀ f g, A f → A g → A (f + g) ∧ N (f + g) ≤ N f + N g) ∧
  (∀ c : ℂ, ∀ f, A f → A (c • f) ∧ N (c • f) = ENNReal.ofReal ‖c‖ * N f) ∧
  ∀ fs : ℕ → AnalyticSymbol, (∀ n, A (fs n)) → NormCauchy N fs →
    ∃ f, A f ∧ NormConverges N fs f

/-- A unital Banach algebra of symbols, modulo equality on its domain. -/
def BanachAlgebraSymbols (S : Set ℂ) (A : AnalyticSymbol → Prop)
    (N : AnalyticSymbol → ℝ≥0∞) : Prop :=
  BanachSymbols S A N ∧ A 1 ∧ N 1 = 1 ∧
    ∀ f g, A f → A g → A (f * g) ∧ N (f * g) ≤ N f * N g

/-- Relative norm closure; the ambient space is supplied separately. -/
def NormClosure (A : AnalyticSymbol → Prop) (N : AnalyticSymbol → ℝ≥0∞) (f : AnalyticSymbol) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ g, A g ∧ N (g - f) < ENNReal.ofReal eps

/-- Uniform approximation on each compact subset, the compact-open topology. -/
def CompactClosure (S : Set ℂ) (A : AnalyticSymbol → Prop) (f : AnalyticSymbol) : Prop :=
  ∀ K : Set ℂ, K ⊆ S → IsCompact K → ∀ eps : ℝ, 0 < eps →
    ∃ g, A g ∧ supSize K (g - f) < ENNReal.ofReal eps

/-- Uniform convergence on compact sets for a sequence. -/
def CompactConverges (S : Set ℂ) (fs : ℕ → AnalyticSymbol) (f : AnalyticSymbol) : Prop :=
  ∀ K : Set ℂ, K ⊆ S → IsCompact K → ∀ eps : ℝ, 0 < eps →
    ∃ k, ∀ n ≥ k, supSize K (fs n - f) < ENNReal.ofReal eps

/-- Nonseparability in the norm topology, expressed using every countable family. -/
def NotSeparableSymbols (A : AnalyticSymbol → Prop) (N : AnalyticSymbol → ℝ≥0∞) : Prop :=
  ∀ fs : ℕ → AnalyticSymbol, (∀ n, A (fs n)) →
    ∃ f, A f ∧ ∃ eps : ℝ, 0 < eps ∧ ∀ n, ENNReal.ofReal eps ≤ N (fs n - f)

/-- Source C0 on the closed half-plane, using canonical boundary values. -/
def Vanishes (f : AnalyticSymbol) : Prop :=
  Tendsto f (infinityWithin hp) (𝓝 0)

/-- Resolvent symbols (p.5). -/
def resolventSymbol (lam : ℂ) (z : ℂ) : ℂ := (lam + z)⁻¹

/-- Finite sums of resolvents, compared only on the indicated domain. -/
def ResolventSpan (S L : Set ℂ) (constants : Bool) (f : AnalyticSymbol) : Prop :=
  ∃ n : ℕ, ∃ c : Fin n → ℂ, ∃ lam : Fin n → ℂ,
    (∀ j, lam j ∈ L) ∧ ∃ c0 : ℂ, (constants = false → c0 = 0) ∧
      EqOn f (fun z => c0 + ∑ j, c j * resolventSymbol (lam j) z) S

/-- Localized derivative integral in Lemma 3.5. -/
def localDerivative (f : AnalyticSymbol) (r delta : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioo 0 delta, ⨆ b : {b : ℝ // |b| ≤ r},
    ENNReal.ofReal ‖deriv f (point a b.1)‖

/-- Exactly the three sequence assumptions of Lemma 3.5; no limit membership. -/
def BConvergence (fs : ℕ → AnalyticSymbol) (f : AnalyticSymbol) : Prop :=
  (∀ n, BesovClass (fs n)) ∧ (∃ C : ℝ, ∀ n, bSize (fs n) ≤ ENNReal.ofReal C) ∧
  (∀ z ∈ hp, Tendsto (fun n => fs n z) atTop (𝓝 (f z))) ∧
  ∀ r : ℝ, 0 < r → ∀ eps : ℝ, 0 < eps → ∃ d : ℝ, 0 < d ∧
    ∀ delta : ℝ, 0 < delta → delta < d → ∀ n,
      localDerivative (fs n) r delta < ENNReal.ofReal eps

/-- The holomorphic arccot branch (3.2). -/
def arccot (z : ℂ) : ℂ := (2 * Complex.I)⁻¹ *
  Complex.log ((z + Complex.I) / (z - Complex.I))

/-- The continuous right-half-plane arccot value at zero is pi/2. -/
def arccotZero (z : ℂ) : ℂ := if z = 0 then (Real.pi / 2 : ℝ) else arccot z

/-- Continuous value of sinh(zt)/t at t=0 (Example 3.3). -/
def sinhQuotient (z : ℂ) (t : ℝ) : ℂ :=
  if t = 0 then z else Complex.sinh (z * (t : ℂ)) / (t : ℂ)

/-- Cayley symbol. -/
def scalarCayley (z : ℂ) : ℂ := (z - 1) / (z + 1)

/-- The regularized inverse-exponential symbol preceding Proposition 3.19. -/
def phiSymbol (t : ℝ) (z : ℂ) : ℂ := z / (z + 1) * Complex.exp (-(t : ℂ) / z)

/-- Euler's beta integral on its positive-parameter domain. -/
def betaValue (a b : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, Real.rpow t (a - 1) * Real.rpow (1 - t) (b - 1)

/-- The boundary average (4.11), defined through continuous native traces. -/
def boundaryAverage (psi : ℝ) (f : AnalyticSymbol) (t : ℝ) : ℂ :=
  (extension (openSectorDomain psi) f (Complex.exp (Complex.I * psi) * (t : ℂ)) +
    extension (openSectorDomain psi) f (Complex.exp (-Complex.I * psi) * (t : ℂ))) / 2

/-- Structural sanity checks on source-domain operations and finite sums. -/
example (a b : ℝ) : (point a b).re = a := by simp [point]

example : (0 : ℂ) ∉ hp := by simp [hp]

example : (1 : ℂ) ∈ hp := by simp [hp]

example (S : Set ℂ) (f : AnalyticSymbol) (z : ℂ) (hz : z ∈ S) :
    extension S f z = f z := by simp [extension, hz]

example (z : ℂ) : sinhQuotient z 0 = z := by simp [sinhQuotient]

example : arccotZero 0 = (Real.pi / 2 : ℝ) := by simp [arccotZero]

example : supSize hp (0 : AnalyticSymbol) = 0 := by simp [supSize]

example : bSemi (0 : AnalyticSymbol) = 0 := by simp [bSemi]

example (s : ℝ) : dSemi s (0 : AnalyticSymbol) = 0 := by simp [dSemi, vSize]

example (psi : ℝ) : hardySize psi (0 : AnalyticSymbol) = 0 := by simp [hardySize]

example (s : ℝ) (z : ℂ) : Qs s 0 z = 0 := by simp [Qs, qsKernel]

example (z : ℂ) : besovPrimitive 0 z = 0 := by simp [besovPrimitive, qKernel]

universe u

section Operators

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Closed densely defined complex-linear operators, represented by their actual
single-valued graph. No semigroup or dense-range hypothesis is built in (p.4). -/
structure DenseClosedGraphOperator (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  graph : Submodule ℂ (X × X)
  graphClosed : IsClosed (graph : Set (X × X))
  singleValued : ∀ x y y2, (x, y) ∈ graph → (x, y2) ∈ graph → y = y2
  domainDense : Dense {x | ∃ y, (x, y) ∈ graph}

/-- A bounded two-sided inverse of z+A, on the actual graph domain. -/
def InverseAt (A : DenseClosedGraphOperator X) (z : ℂ) (R : X →L[ℂ] X) : Prop :=
  (∀ x, (R x, x - z • R x) ∈ A.graph) ∧
    ∀ x y, (x, y) ∈ A.graph → R (z • x + y) = x

/-- A concrete resolvent selector, with an irrelevant fallback off the resolvent set. -/
def plusResolvent (A : DenseClosedGraphOperator X) (z : ℂ) : X →L[ℂ] X :=
  if h : ∃ R, InverseAt A z R then Classical.choose h else 0

/-- Spectrum of A, with the sign appropriate to the z+A resolvent. -/
def operatorSpectrum (A : DenseClosedGraphOperator X) : Set ℂ :=
  {z | ¬ ∃ R : X →L[ℂ] X, InverseAt A (-z) R}

/-- Sectoriality of angle theta uses the CLOSED sector and all larger angles. -/
def SectorialAtAngle (theta : ℝ) (A : DenseClosedGraphOperator X) : Prop :=
  0 ≤ theta ∧ theta < Real.pi ∧ operatorSpectrum A ⊆ closure (openSectorDomain theta) ∧
  ∀ psi : ℝ, theta < psi → psi < Real.pi → ∃ C : ℝ, 0 ≤ C ∧
    ∀ z ∈ openSectorDomain (Real.pi - psi), ‖z • plusResolvent A z‖ ≤ C

/-- The strict pi/2-minus class. -/
def SectorialBelow (A : DenseClosedGraphOperator X) : Prop :=
  ∃ theta : ℝ, 0 ≤ theta ∧ theta < Real.pi / 2 ∧ SectorialAtAngle theta A

/-- M_A with its genuine extended supremum (2.2). -/
def mSize (A : DenseClosedGraphOperator X) : ℝ≥0∞ :=
  ⨆ z : hp, ENNReal.ofReal ‖(z : ℂ) • plusResolvent A z‖

/-- Scalar GSF integral for the square resolvent. -/
def gsfSlice (A : DenseClosedGraphOperator X) (x : X) (ell : X →L[ℂ] ℂ)
    (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ b, ENNReal.ofReal ‖ell ((plusResolvent A (point a b))
    ((plusResolvent A (point a b)) x))‖ ∂volume

/-- Exactly the pointwise GSF assumptions (3.12), without adding a supplied
uniform GSF constant or semigroup as a hypothesis. -/
def GSF (A : DenseClosedGraphOperator X) : Prop :=
  operatorSpectrum A ⊆ closedHp ∧
  ∀ x : X, ∀ ell : X →L[ℂ] ℂ,
    (⨆ a : {a : ℝ // 0 < a}, ENNReal.ofReal a.1 * gsfSlice A x ell a.1) < ⊤

/-- Least uniform GSF constant as an extended supremum over the two unit balls.
The factor 2/pi is NOT part of gamma_A in (3.14). -/
def gammaSize (A : DenseClosedGraphOperator X) : ℝ≥0∞ :=
  ⨆ x : {x : X // ‖x‖ ≤ 1}, ⨆ ell : {ell : X →L[ℂ] ℂ // ‖ell‖ ≤ 1},
    ⨆ a : {a : ℝ // 0 < a}, ENNReal.ofReal a.1 * gsfSlice A x.1 ell.1 a.1

/-- Integrand of the actual weak operator formula (3.15). -/
def weakKernel (A : DenseClosedGraphOperator X) (f : AnalyticSymbol) (x : X)
    (ell : X →L[ℂ] ℂ) (a b : ℝ) : ℂ :=
  (a : ℂ) * ell ((plusResolvent A (point a (-b)))
    ((plusResolvent A (point a (-b))) x)) * deriv f (point a b)

/-- The scalar formula is fixed before any operator is asserted to exist. -/
def weakBValue (A : DenseClosedGraphOperator X) (f : AnalyticSymbol) (x : X)
    (ell : X →L[ℂ] ℂ) : ℂ :=
  infinityValue f * ell x - (2 / (Real.pi : ℂ)) *
    ∫ a, ∫ b, weakKernel A f x ell a b ∂volume ∂positiveVolume

/-- Representation in X, as opposed to a merely bidual-valued weak formula. -/
def RealizesB (A : DenseClosedGraphOperator X) (f : AnalyticSymbol) (F : X →L[ℂ] X) : Prop :=
  ∀ x : X, ∀ ell : X →L[ℂ] ℂ,
    AbsoluteDouble (weakKernel A f x ell) ∧ ell (F x) = weakBValue A f x ell

/-- Canonical value of (3.15) when it is represented by a bounded X-valued
operator; existence is a conclusion of Theorem 3.13. -/
def bOperator (A : DenseClosedGraphOperator X) (f : AnalyticSymbol) : X →L[ℂ] X :=
  if h : ∃ F, RealizesB A f F then Classical.choose h else 0

/-- Algebra homomorphism on native-domain symbols, with domain extensionality. -/
def AlgebraMapOn (S : Set ℂ) (F : AnalyticSymbol → X →L[ℂ] X) (A : AnalyticSymbol → Prop) : Prop :=
  F 0 = 0 ∧ F 1 = ContinuousLinearMap.id ℂ X ∧
  (∀ f g, A f → A g → EqOn f g S → F f = F g) ∧
  (∀ f g, A f → A g → F (f + g) = F f + F g) ∧
  (∀ c : ℂ, ∀ f, A f → F (c • f) = c • F f) ∧
  ∀ f g, A f → A g → F (f * g) = (F f).comp (F g)

/-- Boundedness on a source symbol space, with a uniform constant. -/
def BoundedMapOn (F : AnalyticSymbol → X →L[ℂ] X) (A : AnalyticSymbol → Prop)
    (N : AnalyticSymbol → ℝ≥0∞) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f, A f → ENNReal.ofReal ‖F f‖ ≤ ENNReal.ofReal C * N f

/-- A B-calculus as defined on p.4, with its resolvent normalization. -/
def BCalculus (A : DenseClosedGraphOperator X) (F : AnalyticSymbol → X →L[ℂ] X) : Prop :=
  AlgebraMapOn hp F BesovClass ∧ BoundedMapOn F BesovClass bSize ∧
    ∀ lam ∈ hp, F (resolventSymbol lam) = plusResolvent A lam

/-- Bounded C0-semigroup data, reusing the accepted predicate (source pp.4--5).
The subtype only packages its time map with that predicate; it adds no axioms. -/
abbrev C0SemigroupData (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] :=
  {T : ℝ → X →L[ℂ] X // QAlgorithms.Papers.Independent.Gap48.P07.BoundedC0 T}

example (T : C0SemigroupData X) :
    QAlgorithms.Papers.Independent.Gap48.P07.BoundedC0 T.val := T.property

/-- Generator graph with the paper's negative-generator convention. -/
def Generates (T : C0SemigroupData X) (A : DenseClosedGraphOperator X) : Prop :=
  ∀ x y : X, (x, y) ∈ A.graph ↔
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (T.val t x - x))
      (𝓝[>] 0) (𝓝 (-y))

/-- Exact HP agreement for every finite COMPLEX measure, using a positive
control measure and a complex density as above. -/
def HPCompatible (T : C0SemigroupData X) (F : AnalyticSymbol → X →L[ℂ] X) : Prop :=
  ∀ mu w f, LaplaceRep mu w f → ∀ x : X,
    Integrable (fun t => w t • T.val t x) mu ∧
      F f x = ∫ t, w t • T.val t x ∂mu

/-- Hilbert structure for the SAME complex normed-space structure as the
operators. Equality of the inherited NormedSpace also fixes complex scalars. -/
def HilbertNorm (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] : Prop :=
  ∃ h : InnerProductSpace ℂ X,
    h.toNormedSpace = (inferInstance : NormedSpace ℂ X)

example {Y : Type u} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] :
    HilbertNorm Y := by
  exact ⟨inferInstance, rfl⟩

/-- The bounded Hilbert-semigroup regime, without imposing it on Banach clauses. -/
def HilbertGenerator (A : DenseClosedGraphOperator X) : Prop :=
  HilbertNorm X ∧ ∃ T : C0SemigroupData X, Generates T A

/-- Operator-norm integrand of Theorem 4.1. -/
def besovOperatorIntegrand (A : DenseClosedGraphOperator X) (f : AnalyticSymbol) (a b : ℝ) : X →L[ℂ] X :=
  ((a : ℂ) * deriv f (point a b)) •
    (plusResolvent A (point a (-b))).comp (plusResolvent A (point a (-b)))

/-- Absolute convergence in operator norm, rather than only weak convergence. -/
def AbsoluteOperatorDouble (F : ℝ → ℝ → X →L[ℂ] X) : Prop :=
  AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
    (positiveVolume.prod volume) ∧
  (∫⁻ a, ∫⁻ b, ENNReal.ofReal ‖F a b‖ ∂volume ∂positiveVolume) < ⊤

/-- The eigenfunctional condition for the BANACH transpose: no conjugation. -/
def TransposeEigen (A : DenseClosedGraphOperator X) (lam : ℂ) (ell : X →L[ℂ] ℂ) : Prop :=
  ∀ x y : X, (x, y) ∈ A.graph → ell y = lam * ell x

/-- The concrete Cayley transform I-2(1+A)^(-1). -/
def operatorCayley (A : DenseClosedGraphOperator X) : X →L[ℂ] X :=
  ContinuousLinearMap.id ℂ X - (2 : ℂ) • plusResolvent A 1

example (A : DenseClosedGraphOperator X) (z : ℂ) (h : ¬ ∃ R, InverseAt A z R) :
    plusResolvent A z = 0 := by simp [plusResolvent, h]

example (A : DenseClosedGraphOperator X) (f : AnalyticSymbol) (x : X) :
    weakKernel A f x (0 : X →L[ℂ] ℂ) = 0 := by
  funext a b
  simp [weakKernel]

end Operators

/- BEGIN PAPER STATEMENTS -/

end QAlgorithms.Papers.Independent.Intakenext100.P35


