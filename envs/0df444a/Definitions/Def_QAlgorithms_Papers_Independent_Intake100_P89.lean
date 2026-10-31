-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89
-- name    : QAlgorithms_Papers_Independent_Intake100_P89
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T15:31:48.494835+00:00
-- url     : https://prove2.me/theorems/94a15958-a21b-4377-b0d4-093155fce578
-- title:
--   Definitions for Reproducing kernel Hilbert spaces of Gaussian priors
-- statement:
--   The objects the formalized statements of *Reproducing kernel Hilbert spaces of Gaussian priors* (arXiv:0805.3252) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `L2`: PDF p.3: the real L² space on the source probability space, modulo a.e. equality.
--   - `toL2`: PDF p.3: the L² class of a square-integrable variable. The zero outside-domain value is never used for a coordinate of a source Gaussian process.
--   - `borelLaw`: PDF p.4: Banach-valued laws use exactly the Borel sigma algebra.
--   - `CenteredProcess`: PDF p.3: all finite linear combinations have a centered Gaussian law, including variance zero. This is the finite-dimensional Gaussian convention.
--   - `BorelCenteredGaussianElement`: PDF p.4: a Borel centered Gaussian random element. Norm moments are consequences, and are deliberately not additional hypotheses.
--   - `processCovariance`: PDF p.3: the covariance kernel, with its original ordering.
--   - `processChaos`: PDF p.3: the closed first-order chaos, a concrete Hilbert completion of finite coordinate combinations in the covariance norm.
--   - `processSynthesis`: PDF p.3: the canonical embedding of the process completion into functions.
--   - `processRKHS`: PDF p.3: the function realization of the covariance RKHS. The underlying completion is `processChaos`, not a freely supplied Hilbert space.
--   - `processLift`: PDF pp.3,8: the canonical first-chaos coordinate U(f). Off the RKHS the value is zero. Injectivity on the chaos is asserted below, so there is no noncanonical choice on the source domain.
--   - `processInner`: PDF p.3, (2.2): the extended covariance inner product. Used only on RKHS members.
--   - `processNorm`: PDF p.3: the RKHS norm in the completion, used only on RKHS members.
--   - `analysisMap`: PDF p.5: A sends a continuous real functional to its L² evaluation class.
--   - `banachChaos`: PDF pp.4–5: the Hilbert completion of the covariance range, represented by the closure of its isometric image A(B*).
--   - `synthesis`: PDF p.5: the actual Pettis synthesis A*, implemented by its Bochner integral. For source Gaussian W and h in L² the integrand is integrable.
--   - `covarianceMap`: PDF p.4: the B-valued covariance S(l)=E[W l(W)].
--   - `banachRKHS`: PDF pp.4–5: canonical function realization of the Banach covariance completion.
--   - `banachLift`: PDF p.9, (3.3): the canonical chaos coordinate U(b), zero off its domain.
--   - `banachInner`: PDF p.4: the Hilbert inner product, not the ambient Banach pairing.
--   - `banachNorm`: PDF pp.4–5: the RKHS norm, used only on members.
--   - `rkhsUnitBall`: PDF pp.5–6: the closed Hilbert unit ball embedded in B.
--   - `weakSigma`: PDF p.4: weak standard deviation using the closed dual unit ball. This agrees with the source sphere supremum for nontrivial B, and also covers B={0}.
--   - `dualEvaluationTopology`: PDF p.5: the topology of pointwise convergence on B, namely weak-*.
--   - `NormCompact`: PDF p.6: compactness for the norm topologies, in the source's bounded-set form.
--   - `supportSet`: PDF p.14: support characterized by positive probability in every open ball.
--   - `smallBall`: PDF pp.14–17: centered small-ball exponent. For positive radius Gaussian small balls have positive mass; no logarithm-of-zero convention is used below.
--   - `rkhsConcentration`: PDF p.16, (5.1): concentration function with a CLOSED approximation constraint. For centers in the support and positive radius the feasible set is nonempty and bounded below, as recorded in the sandwich statement.
--   - `normalEnlargement`: PDF pp.14–15: Phi(Phi^{-1}(p)+m), with its continuous endpoint values. The p=1 branch is essential for the identically zero Gaussian law.
--   - `normMedian`: PDF p.15: the uniquely determined median of a nonzero Gaussian norm law.
--   - `HasCover`: PDF p.17: covering number by ambient open norm balls. Infinity is represented by an empty minimization predicate; at the positive source radii finite covers exist, and the entropy statements explicitly retain this condition.
--   - `logCover`: PDF p.17: log of the least finite covering cardinal. The caller must establish existence of a finite cover; otherwise the explicit default is zero.
--   - `AtZeroLE`: PDF p.17: comparison as epsilon decreases to zero; constants precede epsilon.
--   - `AtZeroComparable`: PDF p.17: two-sided asymptotic comparison, with positive constants.
--   - `RegularAtZero`: PDF p.17: measurable positive regular variation at zero, in ratio form.
--   - `powerLog`: PDF p.17: the power-log rate; comparisons only use sufficiently small positive e.
--   - `series`: PDF p.12: deterministic l² synthesis, with convergence established by the series theorem rather than assumed in this definition.
--   - `StandardNormals`: PDF p.12: iid standard normals, including measurability of every representative.
--   - `SeqL2`: PDF pp.12–13: the deterministic coefficient Hilbert space.
--   - `dualCoefficients`: PDF p.13: dual evaluations in the coefficient Hilbert space, with zero only outside their l² domain, which Gaussian convergence excludes.
--   - `identifiableCoefficientSubspace`: PDF p.13: identifiable coefficient subspace for dependent directions.
--   - `Time`: PDF pp.19–22: the closed time interval and its Lebesgue measure.
--   - `timeMeasure`: PDF pp.19–22: Lebesgue measure transported to the interval subtype.
--   - `TimeL2`: PDF pp.19–22: L² derivatives on [0,1], as equivalence classes.
--   - `primitive`: PDF p.20: integration from zero, defined on representatives; L² integrals are unchanged by a.e. replacement of their representative.
--   - `iterPrimitive`: PDF p.20: the zeroth iterate is the identity.
--   - `polynomialReal`: PDF p.13: factorial-normalized polynomial, of degree AT MOST k.
--   - `sobolevPath`: PDF pp.20–21: the Sobolev integral parametrization. The jet is the list of initial derivatives; g is the a.e. (k+1)st derivative. This is exactly C^k with AC kth derivative and L² derivative, with no zero-boundary requirement.
--   - `StandardBrownian`: PDF pp.19–20: the continuous version of standard Brownian motion, pinned by its centered Gaussian law and min(s,t) covariance.
--   - `fractionalIntegral`: PDF p.21: Gamma-normalized deterministic fractional integration.
--   - `RiemannLiouville`: PDF p.21: the complete covariance-law characterization of the continuous Riemann–Liouville process. It does not claim a coupling with an unspecified Ito integral. Gaussian RKHSs depend only on this kernel.
--   - `RKHSSum`: PDF pp.18–19: the full orthogonal direct-sum conclusion, including uniqueness.
--   - `supportSpace`: PDF pp.18–19: the closed support subspace, constructed from the law. For a centered Gaussian law this equals the support itself (Lemma 5.1).
--   - `SupportProjection`: PDF pp.18–19: a continuous projection onto the first closed support, whose kernel contains the second support.
--   - `StrictUniformDistance`: PDF p.22: strict uniform approximation, without totalizing an unbounded sup. For bounded functions on the interval this is exactly ||f-g||_infinity < e.
--   - `wienerIntegral`: PDF p.21: the canonical deterministic Wiener integral, obtained by inverting Brownian covariance synthesis on primitives. For standard Brownian W the Cameron–Martin characterization identifies this with the L²-continuous extension of step-function stochastic integrals.
--   - `rlKernel`: PDF p.21: the deterministic kernel of the Riemann–Liouville Wiener integral. The strict interval eliminates any endpoint ambiguity for negative powers.
--   - `rlPath`: PDF p.21: a Borel continuous version of the actual Wiener-integral process, selected from its coordinate L² classes. Existence is a conclusion below, not a field supplied by a caller; zero is only an outside-domain fallback.
--   - `FractionalDomain`: PDF p.21: existence of the Lebesgue fractional integrals on the whole interval.
--   - `IteratedIntegralDomain`: PDF p.21: the common domain of the k successive ordinary primitives.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, https://arxiv.org/abs/0805.3252v1

import Mathlib

/-!
# Reproducing kernel Hilbert spaces of Gaussian priors

van der Vaart–van Zanten, arXiv:0805.3252v1. Paper-local constructions only.
The completion of the covariance range is realized as the closed span of its
isometric L² image; its embedding is the covariance integral. This realization
retains equivalence classes and does not impose any sample-path topology on an
arbitrary-index process. Source defects and deferred nodes are in HARD.md.
Compilation is pending the explicitly requested batch handoff.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

/-- PDF p.3: the real L² space on the source probability space, modulo a.e. equality. -/
abbrev L2 (P : Measure Omega) := MeasureTheory.Lp ℝ 2 P

/-- PDF p.3: the L² class of a square-integrable variable. The zero outside-domain
value is never used for a coordinate of a source Gaussian process. -/
def toL2 (P : Measure Omega) (X : Omega → ℝ) : L2 P := by
  classical
  exact if h : MemLp X 2 P then h.toLp X else 0

/-- PDF p.4: Banach-valued laws use exactly the Borel sigma algebra. -/
def borelLaw {B : Type*} [TopologicalSpace B] (P : Measure Omega) (W : Omega → B) :
    @Measure B (borel B) := @Measure.map Omega B _ (borel B) W P

/-- PDF p.3: all finite linear combinations have a centered Gaussian law,
including variance zero. This is the finite-dimensional Gaussian convention. -/
def CenteredProcess {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ) : Prop :=
  (∀ t, Measurable (W t)) ∧
  ∀ (n : ℕ) (t : Fin n → T) (a : Fin n → ℝ),
    ∃ variance : NNReal,
      P.map (fun o => ∑ i, a i * W (t i) o) = gaussianReal 0 variance

/-- PDF p.4: a Borel centered Gaussian random element. Norm moments are
consequences, and are deliberately not additional hypotheses. -/
def BorelCenteredGaussianElement {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) : Prop :=
  @Measurable Omega B _ (borel B) W ∧
  ∀ l : B →L[ℝ] ℝ, ∃ variance : NNReal,
    P.map (fun o => l (W o)) = gaussianReal 0 variance

/-- PDF p.3: the covariance kernel, with its original ordering. -/
def processCovariance {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ) (s t : T) : ℝ :=
  ∫ o, W s o * W t o ∂P

/-- PDF p.3: the closed first-order chaos, a concrete Hilbert completion of
finite coordinate combinations in the covariance norm. -/
def processChaos {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ) :
    Submodule ℝ (L2 P) :=
  (Submodule.span ℝ (Set.range (fun t => toL2 P (W t)))).topologicalClosure

/-- PDF p.3: the canonical embedding of the process completion into functions. -/
def processSynthesis {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ)
    (h : L2 P) : T → ℝ := fun t => ∫ o, W t o * h o ∂P

/-- PDF p.3: the function realization of the covariance RKHS. The underlying
completion is `processChaos`, not a freely supplied Hilbert space. -/
def processRKHS {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ) : Set (T → ℝ) :=
  {f | ∃ h : processChaos P W, processSynthesis P W (h : L2 P) = f}

/-- PDF pp.3,8: the canonical first-chaos coordinate U(f). Off the RKHS the
value is zero. Injectivity on the chaos is asserted below, so there is no
noncanonical choice on the source domain. -/
def processLift {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ)
    (f : T → ℝ) : L2 P := by
  classical
  exact if h : ∃ g : processChaos P W, processSynthesis P W (g : L2 P) = f
    then (Classical.choose h).val else 0

/-- PDF p.3, (2.2): the extended covariance inner product. Used only on RKHS members. -/
def processInner {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ)
    (f g : T → ℝ) : ℝ := inner ℝ (processLift P W f) (processLift P W g)

/-- PDF p.3: the RKHS norm in the completion, used only on RKHS members. -/
def processNorm {T : Type v} (P : Measure Omega) (W : T → Omega → ℝ)
    (f : T → ℝ) : ℝ := ‖processLift P W f‖

/-- PDF p.5: A sends a continuous real functional to its L² evaluation class. -/
def analysisMap {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) (l : B →L[ℝ] ℝ) : L2 P :=
  toL2 P (fun o => l (W o))

/-- PDF pp.4–5: the Hilbert completion of the covariance range, represented
by the closure of its isometric image A(B*). -/
def banachChaos {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) : Submodule ℝ (L2 P) :=
  (Submodule.span ℝ (Set.range (analysisMap P W))).topologicalClosure

/-- PDF p.5: the actual Pettis synthesis A*, implemented by its Bochner integral.
For source Gaussian W and h in L² the integrand is integrable. -/
def synthesis {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) (h : L2 P) : B :=
  ∫ o, h o • W o ∂P

/-- PDF p.4: the B-valued covariance S(l)=E[W l(W)]. -/
def covarianceMap {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) (l : B →L[ℝ] ℝ) : B :=
  ∫ o, l (W o) • W o ∂P

/-- PDF pp.4–5: canonical function realization of the Banach covariance completion. -/
def banachRKHS {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) : Set B :=
  {b | ∃ h : banachChaos P W, synthesis P W (h : L2 P) = b}

/-- PDF p.9, (3.3): the canonical chaos coordinate U(b), zero off its domain. -/
def banachLift {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) (b : B) : L2 P := by
  classical
  exact if h : ∃ g : banachChaos P W, synthesis P W (g : L2 P) = b
    then (Classical.choose h).val else 0

/-- PDF p.4: the Hilbert inner product, not the ambient Banach pairing. -/
def banachInner {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) (b c : B) : ℝ :=
  inner ℝ (banachLift P W b) (banachLift P W c)

/-- PDF pp.4–5: the RKHS norm, used only on members. -/
def banachNorm {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) (b : B) : ℝ := ‖banachLift P W b‖

/-- PDF pp.5–6: the closed Hilbert unit ball embedded in B. -/
def rkhsUnitBall {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) : Set B :=
  {b | b ∈ banachRKHS P W ∧ banachNorm P W b ≤ 1}

/-- PDF p.4: weak standard deviation using the closed dual unit ball. This
agrees with the source sphere supremum for nontrivial B, and also covers B={0}. -/
def weakSigma {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) : ℝ :=
  Real.sqrt (sSup {r : ℝ | ∃ l : B →L[ℝ] ℝ, ‖l‖ ≤ 1 ∧
    r = ∫ o, (l (W o)) ^ 2 ∂P})

/-- PDF p.5: the topology of pointwise convergence on B, namely weak-*. -/
def dualEvaluationTopology (B : Type v) [NormedAddCommGroup B] [NormedSpace ℝ B] :
    TopologicalSpace (B →L[ℝ] ℝ) :=
  TopologicalSpace.induced (fun l : B →L[ℝ] ℝ => fun b : B => l b) inferInstance

/-- PDF p.6: compactness for the norm topologies, in the source's bounded-set form. -/
def NormCompact {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (f : E → F) : Prop :=
  ∀ s : Set E, Bornology.IsBounded s → IsCompact (closure (f '' s))

/-- PDF p.14: support characterized by positive probability in every open ball. -/
def supportSet {B : Type v} [NormedAddCommGroup B] (P : Measure Omega)
    (W : Omega → B) : Set B :=
  {b | ∀ r : ℝ, 0 < r → 0 < P {o | dist (W o) b < r}}

/-- PDF pp.14–17: centered small-ball exponent. For positive radius Gaussian
small balls have positive mass; no logarithm-of-zero convention is used below. -/
def smallBall {B : Type v} [NormedAddCommGroup B]
    (P : Measure Omega) (W : Omega → B) (r : ℝ) : ℝ :=
  -Real.log ((P {o | ‖W o‖ < r}).toReal)

/-- PDF p.16, (5.1): concentration function with a CLOSED approximation constraint.
For centers in the support and positive radius the feasible set is nonempty and
bounded below, as recorded in the sandwich statement. -/
def rkhsConcentration {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) (b : B) (r : ℝ) : ℝ :=
  sInf {q : ℝ | ∃ h ∈ banachRKHS P W,
    ‖h - b‖ ≤ r ∧ q = (banachNorm P W h) ^ 2 / 2} + smallBall P W r

/-- PDF pp.14–15: Phi(Phi^{-1}(p)+m), with its continuous endpoint values.
The p=1 branch is essential for the identically zero Gaussian law. -/
def normalEnlargement (p m : ℝ) : ℝ := by
  classical
  exact if p ≤ 0 then 0 else if 1 ≤ p then 1 else
    (cdf (gaussianReal 0 1)) ((sInf {x : ℝ | p ≤ (cdf (gaussianReal 0 1)) x}) + m)

/-- PDF p.15: the uniquely determined median of a nonzero Gaussian norm law. -/
def normMedian {B : Type v} [NormedAddCommGroup B]
    (P : Measure Omega) (W : Omega → B) : ℝ :=
  sInf {r : ℝ | (1 / 2 : ℝ) ≤ (P {o | ‖W o‖ ≤ r}).toReal}

/-- PDF p.17: covering number by ambient open norm balls. Infinity is represented
by an empty minimization predicate; at the positive source radii finite covers
exist, and the entropy statements explicitly retain this condition. -/
def HasCover {B : Type v} [NormedAddCommGroup B] (s : Set B) (r : ℝ) (n : ℕ) : Prop :=
  ∃ centers : Fin n → B, ∀ x ∈ s, ∃ i, dist x (centers i) < r

/-- PDF p.17: log of the least finite covering cardinal. The caller must establish
existence of a finite cover; otherwise the explicit default is zero. -/
def logCover {B : Type v} [NormedAddCommGroup B] (s : Set B) (r : ℝ) : ℝ := by
  classical
  exact if h : ∃ n, HasCover s r n then Real.log (Nat.find h) else 0

/-- PDF p.17: comparison as epsilon decreases to zero; constants precede epsilon. -/
def AtZeroLE (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
    ∀ e : ℝ, 0 < e → e < r → f e ≤ C * g e

/-- PDF p.17: two-sided asymptotic comparison, with positive constants. -/
def AtZeroComparable (f g : ℝ → ℝ) : Prop := AtZeroLE f g ∧ AtZeroLE g f

/-- PDF p.17: measurable positive regular variation at zero, in ratio form. -/
def RegularAtZero (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 < x → 0 < f x) ∧
  ∃ rho : ℝ, ∀ a : ℝ, 0 < a →
    Tendsto (fun x => f (a * x) / f x) (nhdsWithin 0 (Ioi 0)) (𝓝 (a ^ rho))

/-- PDF p.17: the power-log rate; comparisons only use sufficiently small positive e. -/
def powerLog (a b e : ℝ) : ℝ := e ^ (-a) * (Real.log (1 / e)) ^ b

/-- PDF p.12: deterministic l² synthesis, with convergence established by the
series theorem rather than assumed in this definition. -/
def series {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (h : ℕ → B) (w : ℕ → ℝ) : B := ∑' i, w i • h i

/-- PDF p.12: iid standard normals, including measurability of every representative. -/
def StandardNormals {I : Type v} (P : Measure Omega) (Z : I → Omega → ℝ) : Prop :=
  iIndepFun Z P ∧ ∀ i, Measurable (Z i) ∧ P.map (Z i) = gaussianReal 0 1

/-- PDF pp.12–13: the deterministic coefficient Hilbert space. -/
abbrev SeqL2 := lp (fun _ : ℕ => ℝ) 2

/-- PDF p.13: dual evaluations in the coefficient Hilbert space, with zero only
outside their l² domain, which Gaussian convergence excludes. -/
def dualCoefficients {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (h : ℕ → B) (l : B →L[ℝ] ℝ) : SeqL2 := by
  classical
  exact if hm : Memℓp (fun i => l (h i)) 2 then ⟨fun i => l (h i), hm⟩ else 0

/-- PDF p.13: identifiable coefficient subspace for dependent directions. -/
def identifiableCoefficientSubspace {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (h : ℕ → B) : Submodule ℝ SeqL2 :=
  (Submodule.span ℝ (Set.range (dualCoefficients h))).topologicalClosure

/-- PDF pp.19–22: the closed time interval and its Lebesgue measure. -/
abbrev Time := Set.Icc (0 : ℝ) 1

/-- PDF pp.19–22: Lebesgue measure transported to the interval subtype. -/
def timeMeasure : Measure Time :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).comap Subtype.val

/-- PDF pp.19–22: L² derivatives on [0,1], as equivalence classes. -/
abbrev TimeL2 := MeasureTheory.Lp ℝ 2 timeMeasure

/-- PDF p.20: integration from zero, defined on representatives; L² integrals
are unchanged by a.e. replacement of their representative. -/
def primitive (f : Time → ℝ) (t : Time) : ℝ :=
  ∫ s in {s : Time | (s : ℝ) ≤ (t : ℝ)}, f s ∂timeMeasure

/-- PDF p.20: the zeroth iterate is the identity. -/
def iterPrimitive (k : ℕ) (f : Time → ℝ) : Time → ℝ := (primitive^[k]) f

/-- PDF p.13: factorial-normalized polynomial, of degree AT MOST k. -/
def polynomialReal (k : ℕ) (a : Fin (k + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, a i * t ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ)

/-- PDF pp.20–21: the Sobolev integral parametrization. The jet is the list of
initial derivatives; g is the a.e. (k+1)st derivative. This is exactly C^k with
AC kth derivative and L² derivative, with no zero-boundary requirement. -/
def sobolevPath (k : ℕ) (a : Fin (k + 1) → ℝ) (g : TimeL2) : Time → ℝ :=
  fun t => polynomialReal k a (t : ℝ) + iterPrimitive (k + 1) g t

/-- PDF pp.19–20: the continuous version of standard Brownian motion, pinned
by its centered Gaussian law and min(s,t) covariance. -/
def StandardBrownian (P : Measure Omega) (W : Omega → C(Time, ℝ)) : Prop :=
  BorelCenteredGaussianElement P W ∧ ∀ s t : Time,
    processCovariance P (fun t o => W o t) s t = min (s : ℝ) (t : ℝ)

/-- PDF p.21: Gamma-normalized deterministic fractional integration. -/
def fractionalIntegral (a : ℝ) (f : Time → ℝ) (t : Time) : ℝ :=
  (Real.Gamma a)⁻¹ *
    ∫ s in {s : Time | (s : ℝ) < (t : ℝ)},
      ((t : ℝ) - (s : ℝ)) ^ (a - 1) * f s ∂timeMeasure

/-- PDF p.21: the complete covariance-law characterization of the continuous
Riemann–Liouville process. It does not claim a coupling with an unspecified Ito
integral. Gaussian RKHSs depend only on this kernel. -/
def RiemannLiouville (P : Measure Omega) (a : ℝ)
    (R : Omega → C(Time, ℝ)) : Prop :=
  BorelCenteredGaussianElement P R ∧ ∀ s t : Time,
    processCovariance P (fun t o => R o t) s t =
      ∫ z in {z : Time | (z : ℝ) < min (s : ℝ) (t : ℝ)},
        ((s : ℝ) - (z : ℝ)) ^ (a - 1 / 2) *
          ((t : ℝ) - (z : ℝ)) ^ (a - 1 / 2) ∂timeMeasure

/-- PDF pp.18–19: the full orthogonal direct-sum conclusion, including uniqueness. -/
def RKHSSum {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (V W : Omega → B) : Prop :=
  banachRKHS P (fun o => V o + W o) =
    {b | ∃ v ∈ banachRKHS P V, ∃ w ∈ banachRKHS P W, b = v + w} ∧
  (∀ v ∈ banachRKHS P V, ∀ w ∈ banachRKHS P W,
    banachNorm P (fun o => V o + W o) (v + w) ^ 2 =
      banachNorm P V v ^ 2 + banachNorm P W w ^ 2) ∧
  (∀ v1 ∈ banachRKHS P V, ∀ w1 ∈ banachRKHS P W,
    ∀ v2 ∈ banachRKHS P V, ∀ w2 ∈ banachRKHS P W,
    v1 + w1 = v2 + w2 → v1 = v2 ∧ w1 = w2)

/-- Sanity: degree zero is the constant coefficient, including the zero polynomial. -/
example (a : Fin 1 → ℝ) (t : ℝ) : polynomialReal 0 a t = a 0 := by
  simp [polynomialReal]

/-- Sanity: integration order zero is literally the identity. -/
example (f : Time → ℝ) : iterPrimitive 0 f = f := rfl

/-- Sanity: a zero coefficient sequence synthesizes to zero. -/
example {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B] (h : ℕ → B) :
    series h (fun _ => 0) = 0 := by
  simp [series]

/-- Sanity: the Sobolev parametrization at k=0 is a constant plus a primitive. -/
example (a : Fin 1 → ℝ) (g : TimeL2) (t : Time) :
    sobolevPath 0 a g t = a 0 + primitive g t := by
  simp [sobolevPath, polynomialReal, iterPrimitive]

section ProcessResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

end ProcessResults

section BanachResults

variable {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [hComplete : CompleteSpace B] [hSeparable : TopologicalSpace.SeparableSpace B]
variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP hComplete hSeparable

end BanachResults

/-- PDF pp.18–19: the closed support subspace, constructed from the law.
For a centered Gaussian law this equals the support itself (Lemma 5.1). -/
def supportSpace {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (W : Omega → B) : Submodule ℝ B :=
  (Submodule.span ℝ (supportSet P W)).topologicalClosure

/-- PDF pp.18–19: a continuous projection onto the first closed support,
whose kernel contains the second support. -/
def SupportProjection {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (P : Measure Omega) (V W : Omega → B) : Prop :=
  ∃ pi : B →L[ℝ] B,
    (∀ b : B, pi b ∈ supportSpace P V) ∧
    (∀ b ∈ supportSpace P V, pi b = b) ∧
    (∀ b ∈ supportSpace P W, pi b = 0)

section MoreResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

end MoreResults

/-- PDF p.22: strict uniform approximation, without totalizing an unbounded sup.
For bounded functions on the interval this is exactly ||f-g||_infinity < e. -/
def StrictUniformDistance (f g : Time → ℝ) (e : ℝ) : Prop :=
  ∃ d : ℝ, d < e ∧ ∀ t : Time, |f t - g t| ≤ d

/-- PDF p.21: the canonical deterministic Wiener integral, obtained by inverting
Brownian covariance synthesis on primitives. For standard Brownian W the
Cameron–Martin characterization identifies this with the L²-continuous
extension of step-function stochastic integrals. -/
def wienerIntegral (P : Measure Omega) (W : Omega → C(Time, ℝ)) (g : TimeL2) : L2 P :=
  processLift P (fun t o => W o t) (primitive g)

/-- PDF p.21: the deterministic kernel of the Riemann–Liouville Wiener integral.
The strict interval eliminates any endpoint ambiguity for negative powers. -/
def rlKernel (a : ℝ) (t : Time) : TimeL2 :=
  toL2 timeMeasure (fun s : Time =>
    if (s : ℝ) < (t : ℝ) then ((t : ℝ) - (s : ℝ)) ^ (a - 1 / 2) else 0)

/-- PDF p.21: a Borel continuous version of the actual Wiener-integral process,
selected from its coordinate L² classes. Existence is a conclusion below, not
a field supplied by a caller; zero is only an outside-domain fallback. -/
def rlPath (P : Measure Omega) (W : Omega → C(Time, ℝ)) (a : ℝ) : Omega → C(Time, ℝ) := by
  classical
  exact if h : ∃ R : Omega → C(Time, ℝ),
      @Measurable Omega C(Time, ℝ) _ (borel C(Time, ℝ)) R ∧
      ∀ t : Time, MemLp (fun o => R o t) 2 P ∧
        toL2 P (fun o => R o t) = wienerIntegral P W (rlKernel a t)
    then Classical.choose h else fun _ => 0

/-- PDF p.21: existence of the Lebesgue fractional integrals on the whole interval. -/
def FractionalDomain (a : ℝ) (f : Time → ℝ) : Prop :=
  Measurable f ∧ ∀ t : Time, IntegrableOn
    (fun s : Time => ((t : ℝ) - (s : ℝ)) ^ (a - 1) * f s)
    {s : Time | (s : ℝ) < (t : ℝ)} timeMeasure

/-- PDF p.21: the common domain of the k successive ordinary primitives. -/
def IteratedIntegralDomain (k : ℕ) (f : Time → ℝ) : Prop :=
  Measurable f ∧ ∀ j : ℕ, j < k → ∀ t : Time,
    IntegrableOn (iterPrimitive j f) {s : Time | (s : ℝ) ≤ (t : ℝ)} timeMeasure

/-- Sanity: the Wiener kernel of Brownian motion is the interval indicator,
up to an irrelevant endpoint. -/
example (t s : Time) :
    (if (s : ℝ) < (t : ℝ) then ((t : ℝ) - (s : ℝ)) ^ ((1 / 2 : ℝ) - 1 / 2) else 0) =
      (if (s : ℝ) < (t : ℝ) then (1 : ℝ) else 0) := by
  simp

section PathResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89


