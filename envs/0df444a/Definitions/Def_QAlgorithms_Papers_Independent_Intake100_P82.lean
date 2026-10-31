-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82
-- name    : QAlgorithms_Papers_Independent_Intake100_P82
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T15:05:57.866979+00:00
-- url     : https://prove2.me/theorems/be9b02c8-134e-4469-88b8-58e694c63e21
-- title:
--   Definitions for Fluctuation Theorem and Thermodynamic Formalism
-- statement:
--   The objects the formalized statements of *Fluctuation Theorem and Thermodynamic Formalism* (arXiv:1712.05167) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `logSpeed`: Speed-n log probability, evaluated only for n >= 1 in limits. PDF p.13.
--   - `IsRate`: Nonnegative extended rate; goodness is deliberately separate. PDF p.13.
--   - `FullLDP`: Full Borel-set speed-n LDP, including interior and closure. PDF p.13.
--   - `GoodRate`: Compactness of every finite sublevel set. PDF p.27.
--   - `ExtendedRateConvex`: Convexity of an extended scalar function. PDF pp.14,27.
--   - `ReversalExperiment`: An arbitrary regular finite-time reversal experiment. PDF pp.11--12. There is no topology or finite entropy/moment assumption on its sample space.
--   - `reversedLaw`: Reversed probability. PDF p.11.
--   - `experimentLogDensity`: A real representative of the log RN derivative, defined up to null sets. Equivalence and finite probability ensure finite positive density a.e. PDF p.12.
--   - `entropicFunctional`: Extended Laplace integral: no Bochner default on divergent moments. PDF p.12.
--   - `productionLaw`: The law of finite-time entropy production. PDF p.12.
--   - `variationDistance`: Total variation in the source's probability normalization, at most one. PDF p.16; the supremum is over measurable events.
--   - `chernoffTerm`: Chernoff logarithmic error at time n. PDF p.16.
--   - `BoundedBorel`: B(M): pointwise bounded Borel functions, not essential boundedness. PDF p.18.
--   - `BorelSequence`: Positive-time sequence in B(M); the zero term is unused. PDF p.8.
--   - `supNorm`: Supremum norm, used below only for bounded functions on nonempty M. PDF p.18.
--   - `orbitSum`: Ergodic sum, with exactly the terms 0,...,n-1. PDF pp.3,18.
--   - `AdditiveApproximation`: (0.12)/(6.4), keeping the order k after limsup n. PDF pp.8,40.
--   - `ApproximatingFamily`: Continuous approximating family, with no bound assumed uniformly in k. PDF p.8.
--   - `AsymptoticallyAdditive`: Asymptotic additivity, including the Borel and boundedness domain. PDF p.8.
--   - `EquivalentPotentials`: Source equivalence (zero asymptotic seminorm), without pressure normalization. PDF p.8, Remark 0.12.
--   - `potentialSeminorm`: The finite asymptotic seminorm on A(M). PDF p.8.
--   - `bowenBall`: Open Bowen ball; in particular B_0(x,epsilon)=M. PDF p.19.
--   - `bowenOscillation`: Unnormalized absolute oscillation on Bowen balls. The set of values is nonempty and bounded for epsilon>0 and bounded f. PDF pp.21,40.
--   - `variationAtRadius`: Time limsup at fixed radius, taking values in EReal so it cannot collapse on an unbounded family. PDF pp.21,40.
--   - `TemperedVariation`: Tempered variation is a small-radius limit, not a fixed-radius bound. PDF p.40, (6.1).
--   - `WeakAlmostAdditive`: Weak almost additivity: the error C_m depends on the LEFT block m. PDF pp.8,40, (0.13)/(6.2).
--   - `AlmostAdditive`: Almost additivity uses one constant independent of BOTH blocks. PDF p.43 n.24.
--   - `SelfBlockApproximation`: Self-block approximation (6.3); G_k/k, not an independent sequence. PDF p.40.
--   - `ApproximantVariation`: The additional iterated variation condition (6.5). Inner radius limit is asserted to exist; order: n, then epsilon, then k. PDF p.40.
--   - `ProbabilityInvariant`: Invariant probabilities with their usual weak topology inherited from P(M). PDF p.18.
--   - `InvariantProbability`: Invariant probability subtype, with the subspace weak topology. PDF p.18.
--   - `potentialEvaluation`: Constructed invariant evaluation: choose the unique real limit when it exists, otherwise zero. Lemma 2.3 supplies existence on its stated domain. PDF p.19, (2.1).
--   - `empiricalMeasure`: The raw empirical probability measure (normalization is used at n>=1). No type-level probability proof is needed to define its events. PDF p.4.
--   - `empiricalEvents`: Empirical-measure event. Equality to the computed raw measure avoids assuming the theorem's empirical object as free structure data. PDF p.27.
--   - `scalarEvents`: Scalar observable events. PDF p.27.
--   - `ProbabilityConvex`: Convexity on probability measures, using their actual convex combinations. PDF pp.27,33. Zero times infinity has the usual EReal convention.
--   - `partitionBlockEntropy`: Finite measurable partition represented by a finite-valued measurable map. Its n-fold join is indexed by words w of length n; entropy uses natural logs. PDF p.18, the usual Kolmogorov--Sinai entropy convention.
--   - `metricEntropy`: Kolmogorov--Sinai entropy: supremum of entropy rates of all finite Borel partitions. Only evaluated at invariant probabilities; +infinity is allowed. PDF p.18. This is a construction, not an entropy oracle or variational axiom.
--   - `Separated`: Finite orbit-separated sets, exactly the complement of open Bowen balls. PDF p.22.
--   - `Spanning`: Finite spanning sets; centers lie in M. PDF p.22.
--   - `weightedSum`: Finite weighted partition sum before the separated/spanning optimization. PDF p.22.
--   - `separatedSum`: Separated partition sum in ENNReal, retaining unbounded suprema. PDF p.22.
--   - `spanningSum`: Spanning partition sum in ENNReal, with empty infimum +infinity. PDF p.22.
--   - `partitionGrowthUpper`: Upper exponential growth at fixed radius. PDF p.22.
--   - `partitionGrowthLower`: Lower exponential growth at fixed radius. PDF p.22.
--   - `separatedSetPressure`: Topological pressure from finite separated sets. The outer supremum is the monotone small-radius limit; spanning equality is a theorem. PDF p.22.
--   - `additivePressure`: Additive pressure. PDF p.22.
--   - `topologicalEntropy`: Ordinary topological entropy from Mathlib's finite dynamical covers. PDF pp.18,24. Kept independent of the pressure variational conclusions.
--   - `EntropyUSC`: Upper semicontinuity of invariant metric entropy. PDF pp.23--24.
--   - `USCE`: The source's USCE includes finite topological entropy. PDF p.24.
--   - `Specification`: Finite specification, with optional Bowen periodicity, using precisely N-separated integer intervals and length max b - min a. PDF pp.18--19.
--   - `WPS`: Weak periodic specification, with a genuine limit m_delta(n)/n at each fixed radius, followed by the small-radius limit. PDF p.19.
--   - `periodicSet`: Fixed points of phi^n, not primitive orbits modulo shifts. PDF p.18.
--   - `periodicPartition`: Finite periodic partition sum, zero when finite but empty. PDF pp.9,24.
--   - `PAP`: PAP allows early empty sets and uses an extended logarithm. PDF p.24.
--   - `periodicLaw`: Periodic law (0.15) on a finite nonempty periodic set; otherwise the fixed reference Dirac law. The latter is an unused finite initial extension in all asymptotic theorems. PDF p.9; no normalization of a zero measure.
--   - `PeriodicHypotheses`: All four dynamical hypotheses used in Sections 3.1--3.2. PDF pp.27--28.
--   - `ForwardExpansive`: Forward expansiveness. PDF p.25.
--   - `integerOrbit`: Two-sided orbit, using the actual inverse of a homeomorphism. PDF p.25.
--   - `Expansive`: Two-sided expansiveness of a homeomorphism. PDF p.25.
--   - `Symmetry`: Source C-Commutation/R-Reversal, selected by reversal=true for R. The inverse is a homeomorphism inverse, never a chosen arbitrary left inverse. PDF p.28.
--   - `timeReversal`: The time-dependent involution: theta in C, theta o phi^(n-1) in R. Only n>=1 is used. PDF pp.28--29.
--   - `transformed`: Transformed AA sequence, not the additive sum of G_n-G_n o theta. PDF pp.9,28.
--   - `sequenceEntropyProduction`: Entropy production in time n. PDF p.29, (3.8).
--   - `reverseProbability`: Involution pushforward as a probability measure. PDF p.28.
--   - `entropyProductionEvaluation`: ep is used only on invariant probabilities in the nonadditive results. PDF p.30, (3.9).
--   - `Equilibrium`: Equilibrium: invariance and equality of free energy with constructed pressure. PDF p.26, (2.26).
--   - `empiricalRate`: Identified empirical rate. All applications use finite topological entropy; its finite pressure difference never evaluates +infinity - +infinity. PDF pp.27,33, (3.1)/(5.2).
--   - `scalarRate`: Contract a rate through invariant evaluation. Empty fibers have infimum +infinity. PDF p.27.
--   - `fluctuationRate`: Contract the empirical rate through ep on invariant probabilities. PDF p.30.
--   - `fullRealLegendre`: Source Legendre transform with the positive sign in alpha*s. PDF p.27.
--   - `cumulantPressure`: AA scalar pressure perturbation. PDF p.27.
--   - `entropicPressure`: Pressure expression for the entropic pressure. PDF pp.30,32.
--   - `EmpiricalScalarLDP`: All conclusions of Theorem 3.1, explicitly shared by Theorems 4.5 and 5.2. No clause of this predicate is included in the hypotheses of those theorems. PDF p.27.
--   - `FluctuationPrinciple`: All conclusions of Theorem 3.9, including both rate symmetries and the Legendre transform of e(-alpha). PDF p.30.
--   - `FinitePressure`: The real finite pressure domain of normalized Gibbs inequalities. PDF p.31. This is domain data, not a pressure identity or an equilibrium assumption.
--   - `GibbsBounds`: Both Gibbs inequalities with one uniform-over-centers constant. PDF p.31.
--   - `WeakGibbs`: Weak Gibbs: no invariance or ergodicity is imposed on P. PDF p.31.
--   - `C1`: C1: every continuous test, pressure difference normalized by p(G). PDF p.33, (5.3).
--   - `C2`: C2: witnesses depend on radius, never on the center x. The deletion m is OUTSIDE log K and m<n on the eventual small-radius domain. PDF p.34.
--   - `dualRate`: Dual-pressure rate (5.1), used on finite-topological-entropy systems. PDF p.33. The supremum is not turned into a freely chosen rate.
--   - `averagedPeriodicLaw`: Cesaro averaging of the actual periodic law, even for nonadditive potentials. PDF p.26. Only positive n is used.
--   - `WeakCluster`: Weak subsequential convergence expressed against every continuous real test. The index map tends to infinity, ruling out a constant early-time subsequence. PDF p.26.
--   - `AdditiveFluctuationPrinciple`: The additive Theorem A/B conclusion, with contraction over ALL probabilities and the rate identity even for noninvariant Q. PDF pp.4--5.
--   - `ShiftPresentation`: Concrete two-sided finite-type subshift presentation. The matrix is primitive, and coding is onto precisely its allowed sequences, not merely an embedding. The metric on M induces the product topology through the homeomorphism. PDF p.6, Example 0.6.
--   - `cylinderPotential`: Cylinder log probability at coordinates 1,...,n, precisely as printed. Full support is imposed in the example theorem to exclude log(0). PDF p.10.
--   - `ShiftReversal`: Source alphabet reversal for a presented finite-type shift. PDF p.6.
--   - `FullShift`: A full shift is a presentation whose adjacency entries all equal one. PDF p.9.
--   - `OpenSetFullSupport`: Full support without an invariance or ergodicity assumption. PDF p.10.
--   - `additiveScalarRate`: Scalar additive contraction rate used in (1.12). PDF pp.4,17.
--   - `IntroHypotheses`: Introductory reversal hypotheses: expansive homeomorphism, Bowen specification, and the continuous involutive reversal. PDF pp.2--3,19.
--   - `logTimePotential`: First explicit example in Remark 6.6, PDF p.43: spatially constant log n. Time zero is defined but never used.
--   - `alternatingRootPotential`: Second explicit example in Remark 6.6, PDF p.43: sqrt(n) at even positive times and zero at odd times. The PDF image confirms the square root.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, https://arxiv.org/abs/1712.05167v3

import Mathlib

/-!
Paper-local interfaces for arXiv:1712.05167v3. All limits in time are taken at
positive integer times; changing the unused time-zero value changes no limit.
No thermodynamic identity is an assumed field of a structure.
Extended natural logarithms reuse Mathlib ENNReal.log. Distinct paper-local
concepts use specific names; similarly named accepted definitions have different
domains or conventions (see ASSESSMENT.json).
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

/-- Speed-n log probability, evaluated only for n >= 1 in limits. PDF p.13. -/
def logSpeed (n : ℕ) (q : ℝ≥0∞) : EReal :=
  ((n : ℝ)⁻¹ : EReal) * ENNReal.log q

/-- Nonnegative extended rate; goodness is deliberately separate. PDF p.13. -/
def IsRate {Y : Type*} [TopologicalSpace Y] (I : Y → EReal) : Prop :=
  LowerSemicontinuous I ∧ ∀ y, 0 ≤ I y

/-- Full Borel-set speed-n LDP, including interior and closure. PDF p.13. -/
def FullLDP {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (events : ℕ → Set Y → ℝ≥0∞) (I : Y → EReal) : Prop :=
  IsRate I ∧ ∀ A : Set Y, MeasurableSet A →
    -(⨅ y ∈ interior A, I y) ≤
      liminf (fun n : ℕ => logSpeed (n + 1) (events (n + 1) A)) atTop ∧
    limsup (fun n : ℕ => logSpeed (n + 1) (events (n + 1) A)) atTop ≤
      -(⨅ y ∈ closure A, I y)

/-- Compactness of every finite sublevel set. PDF p.27. -/
def GoodRate {Y : Type*} [TopologicalSpace Y] (I : Y → EReal) : Prop :=
  IsRate I ∧ ∀ a : ℝ, IsCompact {y | I y ≤ (a : EReal)}

/-- Convexity of an extended scalar function. PDF pp.14,27. -/
def ExtendedRateConvex (I : ℝ → EReal) : Prop :=
  ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    I (a * x + b * y) ≤ (a : EReal) * I x + (b : EReal) * I y

example : ENNReal.log 0 = ⊥ := by simp [ENNReal.log]

example : ENNReal.log 1 = 0 := by simp [ENNReal.log]

/-- An arbitrary regular finite-time reversal experiment. PDF pp.11--12.
There is no topology or finite entropy/moment assumption on its sample space. -/
structure ReversalExperiment (Omega : Type*) [MeasurableSpace Omega] where
  law : Measure Omega
  probability : IsProbabilityMeasure law
  reversal : Omega → Omega
  measurable_reversal : Measurable reversal
  involutive : Function.Involutive reversal
  forward_ac : law ≪ Measure.map reversal law
  backward_ac : Measure.map reversal law ≪ law

/-- Reversed probability. PDF p.11. -/
def reversedLaw {O : Type*} [MeasurableSpace O] (D : ReversalExperiment O) : Measure O :=
  Measure.map D.reversal D.law

/-- A real representative of the log RN derivative, defined up to null sets.
Equivalence and finite probability ensure finite positive density a.e. PDF p.12. -/
def experimentLogDensity {O : Type*} [MeasurableSpace O] (D : ReversalExperiment O) (x : O) : ℝ :=
  Real.log ((D.law.rnDeriv (reversedLaw D) x).toReal)

/-- Extended Laplace integral: no Bochner default on divergent moments. PDF p.12. -/
def entropicFunctional {O : Type*} [MeasurableSpace O]
    (D : ReversalExperiment O) (a : ℝ) : EReal :=
  ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (-a * experimentLogDensity D x)) ∂D.law)

/-- The law of finite-time entropy production. PDF p.12. -/
def productionLaw {O : Type*} [MeasurableSpace O] (D : ReversalExperiment O) : Measure ℝ :=
  Measure.map (experimentLogDensity D) D.law

/-- Total variation in the source's probability normalization, at most one.
PDF p.16; the supremum is over measurable events. -/
def variationDistance {O : Type*} [MeasurableSpace O] (P Q : Measure O) : ℝ :=
  ⨆ A : {A : Set O // MeasurableSet A}, |(P A.val).toReal - (Q A.val).toReal|

/-- Chernoff logarithmic error at time n. PDF p.16. -/
def chernoffTerm {O : Type*} [MeasurableSpace O]
    (D : ReversalExperiment O) (n : ℕ) : EReal :=
  logSpeed n (ENNReal.ofReal (1 - variationDistance D.law (reversedLaw D)))

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.
include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- B(M): pointwise bounded Borel functions, not essential boundedness. PDF p.18. -/
def BoundedBorel (f : M → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C

/-- Positive-time sequence in B(M); the zero term is unused. PDF p.8. -/
def BorelSequence (G : ℕ → M → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → BoundedBorel (G n)

/-- Supremum norm, used below only for bounded functions on nonempty M. PDF p.18. -/
def supNorm (f : M → ℝ) : ℝ := sSup (Set.range fun x => |f x|)

/-- Ergodic sum, with exactly the terms 0,...,n-1. PDF pp.3,18. -/
def orbitSum (phi : M → M) (f : M → ℝ) (n : ℕ) (x : M) : ℝ :=
  ∑ j ∈ Finset.range n, f (phi^[j] x)

/-- (0.12)/(6.4), keeping the order k after limsup n. PDF pp.8,40. -/
def AdditiveApproximation (phi : M → M) (G : ℕ → M → ℝ)
    (F : ℕ → M → ℝ) : Prop :=
  Tendsto (fun k : ℕ => limsup (fun n : ℕ =>
    ((supNorm (fun x => G (n + 1) x - orbitSum phi (F (k + 1)) (n + 1) x) /
      ((n + 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop) atTop (𝓝 0)

/-- Continuous approximating family, with no bound assumed uniformly in k. PDF p.8. -/
def ApproximatingFamily (phi : M → M) (G F : ℕ → M → ℝ) : Prop :=
  (∀ k, 1 ≤ k → Continuous (F k)) ∧ AdditiveApproximation phi G F

/-- Asymptotic additivity, including the Borel and boundedness domain. PDF p.8. -/
def AsymptoticallyAdditive (phi : M → M) (G : ℕ → M → ℝ) : Prop :=
  BorelSequence G ∧ ∃ F : ℕ → M → ℝ, ApproximatingFamily phi G F

/-- Source equivalence (zero asymptotic seminorm), without pressure normalization.
PDF p.8, Remark 0.12. -/
def EquivalentPotentials (G H : ℕ → M → ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
    supNorm (fun x => G (n + 1) x - H (n + 1) x) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)

/-- The finite asymptotic seminorm on A(M). PDF p.8. -/
def potentialSeminorm (G : ℕ → M → ℝ) : EReal :=
  limsup (fun n : ℕ => (supNorm (G (n + 1)) / ((n + 1 : ℕ) : ℝ) : EReal)) atTop

/-- Open Bowen ball; in particular B_0(x,epsilon)=M. PDF p.19. -/
def bowenBall (phi : M → M) (n : ℕ) (x : M) (epsilon : ℝ) : Set M :=
  {y | ∀ j < n, dist (phi^[j] y) (phi^[j] x) < epsilon}

/-- Unnormalized absolute oscillation on Bowen balls. The set of values is
nonempty and bounded for epsilon>0 and bounded f. PDF pp.21,40. -/
def bowenOscillation (phi : M → M) (f : M → ℝ) (n : ℕ) (epsilon : ℝ) : ℝ :=
  sSup {r | ∃ x y z : M, y ∈ bowenBall phi n x epsilon ∧
    z ∈ bowenBall phi n x epsilon ∧ r = |f y - f z|}

/-- Time limsup at fixed radius, taking values in EReal so it cannot collapse
on an unbounded family. PDF pp.21,40. -/
def variationAtRadius (phi : M → M) (G : ℕ → M → ℝ) (epsilon : ℝ) : EReal :=
  limsup (fun n : ℕ => (bowenOscillation phi (G (n + 1)) (n + 1) epsilon /
    ((n + 1 : ℕ) : ℝ) : EReal)) atTop

/-- Tempered variation is a small-radius limit, not a fixed-radius bound.
PDF p.40, (6.1). -/
def TemperedVariation (phi : M → M) (G : ℕ → M → ℝ) : Prop :=
  Tendsto (variationAtRadius phi G) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Weak almost additivity: the error C_m depends on the LEFT block m.
PDF pp.8,40, (0.13)/(6.2). -/
def WeakAlmostAdditive (phi : M → M) (G : ℕ → M → ℝ) : Prop :=
  ∃ C : ℕ → ℝ,
    Tendsto (fun n : ℕ => C (n + 1) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) ∧
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ x,
      |G (m + n) x - G m x - G n (phi^[m] x)| ≤ C m

/-- Almost additivity uses one constant independent of BOTH blocks. PDF p.43 n.24. -/
def AlmostAdditive (phi : M → M) (G : ℕ → M → ℝ) : Prop :=
  ∃ C : ℝ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ x,
    |G (m + n) x - G m x - G n (phi^[m] x)| ≤ C

/-- Self-block approximation (6.3); G_k/k, not an independent sequence. PDF p.40. -/
def SelfBlockApproximation (phi : M → M) (G : ℕ → M → ℝ) : Prop :=
  AdditiveApproximation phi G (fun k x => G k x / (k : ℝ))

/-- The additional iterated variation condition (6.5). Inner radius limit is
asserted to exist; order: n, then epsilon, then k. PDF p.40. -/
def ApproximantVariation (phi : M → M) (F : ℕ → M → ℝ) : Prop :=
  ∃ v : ℕ → EReal,
    (∀ k, 1 ≤ k → Tendsto (variationAtRadius phi (orbitSum phi (F k)))
      (𝓝[>] (0 : ℝ)) (𝓝 (v k))) ∧
    Tendsto (fun k : ℕ => v (k + 1)) atTop (𝓝 0)

/-- Invariant probabilities with their usual weak topology inherited from P(M).
PDF p.18. -/
def ProbabilityInvariant (phi : M → M) (P : ProbabilityMeasure M) : Prop :=
  Measure.map phi (P : Measure M) = (P : Measure M)

/-- Invariant probability subtype, with the subspace weak topology. PDF p.18. -/
abbrev InvariantProbability (phi : M → M) := {P : ProbabilityMeasure M // ProbabilityInvariant phi P}

/-- Constructed invariant evaluation: choose the unique real limit when it
exists, otherwise zero. Lemma 2.3 supplies existence on its stated domain.
PDF p.19, (2.1). -/
def potentialEvaluation (G : ℕ → M → ℝ) (P : ProbabilityMeasure M) : ℝ :=
  if h : ∃ r : ℝ, Tendsto (fun n : ℕ =>
      (∫ x, G (n + 1) x ∂(P : Measure M)) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 r)
    then Classical.choose h else 0

/-- The raw empirical probability measure (normalization is used at n>=1).
No type-level probability proof is needed to define its events. PDF p.4. -/
def empiricalMeasure (phi : M → M) (n : ℕ) (x : M) : Measure M :=
  ENNReal.ofReal ((n : ℝ)⁻¹) •
    ∑ j ∈ Finset.range n, Measure.dirac (phi^[j] x)

/-- Empirical-measure event. Equality to the computed raw measure avoids
assuming the theorem's empirical object as free structure data. PDF p.27. -/
def empiricalEvents (phi : M → M) (laws : ℕ → Measure M)
    (n : ℕ) (A : Set (ProbabilityMeasure M)) : ℝ≥0∞ :=
  laws n {x | ∃ Q ∈ A, (Q : Measure M) = empiricalMeasure phi n x}

/-- Scalar observable events. PDF p.27. -/
def scalarEvents (laws : ℕ → Measure M) (V : ℕ → M → ℝ)
    (n : ℕ) (A : Set ℝ) : ℝ≥0∞ :=
  laws n {x | V n x / (n : ℝ) ∈ A}

/-- Convexity on probability measures, using their actual convex combinations.
PDF pp.27,33. Zero times infinity has the usual EReal convention. -/
def ProbabilityConvex (J : ProbabilityMeasure M → EReal) : Prop :=
  ∀ (P Q R : ProbabilityMeasure M) (a b : ℝ),
    0 ≤ a → 0 ≤ b → a + b = 1 →
    (R : Measure M) = ENNReal.ofReal a • (P : Measure M) +
      ENNReal.ofReal b • (Q : Measure M) →
    J R ≤ (a : EReal) * J P + (b : EReal) * J Q

example (phi : M → M) (f : M → ℝ) (x : M) : orbitSum phi f 0 x = 0 := by
  simp [orbitSum]

example (phi : M → M) (x : M) (e : ℝ) : bowenBall phi 0 x e = Set.univ := by
  ext y
  simp [bowenBall]

example (phi : M → M) (x : M) : orbitSum phi (fun _ => 0) 1 x = 0 := by
  simp [orbitSum]

/-- Finite measurable partition represented by a finite-valued measurable map.
Its n-fold join is indexed by words w of length n; entropy uses natural logs.
PDF p.18, the usual Kolmogorov--Sinai entropy convention. -/
def partitionBlockEntropy (phi : M → M) (P : ProbabilityMeasure M)
    {k : ℕ} (c : M → Fin k) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin k,
    let p := ((P : Measure M) {x | ∀ j : Fin n, c (phi^[(j : ℕ)] x) = w j}).toReal;
    -p * Real.log p

/-- Kolmogorov--Sinai entropy: supremum of entropy rates of all finite Borel
partitions. Only evaluated at invariant probabilities; +infinity is allowed.
PDF p.18. This is a construction, not an entropy oracle or variational axiom. -/
def metricEntropy (phi : M → M) (P : ProbabilityMeasure M) : EReal :=
  ⨆ (k : ℕ) (_ : 1 ≤ k) (c : M → Fin k) (_ : Measurable c),
    liminf (fun n : ℕ =>
      (partitionBlockEntropy phi P c (n + 1) / ((n + 1 : ℕ) : ℝ) : EReal)) atTop

/-- Finite orbit-separated sets, exactly the complement of open Bowen balls.
PDF p.22. -/
def Separated (phi : M → M) (epsilon : ℝ) (n : ℕ) (E : Finset M) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, x ≠ y → y ∉ bowenBall phi n x epsilon

/-- Finite spanning sets; centers lie in M. PDF p.22. -/
def Spanning (phi : M → M) (epsilon : ℝ) (n : ℕ) (E : Finset M) : Prop :=
  ∀ x : M, ∃ y ∈ E, x ∈ bowenBall phi n y epsilon

/-- Finite weighted partition sum before the separated/spanning optimization.
PDF p.22. -/
def weightedSum (G : ℕ → M → ℝ) (n : ℕ) (E : Finset M) : ℝ≥0∞ :=
  ∑ x ∈ E, ENNReal.ofReal (Real.exp (G n x))

/-- Separated partition sum in ENNReal, retaining unbounded suprema. PDF p.22. -/
def separatedSum (phi : M → M) (G : ℕ → M → ℝ) (e : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ (E : Finset M) (_ : Separated phi e n E), weightedSum G n E

/-- Spanning partition sum in ENNReal, with empty infimum +infinity. PDF p.22. -/
def spanningSum (phi : M → M) (G : ℕ → M → ℝ) (e : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (E : Finset M) (_ : Spanning phi e n E), weightedSum G n E

/-- Upper exponential growth at fixed radius. PDF p.22. -/
def partitionGrowthUpper (Z : ℝ → ℕ → ℝ≥0∞) (e : ℝ) : EReal :=
  limsup (fun n : ℕ => logSpeed (n + 1) (Z e (n + 1))) atTop

/-- Lower exponential growth at fixed radius. PDF p.22. -/
def partitionGrowthLower (Z : ℝ → ℕ → ℝ≥0∞) (e : ℝ) : EReal :=
  liminf (fun n : ℕ => logSpeed (n + 1) (Z e (n + 1))) atTop

/-- Topological pressure from finite separated sets. The outer supremum is the
monotone small-radius limit; spanning equality is a theorem. PDF p.22. -/
def separatedSetPressure (phi : M → M) (G : ℕ → M → ℝ) : EReal :=
  ⨆ (e : ℝ) (_ : 0 < e), partitionGrowthUpper (separatedSum phi G) e

/-- Additive pressure. PDF p.22. -/
def additivePressure (phi : M → M) (f : M → ℝ) : EReal :=
  separatedSetPressure phi (orbitSum phi f)

/-- Ordinary topological entropy from Mathlib's finite dynamical covers.
PDF pp.18,24. Kept independent of the pressure variational conclusions. -/
def topologicalEntropy (phi : M → M) : EReal := Dynamics.coverEntropy phi Set.univ

/-- Upper semicontinuity of invariant metric entropy. PDF pp.23--24. -/
def EntropyUSC (phi : M → M) : Prop :=
  UpperSemicontinuous (fun P : InvariantProbability phi => metricEntropy phi P.val)

/-- The source's USCE includes finite topological entropy. PDF p.24. -/
def USCE (phi : M → M) : Prop :=
  topologicalEntropy phi < ⊤ ∧ EntropyUSC phi

/-- Finite specification, with optional Bowen periodicity, using precisely
N-separated integer intervals and length max b - min a. PDF pp.18--19. -/
def Specification (phi : M → M) (periodic : Bool := false) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ N : ℕ, 1 ≤ N ∧
    ∀ (r : ℕ) (a b : Fin r → ℕ) (points : Fin r → M), 1 ≤ r →
      (∀ i, a i ≤ b i) →
      (∀ i j, i ≠ j → ∀ k l : ℕ, a i ≤ k → k ≤ b i →
        a j ≤ l → l ≤ b j → N ≤ Nat.dist k l) →
      ∃ x : M,
        (∀ i, ∀ k : ℕ, a i ≤ k → k ≤ b i →
          dist (phi^[k] x) (phi^[k] (points i)) < e) ∧
        (periodic = true →
          phi^[((Finset.univ.sup b) - (sInf (Set.range a))) + N] x = x)

/-- Weak periodic specification, with a genuine limit m_delta(n)/n at each
fixed radius, followed by the small-radius limit. PDF p.19. -/
def WPS (phi : M → M) : Prop :=
  ∃ (m : ℝ → ℕ → ℕ) (rho : ℝ → ℝ),
    Tendsto rho (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    ∀ e : ℝ, 0 < e →
      Tendsto (fun n : ℕ => (m e (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (rho e)) ∧
      ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0,
        m e n < n ∧ ∀ x : M, ∃ y ∈ bowenBall phi (n - m e n) x e, phi^[n] y = y

/-- Fixed points of phi^n, not primitive orbits modulo shifts. PDF p.18. -/
def periodicSet (phi : M → M) (n : ℕ) : Set M := {x | phi^[n] x = x}

/-- Finite periodic partition sum, zero when finite but empty. PDF pp.9,24. -/
def periodicPartition (phi : M → M) (G : ℕ → M → ℝ) (n : ℕ) : ℝ≥0∞ :=
  if h : (periodicSet phi n).Finite then weightedSum G n h.toFinset else ⊤

/-- PAP allows early empty sets and uses an extended logarithm. PDF p.24. -/
def PAP (phi : M → M) : Prop :=
  (∀ n : ℕ, 1 ≤ n → (periodicSet phi n).Finite) ∧
    ∀ G : ℕ → M → ℝ, AsymptoticallyAdditive phi G →
      Tendsto (fun n : ℕ => logSpeed (n + 1) (periodicPartition phi G (n + 1)))
        atTop (𝓝 (separatedSetPressure phi G))

/-- Periodic law (0.15) on a finite nonempty periodic set; otherwise the fixed
reference Dirac law. The latter is an unused finite initial extension in all
asymptotic theorems. PDF p.9; no normalization of a zero measure. -/
def periodicLaw (phi : M → M) (G : ℕ → M → ℝ) (reference : M) (n : ℕ) : Measure M :=
  if h : (periodicSet phi n).Finite ∧ (periodicSet phi n).Nonempty then
    (periodicPartition phi G n)⁻¹ •
      ∑ x ∈ h.1.toFinset, ENNReal.ofReal (Real.exp (G n x)) • Measure.dirac x
  else Measure.dirac reference

/-- All four dynamical hypotheses used in Sections 3.1--3.2. PDF pp.27--28. -/
def PeriodicHypotheses (phi : M → M) : Prop :=
  USCE phi ∧ WPS phi ∧ Specification phi ∧ PAP phi

/-- Forward expansiveness. PDF p.25. -/
def ForwardExpansive (phi : M → M) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∀ x y : M,
    (∀ n : ℕ, dist (phi^[n] x) (phi^[n] y) ≤ e) → x = y

/-- Two-sided orbit, using the actual inverse of a homeomorphism. PDF p.25. -/
def integerOrbit (f : M ≃ₜ M) (k : ℤ) (x : M) : M :=
  if 0 ≤ k then f^[k.toNat] x else f.symm^[(-k).toNat] x

/-- Two-sided expansiveness of a homeomorphism. PDF p.25. -/
def Expansive (f : M ≃ₜ M) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∀ x y : M,
    (∀ k : ℤ, dist (integerOrbit f k x) (integerOrbit f k y) ≤ e) → x = y

/-- Source C-Commutation/R-Reversal, selected by reversal=true for R.
The inverse is a homeomorphism inverse, never a chosen arbitrary left inverse.
PDF p.28. -/
def Symmetry (phi : M → M) (theta : M ≃ₜ M) (reversal : Bool) : Prop :=
  Function.Involutive theta ∧
    if reversal then
      ∃ f : M ≃ₜ M, (∀ x, phi x = f x) ∧
        ∀ x, f.symm x = theta (phi (theta x))
    else ∀ x, phi x = theta (phi (theta x))

/-- The time-dependent involution: theta in C, theta o phi^(n-1) in R.
Only n>=1 is used. PDF pp.28--29. -/
def timeReversal (phi : M → M) (theta : M ≃ₜ M) (reversal : Bool)
    (n : ℕ) (x : M) : M :=
  if reversal then theta (phi^[n - 1] x) else theta x

/-- Transformed AA sequence, not the additive sum of G_n-G_n o theta.
PDF pp.9,28. -/
def transformed (phi : M → M) (theta : M ≃ₜ M) (reversal : Bool)
    (G : ℕ → M → ℝ) (n : ℕ) (x : M) : ℝ :=
  G n (timeReversal phi theta reversal n x)

/-- Entropy production in time n. PDF p.29, (3.8). -/
def sequenceEntropyProduction (phi : M → M) (theta : M ≃ₜ M) (reversal : Bool)
    (G : ℕ → M → ℝ) (n : ℕ) (x : M) : ℝ :=
  G n x - transformed phi theta reversal G n x

/-- Involution pushforward as a probability measure. PDF p.28. -/
def reverseProbability (theta : M ≃ₜ M) (Q : ProbabilityMeasure M) : ProbabilityMeasure M :=
  Q.map theta.continuous.measurable.aemeasurable

/-- ep is used only on invariant probabilities in the nonadditive results.
PDF p.30, (3.9). -/
def entropyProductionEvaluation (G : ℕ → M → ℝ) (theta : M ≃ₜ M)
    (Q : ProbabilityMeasure M) : ℝ :=
  potentialEvaluation G Q - potentialEvaluation G (reverseProbability theta Q)

/-- Equilibrium: invariance and equality of free energy with constructed pressure.
PDF p.26, (2.26). -/
def Equilibrium (phi : M → M) (G : ℕ → M → ℝ) (P : ProbabilityMeasure M) : Prop :=
  ProbabilityInvariant phi P ∧ separatedSetPressure phi G = (potentialEvaluation G P : EReal) + metricEntropy phi P

/-- Identified empirical rate. All applications use finite topological entropy;
its finite pressure difference never evaluates +infinity - +infinity.
PDF pp.27,33, (3.1)/(5.2). -/
def empiricalRate (phi : M → M) (G : ℕ → M → ℝ) (Q : ProbabilityMeasure M) : EReal :=
  if ProbabilityInvariant phi Q then
    separatedSetPressure phi G - (potentialEvaluation G Q : EReal) - metricEntropy phi Q
  else ⊤

/-- Contract a rate through invariant evaluation. Empty fibers have infimum
+infinity. PDF p.27. -/
def scalarRate (phi : M → M) (G V : ℕ → M → ℝ) (s : ℝ) : EReal :=
  ⨅ (Q : ProbabilityMeasure M) (_ : ProbabilityInvariant phi Q)
    (_ : potentialEvaluation V Q = s), empiricalRate phi G Q

/-- Contract the empirical rate through ep on invariant probabilities. PDF p.30. -/
def fluctuationRate (phi : M → M) (G : ℕ → M → ℝ)
    (theta : M ≃ₜ M) (s : ℝ) : EReal :=
  ⨅ (Q : ProbabilityMeasure M) (_ : ProbabilityInvariant phi Q)
    (_ : entropyProductionEvaluation G theta Q = s), empiricalRate phi G Q

/-- Source Legendre transform with the positive sign in alpha*s. PDF p.27. -/
def fullRealLegendre (p : ℝ → EReal) (s : ℝ) : EReal :=
  ⨆ a : ℝ, ((a * s : ℝ) : EReal) - p a

/-- AA scalar pressure perturbation. PDF p.27. -/
def cumulantPressure (phi : M → M) (G V : ℕ → M → ℝ) (a : ℝ) : EReal :=
  separatedSetPressure phi (fun n x => G n x + a * V n x) - separatedSetPressure phi G

/-- Pressure expression for the entropic pressure. PDF pp.30,32. -/
def entropicPressure (phi : M → M) (G : ℕ → M → ℝ)
    (theta : M ≃ₜ M) (reversal : Bool) (a : ℝ) : EReal :=
  separatedSetPressure phi (fun n x => (1 - a) * G n x +
    a * transformed phi theta reversal G n x) - separatedSetPressure phi G

/-- All conclusions of Theorem 3.1, explicitly shared by Theorems 4.5 and 5.2.
No clause of this predicate is included in the hypotheses of those theorems.
PDF p.27. -/
def EmpiricalScalarLDP (phi : M → M) (G : ℕ → M → ℝ) (laws : ℕ → Measure M) : Prop :=
  FullLDP (empiricalEvents phi laws) (empiricalRate phi G) ∧
  ProbabilityConvex (empiricalRate phi G) ∧
  ∀ V : ℕ → M → ℝ, AsymptoticallyAdditive phi V →
    FullLDP (scalarEvents laws V) (scalarRate phi G V) ∧
    GoodRate (scalarRate phi G V) ∧ ExtendedRateConvex (scalarRate phi G V) ∧
    ∀ s : ℝ, scalarRate phi G V s = fullRealLegendre (cumulantPressure phi G V) s

/-- All conclusions of Theorem 3.9, including both rate symmetries and the
Legendre transform of e(-alpha). PDF p.30. -/
def FluctuationPrinciple (phi : M → M) (G : ℕ → M → ℝ)
    (theta : M ≃ₜ M) (reversal : Bool) (laws : ℕ → Measure M) : Prop :=
  (∀ Q : ProbabilityMeasure M, ProbabilityInvariant phi Q →
    empiricalRate phi G (reverseProbability theta Q) =
      empiricalRate phi G Q + (entropyProductionEvaluation G theta Q : EReal)) ∧
  FullLDP (scalarEvents laws (sequenceEntropyProduction phi theta reversal G))
    (fluctuationRate phi G theta) ∧
  GoodRate (fluctuationRate phi G theta) ∧ ExtendedRateConvex (fluctuationRate phi G theta) ∧
  (∀ s : ℝ, fluctuationRate phi G theta (-s) = fluctuationRate phi G theta s + (s : EReal)) ∧
  ∀ s : ℝ, fluctuationRate phi G theta s =
    fullRealLegendre (fun a => entropicPressure phi G theta reversal (-a)) s

/-- The real finite pressure domain of normalized Gibbs inequalities. PDF p.31.
This is domain data, not a pressure identity or an equilibrium assumption. -/
def FinitePressure (phi : M → M) (G : ℕ → M → ℝ) : Prop :=
  ∃ p : ℝ, separatedSetPressure phi G = (p : EReal)

/-- Both Gibbs inequalities with one uniform-over-centers constant. PDF p.31. -/
def GibbsBounds (phi : M → M) (G : ℕ → M → ℝ) (P : ProbabilityMeasure M)
    (K : ℝ → ℕ → ℝ) (A : ℝ → Set M) : Prop :=
  (∀ e : ℝ, 0 < e → ∀ n : ℕ, 1 ≤ n → 1 ≤ K e n) ∧
  Tendsto (fun e : ℝ => limsup (fun n : ℕ =>
    (Real.log (K e (n + 1)) / ((n + 1 : ℕ) : ℝ) : EReal)) atTop)
    (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
  ∀ e : ℝ, 0 < e → ∀ n : ℕ, 1 ≤ n → ∀ x ∈ A e,
    ENNReal.ofReal ((K e n)⁻¹ * Real.exp (G n x - (n : ℝ) * (separatedSetPressure phi G).toReal)) ≤
      (P : Measure M) (bowenBall phi n x e) ∧
    (P : Measure M) (bowenBall phi n x e) ≤
      ENNReal.ofReal (K e n * Real.exp (G n x - (n : ℝ) * (separatedSetPressure phi G).toReal))

/-- Weak Gibbs: no invariance or ergodicity is imposed on P. PDF p.31. -/
def WeakGibbs (phi : M → M) (G : ℕ → M → ℝ) (P : ProbabilityMeasure M) : Prop :=
  AsymptoticallyAdditive phi G ∧ FinitePressure phi G ∧
    ∃ K : ℝ → ℕ → ℝ, GibbsBounds phi G P K (fun _ => Set.univ)

/-- C1: every continuous test, pressure difference normalized by p(G).
PDF p.33, (5.3). -/
def C1 (phi : M → M) (G : ℕ → M → ℝ) (laws : ℕ → Measure M) : Prop :=
  ∀ V : C(M, ℝ), Tendsto (fun n : ℕ =>
    logSpeed (n + 1) (∫⁻ x, ENNReal.ofReal (Real.exp (orbitSum phi V (n + 1) x)) ∂laws (n + 1)))
    atTop (𝓝 (separatedSetPressure phi (fun n x => G n x + orbitSum phi V n x) - separatedSetPressure phi G))

/-- C2: witnesses depend on radius, never on the center x. The deletion m
is OUTSIDE log K and m<n on the eventual small-radius domain. PDF p.34. -/
def C2 (phi : M → M) (G : ℕ → M → ℝ) (laws : ℕ → Measure M) : Prop :=
  ∃ (e0 : ℝ) (n0 : ℝ → ℕ) (K : ℝ → ℕ → ℝ) (m : ℝ → ℕ → ℕ),
    0 < e0 ∧
    (∀ e : ℝ, 0 < e → e < e0 → 1 ≤ n0 e ∧
      ∀ n ≥ n0 e, 1 ≤ K e n ∧ m e n < n ∧ ∀ x : M,
        ENNReal.ofReal ((K e n)⁻¹ * Real.exp (G n x - (n : ℝ) * (separatedSetPressure phi G).toReal)) ≤
          laws n (bowenBall phi (n - m e n) x e)) ∧
    Tendsto (fun e : ℝ => limsup (fun n : ℕ =>
      ((Real.log (K e (n + 1)) + (m e (n + 1) : ℝ)) / ((n + 1 : ℕ) : ℝ) : EReal)) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Dual-pressure rate (5.1), used on finite-topological-entropy systems.
PDF p.33. The supremum is not turned into a freely chosen rate. -/
def dualRate (phi : M → M) (G : ℕ → M → ℝ) (Q : ProbabilityMeasure M) : EReal :=
  ⨆ V : C(M, ℝ), (((∫ x, (V x : ℝ) ∂(Q : Measure M)) : ℝ) : EReal) -
    separatedSetPressure phi (fun n x => G n x + orbitSum phi V n x) + separatedSetPressure phi G

/-- Cesaro averaging of the actual periodic law, even for nonadditive potentials.
PDF p.26. Only positive n is used. -/
def averagedPeriodicLaw (phi : M → M) (G : ℕ → M → ℝ) (reference : M) (n : ℕ) : Measure M :=
  ENNReal.ofReal ((n : ℝ)⁻¹) •
    ∑ j ∈ Finset.range n, Measure.map (phi^[j]) (periodicLaw phi G reference n)

/-- Weak subsequential convergence expressed against every continuous real test.
The index map tends to infinity, ruling out a constant early-time subsequence.
PDF p.26. -/
def WeakCluster (laws : ℕ → Measure M) (P : ProbabilityMeasure M) : Prop :=
  ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ V : C(M, ℝ),
    Tendsto (fun j => ∫ x, V x ∂laws (k j)) atTop (𝓝 (∫ x, V x ∂(P : Measure M)))

/-- The additive Theorem A/B conclusion, with contraction over ALL probabilities
and the rate identity even for noninvariant Q. PDF pp.4--5. -/
def AdditiveFluctuationPrinciple (phi : M → M) (g : C(M, ℝ))
    (theta : M ≃ₜ M) (laws : ℕ → Measure M) : Prop :=
  let G := orbitSum phi g
  let sigma := fun x => g x - g (theta x)
  let J := empiricalRate phi G
  let I := fun s : ℝ => ⨅ (Q : ProbabilityMeasure M)
    (_ : (∫ x, sigma x ∂(Q : Measure M)) = s), J Q
  FullLDP (empiricalEvents phi laws) J ∧
  FullLDP (scalarEvents laws (orbitSum phi sigma)) I ∧
  (∀ Q : ProbabilityMeasure M,
    J (reverseProbability theta Q) = J Q + (((∫ x, (sigma x : ℝ) ∂(Q : Measure M)) : ℝ) : EReal)) ∧
  ∀ s : ℝ, I (-s) = I s + (s : EReal)

example (phi : M → M) (G : ℕ → M → ℝ) :
    weightedSum G 1 (∅ : Finset M) = 0 := by simp [weightedSum]

example (phi : M → M) (G : ℕ → M → ℝ) (x : M) :
    sequenceEntropyProduction phi (Homeomorph.refl M) false G 1 x = 0 := by
  simp [sequenceEntropyProduction, transformed, timeReversal]

/-- Concrete two-sided finite-type subshift presentation. The matrix is primitive,
and coding is onto precisely its allowed sequences, not merely an embedding.
The metric on M induces the product topology through the homeomorphism.
PDF p.6, Example 0.6. -/
structure ShiftPresentation (phi : M → M) where
  alphabetSize : ℕ
  alphabet_nonempty : 1 ≤ alphabetSize
  adjacency : Matrix (Fin alphabetSize) (Fin alphabetSize) ℕ
  zero_one : ∀ i j, adjacency i j = 0 ∨ adjacency i j = 1
  primitive : ∃ k : ℕ, 1 ≤ k ∧ ∀ i j, 0 < (adjacency ^ k) i j
  coding : M ≃ₜ {x : ℤ → Fin alphabetSize // ∀ j, adjacency (x j) (x (j + 1)) = 1}
  shift_rule : ∀ x j, (coding (phi x)).val j = (coding x).val (j + 1)

/-- Cylinder log probability at coordinates 1,...,n, precisely as printed.
Full support is imposed in the example theorem to exclude log(0). PDF p.10. -/
def cylinderPotential (phi : M → M) (S : ShiftPresentation phi)
    (P : ProbabilityMeasure M) (n : ℕ) (x : M) : ℝ :=
  Real.log (((P : Measure M) {y | ∀ j : ℕ, 1 ≤ j → j ≤ n →
    (S.coding y).val (j : ℤ) = (S.coding x).val (j : ℤ)}).toReal)

/-- Source alphabet reversal for a presented finite-type shift. PDF p.6. -/
def ShiftReversal (phi : M → M) (S : ShiftPresentation phi) (theta : M ≃ₜ M) : Prop :=
  ∃ p : Equiv.Perm (Fin S.alphabetSize), Function.Involutive p ∧
    ∀ x j, (S.coding (theta x)).val j = p ((S.coding x).val (-j))

/-- A full shift is a presentation whose adjacency entries all equal one.
PDF p.9. -/
def FullShift (phi : M → M) : Prop :=
  ∃ S : ShiftPresentation phi, ∀ i j, S.adjacency i j = 1

/-- Full support without an invariance or ergodicity assumption. PDF p.10. -/
def OpenSetFullSupport (P : ProbabilityMeasure M) : Prop :=
  ∀ U : Set M, IsOpen U → U.Nonempty → 0 < (P : Measure M) U

/-- Scalar additive contraction rate used in (1.12). PDF pp.4,17. -/
def additiveScalarRate (phi : M → M) (g : C(M, ℝ)) (theta : M ≃ₜ M) (s : ℝ) : EReal :=
  ⨅ (Q : ProbabilityMeasure M)
    (_ : (∫ x, (g x - g (theta x)) ∂(Q : Measure M)) = s),
      empiricalRate phi (orbitSum phi g) Q

/-- Introductory reversal hypotheses: expansive homeomorphism, Bowen
specification, and the continuous involutive reversal. PDF pp.2--3,19. -/
def IntroHypotheses (f theta : M ≃ₜ M) : Prop :=
  Expansive f ∧ Specification f true ∧ Symmetry f theta true

/-- First explicit example in Remark 6.6, PDF p.43: spatially constant log n.
Time zero is defined but never used. -/
def logTimePotential (n : ℕ) (_x : M) : ℝ := Real.log (n : ℝ)

/-- Second explicit example in Remark 6.6, PDF p.43: sqrt(n) at even positive
times and zero at odd times. The PDF image confirms the square root. -/
def alternatingRootPotential (n : ℕ) (_x : M) : ℝ :=
  if Even n then Real.sqrt (n : ℝ) else 0

example (G : ℕ → M → ℝ) (n : ℕ) (x : M) :
    weightedSum G n {x} = ENNReal.ofReal (Real.exp (G n x)) := by
  simp [weightedSum]

example (J : ProbabilityMeasure M → EReal) :
    (⨅ Q ∈ (∅ : Set (ProbabilityMeasure M)), J Q) = ⊤ := by
  simp

example (phi : M → M) (theta : M ≃ₜ M) (G : ℕ → M → ℝ) (n : ℕ) (x : M) :
    transformed phi theta true G n x = G n (theta (phi^[n - 1] x)) := by
  rfl

example (phi : M → M) (theta : M ≃ₜ M) (n : ℕ) (x : M) :
    timeReversal phi theta false n x = theta x := by
  rfl

example (phi : M → M) (x : M) : empiricalMeasure phi 0 x = 0 := by
  simp [empiricalMeasure]

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82


