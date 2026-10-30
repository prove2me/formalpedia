-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45
-- name    : QAlgorithms_Papers_Independent_Bridge50_P45
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:10:01.782007+00:00
-- url     : https://prove2.me/theorems/7438a01c-2768-402e-8425-7f578db6c17b
-- title:
--   Definitions for Strong converse exponent for classical-quantum channel coding
-- statement:
--   The objects the formalized statements of *Strong converse exponent for classical-quantum channel coding* (arXiv:1409.3562) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NonzeroPSD`: Nonzero positive semidefinite operators, §II A, PDF p.3.
--   - `meetSupport`: Projection onto the intersection of supports, PDF p.7 (22). The kernel of (I-supp A)+(I-supp B) is exactly that intersection.
--   - `traceLog`: Scalar extended natural logarithm, PDF p.3 (3). Only nonnegative arguments are used.
--   - `asNN`: Nonnegative extended conversion; used only on nonnegative quantities, PDF p.23 (96)-(97).
--   - `Flavor`: Three trace functionals, PDF p.7 (15)-(17).
--   - `rawQ`: Positive-definite trace expressions (15)-(17), PDF p.7.
--   - `regQ`: Regularized extension (18); liminf is defined without assuming existence of the limit. Lemma III.1 states the actual limit and equality with the second regularization.
--   - `regularizedTrace`: Finite-order Q, including the right-limit convention at zero, PDF pp.7,14.
--   - `logTraceFunctional`: Logarithmic Q, PDF p.8 (27).
--   - `finiteD`: Trace-normalized finite-order divergence, including the entropy value at one, PDF pp.8-10.
--   - `renyiValue`: Orders zero and infinity are limits, PDF p.13 (59)-(60).
--   - `renyiSign`: Sign convention (36), PDF p.10.
--   - `EConvexOn`: Convex extended-valued functions via their real epigraphs. This retains empty and unbounded extrema instead of assigning real sSup/sInf default values; PDF p.4.
--   - `EConcaveOn`: Concavity is convexity of the negative, PDF pp.39-40.
--   - `tensorEntries`: Tensor product entries, including the scalar tensor unit at n=0, PDF p.6.
--   - `statesOn`: States on a specified support, PDF p.3.
--   - `entropyObjective`: Weighted entropy objective; at order one the zero-coefficient entropy is omitted, PDF p.10.
--   - `dualObjective`: Dual objective from (39), PDF p.10, before correcting the trace-normalization constant.
--   - `logEuclideanGibbs`: Gibbs numerator in (40), PDF p.10.
--   - `logEuclideanOptimizer`: Optimizer (40); used only when its denominator is finite and positive, PDF p.10.
--   - `Minimizes`: Minimum with attainment, to distinguish min from inf, PDF pp.10-11.
--   - `AttainsMaximum`: Maximum with attainment, PDF pp.10-11.
--   - `lawSupport`: Finitely supported laws on an arbitrary alphabet, PDF p.6. The fallback is unused on lawful input.
--   - `FiniteInputLaw`: Exact finite-law domain; no finite-alphabet assumption, PDF p.6.
--   - `MassLaw`: General probability mass functions, allowing countably infinite support, PDF p.23.
--   - `CQ`: A channel has normalized density outputs, PDF p.6.
--   - `lifted`: Lifted finite-law output, with a finite classical label register, PDF p.6 (14).
--   - `comparison`: Product comparison P tensor sigma in (80), PDF p.20.
--   - `informationObjective`: Both fixed-law information objectives are defined before optimization, PDF p.20 (80)-(81).
--   - `fixedLawInformation`: The two fixed-law Holevo quantities (indices 0 and 1 represent printed i=1,2), PDF p.20.
--   - `cqRenyiCapacity`: Capacity is the first-type finite-law supremum, PDF p.20 (83)-(84). No equality with the second type or radius is assumed.
--   - `cqRenyiRadius`: Divergence radius (85), independent of capacity, PDF p.20.
--   - `ordinaryLawInformation`: Holevo information uses normalized Umegaki divergence, PDF p.19 (76)-(77).
--   - `memorylessOutputs`: Product channel, PDF p.6.
--   - `independentInputLaw`: Product input mass, PDF p.6.
--   - `TensorPermutationInvariant`: Permutation-invariant operator, PDF p.5; the action uses inverse permutations.
--   - `SymmetricLaw`: Symmetric input probability density, PDF p.23.
--   - `Universal`: A chosen universal symmetric state with all conditions of Lemma II.8, PDF pp.5-6.
--   - `pinchedChannel`: Channel pinched by a chosen universal symmetric state, PDF p.23.
--   - `massObjective`: Infinite block-sum objectives for IV.9. Nonnegative ENNReal sums retain infinite values; finite classical label spaces are not imposed on the mass function, PDF p.23.
--   - `massInformation`: General-law information for IV.9, using the block sums (96)-(97), PDF pp.23-24.
--   - `CQBlockCode`: Deterministic encoder and one shared POVM; repeated words and zero effects allowed, PDF p.26. Both blocklength and message count are positive in every use.
--   - `cqAverageSuccess`: Uniform-message average success, PDF p.26.
--   - `CQExponentAchievable`: One sequence simultaneously meets the two liminf criteria, Definition V.1, PDF p.26. Index k represents positive blocklength k+1.
--   - `sc`: Infimum of real R-achievable success exponents, with extended empty infimum, Definition V.1, PDF pp.26-27.
--   - `converseCapacityTransform`: Converse Hoeffding capacity (108), PDF p.27.
--   - `conditionalUmegaki`: Conditional relative entropy, PDF p.28.
--   - `dummyF`: The constructed dummy-channel objective (112), PDF pp.28-29.
--   - `dummyF1`: First constrained infimum (113), PDF p.29; an empty feasible set gives +infinity.
--   - `dummyF2`: Second constrained infimum (114), PDF p.29.
--   - `QuantumBlockCode`: Quantum n-block codes allow arbitrary entangled input density operators, PDF p.36.
--   - `quantumAverageSuccess`: Quantum-channel success uses the full linear tensor extension, PDF p.36.
--   - `QuantumExponentAchievable`: Quantum-channel counterpart of Definition V.1, PDF p.36.
--   - `quantumSc`: Operational quantum strong converse exponent, PDF p.36.
--   - `associated`: Associated cq channel has all input DENSITY operators as alphabet, PDF p.36.
--   - `quantumRenyiCapacity`: Quantum-channel capacity over all finite ensembles of density operators, PDF p.36.
--   - `outputRenyiEntropy`: Renyi entropy, with its entropy limit at one, PDF p.37.
--   - `minOutputEntropy`: Minimum-output entropy, PDF p.37. Lemma VI.2 also records attainment of this infimum in its parameter range, so the minimum is not silently weakened.
--   - `IrreducibleOutputCovariance`: Group covariance includes irreducibility only at the output, PDF pp.36-37. Compactness and continuity are carried by the theorem's group and representation binders.
--   - `KWAdditive`: KW class requires self-tensor minimum-output entropy additivity at EVERY a>1, PDF p.37, in addition to the covariance hypotheses.
--   - `FiniteMeasurePrepare`: Finite-dimensional entanglement-breaking channels in their equivalent measure-and-prepare form, §VI A, PDF p.36. Effects and outputs are actual matrices.
--   - `TraceFamily`: Generic trace functional of Appendix B, across finite register types, PDF p.39.
--   - `ClassicalAgreement`: Classical agreement on commuting positive pairs, Appendix B, PDF p.39.
--   - `genericD`: Generic trace-normalized finite-order divergence (B1), PDF p.39.
--   - `genericInfo`: Generic two Holevo quantities of Appendix B; actual lifted first argument, so no block-additivity axiom is silently added to the generic Q, PDF p.39.
--   - `normalizedAuxiliary`: Auxiliary function with the trace normalization retained, PDF p.39.
--   - `explicitAuxiliary`: Explicit Petz auxiliary expression, without presuming trace-one outputs, PDF p.40.
--   - `JointConvexQ`: Global joint convexity over every positive finite dimension, PDF p.14.
--   - `DataProcessing`: Data processing under every finite-dimensional CPTP map, PDF p.14. Dimensions are quantified globally; witnesses may depend on the order.
--   - `SeparateRange`: Finite-order separate-convexity range, PDF p.15.
--   - `ReferenceRange`: Order-monotonicity range in the second matrix, PDF p.17.
--   - `RegularRange`: Regularization parameter ranges (72), PDF p.17.
--   - `CapacityRange`: Parameter range for the four identifications in IV.2, PDF p.20.
--   - `spectralRatios`: Spectral ratios with overlapping positive spectral projections, PDF p.13 (61).
-- source:
--   Strong converse exponent for classical-quantum channel coding, arXiv:1409.3562v8, https://arxiv.org/abs/1409.3562v8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_SpectralFilter
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

/-! Mosonyi–Ogawa, arXiv:1409.3562v8. All page numbers are PDF pages.
Accepted spectral, support, tensor, pinching and entropy primitives are imported.
Paper-specific composites retain this paper's natural-log, trace-normalized conventions.
Similar short names in the catalogue can describe different mathematical objects.
Compilation is pending the batch mechanical handoff. -/

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology
open Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P45

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)
open QAlgorithms.Papers.Independent.Dependency50.P35 (lnOp)
open QAlgorithms.Papers.Independent.Next46.P23 (eigenvalues)
open QAlgorithms (spectralProjector)

/-- Nonzero positive semidefinite operators, §II A, PDF p.3. -/
def NonzeroPSD {I : Type} [Fintype I] (A : Mat I) : Prop := A.PosSemidef ∧ A ≠ 0

/-- Projection onto the intersection of supports, PDF p.7 (22).
The kernel of (I-supp A)+(I-supp B) is exactly that intersection. -/
def meetSupport {I : Type} [Fintype I] [DecidableEq I] (A B : Mat I) : Mat I :=
  1 - support ((1 - support A) + (1 - support B))

/-- Scalar extended natural logarithm, PDF p.3 (3). Only nonnegative arguments are used. -/
def traceLog (x : EReal) : EReal := ENNReal.log x.toENNReal

/-- Nonnegative extended conversion; used only on nonnegative quantities, PDF p.23 (96)-(97). -/
def asNN (x : EReal) : ℝ≥0∞ := if x = ⊤ then ⊤ else ENNReal.ofReal x.toReal

/-- Three trace functionals, PDF p.7 (15)-(17). -/
inductive Flavor where
  | petz | star | b
  deriving DecidableEq

/-- Positive-definite trace expressions (15)-(17), PDF p.7. -/
def rawQ {I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : ℝ) (rho sigma : Mat I) : ℝ :=
  match t with
  | .petz => (supportPower rho a * supportPower sigma (1-a)).trace.re
  | .star => (supportPower (supportPower rho (1/2) * supportPower sigma ((1-a)/a) * supportPower rho (1/2)) a).trace.re
  | .b => (cfc Real.exp ((a : ℂ) • lnOp rho + ((1-a : ℝ) : ℂ) • lnOp sigma)).trace.re

/-- Regularized extension (18); liminf is defined without assuming existence of the limit.
Lemma III.1 states the actual limit and equality with the second regularization. -/
def regQ {I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : ℝ) (rho sigma : Mat I) : EReal :=
  Filter.liminf (fun e : ℝ => (rawQ t a (rho + (e : ℂ) • 1) (sigma + (e : ℂ) • 1) : EReal))
    (𝓝[>] (0 : ℝ))

/-- Finite-order Q, including the right-limit convention at zero, PDF pp.7,14. -/
def regularizedTrace {I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : ℝ) (rho sigma : Mat I) : EReal :=
  if a = 0 then Filter.liminf (fun z : ℝ => regQ t z rho sigma) (𝓝[>] (0 : ℝ))
  else regQ t a rho sigma

/-- Logarithmic Q, PDF p.8 (27). -/
def logTraceFunctional {I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : ℝ) (rho sigma : Mat I) : EReal := traceLog (regularizedTrace t a rho sigma)

/-- Trace-normalized finite-order divergence, including the entropy value at one, PDF pp.8-10. -/
def finiteD {I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : ℝ) (rho sigma : Mat I) : EReal :=
  if a = 1 then (((rho.trace.re)⁻¹ : ℝ) : EReal) * relativeEntropy rho sigma
  else (((a-1)⁻¹ : ℝ) : EReal) * (logTraceFunctional t a rho sigma - (Real.log rho.trace.re : EReal))

/-- Orders zero and infinity are limits, PDF p.13 (59)-(60). -/
def renyiValue {I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : EReal) (rho sigma : Mat I) : EReal :=
  if a = ⊤ then Filter.liminf (fun z : ℝ => finiteD t z rho sigma) atTop
  else if a = 0 then Filter.liminf (fun z : ℝ => finiteD t z rho sigma) (𝓝[>] (0 : ℝ))
  else finiteD t a.toReal rho sigma

/-- Sign convention (36), PDF p.10. -/
def renyiSign (a : ℝ) : ℝ := if a < 1 then -1 else 1

/-- Convex extended-valued functions via their real epigraphs. This retains empty
and unbounded extrema instead of assigning real sSup/sInf default values; PDF p.4. -/
def EConvexOn {V : Type} [AddCommMonoid V] [Module ℝ V]
    (S : Set V) (f : V → EReal) : Prop :=
  Convex ℝ S ∧ Convex ℝ {p : V × ℝ | p.1 ∈ S ∧ f p.1 ≤ (p.2 : EReal)}

/-- Concavity is convexity of the negative, PDF pp.39-40. -/
def EConcaveOn {V : Type} [AddCommMonoid V] [Module ℝ V]
    (S : Set V) (f : V → EReal) : Prop := EConvexOn S (fun x => -f x)

/-- Tensor product entries, including the scalar tensor unit at n=0, PDF p.6. -/
def tensorEntries {I : Type} (n : ℕ) (A : Fin n → Mat I) : Mat (Fin n → I) :=
  fun u v => ∏ k, A k (u k) (v k)

/-- States on a specified support, PDF p.3. -/
def statesOn {I : Type} [Fintype I] [DecidableEq I] (A : Mat I) : Set (Mat I) :=
  {tau | IsDensityMatrix tau ∧ SupportIncluded tau A}

/-- Weighted entropy objective; at order one the zero-coefficient entropy is omitted, PDF p.10. -/
def entropyObjective {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma tau : Mat I) : EReal :=
  if a = 1 then relativeEntropy tau rho
  else (a : EReal) * relativeEntropy tau rho + ((1-a : ℝ) : EReal) * relativeEntropy tau sigma

/-- Dual objective from (39), PDF p.10, before correcting the trace-normalization constant. -/
def dualObjective {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma tau : Mat I) : EReal :=
  (renyiSign a : EReal) * (relativeEntropy tau sigma - ((a/(a-1) : ℝ) : EReal) * relativeEntropy tau rho)

/-- Gibbs numerator in (40), PDF p.10. -/
def logEuclideanGibbs {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (rho sigma : Mat I) : Mat I :=
  let P := meetSupport rho sigma
  P * cfc Real.exp ((a : ℂ) • (P * lnOp rho * P) + ((1-a : ℝ) : ℂ) • (P * lnOp sigma * P))

/-- Optimizer (40); used only when its denominator is finite and positive, PDF p.10. -/
def logEuclideanOptimizer {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (rho sigma : Mat I) : Mat I :=
  ((regularizedTrace .b a rho sigma).toReal⁻¹ : ℂ) • logEuclideanGibbs a rho sigma

/-- Minimum with attainment, to distinguish min from inf, PDF pp.10-11. -/
def Minimizes {T : Type} (S : Set T) (f : T → EReal) (x : T) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

/-- Maximum with attainment, PDF pp.10-11. -/
def AttainsMaximum {T : Type} (S : Set T) (f : T → EReal) (x : T) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, f y ≤ f x

/-- Finitely supported laws on an arbitrary alphabet, PDF p.6. The fallback is unused on lawful input. -/
def lawSupport {X : Type} (p : X → ℝ) : Finset X :=
  if h : (Function.support p).Finite then h.toFinset else ∅

/-- Exact finite-law domain; no finite-alphabet assumption, PDF p.6. -/
def FiniteInputLaw {X : Type} (p : X → ℝ) : Prop :=
  (Function.support p).Finite ∧ (∀ x, 0 ≤ p x) ∧ ∑ x ∈ lawSupport p, p x = 1

/-- General probability mass functions, allowing countably infinite support, PDF p.23. -/
def MassLaw {X : Type} (p : X → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ Summable p ∧ ∑' x, p x = 1

/-- A channel has normalized density outputs, PDF p.6. -/
def CQ {X I : Type} [Fintype I] (W : X → Mat I) : Prop := ∀ x, IsDensityMatrix (W x)

/-- Lifted finite-law output, with a finite classical label register, PDF p.6 (14). -/
def lifted {X I : Type} [Fintype I] (p : X → ℝ) (W : X → Mat I) :
    Mat ({x // x ∈ lawSupport p} × I) :=
  fun u v => if u.1 = v.1 then (p u.1.1 : ℂ) * W u.1.1 u.2 v.2 else 0

/-- Product comparison P tensor sigma in (80), PDF p.20. -/
def comparison {X I : Type} (p : X → ℝ) (sigma : Mat I) :
    Mat ({x // x ∈ lawSupport p} × I) :=
  fun u v => if u.1 = v.1 then (p u.1.1 : ℂ) * sigma u.2 v.2 else 0

/-- Both fixed-law information objectives are defined before optimization, PDF p.20 (80)-(81). -/
def informationObjective {X I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : EReal) (i : Fin 2) (W : X → Mat I) (p : X → ℝ) (sigma : Mat I) : EReal :=
  if i = 0 then renyiValue t a (lifted p W) (comparison p sigma)
  else ∑ x ∈ lawSupport p, (p x : EReal) * renyiValue t a (W x) sigma

/-- The two fixed-law Holevo quantities (indices 0 and 1 represent printed i=1,2), PDF p.20. -/
def fixedLawInformation {X I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : EReal) (i : Fin 2) (W : X → Mat I) (p : X → ℝ) : EReal :=
  ⨅ sigma : {A : Mat I // IsDensityMatrix A}, informationObjective t a i W p sigma.1

/-- Capacity is the first-type finite-law supremum, PDF p.20 (83)-(84).
No equality with the second type or radius is assumed. -/
def cqRenyiCapacity {X I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : EReal) (W : X → Mat I) : EReal :=
  ⨆ p : {p : X → ℝ // FiniteInputLaw p}, fixedLawInformation t a 0 W p.1

/-- Divergence radius (85), independent of capacity, PDF p.20. -/
def cqRenyiRadius {X I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : EReal) (W : X → Mat I) : EReal :=
  ⨅ sigma : {A : Mat I // IsDensityMatrix A}, ⨆ x, renyiValue t a (W x) sigma.1

/-- Holevo information uses normalized Umegaki divergence, PDF p.19 (76)-(77). -/
def ordinaryLawInformation {X I : Type} [Fintype I] [DecidableEq I] (W : X → Mat I) (p : X → ℝ) : EReal :=
  fixedLawInformation .petz 1 1 W p

/-- Product channel, PDF p.6. -/
def memorylessOutputs {X I : Type} (W : X → Mat I) (n : ℕ) (x : Fin n → X) : Mat (Fin n → I) :=
  tensorEntries n (fun k => W (x k))

/-- Product input mass, PDF p.6. -/
def independentInputLaw {X : Type} (p : X → ℝ) (n : ℕ) (x : Fin n → X) : ℝ := ∏ k, p (x k)

/-- Permutation-invariant operator, PDF p.5; the action uses inverse permutations. -/
def TensorPermutationInvariant {I : Type} {n : ℕ} (A : Mat (Fin n → I)) : Prop :=
  ∀ (pi : Equiv.Perm (Fin n)) u v, A (u ∘ pi.symm) (v ∘ pi.symm) = A u v

/-- Symmetric input probability density, PDF p.23. -/
def SymmetricLaw {X : Type} {n : ℕ} (p : (Fin n → X) → ℝ) : Prop :=
  ∀ (pi : Equiv.Perm (Fin n)) x, p (x ∘ pi.symm) = p x

/-- A chosen universal symmetric state with all conditions of Lemma II.8, PDF pp.5-6. -/
structure Universal (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) where
  state : Mat (Fin n → I)
  v : ℕ
  density : IsDensityMatrix state
  symmetric : TensorPermutationInvariant state
  central : ∀ A : Mat (Fin n → I), TensorPermutationInvariant A → state * A = A * state
  dominates : ∀ A : Mat (Fin n → I), IsDensityMatrix A → TensorPermutationInvariant A →
    (((v : ℝ) : ℂ) • state - A).PosSemidef
  spectralBound : (eigenvalues state).card ≤ v
  polynomialBound : (v : ℝ) ≤ Real.rpow (n+1 : ℕ) (((Fintype.card I + 2 : ℕ) : ℝ) *
    ((Fintype.card I : ℝ) - 1) / 2)

/-- Channel pinched by a chosen universal symmetric state, PDF p.23. -/
def pinchedChannel {X I : Type} [Fintype I] [DecidableEq I]
    (W : X → Mat I) (n : ℕ) (U : Universal I n) : (Fin n → X) → Mat (Fin n → I) :=
  fun x => pinch U.state (memorylessOutputs W n x)

/-- Infinite block-sum objectives for IV.9. Nonnegative ENNReal sums retain infinite
values; finite classical label spaces are not imposed on the mass function, PDF p.23. -/
def massObjective {X I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : ℝ) (i : Fin 2) (W : X → Mat I) (p : X → ℝ) (sigma : Mat I) : EReal :=
  if i = 0 then (((a-1)⁻¹ : ℝ) : EReal) *
    traceLog ((∑' x, ENNReal.ofReal (p x) * asNN (regularizedTrace t a (W x) sigma) : ℝ≥0∞) : EReal)
  else ((∑' x, ENNReal.ofReal (p x) * asNN (renyiValue t a (W x) sigma) : ℝ≥0∞) : EReal)

/-- General-law information for IV.9, using the block sums (96)-(97), PDF pp.23-24. -/
def massInformation {X I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (a : ℝ) (i : Fin 2) (W : X → Mat I) (p : X → ℝ) : EReal :=
  ⨅ sigma : {A : Mat I // IsDensityMatrix A}, massObjective t a i W p sigma.1

/-- Deterministic encoder and one shared POVM; repeated words and zero effects allowed,
PDF p.26. Both blocklength and message count are positive in every use. -/
structure CQBlockCode (X I : Type) [Fintype I] [DecidableEq I] (n : ℕ) where
  messages : ℕ
  positiveMessages : 0 < messages
  encoder : Fin messages → Fin n → X
  decoder : Fin messages → Mat (Fin n → I)
  positiveDecoder : ∀ m, (decoder m).PosSemidef
  completeDecoder : ∑ m, decoder m = 1

/-- Uniform-message average success, PDF p.26. -/
def cqAverageSuccess {X I : Type} [Fintype I] [DecidableEq I]
    (W : X → Mat I) {n : ℕ} (C : CQBlockCode X I n) : ℝ :=
  (C.messages : ℝ)⁻¹ * ∑ m, (memorylessOutputs W n (C.encoder m) * C.decoder m).trace.re

/-- One sequence simultaneously meets the two liminf criteria, Definition V.1, PDF p.26.
Index k represents positive blocklength k+1. -/
def CQExponentAchievable {X I : Type} [Fintype I] [DecidableEq I]
    (W : X → Mat I) (R r : ℝ) : Prop :=
  ∃ C : (k : ℕ) → CQBlockCode X I (k+1),
    (R : EReal) ≤ Filter.liminf (fun k => ((Real.log (C k).messages / (k+1 : ℕ) : ℝ) : EReal)) atTop ∧
    (-r : EReal) ≤ Filter.liminf (fun k => (((k+1 : ℕ) : ℝ)⁻¹ : EReal) * traceLog (cqAverageSuccess W (C k))) atTop

/-- Infimum of real R-achievable success exponents, with extended empty infimum,
Definition V.1, PDF pp.26-27. -/
def sc {X I : Type} [Fintype I] [DecidableEq I] (W : X → Mat I) (R : ℝ) : EReal :=
  sInf {z | ∃ r : ℝ, z = (r : EReal) ∧ CQExponentAchievable W R r}

/-- Converse Hoeffding capacity (108), PDF p.27. -/
def converseCapacityTransform {X I : Type} [Fintype I] [DecidableEq I]
    (t : Flavor) (W : X → Mat I) (R : ℝ) : EReal :=
  ⨆ a : {a : ℝ // 1 < a}, (((a.1-1)/a.1 : ℝ) : EReal) * ((R : EReal) - cqRenyiCapacity t a.1 W)

/-- Conditional relative entropy, PDF p.28. -/
def conditionalUmegaki {X I : Type} [Fintype I] [DecidableEq I]
    (p : X → ℝ) (V W : X → Mat I) : EReal :=
  ∑ x ∈ lawSupport p, (p x : EReal) * relativeEntropy (V x) (W x)

/-- The constructed dummy-channel objective (112), PDF pp.28-29. -/
def dummyF {X I : Type} [Fintype I] [DecidableEq I]
    (p : X → ℝ) (R : ℝ) (W : X → Mat I) : EReal :=
  ⨅ V : {V : X → Mat I // CQ V}, conditionalUmegaki p V.1 W + max 0 ((R : EReal) - ordinaryLawInformation V.1 p)

/-- First constrained infimum (113), PDF p.29; an empty feasible set gives +infinity. -/
def dummyF1 {X I : Type} [Fintype I] [DecidableEq I]
    (p : X → ℝ) (R : ℝ) (W : X → Mat I) : EReal :=
  ⨅ V : {V : X → Mat I // CQ V ∧ (R : EReal) < ordinaryLawInformation V p}, conditionalUmegaki p V.1 W

/-- Second constrained infimum (114), PDF p.29. -/
def dummyF2 {X I : Type} [Fintype I] [DecidableEq I]
    (p : X → ℝ) (R : ℝ) (W : X → Mat I) : EReal :=
  ⨅ V : {V : X → Mat I // CQ V ∧ ordinaryLawInformation V p ≤ (R : EReal)},
    conditionalUmegaki p V.1 W + (R : EReal) - ordinaryLawInformation V.1 p

/-- Quantum n-block codes allow arbitrary entangled input density operators, PDF p.36. -/
structure QuantumBlockCode (I J : Type) [Fintype I] [Fintype J] [DecidableEq J] (n : ℕ) where
  messages : ℕ
  positiveMessages : 0 < messages
  encoder : Fin messages → Mat (Fin n → I)
  densityEncoder : ∀ m, IsDensityMatrix (encoder m)
  decoder : Fin messages → Mat (Fin n → J)
  positiveDecoder : ∀ m, (decoder m).PosSemidef
  completeDecoder : ∑ m, decoder m = 1

/-- Quantum-channel success uses the full linear tensor extension, PDF p.36. -/
def quantumAverageSuccess {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) {n : ℕ} (C : QuantumBlockCode I J n) : ℝ :=
  (C.messages : ℝ)⁻¹ * ∑ m, (piSuperop (fun _ : Fin n => N) (C.encoder m) * C.decoder m).trace.re

/-- Quantum-channel counterpart of Definition V.1, PDF p.36. -/
def QuantumExponentAchievable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) (R r : ℝ) : Prop :=
  ∃ C : (k : ℕ) → QuantumBlockCode I J (k+1),
    (R : EReal) ≤ Filter.liminf (fun k => ((Real.log (C k).messages / (k+1 : ℕ) : ℝ) : EReal)) atTop ∧
    (-r : EReal) ≤ Filter.liminf (fun k => (((k+1 : ℕ) : ℝ)⁻¹ : EReal) * traceLog (quantumAverageSuccess N (C k))) atTop

/-- Operational quantum strong converse exponent, PDF p.36. -/
def quantumSc {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) (R : ℝ) : EReal :=
  sInf {z | ∃ r : ℝ, z = (r : EReal) ∧ QuantumExponentAchievable N R r}

/-- Associated cq channel has all input DENSITY operators as alphabet, PDF p.36. -/
def associated {I J : Type} [Fintype I] (N : Superop I J) :
    {rho : Mat I // IsDensityMatrix rho} → Mat J := fun rho => N rho.1

/-- Quantum-channel capacity over all finite ensembles of density operators, PDF p.36. -/
def quantumRenyiCapacity {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (a : EReal) (N : Superop I J) : EReal := cqRenyiCapacity .star a (associated N)

/-- Renyi entropy, with its entropy limit at one, PDF p.37. -/
def outputRenyiEntropy {J : Type} [Fintype J] [DecidableEq J] (a : ℝ) (rho : Mat J) : EReal :=
  if a = 1 then -((rho * lnOp rho).trace.re : EReal)
  else (((1-a)⁻¹ : ℝ) : EReal) * traceLog ((supportPower rho a).trace.re)

/-- Minimum-output entropy, PDF p.37. Lemma VI.2 also records attainment of
this infimum in its parameter range, so the minimum is not silently weakened. -/
def minOutputEntropy {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (a : ℝ) (N : Superop I J) : EReal :=
  ⨅ rho : {rho : Mat I // IsDensityMatrix rho}, outputRenyiEntropy a (N rho.1)

/-- Group covariance includes irreducibility only at the output, PDF pp.36-37.
Compactness and continuity are carried by the theorem's group and representation binders. -/
def IrreducibleOutputCovariance {G I J : Type} [Group G] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (N : Superop I J)
    (Uin : G →* Matrix.unitaryGroup I ℂ) (Uout : G →* Matrix.unitaryGroup J ℂ) : Prop :=
  (∀ S : Submodule ℂ (J → ℂ),
    (∀ g v, v ∈ S → ((Uout g : Mat J).mulVec v) ∈ S) → S = ⊥ ∨ S = ⊤) ∧
  ∀ g A, N ((Uin g : Mat I) * A * (Uin g : Mat I)ᴴ) =
    (Uout g : Mat J) * N A * (Uout g : Mat J)ᴴ

/-- KW class requires self-tensor minimum-output entropy additivity at EVERY a>1,
PDF p.37, in addition to the covariance hypotheses. -/
def KWAdditive {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (N : Superop I J) : Prop :=
  ∀ a : ℝ, 1 < a → ∀ n : ℕ,
    minOutputEntropy a (piSuperop (fun _ : Fin n => N)) = (n : EReal) * minOutputEntropy a N

/-- Finite-dimensional entanglement-breaking channels in their equivalent
measure-and-prepare form, §VI A, PDF p.36. Effects and outputs are actual matrices. -/
def FiniteMeasurePrepare {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (N : Superop I J) : Prop :=
  ∃ (m : ℕ) (E : Fin m → Mat I) (tau : Fin m → Mat J),
    (∀ k, (E k).PosSemidef) ∧ (∑ k, E k = 1) ∧ (∀ k, IsDensityMatrix (tau k)) ∧
    ∀ A, N A = ∑ k, (A * E k).trace • tau k

/-- Generic trace functional of Appendix B, across finite register types, PDF p.39. -/
abbrev TraceFamily := ∀ {I : Type} [Fintype I] [DecidableEq I], ℝ → Mat I → Mat I → ℝ≥0∞

/-- Classical agreement on commuting positive pairs, Appendix B, PDF p.39. -/
def ClassicalAgreement (Q : TraceFamily) : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (a : ℝ) (rho sigma : Mat I),
    0 < a → a ≠ 1 → NonzeroPSD rho → NonzeroPSD sigma → Commute rho sigma →
    Q a rho sigma = if 1 < a ∧ ¬ SupportIncluded rho sigma then ⊤
      else ENNReal.ofReal (supportPower rho a * supportPower sigma (1-a)).trace.re

/-- Generic trace-normalized finite-order divergence (B1), PDF p.39. -/
def genericD (Q : TraceFamily) {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho sigma : Mat I) : EReal :=
  (((a-1)⁻¹ : ℝ) : EReal) * (traceLog (Q a rho sigma : EReal) - (Real.log rho.trace.re : EReal))

/-- Generic two Holevo quantities of Appendix B; actual lifted first argument,
so no block-additivity axiom is silently added to the generic Q, PDF p.39. -/
def genericInfo (Q : TraceFamily) {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (i : Fin 2) (W : X → Mat I) (p : X → ℝ) : EReal :=
  ⨅ sigma : {A : Mat I // IsDensityMatrix A},
    if i = 0 then genericD Q a (lifted p W) (comparison p sigma.1)
    else ∑ x ∈ lawSupport p, (p x : EReal) * genericD Q a (W x) sigma.1

/-- Auxiliary function with the trace normalization retained, PDF p.39. -/
def normalizedAuxiliary (Q : TraceFamily) {X I : Type} [Fintype I] [DecidableEq I]
    (i : Fin 2) (W : X → Mat I) (p : X → ℝ) (s : ℝ) : EReal :=
  let a := 1/(1+s)
  ((-(a-1)/a : ℝ) : EReal) * genericInfo Q a i W p

/-- Explicit Petz auxiliary expression, without presuming trace-one outputs, PDF p.40. -/
def explicitAuxiliary {X I : Type} [Fintype I] [DecidableEq I]
    (W : X → Mat I) (p : X → ℝ) (s : ℝ) : EReal :=
  -traceLog ((supportPower (∑ x ∈ lawSupport p, (p x : ℂ) • supportPower (W x) (1/(1+s))) (1+s)).trace.re)

/-! Sanity checks pin conventions and degenerate cases; they do not prove target results. -/

example : traceLog 0 = ⊥ := by simp [traceLog]

example {I : Type} [Fintype I] [DecidableEq I] (A B : Mat I)
    (h : ¬ SupportIncluded A B) : relativeEntropy A B = ⊤ := by
  have hker : ¬ QAlgorithms.Papers.Independent.Dependency50.P21.IsSupported A B := h
  simp [relativeEntropy, hker]

example {I : Type} [Fintype I] [DecidableEq I] (A B : Mat I) :
    entropyObjective 1 A B A = relativeEntropy A A := by simp [entropyObjective]

example {I : Type} (A : Mat I) (u v : Fin 0 → I) : copies 0 A u v = 1 := by
  simp [copies]

example {X : Type} (p : X → ℝ) (x : Fin 0 → X) : independentInputLaw p 0 x = 1 := by
  simp [independentInputLaw]

example {I : Type} [Fintype I] [DecidableEq I] :
    supportPower (0 : Mat I) (-1) = 0 := by simp [supportPower, cfc_zero]

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Global joint convexity over every positive finite dimension, PDF p.14. -/
def JointConvexQ (t : Flavor) (a : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → EConvexOn
    {p : Mat (Fin d) × Mat (Fin d) | NonzeroPSD p.1 ∧ NonzeroPSD p.2}
    (fun p => (renyiSign a : EReal) * regularizedTrace t a p.1 p.2)

/-- Data processing under every finite-dimensional CPTP map, PDF p.14.
Dimensions are quantified globally; witnesses may depend on the order. -/
def DataProcessing (t : Flavor) (a : EReal) : Prop :=
  ∀ d e : ℕ, 0 < d → 0 < e → ∀ (rho sigma : Mat (Fin d)) (N : Superop (Fin d) (Fin e)),
    NonzeroPSD rho → NonzeroPSD sigma → IsChannel N →
      renyiValue t a (N rho) (N sigma) ≤ renyiValue t a rho sigma

/-- Finite-order separate-convexity range, PDF p.15. -/
def SeparateRange (t : Flavor) (a : ℝ) : Prop :=
  match t with
  | .petz => 0 ≤ a ∧ a ≤ 2
  | .star => 1/2 ≤ a
  | .b => 0 ≤ a

/-- Order-monotonicity range in the second matrix, PDF p.17. -/
def ReferenceRange (t : Flavor) (a : EReal) : Prop :=
  match t with
  | .petz => 0 ≤ a ∧ a ≤ 1
  | .star => (1/2 : EReal) ≤ a
  | .b => 0 ≤ a

/-- Regularization parameter ranges (72), PDF p.17. -/
def RegularRange (t : Flavor) (a : ℝ) : Prop :=
  0 < a ∧ a ≠ 1 ∧ (t = .b → 1 < a)

/-- Parameter range for the four identifications in IV.2, PDF p.20. -/
def CapacityRange (t : Flavor) (a : ℝ) : Prop :=
  match t with
  | .petz => 0 < a ∧ a ≤ 2
  | .star => 1/2 ≤ a
  | .b => 1 < a

variable {X : Type} [Nonempty X] [Nonempty I]

variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

/-- Spectral ratios with overlapping positive spectral projections, PDF p.13 (61). -/
def spectralRatios (rho sigma : Mat I) : Set EReal :=
  {z | ∃ r ∈ eigenvalues rho, ∃ s ∈ eigenvalues sigma,
    0 < r ∧ 0 < s ∧ 0 < (spectralProjector rho r * spectralProjector sigma s).trace.re ∧ z = ((r/s : ℝ) : EReal)}

end QAlgorithms.Papers.Independent.Bridge50.P45


