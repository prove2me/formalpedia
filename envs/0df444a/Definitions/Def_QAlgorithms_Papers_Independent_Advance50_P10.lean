-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10
-- name    : QAlgorithms_Papers_Independent_Advance50_P10
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T21:30:22.819201+00:00
-- url     : https://prove2.me/theorems/5bfcba45-04f6-4fec-b30b-f67bedca5053
-- title:
--   Definitions for On the quantum Renyi relative entropies and related capacity formulas
-- statement:
--   The objects the formalized statements of *On the quantum Renyi relative entropies and related capacity formulas* (arXiv:0912.1286) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `petzTrace`: Unnormalized Petz trace, with support-only powers, §II, PDF p.3.
--   - `quasiRelative`: Signed quasi-relative entropy, §II, PDF p.3. Order one is unused for Q.
--   - `petzRelativeBits`: The paper's unnormalized Petz relative entropy, with the Umegaki value at one. No division by Tr A is made. In particular A=0 gives minus infinity above one. §II, PDF p.3.
--   - `perturb`: Identity perturbation of the second argument, PDF p.3, (12)–(13).
--   - `petzEntropyBits`: Rényi entropy in bits, PDF p.4, before (18). Used on densities, whose existence forces card I > 0.
--   - `petzHoeffdingBits`: Hoeffding transform, PDF p.4, (19). All extrema are extended-real extrema.
--   - `cqWordChannel`: The memoryless extension on product input words, PDF p.9.
--   - `FinitelySupportedInputLaw`: All finite-support input laws on an arbitrary alphabet, §I, PDF p.2.
--   - `lawObjective`: Lifted fixed-centre divergence, (8), PDF p.2.
--   - `petzLawInformationBits`: Type-1 fixed-law information, (35),(44), PDF pp.8,11.
--   - `capacityOne`: Type-1 capacity, (8), PDF p.2.
--   - `averageDivergence`: Average divergence from a centre, (9), PDF p.2; zero weights are omitted.
--   - `capacityTwo`: Type-2 capacity, (9), PDF p.2.
--   - `divergenceRadiusBits`: Divergence radius, (6),(10), PDF p.2. No attainment is built into the definition.
--   - `sibsonRoot`: Root of the average powered output, PDF p.8, following (33).
--   - `sibsonCentre`: Normalized Sibson root; its positive trace follows from the law and density outputs. PDF p.8, (34).
--   - `sibsonInformation`: The closed trace formula, used only for a>1, PDF p.8, (33)–(36).
--   - `CQWordCode`: Actual finite code with a positive message count and a normalized POVM, PDF p.8.
--   - `cqCodeSuccess`: Average success probability, PDF p.8.
--   - `cqOneShotCapacityBits`: One-shot capacity in bits. The extended supremum also covers epsilon=1. For 0<=epsilon<1 it equals the printed maximum, PDF p.8.
--   - `CodeSequence`: A sequence of actual product-encoding codes, PDF p.9.
--   - `cqSequenceRateBits`: Source rate: the liminf of log M divided by positive block length, PDF p.9. The n=0 value has no effect on the tail limit.
--   - `asymptoticCapacity`: Product-encoding asymptotic average-error capacity, PDF p.9.
--   - `successExponent`: Upper success exponent, retaining log 0=-infinity, PDF p.9.
--   - `typeOneError`: Type-I test error, §I, PDF p.1.
--   - `typeTwoError`: Type-II test error, §I, PDF p.1.
--   - `CorrelatedEffectSequence`: All actual binary tests on a sequence of finite spaces, PDF pp.4–5.
--   - `upperTestingPositive`: Operational upper Hoeffding exponent at positive r, PDF p.4. The first-kind constraint is strict, and no equality with a transform is assumed.
--   - `upperTesting`: At r=0 use the right limit (the infimum on r>0 for this monotone function). This supplies the endpoint used but not explicitly defined in (22), PDF pp.4–5.
--   - `testingCutoff`: Operational negative-slope cutoff, (22), PDF p.5. Unbounded feasible intercepts produce +infinity, as required for orthogonal states.
--   - `meanRenyi`: Mean Rényi entropy as a tail liminf; hypotheses below assert actual convergence. PDF p.5. No exponent identity is encoded in this definition.
--   - `UniformLogTraceLimit`: Theorem III.3's real limiting log trace, uniform on [0,1), PDF p.5. Uniformity is expressed by real error bands in EReal, so no infinities are discarded. The one N works simultaneously for every order a in the interval.
--   - `measureObjective`: The all-measure f and g integrals on K, §IV, PDF p.6. false selects S and true selects signed Q.
--   - `pointObjective`: The corresponding point objective, §IV, PDF p.6.
--   - `FiniteMeasureLaw`: The finitely supported subset of all Borel probability measures, PDF p.6.
--   - `MeasureMixture`: Exact affine-combination relation on probability measures, PDF p.6.
--   - `MeasureAffine`: Affinity without choosing a separate vector-space structure on probability laws, PDF p.6.
--   - `DensityConvex`: Convexity on density operators, using all actual mixtures, PDF pp.3,6.
--   - `ReachesMinimum`: Minimum is asserted by a witness, rather than only an extended infimum, PDF pp.6–7.
--   - `ReachesMaximum`: Maximum is asserted by a witness, PDF p.6.
--   - `SingularMinimax`: The complete chain (28)–(29), with all printed minima attained, PDF p.7. P can be all measures or its finite-support subtype.
--   - `RegularizedMinimax`: The stronger attained chain (25)–(26), PDF p.6.
--   - `CentreFamily`: Selection of regularized minimizing centres, PDF p.6, after IV.3. Only the defining minimization property, not the singular conclusion, is assumed.
--   - `CentreLimit`: The limit centre is tied to a selected family and a positive sequence tending to zero. PDF p.6, bottom right.
--   - `infinityRelative`: Infinite-order Petz relative entropy, PDF p.4.
--   - `helstromWeight`: The optimal common-mixture weight. The finite normalized family has a finite radius. The source exponential is interpreted as 2^x in bits, PDF p.9.
--   - `CommonMixture`: Feasible common mixture, including q=1 for an identical family, PDF p.9.
--   - `exampleFirst`: First classical distribution in the negative example, PDF p.10.
--   - `exampleSecond`: Second classical distribution in the negative example, PDF p.10.
--   - `exampleCentre`: The normalized coordinatewise maximum in the negative example, PDF p.10.
--   - `pairFamily`: Two states viewed as a family, PDF pp.9–10.
--   - `ApproximatelyAffine`: General-state affine relation. The states are the accepted positive trace-class operators on an arbitrary complete complex Hilbert space, PDF p.9, (37).
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, https://arxiv.org/abs/0912.1286v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P25
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P45

/-! Mosonyi–Hiai, arXiv:0912.1286v4. Page citations are PDF pages.
All logarithms are in bits. Powers vanish on the kernel, even at order zero.
The accepted library is used only for its audited concrete primitives.
The signed, unnormalized bit-valued Petz quantities below are specific to this paper.
Compatible frozen primitives are imported; incompatible same-named primitives are not substituted.
Compilation and independent moderation are pending the batch handoff. -/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology
open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P58 (Operator)
open QAlgorithms.Papers.Independent.Information100.P60 (copies)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)
open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)
open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)
open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)
open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.
/-- Borel laws on density operators, §IV, PDF p.6. -/
local instance densityMeasurableSpace (I : Type) [Fintype I] :
    MeasurableSpace ({A : Operator I // IsDensityMatrix A}) := borel ({A : Operator I // IsDensityMatrix A})

/-- The source measurable structure is the Borel structure, §IV, PDF p.6. -/
local instance densityBorelSpace (I : Type) [Fintype I] :
    BorelSpace ({A : Operator I // IsDensityMatrix A}) := ⟨rfl⟩

/-- Unnormalized Petz trace, with support-only powers, §II, PDF p.3. -/
def petzTrace {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (A B : Operator I) : ℝ :=
  (supportPower A a * supportPower B (1 - a)).trace.re

/-- Signed quasi-relative entropy, §II, PDF p.3. Order one is unused for Q. -/
def quasiRelative {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (A B : Operator I) : EReal :=
  if 1 < a ∧ ¬ SupportIncluded A B then ⊤
  else ((if a < 1 then -1 else 1 : ℝ) * petzTrace a A B : ℝ)

/-- The paper's unnormalized Petz relative entropy, with the Umegaki value at one.
No division by Tr A is made. In particular A=0 gives minus infinity above one.
§II, PDF p.3. -/
def petzRelativeBits {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (A B : Operator I) : EReal :=
  if a = 1 then ((1 / Real.log 2 : ℝ) : EReal) * relativeEntropy A B
  else if 1 < a ∧ ¬ SupportIncluded A B then ⊤
  else (((a - 1)⁻¹ : ℝ) : EReal) * logBits (petzTrace a A B : EReal)

/-- Identity perturbation of the second argument, PDF p.3, (12)–(13). -/
def perturb {I : Type} [Fintype I] [DecidableEq I]
    (B : Operator I) (e : ℝ) : Operator I := B + (e : ℂ) • 1

/-- Rényi entropy in bits, PDF p.4, before (18).
Used on densities, whose existence forces card I > 0. -/
def petzEntropyBits {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho : Operator I) : EReal :=
  (Real.logb 2 (Fintype.card I : ℝ) : EReal) -
    petzRelativeBits a rho (((Fintype.card I : ℝ)⁻¹ : ℂ) • 1)

/-- Hoeffding transform, PDF p.4, (19). All extrema are extended-real extrema. -/
def petzHoeffdingBits {I : Type} [Fintype I] [DecidableEq I]
    (r : ℝ) (rho sigma : Operator I) : EReal :=
  ⨆ a : {a : ℝ // 0 ≤ a ∧ a < 1},
    ((-a.1 * r / (1 - a.1) : ℝ) : EReal) + petzRelativeBits a.1 rho sigma

/-- The memoryless extension on product input words, PDF p.9. -/
def cqWordChannel {X I : Type} (W : X → Operator I) (n : ℕ)
    (x : Fin n → X) : Operator (Fin n → I) := tensorEntries n (fun k => W (x k))

/-- All finite-support input laws on an arbitrary alphabet, §I, PDF p.2. -/
def FinitelySupportedInputLaw (X : Type) :=
  {p : X →₀ ℝ // (∀ x, 0 ≤ p x) ∧ p.sum (fun _ w => w) = 1}

/-- Lifted fixed-centre divergence, (8), PDF p.2. -/
def lawObjective {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) (p : FinitelySupportedInputLaw X) (sigma : Operator I) : EReal :=
  petzRelativeBits a (lifted (fun x => p.1 x) W) (comparison (fun x => p.1 x) sigma)

/-- Type-1 fixed-law information, (35),(44), PDF pp.8,11. -/
def petzLawInformationBits {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) (p : FinitelySupportedInputLaw X) : EReal :=
  ⨅ sigma : {A : Operator I // IsDensityMatrix A}, lawObjective a W p sigma.1

/-- Type-1 capacity, (8), PDF p.2. -/
def capacityOne {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) : EReal := ⨆ p : FinitelySupportedInputLaw X, petzLawInformationBits a W p

/-- Average divergence from a centre, (9), PDF p.2; zero weights are omitted. -/
def averageDivergence {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) (p : FinitelySupportedInputLaw X) (sigma : Operator I) : EReal :=
  ∑ x ∈ p.1.support, (p.1 x : EReal) * petzRelativeBits a (W x) sigma

/-- Type-2 capacity, (9), PDF p.2. -/
def capacityTwo {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) : EReal :=
  ⨆ p : FinitelySupportedInputLaw X, ⨅ sigma : {A : Operator I // IsDensityMatrix A}, averageDivergence a W p sigma.1

/-- Divergence radius, (6),(10), PDF p.2. No attainment is built into the definition. -/
def divergenceRadiusBits {X I : Type} [Fintype I] [DecidableEq I]
    (D : Operator I → Operator I → EReal) (W : X → Operator I) : EReal :=
  ⨅ sigma : {A : Operator I // IsDensityMatrix A}, ⨆ x, D (W x) sigma.1

/-- Root of the average powered output, PDF p.8, following (33). -/
def sibsonRoot {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) (p : FinitelySupportedInputLaw X) : Operator I :=
  supportPower (p.1.sum (fun x w => (w : ℂ) • supportPower (W x) a)) (1 / a)

/-- Normalized Sibson root; its positive trace follows from the law and density outputs.
PDF p.8, (34). -/
def sibsonCentre {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) (p : FinitelySupportedInputLaw X) : Operator I :=
  (((sibsonRoot a W p).trace.re)⁻¹ : ℂ) • sibsonRoot a W p

/-- The closed trace formula, used only for a>1, PDF p.8, (33)–(36). -/
def sibsonInformation {X I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (W : X → Operator I) (p : FinitelySupportedInputLaw X) : EReal :=
  ((a / (a - 1) : ℝ) : EReal) * logBits ((sibsonRoot a W p).trace.re : EReal)

/-- Actual finite code with a positive message count and a normalized POVM, PDF p.8. -/
structure CQWordCode (X I : Type) [Fintype I] [DecidableEq I] where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → X
  decode : Fin messages → Operator I
  valid_decode : IsPOVM decode

/-- Average success probability, PDF p.8. -/
def cqCodeSuccess {X I : Type} [Fintype I] [DecidableEq I]
    (W : X → Operator I) (C : CQWordCode X I) : ℝ :=
  (C.messages : ℝ)⁻¹ * ∑ i, (W (C.encode i) * C.decode i).trace.re

/-- One-shot capacity in bits. The extended supremum also covers epsilon=1.
For 0<=epsilon<1 it equals the printed maximum, PDF p.8. -/
def cqOneShotCapacityBits {X I : Type} [Fintype I] [DecidableEq I]
    (e : ℝ) (W : X → Operator I) : EReal :=
  sSup {v | ∃ C : CQWordCode X I, 1 - cqCodeSuccess W C ≤ e ∧
    v = (Real.logb 2 (C.messages : ℝ) : EReal)}

/-- A sequence of actual product-encoding codes, PDF p.9. -/
abbrev CodeSequence (X I : Type) [Fintype I] [DecidableEq I] :=
  (n : ℕ) → CQWordCode (Fin n → X) (Fin n → I)

/-- Source rate: the liminf of log M divided by positive block length, PDF p.9.
The n=0 value has no effect on the tail limit. -/
def cqSequenceRateBits {X I : Type} [Fintype I] [DecidableEq I]
    (C : CodeSequence X I) : EReal :=
  Filter.liminf (fun n : ℕ => (Real.logb 2 ((C n).messages : ℝ) / (n : ℝ) : EReal)) atTop

/-- Product-encoding asymptotic average-error capacity, PDF p.9. -/
def asymptoticCapacity {X I : Type} [Fintype I] [DecidableEq I]
    (e : ℝ) (W : X → Operator I) : EReal :=
  sSup {v | ∃ C : CodeSequence X I,
    Filter.limsup (fun n => (1 - cqCodeSuccess (cqWordChannel W n) (C n) : EReal)) atTop ≤
      (e : EReal) ∧ v = cqSequenceRateBits C}

/-- Upper success exponent, retaining log 0=-infinity, PDF p.9. -/
def successExponent {X I : Type} [Fintype I] [DecidableEq I]
    (W : X → Operator I) (C : CodeSequence X I) : EReal :=
  Filter.limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
    logBits (cqCodeSuccess (cqWordChannel W n) (C n) : EReal)) atTop

/-- Type-I test error, §I, PDF p.1. -/
def typeOneError {I : Type} [Fintype I] [DecidableEq I]
    (rho T : Operator I) : ℝ := (rho * (1 - T)).trace.re

/-- Type-II test error, §I, PDF p.1. -/
def typeTwoError {I : Type} [Fintype I] (sigma T : Operator I) : ℝ :=
  (sigma * T).trace.re

/-- All actual binary tests on a sequence of finite spaces, PDF pp.4–5. -/
abbrev CorrelatedEffectSequence (J : ℕ → Type) [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)] :=
  (n : ℕ) → {T : Operator (J n) // IsEffect T}

/-- Operational upper Hoeffding exponent at positive r, PDF p.4.
The first-kind constraint is strict, and no equality with a transform is assumed. -/
def upperTestingPositive {J : ℕ → Type} [∀ n, Fintype (J n)]
    [∀ n, DecidableEq (J n)] (c : ℕ → ℕ)
    (rho sigma : (n : ℕ) → Operator (J n)) (r : ℝ) : EReal :=
  sInf {v | ∃ T : CorrelatedEffectSequence J,
    Filter.limsup (fun n : ℕ => (((c n : ℝ)⁻¹ : ℝ) : EReal) *
      logBits (typeOneError (rho n) (T n).1 : EReal)) atTop < (-r : EReal) ∧
    v = Filter.limsup (fun n : ℕ => (((c n : ℝ)⁻¹ : ℝ) : EReal) *
      logBits (typeTwoError (sigma n) (T n).1 : EReal)) atTop}

/-- At r=0 use the right limit (the infimum on r>0 for this monotone function).
This supplies the endpoint used but not explicitly defined in (22), PDF pp.4–5. -/
def upperTesting {J : ℕ → Type} [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (c : ℕ → ℕ) (rho sigma : (n : ℕ) → Operator (J n)) (r : ℝ) : EReal :=
  if r = 0 then ⨅ t : {t : ℝ // 0 < t}, upperTestingPositive c rho sigma t.1
  else upperTestingPositive c rho sigma r

/-- Operational negative-slope cutoff, (22), PDF p.5. Unbounded feasible intercepts
produce +infinity, as required for orthogonal states. -/
def testingCutoff {J : ℕ → Type} [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (c : ℕ → ℕ) (rho sigma : (n : ℕ) → Operator (J n)) (k : ℝ) : EReal :=
  sSup {v | ∃ r0 : ℝ, 0 ≤ r0 ∧ v = (r0 : EReal) ∧
    ∀ r : ℝ, 0 ≤ r → upperTesting c rho sigma r ≤ (k * (r0 - r) : EReal)}

/-- Mean Rényi entropy as a tail liminf; hypotheses below assert actual convergence.
PDF p.5. No exponent identity is encoded in this definition. -/
def meanRenyi {J : ℕ → Type} [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (c : ℕ → ℕ) (rho sigma : (n : ℕ) → Operator (J n)) (a : ℝ) : EReal :=
  Filter.liminf (fun n : ℕ => (((c n : ℝ)⁻¹ : ℝ) : EReal) * petzRelativeBits a (rho n) (sigma n)) atTop

/-- Theorem III.3's real limiting log trace, uniform on [0,1), PDF p.5.
Uniformity is expressed by real error bands in EReal, so no infinities are discarded.
The one N works simultaneously for every order a in the interval. -/
def UniformLogTraceLimit {J : ℕ → Type} [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (c : ℕ → ℕ) (rho sigma : (n : ℕ) → Operator (J n)) (psi : ℝ → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℝ, 0 ≤ a → a < 1 →
    ((psi a - delta : ℝ) : EReal) ≤
      (((c n : ℝ)⁻¹ * (a - 1) : ℝ) : EReal) * petzRelativeBits a (rho n) (sigma n) ∧
    (((c n : ℝ)⁻¹ * (a - 1) : ℝ) : EReal) * petzRelativeBits a (rho n) (sigma n) ≤
      ((psi a + delta : ℝ) : EReal)

/-- The all-measure f and g integrals on K, §IV, PDF p.6.
false selects S and true selects signed Q. -/
def measureObjective {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (useQ : Bool) (a e : ℝ)
    (p : ProbabilityMeasure K) (sigma : {A : Operator I // IsDensityMatrix A}) : EReal :=
  extendedIntegral (p : Measure K) (fun rho =>
    if useQ then quasiRelative a rho.1.1 (perturb sigma.1 e)
    else petzRelativeBits a rho.1.1 (perturb sigma.1 e))

/-- The corresponding point objective, §IV, PDF p.6. -/
def pointObjective {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (useQ : Bool) (a e : ℝ) (sigma : {A : Operator I // IsDensityMatrix A}) (rho : K) : EReal :=
  if useQ then quasiRelative a rho.1.1 (perturb sigma.1 e)
  else petzRelativeBits a rho.1.1 (perturb sigma.1 e)

/-- The finitely supported subset of all Borel probability measures, PDF p.6. -/
def FiniteMeasureLaw {T : Type*} [MeasurableSpace T] (p : ProbabilityMeasure T) : Prop :=
  ∃ s : Finset T, (p : Measure T) ((s : Set T)ᶜ) = 0

/-- Exact affine-combination relation on probability measures, PDF p.6. -/
def MeasureMixture {T : Type*} [MeasurableSpace T] (t : ℝ)
    (p q r : ProbabilityMeasure T) : Prop :=
  (r : Measure T) = ENNReal.ofReal (1 - t) • (p : Measure T) +
    ENNReal.ofReal t • (q : Measure T)

/-- Affinity without choosing a separate vector-space structure on probability laws, PDF p.6. -/
def MeasureAffine {T : Type*} [MeasurableSpace T] (F : ProbabilityMeasure T → EReal) : Prop :=
  ∀ p q r, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → MeasureMixture t p q r →
    F r = ((1 - t : ℝ) : EReal) * F p + (t : EReal) * F q

/-- Convexity on density operators, using all actual mixtures, PDF pp.3,6. -/
def DensityConvex {I : Type} [Fintype I] (F : {A : Operator I // IsDensityMatrix A} → EReal) : Prop :=
  ∀ sigma tau omega : {A : Operator I // IsDensityMatrix A}, ∀ t : ℝ, 0 < t → t < 1 → omega.1 = AffineMap.lineMap sigma.1 tau.1 t →
    F omega ≤ ((1 - t : ℝ) : EReal) * F sigma + (t : EReal) * F tau

/-- Minimum is asserted by a witness, rather than only an extended infimum, PDF pp.6–7. -/
def ReachesMinimum {T : Type*} (F : T → EReal) : Prop := ∃ t, F t = ⨅ x, F x

/-- Maximum is asserted by a witness, PDF p.6. -/
def ReachesMaximum {T : Type*} (F : T → EReal) : Prop := ∃ t, F t = ⨆ x, F x

/-- The complete chain (28)–(29), with all printed minima attained, PDF p.7.
P can be all measures or its finite-support subtype. -/
def SingularMinimax {P S T : Type*} (F : P → S → EReal) (G : S → T → EReal)
    (centre : S) : Prop :=
  (∀ p, ReachesMinimum (F p)) ∧
  (⨆ p, F p centre) = (⨅ sigma, ⨆ p, F p sigma) ∧
  (⨅ sigma, ⨆ p, F p sigma) = (⨆ p, ⨅ sigma, F p sigma) ∧
  (⨆ p, ⨅ sigma, F p sigma) = (⨅ sigma, ⨆ rho, G sigma rho) ∧
  (⨅ sigma, ⨆ rho, G sigma rho) = (⨆ rho, G centre rho)

/-- The stronger attained chain (25)–(26), PDF p.6. -/
def RegularizedMinimax {P S T : Type*} (F : P → S → EReal) (G : S → T → EReal)
    (centre : S) : Prop :=
  SingularMinimax F G centre ∧
  (∀ sigma, ReachesMaximum (fun p => F p sigma)) ∧
  (∀ sigma, ReachesMaximum (G sigma)) ∧
  ReachesMaximum (fun p => ⨅ sigma, F p sigma)

/-- Selection of regularized minimizing centres, PDF p.6, after IV.3.
Only the defining minimization property, not the singular conclusion, is assumed. -/
def CentreFamily {I : Type} [Fintype I] [DecidableEq I]
    (K : Set ({A : Operator I // IsDensityMatrix A})) (useQ : Bool) (a : ℝ) (centres : ℝ → {A : Operator I // IsDensityMatrix A}) : Prop :=
  ∀ e : ℝ, 0 < e →
    (⨆ p : ProbabilityMeasure K, measureObjective K useQ a e p (centres e)) =
      ⨅ sigma : {A : Operator I // IsDensityMatrix A}, ⨆ p : ProbabilityMeasure K, measureObjective K useQ a e p sigma

/-- The limit centre is tied to a selected family and a positive sequence tending to zero.
PDF p.6, bottom right. -/
def CentreLimit {I : Type} [Fintype I] (centres : ℝ → {A : Operator I // IsDensityMatrix A})
    (sigma : {A : Operator I // IsDensityMatrix A}) : Prop :=
  ∃ e : ℕ → ℝ, (∀ n, 0 < e n) ∧ Tendsto e atTop (𝓝 0) ∧
    Tendsto (fun n => centres (e n)) atTop (𝓝 sigma)

/-- Infinite-order Petz relative entropy, PDF p.4. -/
def infinityRelative {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Operator I) : EReal := Filter.liminf (fun a : ℝ => petzRelativeBits a rho sigma) atTop

/-- The optimal common-mixture weight. The finite normalized family has a finite radius.
The source exponential is interpreted as 2^x in bits, PDF p.9. -/
def helstromWeight {I : Type} [Fintype I] [DecidableEq I] {r : ℕ}
    (rho : Fin r → Operator I) : ℝ := Real.rpow 2 (-(divergenceRadiusBits maxRelative rho).toReal)

/-- Feasible common mixture, including q=1 for an identical family, PDF p.9. -/
def CommonMixture {I : Type} [Fintype I] {r : ℕ}
    (rho : Fin r → Operator I) (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ ∃ sigma : {A : Operator I // IsDensityMatrix A}, ∃ tau : Fin r → {A : Operator I // IsDensityMatrix A},
    ∀ i, sigma.1 = (q : ℂ) • rho i + ((1 - q : ℝ) : ℂ) • (tau i).1

/-- First classical distribution in the negative example, PDF p.10. -/
def exampleFirst : Operator (Fin 3) := Matrix.diagonal ![(1/2 : ℂ), 1/4, 1/4]

/-- Second classical distribution in the negative example, PDF p.10. -/
def exampleSecond : Operator (Fin 3) := Matrix.diagonal ![(1/2 : ℂ), 1/6, 1/3]

/-- The normalized coordinatewise maximum in the negative example, PDF p.10. -/
def exampleCentre : Operator (Fin 3) := Matrix.diagonal ![(6/13 : ℂ), 3/13, 4/13]

/-- Two states viewed as a family, PDF pp.9–10. -/
def pairFamily {I : Type} (A B : Operator I) (i : Fin 2) : Operator I :=
  if i = 0 then A else B

/-- General-state affine relation. The states are the accepted positive trace-class
operators on an arbitrary complete complex Hilbert space, PDF p.9, (37). -/
def ApproximatelyAffine {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {J : Type*} (b : HilbertBasis J ℂ H)
    (f : QAlgorithms.Papers.Independent.Dependency50.P13.State b → ℂ) : Prop :=
  ∀ rho sigma omega : QAlgorithms.Papers.Independent.Dependency50.P13.State b, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    omega.1.1 = ((1 - t : ℝ) : ℂ) • rho.1.1 + (t : ℂ) • sigma.1.1 →
    ‖f omega - (1 - t) • f rho - t • f sigma‖ ≤ binEntropy2 t

/-- Sanity: log zero is genuinely minus infinity, PDF p.3. -/
example : logBits 0 = ⊥ := by simp [logBits]

/-- Sanity: t=0 selects the first operand of mix, PDF p.6. -/
example {I : Type} (A B : Operator I) : AffineMap.lineMap A B (0 : ℝ) = A := by simp

/-- Sanity: t=1 selects the second operand, PDF p.6. -/
example {I : Type} (A B : Operator I) : AffineMap.lineMap A B (1 : ℝ) = B := by simp

/-- Sanity: the n=0 tensor product is the scalar identity, PDF p.9. -/
example {I : Type} (A : Operator I) (u v : Fin 0 → I) : copies 0 A u v = 1 := by
  simp [copies]

/-- Sanity: the first member of the explicit pair is the first matrix, PDF p.10. -/
example : pairFamily exampleFirst exampleSecond 0 = exampleFirst := by
  simp [pairFamily]

/-- Sanity: order one uses the unnormalized Umegaki expression in bits, PDF p.3. -/
example {I : Type} [Fintype I] [DecidableEq I] (A B : Operator I) :
    petzRelativeBits 1 A B = ((1 / Real.log 2 : ℝ) : EReal) * relativeEntropy A B := by
  simp [petzRelativeBits]

/-- Sanity: the zero test rejects the null hypothesis with probability one on a state,
before using its normalization, PDF p.1. -/
example {I : Type} [Fintype I] [DecidableEq I] (A : Operator I) :
    typeOneError A 0 = A.trace.re := by
  simp [typeOneError]

/-- Sanity: the zero test has zero type-II error, PDF p.1. -/
example {I : Type} [Fintype I] (A : Operator I) : typeTwoError A 0 = 0 := by
  simp [typeTwoError]

/-- Sanity: integration against the zero measure vanishes, PDF p.6. -/
example {T : Type*} [MeasurableSpace T] (f : T → EReal) :
    extendedIntegral (0 : Measure T) f = 0 := by
  simp [extendedIntegral]

/-- Sanity: the point objective's Q branch retains the signed Q quantity, PDF p.6. -/
example {I : Type} [Fintype I] [DecidableEq I] (K : Set ({A : Operator I // IsDensityMatrix A}))
    (a e : ℝ) (sigma : {A : Operator I // IsDensityMatrix A}) (rho : K) :
    pointObjective K true a e sigma rho = quasiRelative a rho.1.1 (perturb sigma.1 e) := by
  rfl

end QAlgorithms.Papers.Independent.Advance50.P10


