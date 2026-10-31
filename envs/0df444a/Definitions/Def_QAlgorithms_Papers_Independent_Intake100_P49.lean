-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P49
-- name    : QAlgorithms_Papers_Independent_Intake100_P49
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:28:38.737469+00:00
-- url     : https://prove2.me/theorems/48bfa2de-59ff-439c-bd5a-e0771c0a4c4b
-- title:
--   Definitions for The strong converse exponent of discriminating infinite-dimensional quantum states
-- statement:
--   The objects the formalized statements of *The strong converse exponent of discriminating infinite-dimensional quantum states* (arXiv:2107.08036) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NonzeroPositive`: Section II, PDF pp.2--3: self-adjoint positive operators, excluding zero.
--   - `positiveSpectralPower`: Section II, PDF p.3: bounded spectral power, used only for strictly positive exponents. This helper does not represent unbounded negative powers or support A^0.
--   - `IsReducedRelative`: Lemma III.1 and Remark III.3, PDF pp.5--7: reduced bounded positive solution. The kernel condition is exactly support(R)<=support(sigma) for positive R.
--   - `relativeBounded`: Definition III.2 and Remark III.3, PDF p.7: B_alpha_z through its equivalent unique reduced positive factorization. No bound on Q is used to define it.
--   - `reducedRelative`: Remark III.3, PDF p.7: reduced operator from the concrete factorization. Default zero is outside the relative bounded domain.
--   - `alphaZQ`: Definition III.9, PDF p.8: Q from the reduced operator's z-power trace. Missing bounded factorization and divergent trace both give infinity.
--   - `relativeSchatten`: Definition III.7, PDF p.8: relative Schatten class with finite z-power trace.
--   - `alphaZD`: Definition III.9, PDF p.8: unnormalized divergence, with extended natural log.
--   - `renyiDTilde`: Definition III.10, PDF p.8: trace correction, used with positive finite mass.
--   - `operatorCompression`: Section II, PDF p.3: K A K*, for maps between distinct Hilbert spaces.
--   - `NonzeroCompressionPair`: Section II, PDF p.3: both compressed outputs must be nonzero.
--   - `OrthogonalProjectionOperator`: Section II, PDF p.3: orthogonal projection, with no rank restriction.
--   - `HasFiniteOperatorRange`: Section II, PDF p.3: bounded operator with finite-dimensional range.
--   - `OperatorEffect`: Section II, PDF p.3: all effects, including zero.
--   - `renyiQFa`: Definition III.35, PDF p.17: Q finite approximation, using actual finite-rank orthogonal projections with both compressed outputs nonzero.
--   - `renyiDFa`: Definition III.35, PDF p.17: source's equivalent logarithm-of-Q formula for Dfa.
--   - `renyiDTildeFa`: Definition III.35, PDF p.17: Dtilde finite approximation uses original Tr(rho).
--   - `variationalF`: PDF p.12, (III.33): F(A), with z/alpha power inside the trace.
--   - `variationalG`: PDF p.12, (III.33): G(A), with z/(alpha-1) power inside the trace.
--   - `FinitePenalty`: PDF p.12: finite spectral-penalty domain, including A=0.
--   - `PositiveFinitePenalty`: PDF p.12: positive finite penalty makes log G finite.
--   - `additivePayoff`: PDF p.12: additive payoff, only used with finite G.
--   - `logarithmicPayoff`: PDF p.12: logarithmic payoff, only used with positive finite G.
--   - `VariationalHypothesis`: PDF p.12: the three alternatives a/b/c, without imposing Q finite.
--   - `maxD`: PDF p.7, (III.15): max-relative entropy from the extended domination gauge.
--   - `tildePsi`: PDF p.23, (III.74)--(III.75): perspective with correct endpoint extension. The defective non-tilde psi(+infinity) clause is never used.
--   - `tildePsiFa`: PDF p.23: ordinary finite approximation of the perspective, with endpoints, formed by compressions; it is not defined by a desired approximation theorem.
--   - `hoeffdingFa`: Definition III.50, PDF p.23: ordinary-fa, with the open parameter interval.
--   - `hatHoeffdingFa`: Definition III.50, PDF p.23: endpoint-inclusive ordinary-fa anti-divergence. The extended supremum equals the source's attained maximum.
--   - `OperatorStrongLimit`: Section II, PDF p.3: strong convergence of maps between distinct spaces.
--   - `HeisenbergOperation`: Section IV C, PDF pp.33--34, (IV.119): normal unital CP map with an actual countable Kraus representation. Vector HasSum is its strong operator sum. Finite Kraus families are zero-padded. For separable H,K these represent exactly the source's maps, by its cited Stinespring representation.
--   - `DualDefined`: PDF p.34: partial dual defined precisely when the positive Kraus sum has a bounded positive strong limit. No automatic definedness on general PSD inputs.
--   - `partialDual`: PDF p.34: partial dual from its actual strong sum; zero outside its domain.
--   - `BinarySequence`: Section IV A, PDF p.28: arbitrary binary operator sequences. Index k means positive block length k+1. Spaces may vary; both operators are nonzero PSD.
--   - `SequenceTest`: Definition IV.1, PDF p.28: all effects at every block length, including zero.
--   - `sequenceRate`: PDF p.28: negative logarithmic generalized weight per positive block length. False is the null-hypothesis success weight, true is the type-II error weight.
--   - `FeasibleTestSequence`: Definition IV.1, PDF p.28: common lower type-II exponent constraint.
--   - `zeroSequenceTest`: PDF p.28: zero tests are permitted at every positive block length.
--   - `lowerSC`: Definition IV.1, PDF p.28: lower strong-converse exponent.
--   - `upperSC`: Definition IV.1, PDF p.28: upper strong-converse exponent.
--   - `limitSC`: Definition IV.1, PDF p.28: exponent restricted to sequences whose success exponent has an existing extended limit; this is not a limsup surrogate.
--   - `sequenceTildePsi`: PDF p.28: sequence perspective, a limsup of per-block single-system values.
--   - `sequenceHatHoeffding`: PDF p.28: endpoint-inclusive sequence Hoeffding anti-divergence.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, https://arxiv.org/abs/2107.08036v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-!
Mosonyi, arXiv:2107.08036v5. References are PDF pages.
Explicit deferrals appear in HARD.md and GAPS.json. Compilation is pending.
Q is constructed from the reduced bounded operator independently of variational
formulas and finite approximations. No unbounded power is encoded by bounded CFC.
-/

noncomputable section

open Filter
open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass TraceClass traceNormTopology)

open QAlgorithms.Papers.Independent.Bridge50.P48 (hilbertPositiveTrace)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Section II, PDF pp.2--3: self-adjoint positive operators, excluding zero. -/
def NonzeroPositive (A : H →L[ℂ] H) : Prop := IsPositive A ∧ A ≠ 0

example : ¬ NonzeroPositive (0 : H →L[ℂ] H) := by simp [NonzeroPositive]

/-- Section II, PDF p.3: bounded spectral power, used only for strictly positive
exponents. This helper does not represent unbounded negative powers or support A^0. -/
def positiveSpectralPower (A : H →L[ℂ] H) (p : ℝ) : H →L[ℂ] H :=
  cfc (fun x : ℝ => Real.rpow x p) A

example (A : H →L[ℂ] H) (hA : IsPositive A) : positiveSpectralPower A 1 = A := by
  unfold positiveSpectralPower
  have hfun : (fun x : ℝ => Real.rpow x 1) = (fun x : ℝ => x) := by
    funext x
    exact Real.rpow_one x
  rw [hfun]
  exact cfc_id' ℝ A (ha := hA.1)

/-- Lemma III.1 and Remark III.3, PDF pp.5--7: reduced bounded positive solution.
The kernel condition is exactly support(R)<=support(sigma) for positive R. -/
def IsReducedRelative (alpha z : ℝ) (rho sigma R : H →L[ℂ] H) : Prop :=
  IsPositive R ∧
  positiveSpectralPower sigma ((alpha - 1) / (2 * z)) * R *
    positiveSpectralPower sigma ((alpha - 1) / (2 * z)) = positiveSpectralPower rho (alpha / z) ∧
  ∀ x, sigma x = 0 → R x = 0

/-- Definition III.2 and Remark III.3, PDF p.7: B_alpha_z through its equivalent
unique reduced positive factorization. No bound on Q is used to define it. -/
def relativeBounded (alpha z : ℝ) (rho sigma : H →L[ℂ] H) : Prop :=
  NonzeroPositive rho ∧ ∃ R, IsReducedRelative alpha z rho sigma R

/-- Remark III.3, PDF p.7: reduced operator from the concrete factorization.
Default zero is outside the relative bounded domain. -/
def reducedRelative (alpha z : ℝ) (rho sigma : H →L[ℂ] H) : H →L[ℂ] H :=
  if h : ∃ R, IsReducedRelative alpha z rho sigma R then h.choose else 0

example (alpha z : ℝ) (rho sigma : H →L[ℂ] H)
    (h : ¬ ∃ R, IsReducedRelative alpha z rho sigma R) :
    reducedRelative alpha z rho sigma = 0 := by simp [reducedRelative, h]

/-- Definition III.9, PDF p.8: Q from the reduced operator's z-power trace.
Missing bounded factorization and divergent trace both give infinity. -/
def alphaZQ {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : ℝ≥0∞ :=
  if relativeBounded alpha z rho sigma then
    hilbertPositiveTrace b (positiveSpectralPower (reducedRelative alpha z rho sigma) z)
  else ⊤

example {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ) (sigma : H →L[ℂ] H) :
    alphaZQ b alpha z 0 sigma = ⊤ := by
  simp [alphaZQ, relativeBounded, NonzeroPositive]

/-- Definition III.7, PDF p.8: relative Schatten class with finite z-power trace. -/
def relativeSchatten {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : Prop :=
  relativeBounded alpha z rho sigma ∧
    hilbertPositiveTrace b (positiveSpectralPower (reducedRelative alpha z rho sigma) z) < ⊤

/-- Definition III.9, PDF p.8: unnormalized divergence, with extended natural log. -/
def alphaZD {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  ((1 / (alpha - 1) : ℝ) : EReal) * ENNReal.log (alphaZQ b alpha z rho sigma)

/-- Definition III.10, PDF p.8: trace correction, used with positive finite mass. -/
def renyiDTilde {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  alphaZD b alpha z rho sigma -
    ((1 / (alpha - 1) : ℝ) : EReal) * ENNReal.log (hilbertPositiveTrace b rho)

example {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) (h : hilbertPositiveTrace b rho = 1) :
    renyiDTilde b alpha z rho sigma = alphaZD b alpha z rho sigma := by
  simp [renyiDTilde, h]

/-- Section II, PDF p.3: K A K*, for maps between distinct Hilbert spaces. -/
def operatorCompression (L : H →L[ℂ] K) (A : H →L[ℂ] H) : K →L[ℂ] K :=
  L.comp (A.comp L.adjoint)

example (L : H →L[ℂ] K) : operatorCompression L 0 = 0 := by simp [operatorCompression]

/-- Section II, PDF p.3: both compressed outputs must be nonzero. -/
def NonzeroCompressionPair (rho sigma : H →L[ℂ] H) (L : H →L[ℂ] K) : Prop :=
  operatorCompression L rho ≠ 0 ∧ operatorCompression L sigma ≠ 0

/-- Section II, PDF p.3: orthogonal projection, with no rank restriction. -/
def OrthogonalProjectionOperator (P : H →L[ℂ] H) : Prop := P.adjoint = P ∧ P * P = P

example : OrthogonalProjectionOperator (0 : H →L[ℂ] H) := by simp [OrthogonalProjectionOperator]

/-- Section II, PDF p.3: bounded operator with finite-dimensional range. -/
def HasFiniteOperatorRange (L : H →L[ℂ] K) : Prop :=
  FiniteDimensional ℂ (LinearMap.range L.toLinearMap)

/-- Section II, PDF p.3: all effects, including zero. -/
def OperatorEffect (T : H →L[ℂ] H) : Prop := IsPositive T ∧ IsPositive (1 - T)

example : OperatorEffect (0 : H →L[ℂ] H) := by
  constructor
  · simp [IsPositive]
  · simp only [sub_zero]
    refine ⟨ContinuousLinearMap.adjoint_one (𝕜 := ℂ) (E := H), ?_⟩
    intro x
    change 0 ≤ (inner ℂ x x).re
    exact @inner_self_nonneg ℂ _ _ _ _ x

/-- Definition III.35, PDF p.17: Q finite approximation, using actual finite-rank
orthogonal projections with both compressed outputs nonzero. -/
def renyiQFa {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ P : {P : H →L[ℂ] H // OrthogonalProjectionOperator P ∧ HasFiniteOperatorRange P ∧ NonzeroCompressionPair rho sigma P},
    alphaZQ b alpha z (operatorCompression P.val rho) (operatorCompression P.val sigma)

/-- Definition III.35, PDF p.17: source's equivalent logarithm-of-Q formula for Dfa. -/
def renyiDFa {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  ((1 / (alpha - 1) : ℝ) : EReal) * ENNReal.log (renyiQFa b alpha z rho sigma)

/-- Definition III.35, PDF p.17: Dtilde finite approximation uses original Tr(rho). -/
def renyiDTildeFa {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  renyiDFa b alpha z rho sigma -
    ((1 / (alpha - 1) : ℝ) : EReal) * ENNReal.log (hilbertPositiveTrace b rho)

example {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) (h : hilbertPositiveTrace b rho = 1) :
    renyiDTildeFa b alpha z rho sigma = renyiDFa b alpha z rho sigma := by
  simp [renyiDTildeFa, h]

/-- PDF p.12, (III.33): F(A), with z/alpha power inside the trace. -/
def variationalF {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho A : H →L[ℂ] H) : ℝ≥0∞ :=
  hilbertPositiveTrace b (positiveSpectralPower
    (positiveSpectralPower A (1 / 2) * positiveSpectralPower rho (alpha / z) * positiveSpectralPower A (1 / 2))
    (z / alpha))

/-- PDF p.12, (III.33): G(A), with z/(alpha-1) power inside the trace. -/
def variationalG {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (sigma A : H →L[ℂ] H) : ℝ≥0∞ :=
  hilbertPositiveTrace b (positiveSpectralPower
    (positiveSpectralPower A (1 / 2) * positiveSpectralPower sigma ((alpha - 1) / z) *
      positiveSpectralPower A (1 / 2)) (z / (alpha - 1)))

/-- PDF p.12: finite spectral-penalty domain, including A=0. -/
def FinitePenalty {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (sigma A : H →L[ℂ] H) : Prop :=
  IsPositive A ∧ variationalG b alpha z sigma A < ⊤

/-- PDF p.12: positive finite penalty makes log G finite. -/
def PositiveFinitePenalty {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (sigma A : H →L[ℂ] H) : Prop :=
  FinitePenalty b alpha z sigma A ∧ 0 < variationalG b alpha z sigma A

/-- PDF p.12: additive payoff, only used with finite G. -/
def additivePayoff {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma A : H →L[ℂ] H) : EReal :=
  (alpha : EReal) * (variationalF b alpha z rho A : EReal) +
    ((1 - alpha : ℝ) : EReal) * (variationalG b alpha z sigma A : EReal)

/-- PDF p.12: logarithmic payoff, only used with positive finite G. -/
def logarithmicPayoff {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma A : H →L[ℂ] H) : EReal :=
  (alpha : EReal) * ENNReal.log (variationalF b alpha z rho A) +
    ((1 - alpha : ℝ) : EReal) * ENNReal.log (variationalG b alpha z sigma A)

/-- PDF p.12: the three alternatives a/b/c, without imposing Q finite. -/
def VariationalHypothesis {I : Type*} (b : HilbertBasis I ℂ H) (alpha z : ℝ)
    (rho sigma : H →L[ℂ] H) : Prop :=
  (¬ relativeBounded alpha z rho sigma) ∨
  (relativeBounded alpha z rho sigma ∧ ¬ relativeSchatten b alpha z rho sigma ∧
    IsCompactOperator sigma) ∨ relativeSchatten b alpha z rho sigma

/-- PDF p.7, (III.15): max-relative entropy from the extended domination gauge. -/
def maxD (rho sigma : H →L[ℂ] H) : EReal :=
  ENNReal.log (QAlgorithms.Papers.Independent.Bridge50.P48.maxSandwichNorm (rho, sigma))

/-- PDF p.23, (III.74)--(III.75): perspective with correct endpoint extension.
The defective non-tilde psi(+infinity) clause is never used. -/
def tildePsi {I : Type*} (b : HilbertBasis I ℂ H) (u : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  if u = 0 then ENNReal.log (hilbertPositiveTrace b rho)
  else if u = 1 then maxD rho sigma
  else if 0 < u ∧ u < 1 then
    ((1 - u : ℝ) : EReal) * ENNReal.log (alphaZQ b (1 / (1 - u)) (1 / (1 - u)) rho sigma)
  else ⊤

example {I : Type*} (b : HilbertBasis I ℂ H) (rho sigma : H →L[ℂ] H) :
    tildePsi b 0 rho sigma = ENNReal.log (hilbertPositiveTrace b rho) ∧
      tildePsi b 1 rho sigma = maxD rho sigma := by simp [tildePsi]

/-- PDF p.23: ordinary finite approximation of the perspective, with endpoints,
formed by compressions; it is not defined by a desired approximation theorem. -/
def tildePsiFa {I : Type*} (b : HilbertBasis I ℂ H) (u : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  ⨆ P : {P : H →L[ℂ] H // OrthogonalProjectionOperator P ∧ HasFiniteOperatorRange P ∧ NonzeroCompressionPair rho sigma P},
    tildePsi b u (operatorCompression P.val rho) (operatorCompression P.val sigma)

/-- Definition III.50, PDF p.23: ordinary-fa, with the open parameter interval. -/
def hoeffdingFa {I : Type*} (b : HilbertBasis I ℂ H) (r : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  ⨆ u : Set.Ioo (0 : ℝ) 1, ((u.val * r : ℝ) : EReal) - tildePsiFa b u.val rho sigma

/-- Definition III.50, PDF p.23: endpoint-inclusive ordinary-fa anti-divergence.
The extended supremum equals the source's attained maximum. -/
def hatHoeffdingFa {I : Type*} (b : HilbertBasis I ℂ H) (r : ℝ)
    (rho sigma : H →L[ℂ] H) : EReal :=
  ⨆ u : Set.Icc (0 : ℝ) 1, ((u.val * r : ℝ) : EReal) - tildePsiFa b u.val rho sigma

/-- Section II, PDF p.3: strong convergence of maps between distinct spaces. -/
def OperatorStrongLimit (L : ℕ → H →L[ℂ] K) (M : H →L[ℂ] K) : Prop :=
  ∀ x, Tendsto (fun n => L n x) atTop (nhds (M x))

example (M : H →L[ℂ] K) : OperatorStrongLimit (fun _ => M) M :=
  fun _ => tendsto_const_nhds

/-- Section IV C, PDF pp.33--34, (IV.119): normal unital CP map with an actual
countable Kraus representation. Vector HasSum is its strong operator sum.
Finite Kraus families are zero-padded. For separable H,K these represent exactly
the source's maps, by its cited Stinespring representation. -/
structure HeisenbergOperation (H K : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  map : (K →L[ℂ] K) → (H →L[ℂ] H)
  kraus : ℕ → H →L[ℂ] K
  representation : ∀ A x, HasSum
    (fun i => (kraus i).adjoint (A (kraus i x))) (map A x)
  unital : map 1 = 1

/-- PDF p.34: partial dual defined precisely when the positive Kraus sum has a
bounded positive strong limit. No automatic definedness on general PSD inputs. -/
def DualDefined (Phi : HeisenbergOperation H K) (A : H →L[ℂ] H) : Prop :=
  ∃ B : K →L[ℂ] K, IsPositive B ∧
    ∀ y, HasSum (fun i => Phi.kraus i (A ((Phi.kraus i).adjoint y))) (B y)

/-- PDF p.34: partial dual from its actual strong sum; zero outside its domain. -/
def partialDual (Phi : HeisenbergOperation H K) (A : H →L[ℂ] H) : K →L[ℂ] K :=
  if h : DualDefined Phi A then h.choose else 0

example (Phi : HeisenbergOperation H K) (A : H →L[ℂ] H) (h : ¬ DualDefined Phi A) :
    partialDual Phi A = 0 := by simp [partialDual, h]

example (Phi : HeisenbergOperation H K) : DualDefined Phi 0 := by
  -- PDF p.34: zero has a bounded dual sum, even when other inputs do not.
  refine ⟨0, by simp [IsPositive], ?_⟩
  intro y
  simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : K)) 0)

/-- Section IV A, PDF p.28: arbitrary binary operator sequences. Index k means
positive block length k+1. Spaces may vary; both operators are nonzero PSD. -/
structure BinarySequence where
  data : ℕ → QAlgorithms.Papers.Independent.Claimed50.P46.QuantumData
  nonzero : ∀ k, (data k).rho ≠ 0 ∧ (data k).sigma ≠ 0
  separable : ∀ k, TopologicalSpace.SeparableSpace (data k).H

/-- Definition IV.1, PDF p.28: all effects at every block length, including zero. -/
def SequenceTest (S : BinarySequence) :=
  (k : ℕ) → {T : (S.data k).H →L[ℂ] (S.data k).H // OperatorEffect T}

/-- PDF p.28: negative logarithmic generalized weight per positive block length.
False is the null-hypothesis success weight, true is the type-II error weight. -/
def sequenceRate (S : BinarySequence) (T : SequenceTest S) (alternative : Bool)
    (k : ℕ) : EReal :=
  let A := if alternative then (S.data k).sigma else (S.data k).rho
  let weight := QAlgorithms.Papers.Independent.Claimed50.P46.quantumWeight
    (S.data k) A (T k).val
  let scale : EReal := ((1 / ((k : ℝ) + 1) : ℝ) : EReal)
  show EReal from -(scale * ENNReal.log weight)

/-- Definition IV.1, PDF p.28: common lower type-II exponent constraint. -/
def FeasibleTestSequence (S : BinarySequence) (r : ℝ) (T : SequenceTest S) : Prop :=
  (r : EReal) ≤ liminf (sequenceRate S T true) atTop

/-- PDF p.28: zero tests are permitted at every positive block length. -/
def zeroSequenceTest (S : BinarySequence) : SequenceTest S :=
  fun k => ⟨0, by
    constructor
    · simp [IsPositive]
    · simp only [sub_zero]
      refine ⟨ContinuousLinearMap.adjoint_one (𝕜 := ℂ) (E := (S.data k).H), ?_⟩
      intro x
      change 0 ≤ (inner ℂ x x).re
      exact @inner_self_nonneg ℂ _ _ _ _ x⟩

example (S : BinarySequence) (k : ℕ) : (zeroSequenceTest S k).val = 0 := rfl

/-- Definition IV.1, PDF p.28: lower strong-converse exponent. -/
def lowerSC (S : BinarySequence) (r : ℝ) : EReal :=
  sInf {v | ∃ T : SequenceTest S, FeasibleTestSequence S r T ∧
    v = liminf (sequenceRate S T false) atTop}

/-- Definition IV.1, PDF p.28: upper strong-converse exponent. -/
def upperSC (S : BinarySequence) (r : ℝ) : EReal :=
  sInf {v | ∃ T : SequenceTest S, FeasibleTestSequence S r T ∧
    v = limsup (sequenceRate S T false) atTop}

/-- Definition IV.1, PDF p.28: exponent restricted to sequences whose success
exponent has an existing extended limit; this is not a limsup surrogate. -/
def limitSC (S : BinarySequence) (r : ℝ) : EReal :=
  sInf {v | ∃ T : SequenceTest S, FeasibleTestSequence S r T ∧
    Tendsto (sequenceRate S T false) atTop (nhds v)}

/-- PDF p.28: sequence perspective, a limsup of per-block single-system values. -/
def sequenceTildePsi (S : BinarySequence) (u : ℝ) : EReal :=
  limsup (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : EReal) *
    tildePsi (S.data k).basis u (S.data k).rho (S.data k).sigma) atTop

/-- PDF p.28: endpoint-inclusive sequence Hoeffding anti-divergence. -/
def sequenceHatHoeffding (S : BinarySequence) (r : ℝ) : EReal :=
  ⨆ u : Set.Icc (0 : ℝ) 1, ((u.val * r : ℝ) : EReal) - sequenceTildePsi S u.val

end QAlgorithms.Papers.Independent.Intake100.P49


