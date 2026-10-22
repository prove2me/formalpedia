-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P43
-- name    : QAlgorithms_Papers_Independent_Gap48_P43
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:34:23.972206+00:00
-- url     : https://prove2.me/theorems/fe5bf091-9db0-4dbb-adaf-fb68aad728d0
-- title:
--   Definitions for Quantum privacy and quantum coherence
-- statement:
--   The objects the formalized statements of *Quantum privacy and quantum coherence* (arXiv:quant-ph/9709058) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PureDilation`: PDF p.2, (1): one unitary evolution with the complete, initially pure normalized environment, including any purifying systems and Eve's apparatus.
--   - `bobOutput`: PDF pp.2--3, (1),(4): Bob's channel output, tracing the SAME joint state.
--   - `eveOutput`: PDF pp.2--4, (6): the complete complementary environment output.
--   - `averageInput`: PDF p.3, (3): computed density of a discrete signal ensemble. Normalized nuclear states and weights of sum one ensure convergence in trace norm, hence absolute convergence of every displayed scalar coefficient.
--   - `FiniteOutputEntropies`: PDF pp.3--4: the ordinary finite domain of (5),(6),(11). No input-entropy restriction or finite-dimensional system is added.
--   - `holevoBits`: PDF pp.3--4, (5)--(6): signed ordinary entropy difference in bits. Used with FiniteOutputEntropies, so neither real conversion hides infinity.
--   - `ActivePure`: PDF p.4, before (10): only signals of positive probability must be pure. PureState includes a norm-one vector witness; no orthogonality is imposed.
--   - `bornEventWeight`: PDF pp.3--4: Tr(M(S) rho), computed using the bounded realization. For the density operators used below this is a convergent trace-class trace.
--   - `bornOutcomeLaw`: PDF pp.3--4: the mixed-state Born measure, determined on measurable events. A normalized density and a POVM always give a unique such measure (by spectral mixture of the POVM's vector laws). Choice selects that measure, not an arbitrary outcome distribution. The explicit zero branch only totalizes invalid arrays; all source uses are actual computed output densities. No Born-law existence or Holevo inequality is assumed as a hypothesis of the statements.
--   - `outcomeMixture`: PDF p.3: unconditional outcome law, computed from the signal probabilities and conditional Born measures. This also covers arbitrary measurable outcomes.
--   - `measuredInformation`: PDF pp.3--4: classical information between the signal label and measured outcome, in bits: sum_n p_n D(mu_n || sum_k p_k mu_k)/ln 2. Mathlib KL retains infinity on nonintegrability, rather than returning zero. This is an actual Born-law mutual information, not a freely assigned number.
--   - `guaranteedPrivacy`: PDF p.4, (7)--(8): infimum over ALL measurements of the full environment. Every outcome type and measurable structure is allowed; classical randomized postprocessing is included in POVMs. Compatible pure dilations give the same class of attainable laws by Stinespring isometry equivalence. In particular this is not a restriction to one selected attack. EReal preserves negative privacy and has a genuine infimum; Bob's information is a finite real in the theorem.
-- source:
--   Quantum privacy and quantum coherence, arXiv:quant-ph/9709058v2, https://arxiv.org/abs/quant-ph/9709058v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

/-!
Schumacher--Westmoreland, quant-ph/9709058v2, PDF pp.2--5.
The registers are completed l2 spaces, with no dimension or separability cutoff.
Discrete ensembles are finite or countable (finite ones have zero padding).
Both outputs are computed from ONE unitary and ONE normalized pure environment.
All ordinary entropy differences carry their finite-domain hypotheses.
The source's undefined optimization over block protocols is deferred; the three
statements here are (8), (11), and the decomposition independence observation.
Compilation and independent review are pending the separate batch handoff.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Gap48.P43

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState productCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble boundedConjugation traceSecond traceFirst)
open QAlgorithms.Papers.Independent.Frontier18.P18
  (boundedOperator operatorCoeff)
open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits)
open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (1): one unitary evolution with the complete, initially pure
normalized environment, including any purifying systems and Eve's apparatus. -/
structure PureDilation (Q E : Type) where
  initial : PureState E
  unitary : Hilbert (Q × E) ≃ₗᵢ[ℂ] Hilbert (Q × E)

/-- PDF pp.2--3, (1),(4): Bob's channel output, tracing the SAME joint state. -/
def bobOutput {Q E : Type} (d : PureDilation Q E) (rho : Matrix Q Q ℂ) :
    Matrix Q Q ℂ := traceSecond (boundedConjugation d.unitary.toLinearIsometry.toContinuousLinearMap
      (productCoeff rho d.initial.val.coefficients))

/-- PDF pp.2--4, (6): the complete complementary environment output. -/
def eveOutput {Q E : Type} (d : PureDilation Q E) (rho : Matrix Q Q ℂ) :
    Matrix E E ℂ := traceFirst (boundedConjugation d.unitary.toLinearIsometry.toContinuousLinearMap
      (productCoeff rho d.initial.val.coefficients))

/-- PDF p.3, (3): computed density of a discrete signal ensemble.
Normalized nuclear states and weights of sum one ensure convergence in trace
norm, hence absolute convergence of every displayed scalar coefficient. -/
def averageInput {Q : Type} (a : CountableStateEnsemble Q) : Matrix Q Q ℂ :=
  fun i j => ∑' n, ((a.weight n).toReal : ℂ) * (a.state n).coefficients i j

/-- PDF pp.3--4: the ordinary finite domain of (5),(6),(11).
No input-entropy restriction or finite-dimensional system is added. -/
def FiniteOutputEntropies {Q H : Type} (a : CountableStateEnsemble Q)
    (f : Matrix Q Q ℂ → Matrix H H ℂ) : Prop :=
  spectralEntropyBits (f (averageInput a)) < ⊤ ∧
    (∑' n, a.weight n * spectralEntropyBits (f (a.state n).coefficients)) < ⊤

/-- PDF pp.3--4, (5)--(6): signed ordinary entropy difference in bits.
Used with FiniteOutputEntropies, so neither real conversion hides infinity. -/
def holevoBits {Q H : Type} (a : CountableStateEnsemble Q)
    (f : Matrix Q Q ℂ → Matrix H H ℂ) : ℝ :=
  (spectralEntropyBits (f (averageInput a))).toReal -
    (∑' n, a.weight n * spectralEntropyBits (f (a.state n).coefficients)).toReal

/-- PDF p.4, before (10): only signals of positive probability must be pure.
PureState includes a norm-one vector witness; no orthogonality is imposed. -/
def ActivePure {Q : Type} (a : CountableStateEnsemble Q) : Prop :=
  ∀ n, a.weight n ≠ 0 → ∃ psi : PureState Q, psi.val = a.state n

/-- PDF pp.3--4: Tr(M(S) rho), computed using the bounded realization.
For the density operators used below this is a convergent trace-class trace. -/
def bornEventWeight {H X : Type} [MeasurableSpace X]
    (M : HilbertPOVM (Hilbert H) X) (rho : Matrix H H ℂ) (S : Set X) : ℝ :=
  (∑' i, operatorCoeff ((M.effect S).comp (boundedOperator rho)) i i).re

/-- PDF pp.3--4: the mixed-state Born measure, determined on measurable events.
A normalized density and a POVM always give a unique such measure (by spectral
mixture of the POVM's vector laws). Choice selects that measure, not an arbitrary
outcome distribution. The explicit zero branch only totalizes invalid arrays;
all source uses are actual computed output densities. No Born-law existence or
Holevo inequality is assumed as a hypothesis of the statements. -/
def bornOutcomeLaw {H X : Type} [MeasurableSpace X]
    (M : HilbertPOVM (Hilbert H) X) (rho : Matrix H H ℂ) : Measure X :=
  if h : ∃ mu : Measure X, ∀ S, MeasurableSet S →
      mu S = ENNReal.ofReal (bornEventWeight M rho S)
  then h.choose else 0

/-- PDF p.3: unconditional outcome law, computed from the signal probabilities
and conditional Born measures. This also covers arbitrary measurable outcomes. -/
def outcomeMixture {Q H X : Type} [MeasurableSpace X]
    (a : CountableStateEnsemble Q) (f : Matrix Q Q ℂ → Matrix H H ℂ)
    (M : HilbertPOVM (Hilbert H) X) : Measure X :=
  Measure.sum (fun n => a.weight n • bornOutcomeLaw M (f (a.state n).coefficients))

/-- PDF pp.3--4: classical information between the signal label and measured
outcome, in bits: sum_n p_n D(mu_n || sum_k p_k mu_k)/ln 2.
Mathlib KL retains infinity on nonintegrability, rather than returning zero.
This is an actual Born-law mutual information, not a freely assigned number. -/
def measuredInformation {Q H X : Type} [MeasurableSpace X]
    (a : CountableStateEnsemble Q) (f : Matrix Q Q ℂ → Matrix H H ℂ)
    (M : HilbertPOVM (Hilbert H) X) : ℝ≥0∞ :=
  (∑' n, a.weight n * InformationTheory.klDiv
    (bornOutcomeLaw M (f (a.state n).coefficients)) (outcomeMixture a f M)) /
      ENNReal.ofReal (Real.log 2)

/-- PDF p.4, (7)--(8): infimum over ALL measurements of the full environment.
Every outcome type and measurable structure is allowed; classical randomized
postprocessing is included in POVMs. Compatible pure dilations give the same
class of attainable laws by Stinespring isometry equivalence. In particular this
is not a restriction to one selected attack. EReal preserves negative privacy
and has a genuine infimum; Bob's information is a finite real in the theorem. -/
def guaranteedPrivacy {Q E : Type} (a : CountableStateEnsemble Q)
    (d : PureDilation Q E) (bobInformation : ℝ) : EReal :=
  ⨅ X : Type, ⨅ mX : MeasurableSpace X,
    letI := mX
    ⨅ M : HilbertPOVM (Hilbert E) X,
      (bobInformation : EReal) - (measuredInformation a (eveOutput d) M).toEReal

/-! Sanity examples for definition bodies, without proving any source result. -/

example {Q : Type} (a : CountableStateEnsemble Q) (i j : Q) :
    averageInput a i j =
      ∑' n, ((a.weight n).toReal : ℂ) * (a.state n).coefficients i j := rfl

example {Q E : Type} (d : PureDilation Q E) (rho : Matrix Q Q ℂ) :
    bobOutput d rho = traceSecond (boundedConjugation d.unitary.toLinearIsometry.toContinuousLinearMap
      (productCoeff rho d.initial.val.coefficients)) ∧
    eveOutput d rho = traceFirst (boundedConjugation d.unitary.toLinearIsometry.toContinuousLinearMap
      (productCoeff rho d.initial.val.coefficients)) := ⟨rfl, rfl⟩

example {Q H : Type} (a : CountableStateEnsemble Q)
    (f : Matrix Q Q ℂ → Matrix H H ℂ) (h : FiniteOutputEntropies a f) :
    spectralEntropyBits (f (averageInput a)) < ⊤ ∧
    (∑' n, a.weight n * spectralEntropyBits (f (a.state n).coefficients)) < ⊤ := h

example {Q : Type} (a : CountableStateEnsemble Q) (h : ActivePure a)
    (n : ℕ) (hn : a.weight n ≠ 0) :
    ∃ psi : PureState Q, psi.val = a.state n := h n hn

example {H X : Type} [MeasurableSpace X] (M : HilbertPOVM (Hilbert H) X)
    (rho : Matrix H H ℂ)
    (h : ∃ mu : Measure X, ∀ S, MeasurableSet S →
      mu S = ENNReal.ofReal (bornEventWeight M rho S)) :
    ∀ S, MeasurableSet S → bornOutcomeLaw M rho S =
      ENNReal.ofReal (bornEventWeight M rho S) := by
  simpa only [bornOutcomeLaw, dif_pos h] using h.choose_spec

example {H X : Type} [MeasurableSpace X] (M : HilbertPOVM (Hilbert H) X)
    (rho : Matrix H H ℂ) : bornOutcomeLaw M rho ∅ = 0 := measure_empty

example {Q H : Type} (a : CountableStateEnsemble Q)
    (f : Matrix Q Q ℂ → Matrix H H ℂ) (n : ℕ) (hn : a.weight n = 0) :
    a.weight n * spectralEntropyBits (f (a.state n).coefficients) = 0 := by
  rw [hn, zero_mul]

example {Q E : Type} (d : PureDilation Q E) :
    ∃ u : Hilbert E, ‖u‖ = 1 ∧ d.initial.val.coefficients =
      QAlgorithms.Papers.Independent.Dependency50.P33.rankOne u := d.initial.property

end QAlgorithms.Papers.Independent.Gap48.P43


