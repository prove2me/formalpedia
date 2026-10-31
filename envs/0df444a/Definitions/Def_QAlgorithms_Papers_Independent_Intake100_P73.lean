-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73
-- name    : QAlgorithms_Papers_Independent_Intake100_P73
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:50:37.767295+00:00
-- url     : https://prove2.me/theorems/38db7020-0921-41c9-96aa-69166b108065
-- title:
--   Definitions for General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel
-- statement:
--   The objects the formalized statements of *General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel* (arXiv:cs/0503088) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsDiscreteStochastic`: PDF p.2: normalized classical discrete stochastic rows, without finiteness.
--   - `discreteOutputMixture`: PDF p.2: discreteOutputMixture mixture. Theorem inputs are PMFs or actual iid/uniform laws.
--   - `fullL1`: PDF p.4: FULL L1 distance; for probability laws it lies in [0,2].
--   - `klAtom`: PDF pp.4,9: nonnegative KL generator. On normalized laws its sum equals sum p log(p/q), since -p+q cancels globally. At p=0 its generator limit is q; the SOURCE's p log(p/q) term itself is zero there. Positive p and zero q give infinity. This representation avoids any nonsummable signed real tsum.
--   - `discreteKLDivergence`: PDF pp.4,9: extended nonnegative KL in nats, by nonnegative summation.
--   - `logLikelihood`: PDF p.9: extended likelihood. Zero numerator has zero probability; positive numerator and zero denominator give +infinity, never Real.log(p/0).
--   - `jointEvent`: PDF pp.2,4: event probability under the actual joint law p(x)W_x(y).
--   - `upperLikelihoodMass`: PDF p.4: upper truncation >C; the joint-support guard removes null rows.
--   - `lowTail`: PDF p.4: low likelihood probability, with the source's weak <=C boundary.
--   - `deltaPrime`: PDF p.4: upperLikelihoodMass-prime = E_p sum_{W_x/W_p<=C} W_x^2/W_p. Joint/discreteOutputMixture zero mass is removed BEFORE division. On normalized channels it is at most C, so all later toReal conversions are of finite quantities.
--   - `entropySummand`: PDF p.4: entropySummand(0)=0, agreeing with the continuous entropy summand.
--   - `phiMoment`: PDF p.4: exp(hayashiPhi(t|W,p)), with the source's power 1/(1+t).
--   - `hayashiPhi`: PDF pp.4,10: extended hayashiPhi; its normalized zero endpoint is zero.
--   - `discretePsiMoment`: PDF p.10: exp(hayashiPsi), excluding zero mixture mass before negative powers.
--   - `hayashiPsi`: PDF p.10: fixed-input hayashiPsi; hayashiPsi(0)=0 for normalized laws.
--   - `worstPsi`: PDF p.10: printed worst-input hayashiPsi, with the UNUSUAL exponent 1-s retained literally. A numerical supremum asserts no maximizing law.
--   - `l1Bound`: PDF p.4, (9)/(12): no extra factor two inside the square root.
--   - `klBound`: PDF p.4, (10)/(13): one-shot KL bound; -1/2<=t<0 where used. An infinite moment remains infinite, rather than being converted to a real.
--   - `entropyBound`: PDF p.4, (11)/(14): entropy bound; invoked only when Y is finite.
--   - `Book`: PDF p.4: positive tuple codebook; repeated input symbols are allowed.
--   - `empirical`: PDF p.4: actual empirical discreteOutputMixture of a tuple codebook.
--   - `tupleOutput`: PDF p.4: empirical discreteOutputMixture for a specified M-tuple.
--   - `iidExpectation`: PDF p.4, Lemma 2: actual expectation under the iid tuple distribution p^M.
--   - `bestApproximation`: PDF p.6: infimum over ACTUAL positive tuple codes of size AT MOST M. KL and L1 have separate optima. No attainment is asserted.
--   - `worstApproximation`: PDF p.6: supremum of the approximation optimum over ALL input laws.
--   - `IdentificationCode`: PDF pp.2,7: nonempty identification code; regions need not be disjoint.
--   - `firstError`: PDF p.2: maximal first error, bounded by one on stochastic channels.
--   - `secondError`: PDF p.2: maximal second error. The singleton's empty nonnegative supremum is zero; empty MESSAGE codes remain excluded.
--   - `DiscreteStochasticWiretapCode`: PDF p.6: stochastic wiretap code with positive count and disjoint regions.
--   - `averageBobError`: PDF p.6: UNIFORM-message average Bob error, not a maximal error.
--   - `eveOutputMarginal`: PDF p.6: actual Eve discreteOutputMixture marginal of the uniform message.
--   - `averageEveDivergence`: PDF p.6: Eve mutual information, extended KL in nats.
--   - `eveDistance`: PDF p.6: average full L1 over ordered DISTINCT pairs. The empty pair average at M=1 is explicitly zero.
--   - `length`: PDF pp.7–12: all exponent denominators are positive lengths.
--   - `sampleCount`: PDF pp.7,10: positive integer rounding of exp(nR), preserving its log rate.
--   - `liminfErrorExponent`: PDF pp.10,12: liminf normalized negative log, with +infinity at zero error.
--   - `informationTailProbability`: PDF p.7: spectral upper-tail probability at a finite normalized threshold.
--   - `spectralLow`: PDF p.7: complementary low-event probability, with <=a.
--   - `epsilonInformationSpectrum`: PDF p.7: epsilon upper/lower spectra: true uses limsup upper tail, false uses liminf. At epsilon=1 the condition is STRICT <1. Extended infima avoid empty/unbounded-set defaults.
--   - `complementarySpectrum`: PDF p.7: complementary expression uses OPPOSITE limits. SOURCE CORRECTION: at epsilon=1 use low<=0 rather than the displayed low<0.
--   - `identificationRate`: PDF p.7: double-log rate. N=1 gives -infinity, not a Real.log 0 fallback.
--   - `identificationCapacity`: PDF p.7: D and D-dagger with operational zero-rate baseline. Only the first-error limit changes. At mu=0 replace strict <mu with equality to zero; second error always uses limsup.
--   - `simulationCapacity`: PDF p.7: S and S-dagger. SOURCE CORRECTION: printed SUP over achievable simulation rates is INF; the feasible set is upward closed, and pp.8–9 use its infimum. At epsilon=2 the error comparison is strict <2.
--   - `normalizedMessageLog`: PDF p.9: ordinary log transmission rate, not double-log rate.
--   - `generalSecrecyCapacity`: PDF p.9: general capacities. true requires I_E/n->0; false requires pairwise full L1->0. Both require average Bob error->0, with zero-rate baseline.
--   - `spectralDifference`: PDF p.9: proof-based finite-threshold cuts, avoiding infinity-infinity.
--   - `preprocessedBound`: PDF p.9: all auxiliary alphabets, laws, and stochastic preprocessing channels. The SAME Q precedes Bob and Eve. The universe is arbitrary.
--   - `memorylessKernel`: PDF p.10: memoryless product kernel; code inputs need NOT be iid.
--   - `iidReferenceMass`: PDF p.10: only the reference law is tensorized.
--   - `fixedResolvabilityExponent`: PDF p.10: fixed-input optimal exponent, optimizing ACTUAL code sequences with limsup rate<=R. The error exponent is a liminf with extended logarithms.
--   - `worstExponent`: PDF p.10: worst-case exponent; block input laws are arbitrary, not only iid. The underlying extrema are numerical values, without unattained code witnesses.
--   - `psiExponent`: PDF pp.10,12, (36)/(60): hayashiPsi exponent with denominator 1+s.
--   - `phiExponent`: PDF pp.10,12, (37)/(59): hayashiPhi exponent; t=0 has objective zero.
--   - `worstPsiExponent`: PDF p.10, (38): worst hayashiPsi exponent, retaining the printed moment.
--   - `worstPhiExponent`: PDF p.10, (39): input optimization BEFORE optimizing t.
--   - `reliabilityExponent`: PDF p.12, (58): Bob reliability includes message plus sacrifice rate.
--   - `iidMaximumLikelihoodDecision`: Hayashi PDF p.6, Gallager [7] ingredient: select an actual maximum-likelihood message, with an arbitrary fixed tie convention. N is positive.
--   - `iidMaximumLikelihoodError`: Hayashi PDF p.6: actual uniform-message error of the selected ML decoder on a deterministic tuple. It counts repeated entries as different messages.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, https://arxiv.org/abs/cs/0503088v2

import Mathlib

/-!
Hayashi, arXiv:cs/0503088v2. Classical discrete channels, natural logarithms,
and full L1 distance. Positive blocklength n is indexed by k with n=k+1.
All new definitions are local to this paper. No accepted definition is modified.
Model-specific names distinguish these arbitrary discrete classical objects from
inequivalent frozen declarations; see MODERATION_NOTES.md for exact comparisons.
The printed sup defining simulation capacity is corrected to inf, as required
by the operational proof. Compilation and independent moderation are pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- PDF p.2: normalized classical discrete stochastic rows, without finiteness. -/
def IsDiscreteStochastic {X Y : Type*} (W : X → Y → ℝ≥0∞) : Prop :=
  ∀ x, (∑' y, W x y) = 1

/-- PDF p.2: discreteOutputMixture mixture. Theorem inputs are PMFs or actual iid/uniform laws. -/
def discreteOutputMixture {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∑' x, p x * W x y

/-- PDF p.4: FULL L1 distance; for probability laws it lies in [0,2]. -/
def fullL1 {Y : Type*} (p q : Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' y, ((p y - q y) + (q y - p y))

/-- PDF pp.4,9: nonnegative KL generator. On normalized laws its sum equals
sum p log(p/q), since -p+q cancels globally. At p=0 its generator limit is q;
the SOURCE's p log(p/q) term itself is zero there. Positive p and zero q give
infinity. This representation avoids any nonsummable signed real tsum. -/
def klAtom (p q : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 then q else if q = 0 then ⊤ else
    q * ENNReal.ofReal
      ((p.toReal / q.toReal) * Real.log (p.toReal / q.toReal) - p.toReal / q.toReal + 1)

/-- PDF pp.4,9: extended nonnegative KL in nats, by nonnegative summation. -/
def discreteKLDivergence {Y : Type*} (p q : Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' y, klAtom (p y) (q y)

/-- PDF p.9: extended likelihood. Zero numerator has zero probability;
positive numerator and zero denominator give +infinity, never Real.log(p/0). -/
def logLikelihood (p q : ℝ≥0∞) : EReal :=
  if p = 0 then ⊥ else if q = 0 then ⊤ else (Real.log (p.toReal / q.toReal) : EReal)

/-- PDF pp.2,4: event probability under the actual joint law p(x)W_x(y). -/
def jointEvent {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞)
    (A : X → Y → Prop) : ℝ≥0∞ :=
  ∑' x, ∑' y, if A x y then p x * W x y else 0

/-- PDF p.4: upper truncation >C; the joint-support guard removes null rows. -/
def upperLikelihoodMass {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (C : ℝ) : ℝ :=
  (jointEvent W p (fun x y => 0 < p x ∧ 0 < discreteOutputMixture W p y ∧
    ENNReal.ofReal C < W x y / discreteOutputMixture W p y)).toReal

/-- PDF p.4: low likelihood probability, with the source's weak <=C boundary. -/
def lowTail {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (C : ℝ) : ℝ :=
  (jointEvent W p (fun x y => W x y / discreteOutputMixture W p y ≤ ENNReal.ofReal C)).toReal

/-- PDF p.4: upperLikelihoodMass-prime = E_p sum_{W_x/W_p<=C} W_x^2/W_p.
Joint/discreteOutputMixture zero mass is removed BEFORE division. On normalized channels it
is at most C, so all later toReal conversions are of finite quantities. -/
def deltaPrime {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (C : ℝ) : ℝ≥0∞ :=
  ∑' x, ∑' y, if 0 < p x ∧ 0 < discreteOutputMixture W p y ∧
      W x y / discreteOutputMixture W p y ≤ ENNReal.ofReal C then
    p x * (W x y) ^ 2 / discreteOutputMixture W p y else 0

/-- PDF p.4: entropySummand(0)=0, agreeing with the continuous entropy summand. -/
def entropySummand (a : ℝ) : ℝ := if a = 0 then 0 else -a * Real.log a

/-- PDF p.4: exp(hayashiPhi(t|W,p)), with the source's power 1/(1+t). -/
def phiMoment {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∑' y, (∑' x, p x * (W x y) ^ (1 / (1 + t))) ^ (1 + t)

/-- PDF pp.4,10: extended hayashiPhi; its normalized zero endpoint is zero. -/
def hayashiPhi {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (t : ℝ) : EReal :=
  if t = 0 then 0 else ENNReal.log (phiMoment W p t)

/-- PDF p.10: exp(hayashiPsi), excluding zero mixture mass before negative powers. -/
def discretePsiMoment {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∑' y, if discreteOutputMixture W p y = 0 then 0 else
    (∑' x, p x * (W x y) ^ (1 + s)) * (discreteOutputMixture W p y) ^ (-s)

/-- PDF p.10: fixed-input hayashiPsi; hayashiPsi(0)=0 for normalized laws. -/
def hayashiPsi {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (s : ℝ) : EReal :=
  if s = 0 then 0 else ENNReal.log (discretePsiMoment W p s)

/-- PDF p.10: printed worst-input hayashiPsi, with the UNUSUAL exponent 1-s
retained literally. A numerical supremum asserts no maximizing law. -/
def worstPsi {X Y : Type*} (W : X → Y → ℝ≥0∞) (s : ℝ) : EReal :=
  ENNReal.log (⨆ p : PMF X, ∑' y, (∑' x, p x * (W x y) ^ (1 + s)) ^ (1 - s))

/-- PDF p.4, (9)/(12): no extra factor two inside the square root. -/
def l1Bound {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞)
    (C : ℝ) (M : ℕ) : ℝ :=
  2 * upperLikelihoodMass W p C + Real.sqrt ((deltaPrime W p C).toReal / M)

/-- PDF p.4, (10)/(13): one-shot KL bound; -1/2<=t<0 where used.
An infinite moment remains infinite, rather than being converted to a real. -/
def klBound {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞)
    (M : ℕ) (t : ℝ) : EReal :=
  ENNReal.log (1 + (M : ℝ≥0∞) ^ t * phiMoment W p t) / ((-t : ℝ) : EReal)

/-- PDF p.4, (11)/(14): entropy bound; invoked only when Y is finite. -/
def entropyBound {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞)
    (M : ℕ) (C : ℝ) : ℝ :=
  entropySummand (upperLikelihoodMass W p C) + upperLikelihoodMass W p C * Real.log (Nat.card Y) +
    (deltaPrime W p C).toReal / M

/-- PDF p.4: positive tuple codebook; repeated input symbols are allowed. -/
structure Book (X : Type*) where
  size : ℕ
  positive : 0 < size
  entry : Fin size → X

/-- PDF p.4: actual empirical discreteOutputMixture of a tuple codebook. -/
def empirical {X Y : Type*} (W : X → Y → ℝ≥0∞) (b : Book X) (y : Y) : ℝ≥0∞ :=
  (b.size : ℝ≥0∞)⁻¹ * ∑ i, W (b.entry i) y

/-- PDF p.4: empirical discreteOutputMixture for a specified M-tuple. -/
def tupleOutput {X Y : Type*} (W : X → Y → ℝ≥0∞) {M : ℕ}
    (a : Fin M → X) (y : Y) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ i, W (a i) y

/-- PDF p.4, Lemma 2: actual expectation under the iid tuple distribution p^M. -/
def iidExpectation {X : Type*} (p : PMF X) (M : ℕ)
    (f : (Fin M → X) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, (∏ i, p (a i)) * f a

/-- PDF p.6: infimum over ACTUAL positive tuple codes of size AT MOST M.
KL and L1 have separate optima. No attainment is asserted. -/
def bestApproximation {X Y : Type*} (kl : Bool) (M : ℕ)
    (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) : ℝ≥0∞ :=
  sInf {v | ∃ b : Book X, b.size ≤ M ∧ v =
    if kl then discreteKLDivergence (empirical W b) (discreteOutputMixture W p)
    else fullL1 (empirical W b) (discreteOutputMixture W p)}

/-- PDF p.6: supremum of the approximation optimum over ALL input laws. -/
def worstApproximation {X Y : Type*} (kl : Bool) (M : ℕ)
    (W : X → Y → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ p : PMF X, bestApproximation kl M W p

/-- PDF pp.2,7: nonempty identification code; regions need not be disjoint. -/
structure IdentificationCode (X Y : Type*) where
  messages : ℕ
  positive : 0 < messages
  encoder : Fin messages → PMF X
  region : Fin messages → Set Y

/-- PDF p.2: maximal first error, bounded by one on stochastic channels. -/
def firstError {X Y : Type*} (W : X → Y → ℝ≥0∞) (c : IdentificationCode X Y) : ℝ :=
  (⨆ i, ∑' y, if y ∈ c.region i then 0 else discreteOutputMixture W (c.encoder i) y).toReal

/-- PDF p.2: maximal second error. The singleton's empty nonnegative supremum
is zero; empty MESSAGE codes remain excluded. -/
def secondError {X Y : Type*} (W : X → Y → ℝ≥0∞) (c : IdentificationCode X Y) : ℝ :=
  (⨆ i, ⨆ j, ⨆ (_ : i ≠ j), ∑' y,
    if y ∈ c.region i then discreteOutputMixture W (c.encoder j) y else 0).toReal

/-- PDF p.6: stochastic wiretap code with positive count and disjoint regions. -/
structure DiscreteStochasticWiretapCode (X Y : Type*) where
  messages : ℕ
  positive : 0 < messages
  encoder : Fin messages → PMF X
  region : Fin messages → Set Y
  disjoint : Pairwise (fun i j => Disjoint (region i) (region j))

/-- PDF p.6: UNIFORM-message average Bob error, not a maximal error. -/
def averageBobError {X Y : Type*} (W : X → Y → ℝ≥0∞) (c : DiscreteStochasticWiretapCode X Y) : ℝ≥0∞ :=
  (c.messages : ℝ≥0∞)⁻¹ * ∑ i, ∑' y,
    if y ∈ c.region i then 0 else discreteOutputMixture W (c.encoder i) y

/-- PDF p.6: actual Eve discreteOutputMixture marginal of the uniform message. -/
def eveOutputMarginal {X Y Z : Type*} (W : X → Z → ℝ≥0∞) (c : DiscreteStochasticWiretapCode X Y)
    (z : Z) : ℝ≥0∞ :=
  (c.messages : ℝ≥0∞)⁻¹ * ∑ i, discreteOutputMixture W (c.encoder i) z

/-- PDF p.6: Eve mutual information, extended KL in nats. -/
def averageEveDivergence {X Y Z : Type*} (W : X → Z → ℝ≥0∞) (c : DiscreteStochasticWiretapCode X Y) : ℝ≥0∞ :=
  (c.messages : ℝ≥0∞)⁻¹ * ∑ i, discreteKLDivergence (discreteOutputMixture W (c.encoder i)) (eveOutputMarginal W c)

/-- PDF p.6: average full L1 over ordered DISTINCT pairs.
The empty pair average at M=1 is explicitly zero. -/
def eveDistance {X Y Z : Type*} (W : X → Z → ℝ≥0∞) (c : DiscreteStochasticWiretapCode X Y) : ℝ≥0∞ :=
  if c.messages = 1 then 0 else
    ((c.messages : ℝ≥0∞) * (c.messages - 1 : ℕ))⁻¹ *
      ∑ i, ∑ j, if i = j then 0 else
        fullL1 (discreteOutputMixture W (c.encoder i)) (discreteOutputMixture W (c.encoder j))

/-- PDF pp.7–12: all exponent denominators are positive lengths. -/
def length (k : ℕ) : ℕ := k + 1

/-- PDF pp.7,10: positive integer rounding of exp(nR), preserving its log rate. -/
def sampleCount (k : ℕ) (R : ℝ) : ℕ := max 1 ⌈Real.exp ((length k : ℝ) * R)⌉₊

/-- PDF pp.10,12: liminf normalized negative log, with +infinity at zero error. -/
def liminfErrorExponent (e : ℕ → ℝ≥0∞) : EReal :=
  Filter.liminf (fun k => -ENNReal.log (e k) / (length k : EReal)) atTop

/-- PDF p.7: spectral upper-tail probability at a finite normalized threshold. -/
def informationTailProbability {X Y : ℕ → Type*} (W : (k : ℕ) → X k → Y k → ℝ≥0∞)
    (p : (k : ℕ) → PMF (X k)) (a : ℝ) (k : ℕ) : ℝ :=
  (jointEvent (W k) (p k) (fun x y => (a : EReal) <
    logLikelihood (W k x y) (discreteOutputMixture (W k) (p k) y) / (length k : EReal))).toReal

/-- PDF p.7: complementary low-event probability, with <=a. -/
def spectralLow {X Y : ℕ → Type*} (W : (k : ℕ) → X k → Y k → ℝ≥0∞)
    (p : (k : ℕ) → PMF (X k)) (a : ℝ) (k : ℕ) : ℝ :=
  (jointEvent (W k) (p k) (fun x y =>
    logLikelihood (W k x y) (discreteOutputMixture (W k) (p k) y) / (length k : EReal) ≤ (a : EReal))).toReal

/-- PDF p.7: epsilon upper/lower spectra: true uses limsup upper tail, false
uses liminf. At epsilon=1 the condition is STRICT <1. Extended infima avoid
empty/unbounded-set defaults. -/
def epsilonInformationSpectrum {X Y : ℕ → Type*} (upper : Bool)
    (W : (k : ℕ) → X k → Y k → ℝ≥0∞) (p : (k : ℕ) → PMF (X k)) (eps : ℝ) : EReal :=
  sInf {v : EReal | ∃ a : ℝ, v = (a : EReal) ∧
    let tail := if upper then Filter.limsup (informationTailProbability W p a) atTop
      else Filter.liminf (informationTailProbability W p a) atTop
    if eps = 1 then tail < 1 else tail ≤ eps}

/-- PDF p.7: complementary expression uses OPPOSITE limits.
SOURCE CORRECTION: at epsilon=1 use low<=0 rather than the displayed low<0. -/
def complementarySpectrum {X Y : ℕ → Type*} (upper : Bool)
    (W : (k : ℕ) → X k → Y k → ℝ≥0∞) (p : (k : ℕ) → PMF (X k)) (eps : ℝ) : EReal :=
  sSup {v : EReal | ∃ a : ℝ, v = (a : EReal) ∧
    let low := if upper then Filter.liminf (spectralLow W p a) atTop
      else Filter.limsup (spectralLow W p a) atTop
    if eps = 1 then low ≤ 0 else low < 1 - eps}

/-- PDF p.7: double-log rate. N=1 gives -infinity, not a Real.log 0 fallback. -/
def identificationRate {X Y : Type*} (c : IdentificationCode X Y) (k : ℕ) : EReal :=
  ENNReal.log (ENNReal.ofReal (Real.log c.messages)) / (length k : EReal)

/-- PDF p.7: D and D-dagger with operational zero-rate baseline. Only the
first-error limit changes. At mu=0 replace strict <mu with equality to zero;
second error always uses limsup. -/
def identificationCapacity {X Y : ℕ → Type*} (optimistic : Bool)
    (W : (k : ℕ) → X k → Y k → ℝ≥0∞) (mu lam : ℝ) : EReal :=
  max 0 (sSup {r : EReal | ∃ c : (k : ℕ) → IdentificationCode (X k) (Y k),
    r = Filter.liminf (fun k => identificationRate (c k) k) atTop ∧
    (let e := if optimistic then Filter.liminf (fun k => firstError (W k) (c k)) atTop
      else Filter.limsup (fun k => firstError (W k) (c k)) atTop
     if mu = 0 then e = 0 else e < mu) ∧
    Filter.limsup (fun k => secondError (W k) (c k)) atTop ≤ lam})

/-- PDF p.7: S and S-dagger. SOURCE CORRECTION: printed SUP over achievable
simulation rates is INF; the feasible set is upward closed, and pp.8–9 use
its infimum. At epsilon=2 the error comparison is strict <2. -/
def simulationCapacity {X Y : ℕ → Type*} (optimistic : Bool)
    (W : (k : ℕ) → X k → Y k → ℝ≥0∞) (eps : ℝ) : EReal :=
  sInf {r : EReal | ∃ R : ℝ, 0 ≤ R ∧ r = (R : EReal) ∧
    let e := if optimistic then Filter.liminf
        (fun k => (worstApproximation false (sampleCount k R) (W k)).toReal) atTop
      else Filter.limsup
        (fun k => (worstApproximation false (sampleCount k R) (W k)).toReal) atTop
    if eps = 2 then e < 2 else e ≤ eps}

/-- PDF p.9: ordinary log transmission rate, not double-log rate. -/
def normalizedMessageLog {X Y : Type*} (c : DiscreteStochasticWiretapCode X Y) (k : ℕ) : EReal :=
  (Real.log c.messages : EReal) / (length k : EReal)

/-- PDF p.9: general capacities. true requires I_E/n->0; false requires
pairwise full L1->0. Both require average Bob error->0, with zero-rate baseline. -/
def generalSecrecyCapacity {X Y Z : ℕ → Type*} (kl : Bool)
    (B : (k : ℕ) → X k → Y k → ℝ≥0∞) (E : (k : ℕ) → X k → Z k → ℝ≥0∞) : EReal :=
  max 0 (sSup {r : EReal | ∃ c : (k : ℕ) → DiscreteStochasticWiretapCode (X k) (Y k),
    r = Filter.liminf (fun k => normalizedMessageLog (c k) k) atTop ∧
    Tendsto (fun k => averageBobError (B k) (c k)) atTop (nhds 0) ∧
    if kl then Tendsto (fun k => averageEveDivergence (E k) (c k) / (length k : ℝ≥0∞)) atTop (nhds 0)
      else Tendsto (fun k => eveDistance (E k) (c k)) atTop (nhds 0)})

/-- PDF p.9: proof-based finite-threshold cuts, avoiding infinity-infinity. -/
def spectralDifference (lo hi : EReal) : EReal :=
  sSup {v : EReal | ∃ a b : ℝ, (a : EReal) < lo ∧ hi < (b : EReal) ∧ v = (a - b : ℝ)}

/-- PDF p.9: all auxiliary alphabets, laws, and stochastic preprocessing
channels. The SAME Q precedes Bob and Eve. The universe is arbitrary. -/
def preprocessedBound {X Y Z : ℕ → Type u}
    (B : (k : ℕ) → X k → Y k → ℝ≥0∞) (E : (k : ℕ) → X k → Z k → ℝ≥0∞) : EReal :=
  max 0 (sSup {r : EReal | ∃ A : ℕ → Type u,
    ∃ Q : (k : ℕ) → A k → PMF (X k), ∃ p : (k : ℕ) → PMF (A k),
      r = spectralDifference
        (epsilonInformationSpectrum false (fun k a => discreteOutputMixture (B k) (Q k a)) p 1)
        (epsilonInformationSpectrum true (fun k a => discreteOutputMixture (E k) (Q k a)) p 0)})

/-- PDF p.10: memoryless product kernel; code inputs need NOT be iid. -/
def memorylessKernel {X Y : Type*} (W : X → Y → ℝ≥0∞) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) : ℝ≥0∞ := ∏ i, W (x i) (y i)

/-- PDF p.10: only the reference law is tensorized. -/
def iidReferenceMass {X : Type*} (p : PMF X) (n : ℕ) (x : Fin n → X) : ℝ≥0∞ :=
  ∏ i, p (x i)

/-- PDF p.10: fixed-input optimal exponent, optimizing ACTUAL code sequences
with limsup rate<=R. The error exponent is a liminf with extended logarithms. -/
def fixedResolvabilityExponent {X Y : Type*} (kl : Bool) (W : X → Y → ℝ≥0∞)
    (p : PMF X) (R : ℝ) : EReal :=
  sSup {e : EReal | ∃ b : (k : ℕ) → Book (Fin (length k) → X),
    Filter.limsup (fun k => (Real.log (b k).size : EReal) / (length k : EReal)) atTop ≤ (R : EReal) ∧
    e = liminfErrorExponent (fun k => if kl then
      discreteKLDivergence (empirical (memorylessKernel W (length k)) (b k))
        (discreteOutputMixture (memorylessKernel W (length k)) (iidReferenceMass p (length k)))
      else fullL1 (empirical (memorylessKernel W (length k)) (b k))
        (discreteOutputMixture (memorylessKernel W (length k)) (iidReferenceMass p (length k))))}

/-- PDF p.10: worst-case exponent; block input laws are arbitrary, not only iid.
The underlying extrema are numerical values, without unattained code witnesses. -/
def worstExponent {X Y : Type*} (kl : Bool) (W : X → Y → ℝ≥0∞) (R : ℝ) : EReal :=
  liminfErrorExponent (fun k => worstApproximation kl (sampleCount k R) (memorylessKernel W (length k)))

/-- PDF pp.10,12, (36)/(60): hayashiPsi exponent with denominator 1+s. -/
def psiExponent {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : PMF X) (R : ℝ) : EReal :=
  sSup ((fun s : ℝ => (-hayashiPsi W p s + ((s * R : ℝ) : EReal)) /
    ((1 + s : ℝ) : EReal)) '' Set.Icc 0 1)

/-- PDF pp.10,12, (37)/(59): hayashiPhi exponent; t=0 has objective zero. -/
def phiExponent {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : PMF X) (R : ℝ) : EReal :=
  sSup ((fun t : ℝ => -hayashiPhi W p t - ((t * R : ℝ) : EReal)) '' Set.Icc (-(1 / 2)) 0)

/-- PDF p.10, (38): worst hayashiPsi exponent, retaining the printed moment. -/
def worstPsiExponent {X Y : Type*} (W : X → Y → ℝ≥0∞) (R : ℝ) : EReal :=
  sSup ((fun s : ℝ => (-worstPsi W s + ((s * R : ℝ) : EReal)) /
    ((1 + s : ℝ) : EReal)) '' Set.Icc 0 1)

/-- PDF p.10, (39): input optimization BEFORE optimizing t. -/
def worstPhiExponent {X Y : Type*} (W : X → Y → ℝ≥0∞) (R : ℝ) : EReal :=
  sSup ((fun t : ℝ => -(⨆ p : PMF X, hayashiPhi W p t) - ((t * R : ℝ) : EReal)) ''
    Set.Icc (-(1 / 2)) 0)

/-- PDF p.12, (58): Bob reliability includes message plus sacrifice rate. -/
def reliabilityExponent {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : PMF X) (R : ℝ) : EReal :=
  sSup ((fun s : ℝ => -hayashiPhi W p s - ((s * R : ℝ) : EReal)) '' Set.Icc 0 1)

/-- Sanity: a support mismatch gives infinite KL. -/
example : klAtom 1 0 = ⊤ := by simp [klAtom]

/-- Sanity: one empirical sample gives the actual selected channel row. -/
example {X Y : Type*} (W : X → Y → ℝ≥0∞) (a : Fin 1 → X) (y : Y) :
    tupleOutput W a y = W (a 0) y := by simp [tupleOutput]

/-- Sanity: a one-use product channel preserves its row. -/
example {X Y : Type*} (W : X → Y → ℝ≥0∞) (x : Fin 1 → X) (y : Fin 1 → Y) :
    memorylessKernel W 1 x y = W (x 0) (y 0) := by simp [memorylessKernel]

/-- Sanity: exact zero error gives an infinite negative logarithm. -/
example : -ENNReal.log 0 = (⊤ : EReal) := by simp

/-- Hayashi PDF p.6, Gallager [7] ingredient: select an actual maximum-likelihood
message, with an arbitrary fixed tie convention. N is positive. -/
def iidMaximumLikelihoodDecision {X Y : Type*} {N : ℕ}
    (W : X → Y → ℝ≥0∞) (a : Fin N → X) (hN : 0 < N) (y : Y) : Fin N :=
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  Classical.epsilon (fun i => ∀ j, W (a j) y ≤ W (a i) y)

/-- Hayashi PDF p.6: actual uniform-message error of the selected ML decoder
on a deterministic tuple. It counts repeated entries as different messages. -/
def iidMaximumLikelihoodError {X Y : Type*} {N : ℕ}
    (W : X → Y → ℝ≥0∞) (a : Fin N → X) (hN : 0 < N) : ℝ≥0∞ :=
  (N : ℝ≥0∞)⁻¹ * ∑ i, ∑' y,
    if iidMaximumLikelihoodDecision W a hN y = i then 0 else W (a i) y

/-- Sanity: a one-message ML decoder selects its only message. -/
example {X Y : Type*} (W : X → Y → ℝ≥0∞) (a : Fin 1 → X) (y : Y) :
    iidMaximumLikelihoodDecision W a (by decide) y = 0 := by
  exact Subsingleton.elim _ _

end QAlgorithms.Papers.Independent.Intake100.P73


