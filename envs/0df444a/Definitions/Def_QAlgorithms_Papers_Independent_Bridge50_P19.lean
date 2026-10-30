-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P19
-- name    : QAlgorithms_Papers_Independent_Bridge50_P19
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:54:59.653552+00:00
-- url     : https://prove2.me/theorems/d6b43078-7cf0-44da-972a-323d08fdef36
-- title:
--   Definitions for Unconstrained Capacities of Quantum Key Distribution and Entanglement Distillation for Pure-Loss Bosonic Broadcast Channels
-- statement:
--   The objects the formalized statements of *Unconstrained Capacities of Quantum Key Distribution and Entanglement Distillation for Pure-Loss Bosonic Broadcast Channels* (arXiv:1706.06746) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `detectedAmplitude`: PDF pp.7–8, Fig.5 and (30): amplitude of the TMSV after the broadcast channel and both trusted 50% detector losses. Coordinates 0,1,2 are Alice, Bob's detected mode and Charlie's detected mode. The unmeasured modes can be combined into one vacuum output for this classical marginal only.
--   - `detectedResource`: PDF p.8: actual three-mode density before the sifted homodyne readings. This partial trace includes all undetected output modes.
--   - `quadratureTerm`: PDF p.8, corrected (32): the number-basis Born term for the measured coordinates. The Hermite wavefunctions have vacuum variance 1/2.
--   - `quadratureDensity`: PDF p.8, corrected (32): actual marginal outcome density relative to Lebesgue measure. Series convergence and probability normalization are conclusions, not assumptions encoding the entropy calculation.
--   - `measuredEntropyBits`: PDF p.8, (33)–(38): differential Shannon entropy in bits of the actual measured marginal. Integrability is supplied by the theorem before use.
--   - `measuredSets`: PDF p.8: the six measured marginals explicitly evaluated in (33)–(38).
--   - `RegularMeasuredMarginal`: PDF p.8: analytic validity of the Born-density and entropy expressions. This guard is a conclusion of the evaluation theorem.
--   - `groupedAmplitude`: PDF pp.8–9, Fig.5(c),(39): vacuum splitter powers for the combined adversary C'=CE, the detected receiver mode, and trusted detector vacuum. For receiver power t in [0,1] these sum to one. The sign of C' is a removable local phase, fixed positive here. C' never includes trusted detector loss.
--   - `groupedJoint`: PDF pp.8–9, (39): actual C',B density, obtained by splitting a thermal signal of mean mu and tracing only the trusted detector port. Tracing Alice makes the input photon number diagonal. No entropy formula defines this state.
--   - `groupedMarginal`: PDF p.9, (40): the true unconditioned C'=CE marginal.
--   - `conditionalNumerator`: PDF p.9, (43)–(46): unnormalized conditional C' density from the homodyne spectral density on the detected receiver mode. Conditional means are retained through the outcome-dependent Hermite functions.
--   - `receiverDensity`: PDF p.9: actual homodyne outcome probability density.
--   - `conditionalAdversary`: PDF p.9: normalized measurement-conditioned adversary state. The theorem establishes a strictly positive denominator for every real y.
--   - `oscillatorEntropyBits`: PDF p.9, (40),(46): genuine spectral von Neumann entropy in bits. Finiteness is established before conversion to a real number.
--   - `adversaryHolevoBits`: PDF pp.8–9: Holevo information between the detected classical receiver outcome and CE (or BE in the swapped ordering). This is quantum side information, not the mutual information of two classical outcomes.
--   - `conditionalOccupation`: PDF p.9, (45),(46): (sqrt(alpha beta)-1)/2, with v=2mu+1. This scalar is an evaluation target, never the definition of a density or entropy.
-- source:
--   Unconstrained Capacities of Quantum Key Distribution and Entanglement Distillation for Pure-Loss Bosonic Broadcast Channels, arXiv:1706.06746v1, https://arxiv.org/abs/1706.06746v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

/-!
# arXiv:1706.06746v1: broadcast CVQKD information evaluation

PDF pp.7–9. The operational capacity and key-distillation nodes are deferred,
not identified with scalar polytopes. Two resource nodes reuse Support50.P48.
The theorem below evaluates actual Born densities and quantum conditional
states on the complete oscillator number basis. No covariance-only state
predicate, photon cutoff, independently supplied information number, or
outcome-independent conditional density is used.

Quadratures have vacuum variance 1/2 (quantum doubled covariance I). Sifting
conditions on Alice's public quadrature choice; phase symmetry permits the
q quadrature throughout. Trusted detector loss is traced, never given to Eve.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P19

open MeasureTheory
open scoped BigOperators ENNReal NNReal
open QAlgorithms.Papers.Independent.Dependency50.P30
  (PureLossBroadcastParameters thermalEntropyBits)
open QAlgorithms.Papers.Independent.Support50.P48
  (tmsvWeight vacuumAmplitude subsystem)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Gap48.P13 (hermiteValue)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7–8, Fig.5 and (30): amplitude of the TMSV after the broadcast
channel and both trusted 50% detector losses. Coordinates 0,1,2 are Alice,
Bob's detected mode and Charlie's detected mode. The unmeasured modes can
be combined into one vacuum output for this classical marginal only. -/
def detectedAmplitude (p : PureLossBroadcastParameters 2) (mu : ℝ≥0)
    (a : Fin 3 → ℕ) (e : ℕ) : ℝ :=
  Real.sqrt (tmsvWeight mu (a 0)) *
    vacuumAmplitude
      ![p.transmissivity 0 / 2, p.transmissivity 1 / 2,
        1 - p.transmissivity 0 / 2 - p.transmissivity 1 / 2]
      ![a 1, a 2, e] (a 0)

/-- PDF p.8: actual three-mode density before the sifted homodyne readings.
This partial trace includes all undetected output modes. -/
def detectedResource (p : PureLossBroadcastParameters 2) (mu : ℝ≥0) :
    Matrix (Fin 3 → ℕ) (Fin 3 → ℕ) ℂ :=
  fun a b => ∑' e : ℕ,
    (detectedAmplitude p mu a e : ℂ) * (detectedAmplitude p mu b e : ℂ)

/-- PDF p.8, corrected (32): the number-basis Born term for the measured
coordinates. The Hermite wavefunctions have vacuum variance 1/2. -/
def quadratureTerm (p : PureLossBroadcastParameters 2) (mu : ℝ≥0)
    (S : Finset (Fin 3)) (x : S → ℝ) (a b : S → ℕ) : ℂ :=
  subsystem S (detectedResource p mu) a b *
    (∏ i : S, hermiteValue (a i) (x i)) *
    star (∏ i : S, hermiteValue (b i) (x i))

/-- PDF p.8, corrected (32): actual marginal outcome density relative to
Lebesgue measure. Series convergence and probability normalization are
conclusions, not assumptions encoding the entropy calculation. -/
def quadratureDensity (p : PureLossBroadcastParameters 2) (mu : ℝ≥0)
    (S : Finset (Fin 3)) (x : S → ℝ) : ℝ :=
  (∑' a : S → ℕ, ∑' b : S → ℕ, quadratureTerm p mu S x a b).re

/-- PDF p.8, (33)–(38): differential Shannon entropy in bits of the actual
measured marginal. Integrability is supplied by the theorem before use. -/
def measuredEntropyBits (p : PureLossBroadcastParameters 2) (mu : ℝ≥0)
    (S : Finset (Fin 3)) : ℝ :=
  -∫ x : S → ℝ, quadratureDensity p mu S x *
    Real.logb 2 (quadratureDensity p mu S x)

/-- PDF p.8: the six measured marginals explicitly evaluated in (33)–(38). -/
def measuredSets : Finset (Finset (Fin 3)) :=
  {Finset.univ, {0}, {1}, {2}, {0, 1}, {0, 2}}

/-- PDF p.8: analytic validity of the Born-density and entropy expressions.
This guard is a conclusion of the evaluation theorem. -/
def RegularMeasuredMarginal (p : PureLossBroadcastParameters 2) (mu : ℝ≥0)
    (S : Finset (Fin 3)) : Prop :=
  (∀ x : S → ℝ,
    (∀ a : S → ℕ, Summable (fun b => quadratureTerm p mu S x a b)) ∧
    Summable (fun a : S → ℕ => ∑' b : S → ℕ, quadratureTerm p mu S x a b)) ∧
  (∀ x : S → ℝ, 0 ≤ quadratureDensity p mu S x) ∧
  Integrable (quadratureDensity p mu S) ∧
  (∫ x : S → ℝ, quadratureDensity p mu S x) = 1 ∧
  Integrable (fun x : S → ℝ =>
    quadratureDensity p mu S x * Real.logb 2 (quadratureDensity p mu S x))

/-- PDF pp.8–9, Fig.5(c),(39): vacuum splitter powers for the combined
adversary C'=CE, the detected receiver mode, and trusted detector vacuum.
For receiver power t in [0,1] these sum to one. The sign of C' is a removable
local phase, fixed positive here. C' never includes trusted detector loss. -/
def groupedAmplitude (t : ℝ≥0) (a b e n : ℕ) : ℝ :=
  vacuumAmplitude ![1 - t, t / 2, t / 2] ![a, b, e] n

/-- PDF pp.8–9, (39): actual C',B density, obtained by splitting a thermal
signal of mean mu and tracing only the trusted detector port. Tracing Alice
makes the input photon number diagonal. No entropy formula defines this state. -/
def groupedJoint (t mu : ℝ≥0) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun a b => ∑' e : ℕ, if a.1 + a.2 = b.1 + b.2 then
    ((tmsvWeight mu (a.1 + a.2 + e) *
      groupedAmplitude t a.1 a.2 e (a.1 + a.2 + e) *
      groupedAmplitude t b.1 b.2 e (b.1 + b.2 + e) : ℝ) : ℂ)
    else 0

/-- PDF p.9, (40): the true unconditioned C'=CE marginal. -/
def groupedMarginal (t mu : ℝ≥0) : Matrix ℕ ℕ ℂ :=
  fun a b => ∑' k : ℕ, groupedJoint t mu (a, k) (b, k)

/-- PDF p.9, (43)–(46): unnormalized conditional C' density from the
homodyne spectral density on the detected receiver mode. Conditional means
are retained through the outcome-dependent Hermite functions. -/
def conditionalNumerator (t mu : ℝ≥0) (y : ℝ) : Matrix ℕ ℕ ℂ :=
  fun a b => ∑' k : ℕ, ∑' l : ℕ,
    groupedJoint t mu (a, k) (b, l) * hermiteValue k y * star (hermiteValue l y)

/-- PDF p.9: actual homodyne outcome probability density. -/
def receiverDensity (t mu : ℝ≥0) (y : ℝ) : ℝ :=
  ∑' a : ℕ, (conditionalNumerator t mu y a a).re

/-- PDF p.9: normalized measurement-conditioned adversary state.
The theorem establishes a strictly positive denominator for every real y. -/
def conditionalAdversary (t mu : ℝ≥0) (y : ℝ) : Matrix ℕ ℕ ℂ :=
  fun a b => conditionalNumerator t mu y a b / (receiverDensity t mu y : ℂ)

/-- PDF p.9, (40),(46): genuine spectral von Neumann entropy in bits.
Finiteness is established before conversion to a real number. -/
def oscillatorEntropyBits (rho : Matrix ℕ ℕ ℂ) : ℝ≥0∞ :=
  extendedEntropyNats rho / ENNReal.ofReal (Real.log 2)

/- PDF p.9, (46): write this experiment's real-outcome entropy average
inline below. The imported Next46.P32.conditionalEntropyAverage instead
averages coherent-state ensembles over complex outcomes in nats; it cannot
replace the homodyne-conditioned entropy in bits. -/

/-- PDF pp.8–9: Holevo information between the detected classical receiver
outcome and CE (or BE in the swapped ordering). This is quantum side
information, not the mutual information of two classical outcomes. -/
def adversaryHolevoBits (t mu : ℝ≥0) : ℝ :=
  (oscillatorEntropyBits (groupedMarginal t mu)).toReal -
    (∫ y : ℝ, receiverDensity t mu y *
      (oscillatorEntropyBits (conditionalAdversary t mu y)).toReal)

/-- PDF p.9, (45),(46): (sqrt(alpha beta)-1)/2, with v=2mu+1.
This scalar is an evaluation target, never the definition of a density or entropy. -/
def conditionalOccupation (t mu : ℝ≥0) : ℝ :=
  let alpha := 1 + (1 - (t : ℝ)) * (2 * (mu : ℝ)) / ((t : ℝ) * (mu : ℝ) + 1)
  let beta := 1 + (1 - (t : ℝ)) * (2 * (mu : ℝ))
  (Real.sqrt (alpha * beta) - 1) / 2

/-- The source vacuum TMSV remains the full network vacuum. -/
example (p : PureLossBroadcastParameters 2) :
    detectedAmplitude p 0 (fun _ => 0) 0 = 1 := by
  simp [detectedAmplitude, tmsvWeight, vacuumAmplitude, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- Every splitting stage preserves the vacuum, including zero-power ports. -/
example (t : ℝ≥0) : groupedAmplitude t 0 0 0 0 = 1 := by
  simp [groupedAmplitude, vacuumAmplitude, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- Vacuum input has zero conditional thermal occupation, even at t=0 or t=1. -/
example (t : ℝ≥0) : conditionalOccupation t 0 = 0 := by
  simp [conditionalOccupation]

/-- The covariance expression has no denominator singularity at zero receiver power. -/
example (mu : ℝ≥0) : conditionalOccupation 1 mu = 0 := by
  simp [conditionalOccupation]

end QAlgorithms.Papers.Independent.Bridge50.P19


