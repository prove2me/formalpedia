-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P42
-- name    : QAlgorithms_Papers_Independent_Bridge50_P42
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:01:26.715161+00:00
-- url     : https://prove2.me/theorems/414a954a-fb49-4ef4-964b-04b1403b7856
-- title:
--   Definitions for Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels
-- statement:
--   The objects the formalized statements of *Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels* (arXiv:1406.6758) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `StochasticRows`: PDF pp.3,5: normalized stochastic rows of a classical channel.
--   - `DegradedDMC`: PDF p.5, (39): the two actual factors of a physically degraded DMC.
--   - `DegradedDMC.eve`: PDF p.6: the actual Eve marginal, obtained by composing the two channels.
--   - `DegradedDMC.joint`: PDF p.5, (39): actual single-use joint law given the input.
--   - `inducedFiniteOutput`: PDF p.3: the output law induced by a finite input law.
--   - `finiteChannelInformation`: PDF p.5, (41), and p.6: finite Shannon mutual information in bits. Reuse the frozen joint-law information applied to p(x)V(y|x). Zero joint mass contributes zero; positive mass has positive marginal factors for normalized laws. Its joint/product likelihood ratio equals V(y|x)/P_Y(y) on actual support.
--   - `finiteChannelCapacity`: PDF p.6: reuse the accepted Shannon capacity of a normalized finite DMC. The zero fallback is outside the normalized-channel domain used by every theorem. On fixed nonempty finite alphabets the supremum is finite and attained.
--   - `secrecyInfo`: PDF p.5, (41): I(X;Y)-I(X;Z) for the actual degraded channel marginals.
--   - `secrecyCapacity`: PDF p.5, (41): the finite single-letter secrecy capacity. Theorem 3 below also retains attainment of this optimization.
--   - `independentBlockKernel`: PDF pp.5–6, (40),(43): independent component channel on a block of length k+1.
--   - `DiscreteWiretapCode`: PDF p.3, Definition 2: arbitrary finite positive message count, stochastic encoder, and deterministic decoder, on the discrete block alphabets.
--   - `DiscreteWiretapCode.error`: PDF p.3, (14): average error for a uniform message and the actual Bob channel.
--   - `DiscreteWiretapCode.messageEve`: PDF p.3, Definition 1: actual joint law of the uniform message and Eve output.
--   - `DiscreteWiretapCode.independentEve`: PDF p.3, Definition 1: product of the uniform message law and actual Eve marginal.
--   - `SecrecyMetric`: PDF p.3, (5)–(10): the six distinct secrecy metrics, in the paper's order.
--   - `DiscreteWiretapCode.leakage`: PDF p.3, (5)–(10): leakage in all six metrics. The threshold is arbitrary. For actual finite-message joint/product laws, positive joint mass implies positive product mass; their likelihood ratios are finite on actual support. Zero joint mass is explicitly excluded from the divergence and probability sums.
--   - `RateAtLeast`: PDF pp.3–4, (16),(24): liminf block rate at least R, written without a real-valued liminf default on unbounded rate sequences.
--   - `Secure`: PDF pp.3–4: a single code sequence has vanishing leakage for every eta>0. `none` removes the secrecy condition for the point-to-point comparison only.
--   - `DiscreteReliable`: PDF pp.3–4, (16),(24): ordinary limsup-error and strict optimistic liminf-error criteria. The latter is a fixed positive margin on infinitely many lengths.
--   - `discreteOperationalCapacity`: PDF pp.3–4, Definitions 3–4, using the equivalent supremum formulation (24). Extrema take place in EReal, so neither empty nor unbounded sets get default zero.
--   - `PartialStrongConverse`: PDF p.4, Definition 5: actual endpoint equality, not just interior invariance.
--   - `CapacityConclusion`: PDF p.4, (27)–(29): endpoint value and all error-tolerance consequences.
--   - `WeaklySymmetric`: PDF p.6: rows are permutations and all column sums are equal.
--   - `capacityAverage`: PDF p.6, (45)–(47): Cesaro averages over the first k+1 components.
--   - `maximizingInput`: PDF p.6: construct a maximizing input from V itself. The zero fallback is used only outside the nonempty finite normalized-channel domain; the maximum exists in that domain. No comparison output distribution is supplied as data.
--   - `capacityOutput`: PDF p.6: the capacity-achieving output law, constructed from the channel.
--   - `rowInformationVariance`: PDF p.6, (46): row variance on actual row support. Unreachable outputs have mass zero and do not contribute; all reachable output denominators are positive.
--   - `PointStrongConverse`: PDF p.6: the usual point-to-point strong converse, in endpoint-capacity form. The dummy singleton Eve output imposes no secrecy condition.
--   - `InputProcess`: PDF p.8, (66)–(69): arbitrary block input laws, with no consistency or independence requirement across or within blocklengths.
--   - `blockJoint`: PDF pp.5,8, (40),(68): actual joint law induced by an arbitrary block input.
--   - `conditionalDensity`: PDF p.8, (67): normalized conditional information density. On positive actual joint support, W(z|x), P(z), P(y,z) are positive. The value off actual support is explicitly zero and never enters probabilities.
--   - `spectralConditionalSup`: PDF pp.4,8, (31),(67)–(69): the 1-p-limsup conditional information rate, with the strict lower-tail probability condition from (31), valued in EReal.
--   - `realGaussianDensity`: PDF p.3, (4), and p.6, (48): Gaussian density with positive standard deviation sigma in the theorem domain; Mathlib parameterizes it by variance.
--   - `gaussianBlockDensity`: PDF p.6, (48): memoryless real Gaussian conditional output density.
--   - `gaussianJointDensity`: PDF p.6: physical joint realization, with the source's added noise variance. Operational quantities below use its Bob and Eve marginals, respectively N(x,sigma1^2) and N(x,sigma2^2); they do not assume these two outputs independent given x.
--   - `powerBall`: PDF p.6, (49)–(50): the CLOSED block power ball.
--   - `PowerConstrainedGaussianCode`: PDF pp.3,6, Definition 2 and (49): all Borel stochastic encoders on the power ball, including non-atomic ones, and a deterministic measurable decoder. Uniform messages make per-message almost-sure power equivalent to (49).
--   - `PowerConstrainedGaussianCode.error`: PDF p.3, (14), specialized to (48): average decoding error obtained by integrating the actual Bob density and stochastic input measure. For positive sigma, these are integrals of measurable probability kernels, bounded by one.
--   - `PowerConstrainedGaussianCode.messageEve`: PDF p.3, Definition 1: the actual joint message/Eve density relative to counting measure times Lebesgue measure. Positive Gaussian noise gives a finite, strictly positive conditional output density for every z and every message.
--   - `PowerConstrainedGaussianCode.independentEve`: PDF p.3: product of the uniform message law and the actual Eve marginal.
--   - `PowerConstrainedGaussianCode.leakage`: PDF p.3, (5)–(10): all six metrics for the Gaussian code's actual densities. In the positive-noise domain q is positive and p/q <= M. The negative part of p log(p/q) is bounded by a constant times q; its positive part by p log M. Thus these real integrals are integrable, not Bochner defaults on bad functions.
--   - `GaussianReliable`: PDF pp.3–4: the ordinary and strict optimistic reliability conditions for Gaussian code sequences, with the same epsilon endpoint conventions.
--   - `gaussianOperationalCapacity`: PDF pp.3–4,6: operational capacities of the actual real Gaussian channel under the almost-sure block power constraint. Rate is liminf log M/(k+1). One code sequence works for every positive threshold eta; encoders are arbitrary Borel probability measures on the ball, not restricted Gaussian inputs.
--   - `gaussianSecrecyCapacity`: PDF p.6, (51): the Gaussian secrecy capacity in bits per channel use.
-- source:
--   Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels, arXiv:1406.6758v2, https://arxiv.org/abs/1406.6758v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

/-!
Tan and Bloch, arXiv:1406.6758v2. Paper-local finite classical coding models.
Block index k represents the positive length k+1; component index zero represents
component 1 in the paper. All logarithms and rates are in bits. The general-alphabet
formulas and Poisson extension are deferred in HARD.md.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P42

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

/-- PDF pp.3,5: normalized stochastic rows of a classical channel. -/
def StochasticRows {A B : Type*} [Fintype B] (V : A → B → ℝ) : Prop :=
  ∀ a, IsLaw (V a)

/-- PDF p.5, (39): the two actual factors of a physically degraded DMC. -/
structure DegradedDMC (X Y Z : Type*) [Fintype Y] [Fintype Z] where
  main : X → Y → ℝ
  degrade : Y → Z → ℝ
  main_law : StochasticRows main
  degrade_law : StochasticRows degrade

/-- PDF p.6: the actual Eve marginal, obtained by composing the two channels. -/
def DegradedDMC.eve {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : DegradedDMC X Y Z) (x : X) (z : Z) : ℝ :=
  ∑ y, W.main x y * W.degrade y z

/-- PDF p.5, (39): actual single-use joint law given the input. -/
def DegradedDMC.joint {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : DegradedDMC X Y Z) (x : X) (y : Y) (z : Z) : ℝ :=
  W.main x y * W.degrade y z

/-- PDF p.3: the output law induced by a finite input law. -/
def inducedFiniteOutput {X Y : Type*} [Fintype X]
    (V : X → Y → ℝ) (p : X → ℝ) (y : Y) : ℝ := ∑ x, p x * V x y

/-- PDF p.5, (41), and p.6: finite Shannon mutual information in bits.
Reuse the frozen joint-law information applied to p(x)V(y|x). Zero joint mass
contributes zero; positive mass has positive marginal factors for normalized laws.
Its joint/product likelihood ratio equals V(y|x)/P_Y(y) on actual support. -/
def finiteChannelInformation {X Y : Type*} [Fintype X] [Fintype Y]
    (V : X → Y → ℝ) (p : X → ℝ) : ℝ :=
  QAlgorithms.mutualInfoBits (fun xy : X × Y => p xy.1 * V xy.1 xy.2)

/-- PDF p.6: reuse the accepted Shannon capacity of a normalized finite DMC.
The zero fallback is outside the normalized-channel domain used by every theorem.
On fixed nonempty finite alphabets the supremum is finite and attained. -/
def finiteChannelCapacity {X Y : Type*} [Fintype X] [Fintype Y]
    (V : X → Y → ℝ) : ℝ :=
  if h : StochasticRows V then
    QAlgorithms.Papers.Independent.Dependency50.P45.shannonCapacity
      { prob := V
        nonnegative := fun x => (h x).1
        normalized := fun x => (h x).2 }
  else 0

/-- PDF p.5, (41): I(X;Y)-I(X;Z) for the actual degraded channel marginals. -/
def secrecyInfo {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : DegradedDMC X Y Z) (p : X → ℝ) : ℝ :=
  finiteChannelInformation W.main p - finiteChannelInformation W.eve p

/-- PDF p.5, (41): the finite single-letter secrecy capacity.
Theorem 3 below also retains attainment of this optimization. -/
def secrecyCapacity {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : DegradedDMC X Y Z) : ℝ :=
  sSup {r : ℝ | ∃ p : X → ℝ, IsLaw p ∧ r = secrecyInfo W p}

/-- PDF pp.5–6, (40),(43): independent component channel on a block of length k+1. -/
def independentBlockKernel {X Y : Type*} (V : ℕ → X → Y → ℝ) (k : ℕ)
    (x : Fin (k + 1) → X) (y : Fin (k + 1) → Y) : ℝ :=
  ∏ j, V j.val (x j) (y j)

/-- PDF p.3, Definition 2: arbitrary finite positive message count, stochastic
encoder, and deterministic decoder, on the discrete block alphabets. -/
structure DiscreteWiretapCode (X Y : Type*) [Fintype X] (k : ℕ) where
  messages : ℕ
  positive : 0 < messages
  encoder : Fin messages → (Fin (k + 1) → X) → ℝ
  encoder_law : ∀ m, IsLaw (encoder m)
  decoder : (Fin (k + 1) → Y) → Fin messages

/-- PDF p.3, (14): average error for a uniform message and the actual Bob channel. -/
def DiscreteWiretapCode.error {X Y : Type*} [Fintype X] [Fintype Y] {k : ℕ}
    (c : DiscreteWiretapCode X Y k) (V : ℕ → X → Y → ℝ) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m, ∑ x, ∑ y,
    if c.decoder y = m then 0 else c.encoder m x * independentBlockKernel V k x y

/-- PDF p.3, Definition 1: actual joint law of the uniform message and Eve output. -/
def DiscreteWiretapCode.messageEve {X Y Z : Type*} [Fintype X] [Fintype Z] {k : ℕ}
    (c : DiscreteWiretapCode X Y k) (V : ℕ → X → Z → ℝ)
    (m : Fin c.messages) (z : Fin (k + 1) → Z) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ x, c.encoder m x * independentBlockKernel V k x z

/-- PDF p.3, Definition 1: product of the uniform message law and actual Eve marginal. -/
def DiscreteWiretapCode.independentEve {X Y Z : Type*} [Fintype X] [Fintype Z] {k : ℕ}
    (c : DiscreteWiretapCode X Y k) (V : ℕ → X → Z → ℝ)
    (_m : Fin c.messages) (z : Fin (k + 1) → Z) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m, c.messageEve V m z

/-- PDF p.3, (5)–(10): the six distinct secrecy metrics, in the paper's order. -/
inductive SecrecyMetric where
  | divergence | variation | tail | normalizedDivergence | normalizedVariation | normalizedTail
  deriving DecidableEq

/-- PDF p.3, (5)–(10): leakage in all six metrics. The threshold is arbitrary.
For actual finite-message joint/product laws, positive joint mass implies positive
product mass; their likelihood ratios are finite on actual support. Zero joint
mass is explicitly excluded from the divergence and probability sums. -/
def DiscreteWiretapCode.leakage {X Y Z : Type*} [Fintype X] [Fintype Z] {k : ℕ}
    (c : DiscreteWiretapCode X Y k) (V : ℕ → X → Z → ℝ) (i : SecrecyMetric) (eta : ℝ) : ℝ :=
  let p := c.messageEve V
  let q := c.independentEve V
  let d := ∑ m, ∑ z, if p m z = 0 then 0 else p m z * log2 (p m z / q m z)
  let v := (1 / 2 : ℝ) * ∑ m, ∑ z, |p m z - q m z|
  let tail := fun (scale : ℝ) => ∑ m, ∑ z,
    if 0 < p m z ∧ eta < log2 (p m z / q m z) / scale then p m z else 0
  match i with
  | .divergence => d
  | .variation => v
  | .tail => tail 1
  | .normalizedDivergence => d / (k + 1 : ℝ)
  | .normalizedVariation => v / (k + 1 : ℝ)
  | .normalizedTail => tail (k + 1 : ℝ)

/-- PDF pp.3–4, (16),(24): liminf block rate at least R, written without a
real-valued liminf default on unbounded rate sequences. -/
def RateAtLeast {X Y : Type*} [Fintype X]
    (c : (k : ℕ) → DiscreteWiretapCode X Y k) (R : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop,
    R - delta ≤ log2 ((c k).messages : ℝ) / (k + 1 : ℝ)

/-- PDF pp.3–4: a single code sequence has vanishing leakage for every eta>0.
`none` removes the secrecy condition for the point-to-point comparison only. -/
def Secure {X Y Z : Type*} [Fintype X] [Fintype Z]
    (c : (k : ℕ) → DiscreteWiretapCode X Y k) (V : ℕ → X → Z → ℝ)
    (i : Option SecrecyMetric) : Prop :=
  match i with
  | none => True
  | some metric => ∀ eta : ℝ, 0 < eta →
      Tendsto (fun k => (c k).leakage V metric eta) atTop (nhds 0)

/-- PDF pp.3–4, (16),(24): ordinary limsup-error and strict optimistic
liminf-error criteria. The latter is a fixed positive margin on infinitely many lengths. -/
def DiscreteReliable {X Y : Type*} [Fintype X] [Fintype Y]
    (c : (k : ℕ) → DiscreteWiretapCode X Y k) (V : ℕ → X → Y → ℝ)
    (optimistic : Bool) (eps : ℝ) : Prop :=
  if optimistic then
    ∃ delta : ℝ, 0 < delta ∧ ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ (c k).error V < eps - delta
  else ∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop, (c k).error V ≤ eps + delta

/-- PDF pp.3–4, Definitions 3–4, using the equivalent supremum formulation (24).
Extrema take place in EReal, so neither empty nor unbounded sets get default zero. -/
def discreteOperationalCapacity {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (V : ℕ → X → Y → ℝ) (E : ℕ → X → Z → ℝ)
    (i : Option SecrecyMetric) (optimistic : Bool) (eps : ℝ) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, r = (R : EReal) ∧
    ∃ c : (k : ℕ) → DiscreteWiretapCode X Y k,
      RateAtLeast c R ∧ Secure c E i ∧ DiscreteReliable c V optimistic eps}

/-- PDF p.4, Definition 5: actual endpoint equality, not just interior invariance. -/
def PartialStrongConverse {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : ℕ → DegradedDMC X Y Z) (i : SecrecyMetric) : Prop :=
  discreteOperationalCapacity (fun j => (W j).main) (fun j => (W j).eve) (some i) false 0 =
    discreteOperationalCapacity (fun j => (W j).main) (fun j => (W j).eve) (some i) true 1

/-- PDF p.4, (27)–(29): endpoint value and all error-tolerance consequences. -/
def CapacityConclusion {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : ℕ → DegradedDMC X Y Z) (i : SecrecyMetric) (C : ℝ) : Prop :=
  PartialStrongConverse W i ∧
  (∀ eps : ℝ, 0 ≤ eps → eps < 1 →
    discreteOperationalCapacity (fun j => (W j).main) (fun j => (W j).eve) (some i) false eps =
      (C : EReal)) ∧
  (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
    discreteOperationalCapacity (fun j => (W j).main) (fun j => (W j).eve) (some i) true eps =
      (C : EReal))

/-- PDF p.6: rows are permutations and all column sums are equal. -/
def WeaklySymmetric {X Y : Type*} [Fintype X]
    (V : X → Y → ℝ) : Prop :=
  (∀ x x', ∃ e : Equiv.Perm Y, ∀ y, V x y = V x' (e y)) ∧
  ∀ y y', ∑ x, V x y = ∑ x, V x y'

/-- PDF p.6, (45)–(47): Cesaro averages over the first k+1 components. -/
def capacityAverage {X Y : Type*} [Fintype X] [Fintype Y]
    (V : ℕ → X → Y → ℝ) (k : ℕ) : ℝ :=
  (∑ j : Fin (k + 1), finiteChannelCapacity (V j.val)) / (k + 1 : ℝ)

/-- PDF p.6: construct a maximizing input from V itself. The zero fallback is
used only outside the nonempty finite normalized-channel domain; the maximum
exists in that domain. No comparison output distribution is supplied as data. -/
def maximizingInput {X Y : Type*} [Fintype X] [Fintype Y]
    (V : X → Y → ℝ) : X → ℝ :=
  if h : ∃ p : X → ℝ, IsLaw p ∧ ∀ q : X → ℝ, IsLaw q →
      finiteChannelInformation V q ≤ finiteChannelInformation V p then Classical.choose h else fun _ => 0

/-- PDF p.6: the capacity-achieving output law, constructed from the channel. -/
def capacityOutput {X Y : Type*} [Fintype X] [Fintype Y]
    (V : X → Y → ℝ) : Y → ℝ := inducedFiniteOutput V (maximizingInput V)

/-- PDF p.6, (46): row variance on actual row support. Unreachable outputs
have mass zero and do not contribute; all reachable output denominators are positive. -/
def rowInformationVariance {X Y : Type*} [Fintype X] [Fintype Y]
    (V : X → Y → ℝ) (x : X) : ℝ :=
  let d := fun y => if V x y = 0 then 0 else log2 (V x y / capacityOutput V y)
  let mean := ∑ y, V x y * d y
  ∑ y, V x y * (d y - mean) ^ 2

/-- PDF p.6: the usual point-to-point strong converse, in endpoint-capacity form.
The dummy singleton Eve output imposes no secrecy condition. -/
def PointStrongConverse {X Y : Type*} [Fintype X] [Fintype Y]
    (V : ℕ → X → Y → ℝ) : Prop :=
  discreteOperationalCapacity V (fun _ _ (_ : Unit) => 1) none false 0 =
    discreteOperationalCapacity V (fun _ _ (_ : Unit) => 1) none true 1

/-- PDF p.8, (66)–(69): arbitrary block input laws, with no consistency or
independence requirement across or within blocklengths. -/
def InputProcess (X : Type*) [Fintype X] :=
  (k : ℕ) → {p : (Fin (k + 1) → X) → ℝ // IsLaw p}

/-- PDF pp.5,8, (40),(68): actual joint law induced by an arbitrary block input. -/
def blockJoint {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : DegradedDMC X Y Z) (P : InputProcess X) (k : ℕ)
    (x : Fin (k + 1) → X) (y : Fin (k + 1) → Y) (z : Fin (k + 1) → Z) : ℝ :=
  (P k).val x * ∏ j, W.joint (x j) (y j) (z j)

/-- PDF p.8, (67): normalized conditional information density.
On positive actual joint support, W(z|x), P(z), P(y,z) are positive.
The value off actual support is explicitly zero and never enters probabilities. -/
def conditionalDensity {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : DegradedDMC X Y Z) (P : InputProcess X) (k : ℕ)
    (x : Fin (k + 1) → X) (y : Fin (k + 1) → Y) (z : Fin (k + 1) → Z) : ℝ :=
  let p := blockJoint W P k
  if p x y z = 0 then 0 else
    let wyz := ∏ j, W.joint (x j) (y j) (z j)
    let wz := ∏ j, W.eve (x j) (z j)
    let pyz := ∑ a, p a y z
    let pz := ∑ a, ∑ b, p a b z
    log2 ((wyz / wz) / (pyz / pz)) / (k + 1 : ℝ)

/-- PDF pp.4,8, (31),(67)–(69): the 1-p-limsup conditional information rate,
with the strict lower-tail probability condition from (31), valued in EReal. -/
def spectralConditionalSup {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : DegradedDMC X Y Z) (P : InputProcess X) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, r = (R : EReal) ∧
    ∃ delta : ℝ, 0 < delta ∧ ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
      (∑ x, ∑ y, ∑ z,
        if conditionalDensity W P k x y z ≤ R then blockJoint W P k x y z else 0)
          < 1 - delta}

/-- PDF p.3, (4), and p.6, (48): Gaussian density with positive standard
 deviation sigma in the theorem domain; Mathlib parameterizes it by variance. -/
def realGaussianDensity (sigma mu y : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal mu ⟨sigma ^ 2, sq_nonneg sigma⟩ y

/-- PDF p.6, (48): memoryless real Gaussian conditional output density. -/
def gaussianBlockDensity (sigma : ℝ) (k : ℕ)
    (x y : Fin (k + 1) → ℝ) : ℝ :=
  ∏ j, realGaussianDensity sigma (x j) (y j)

/-- PDF p.6: physical joint realization, with the source's added noise variance.
Operational quantities below use its Bob and Eve marginals, respectively N(x,sigma1^2)
and N(x,sigma2^2); they do not assume these two outputs independent given x. -/
def gaussianJointDensity (sigma1 sigma2 x y z : ℝ) : ℝ :=
  realGaussianDensity sigma1 x y * realGaussianDensity (Real.sqrt (sigma2 ^ 2 - sigma1 ^ 2)) y z

/-- PDF p.6, (49)–(50): the CLOSED block power ball. -/
def powerBall (S : ℝ) (k : ℕ) : Set (Fin (k + 1) → ℝ) :=
  {x | ∑ j, (x j) ^ 2 ≤ (k + 1 : ℝ) * S}

/-- PDF pp.3,6, Definition 2 and (49): all Borel stochastic encoders on the
power ball, including non-atomic ones, and a deterministic measurable decoder.
Uniform messages make per-message almost-sure power equivalent to (49). -/
structure PowerConstrainedGaussianCode (S : ℝ) (k : ℕ) where
  messages : ℕ
  positive : 0 < messages
  encoder : Fin messages → MeasureTheory.Measure (Fin (k + 1) → ℝ)
  encoder_probability : ∀ m, MeasureTheory.IsProbabilityMeasure (encoder m)
  encoder_power : ∀ m, encoder m (powerBall S k) = 1
  decoder : (Fin (k + 1) → ℝ) → Fin messages
  decoder_measurable : ∀ m, MeasurableSet {y | decoder y = m}

/-- PDF p.3, (14), specialized to (48): average decoding error obtained by
integrating the actual Bob density and stochastic input measure. For positive
sigma, these are integrals of measurable probability kernels, bounded by one. -/
def PowerConstrainedGaussianCode.error {S : ℝ} {k : ℕ} (c : PowerConstrainedGaussianCode S k) (sigma1 : ℝ) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    ∫ x, (∫ y, if c.decoder y = m then 0 else gaussianBlockDensity sigma1 k x y)
      ∂(c.encoder m)

/-- PDF p.3, Definition 1: the actual joint message/Eve density relative to
counting measure times Lebesgue measure. Positive Gaussian noise gives a finite,
strictly positive conditional output density for every z and every message. -/
def PowerConstrainedGaussianCode.messageEve {S : ℝ} {k : ℕ} (c : PowerConstrainedGaussianCode S k)
    (sigma2 : ℝ) (m : Fin c.messages) (z : Fin (k + 1) → ℝ) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∫ x, gaussianBlockDensity sigma2 k x z ∂(c.encoder m)

/-- PDF p.3: product of the uniform message law and the actual Eve marginal. -/
def PowerConstrainedGaussianCode.independentEve {S : ℝ} {k : ℕ} (c : PowerConstrainedGaussianCode S k)
    (sigma2 : ℝ) (_m : Fin c.messages) (z : Fin (k + 1) → ℝ) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m, c.messageEve sigma2 m z

/-- PDF p.3, (5)–(10): all six metrics for the Gaussian code's actual densities.
In the positive-noise domain q is positive and p/q <= M. The negative part of
p log(p/q) is bounded by a constant times q; its positive part by p log M.
Thus these real integrals are integrable, not Bochner defaults on bad functions. -/
def PowerConstrainedGaussianCode.leakage {S : ℝ} {k : ℕ} (c : PowerConstrainedGaussianCode S k)
    (sigma2 : ℝ) (i : SecrecyMetric) (eta : ℝ) : ℝ :=
  let p := c.messageEve sigma2
  let q := c.independentEve sigma2
  let d := ∑ m, ∫ z, p m z * log2 (p m z / q m z)
  let v := (1 / 2 : ℝ) * ∑ m, ∫ z, |p m z - q m z|
  let tail := fun (scale : ℝ) => ∑ m, ∫ z,
    if eta < log2 (p m z / q m z) / scale then p m z else 0
  match i with
  | .divergence => d
  | .variation => v
  | .tail => tail 1
  | .normalizedDivergence => d / (k + 1 : ℝ)
  | .normalizedVariation => v / (k + 1 : ℝ)
  | .normalizedTail => tail (k + 1 : ℝ)

/-- PDF pp.3–4: the ordinary and strict optimistic reliability conditions for
Gaussian code sequences, with the same epsilon endpoint conventions. -/
def GaussianReliable {S : ℝ} (c : (k : ℕ) → PowerConstrainedGaussianCode S k)
    (sigma1 : ℝ) (optimistic : Bool) (eps : ℝ) : Prop :=
  if optimistic then
    ∃ delta : ℝ, 0 < delta ∧ ∀ N : ℕ, ∃ k : ℕ,
      N ≤ k ∧ (c k).error sigma1 < eps - delta
  else ∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop, (c k).error sigma1 ≤ eps + delta

/-- PDF pp.3–4,6: operational capacities of the actual real Gaussian channel
under the almost-sure block power constraint. Rate is liminf log M/(k+1).
One code sequence works for every positive threshold eta; encoders are arbitrary
Borel probability measures on the ball, not restricted Gaussian inputs. -/
def gaussianOperationalCapacity (sigma1 sigma2 S : ℝ) (i : SecrecyMetric)
    (optimistic : Bool) (eps : ℝ) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, r = (R : EReal) ∧
    ∃ c : (k : ℕ) → PowerConstrainedGaussianCode S k,
      (∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop,
        R - delta ≤ log2 ((c k).messages : ℝ) / (k + 1 : ℝ)) ∧
      (∀ eta : ℝ, 0 < eta →
        Tendsto (fun k => (c k).leakage sigma2 i eta) atTop (nhds 0)) ∧
      GaussianReliable c sigma1 optimistic eps}

/-- PDF p.6, (51): the Gaussian secrecy capacity in bits per channel use. -/
def gaussianSecrecyCapacity (sigma1 sigma2 S : ℝ) : ℝ :=
  (1 / 2 : ℝ) * log2 (1 + S / sigma1 ^ 2) -
    (1 / 2 : ℝ) * log2 (1 + S / sigma2 ^ 2)

/-- The power constraint includes the zero vector; it is an inequality, not a sphere. -/
example (S : ℝ) (hS : 0 ≤ S) (k : ℕ) :
    (fun _ : Fin (k + 1) => (0 : ℝ)) ∈ powerBall S k := by
  change (∑ _j : Fin (k + 1), (0 : ℝ) ^ 2) ≤ (k + 1 : ℝ) * S
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
  positivity

/-- The scalar noise density has mass one for every positive standard deviation. -/
example (sigma : ℝ) (hsigma : 0 < sigma) :
    (∫ y, realGaussianDensity sigma 0 y) = 1 := by
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  have hv : (0 : NNReal) < ⟨sigma ^ 2, sq_nonneg sigma⟩ := by
    exact_mod_cast sq_pos_of_pos hsigma
  exact ne_of_gt hv

/-- Normalization and base convention sanity check. -/
example : IsLaw (fun _ : Unit => (1 : ℝ)) ∧ log2 1 = 0 := by
  simp [IsLaw, log2]

/-- The singleton input/output channel carries zero mutual information. -/
example : finiteChannelInformation (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) (fun _ => 1) = 0 := by
  simp [finiteChannelInformation, QAlgorithms.mutualInfoBits]

/-- Positive block indexing: the first block contains exactly one channel use. -/
example {X Y : Type*} (V : ℕ → X → Y → ℝ) (x : Fin 1 → X) (y : Fin 1 → Y) :
    independentBlockKernel V 0 x y = V 0 (x 0) (y 0) := by
  simp [independentBlockKernel]

end QAlgorithms.Papers.Independent.Bridge50.P42


