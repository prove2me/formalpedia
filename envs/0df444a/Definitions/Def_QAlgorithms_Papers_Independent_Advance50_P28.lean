-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28
-- name    : QAlgorithms_Papers_Independent_Advance50_P28
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:44:04.999765+00:00
-- url     : https://prove2.me/theorems/f80ac793-8a5d-4bc9-96b9-f6b4a8a12a1b
-- title:
--   Definitions for Tight exponential analysis of universally composable privacy amplification and its applications
-- statement:
--   The objects the formalized statements of *Tight exponential analysis of universally composable privacy amplification and its applications* (arXiv:1010.1358) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsSubLaw`: PDF p.3: finite subprobability vectors, including the zero vector.
--   - `l1`: PDF p.3, (1): full L1 distance.
--   - `finiteVectorMass`: PDF p.3, (7): the finiteVectorMass of a finite vector.
--   - `hashFiberMass`: PDF p.3: hash pushforward, summing the whole fiber.
--   - `extractionError`: PDF p.3, (7): deviation from the finiteVectorMass-scaled uniform output.
--   - `HashEnsemble`: PDF pp.3–4: the distribution of the random hash itself. Any seed induces this finite distribution; choosing it before the source keeps the seed independent.
--   - `Universal2`: PDF p.3, Condition 1: only the collision constraint is imposed.
--   - `StronglyUniversal2`: PDF p.4, Condition 3: a uniform hash value independent of the ENTIRE tuple of all other hash values, expressed by its joint cylinders.
--   - `expectedError`: PDF p.3, (9): expected full L1 error with independent public seed.
--   - `renyiPowerSum`: PDF p.3: the Renyi renyiPowerSum of order 1+s; it also handles zero subdistributions.
--   - `renyiNumerator`: PDF pp.3–4: s H_(1+s); its continuous endpoint at s=0 is zero for a law.
--   - `peak`: PDF p.6: largest atom; on finite nonempty alphabets this supremum is attained.
--   - `directExponent`: PDF p.4, (18): direct universal2 exponent. The objective is continuous on [0,1].
--   - `intrinsicExponent`: PDF p.9, (58): specialized direct exponent; denominator 1+s is absent.
--   - `smoothExponent`: PDF p.7, (35)–(37): s is unbounded; a supremum need not have a finite optimizer.
--   - `compactSmoothObjective`: PDF p.7, (36)–(37): compactified objective. At t=1 use H_infinity, at t=0 use 0.
--   - `iid`: PDF p.4 onward: product law on n independently sampled letters.
--   - `negativeLogRate`: PDF pp.4,7,9: extended negative logarithmic rate, used at positive blocklengths. The n=0 convention is irrelevant to every limit at infinity.
--   - `smoothingBenchmark`: PDF p.7, (37): minimization over all subdistributions, including zero.
--   - `intrinsicExtractionError`: PDF p.7: all extractors to floor(exp(nR)) outputs, no optimization surrogate.
--   - `counts`: PDF p.5: a type is the empirical count vector of an actual word.
--   - `types`: PDF pp.5,8: all realized n-types, with no artificial impossible count vectors.
--   - `typeAtom`: PDF p.5, (22): the common probability of each word of a type, directly as a product, so zero-support types have probability zero without log(0).
--   - `typeMass`: PDF p.5, (23): actual finiteVectorMass of a type class.
--   - `firstTypes`: PDF p.8, T_n^1[M]: equivalent to D+H >= log M/n at n>0, including infinite cross-entropy when a positive count falls outside the support of P.
--   - `secondTypes`: PDF p.8, T_n^2[M]: this set need not be disjoint from T_n^1[M].
--   - `rareTypePeak`: PDF p.8, (48): empty maximum of nonnegative atom probabilities is zero.
--   - `IsConditionalLaw`: PDF p.10: a measurable normalized conditional probability vector. Values on null fibers may be any probability vector; the definitions integrate them out.
--   - `conditionalLeakage`: PDF p.10: full conditional L1 leakage against the uniform key and actual Eve marginal.
--   - `expectedConditionalLeakage`: PDF p.10, (66): seed expectation; the seed is independent of (A,E).
--   - `publicSeedLeakage`: PDF p.10, (66): actual joint (key,E,public seed) distance; the factors inside absolute values are the joint conditional densities relative to mu and counting.
--   - `conditionalPhi`: PDF p.10: conditional phi; finite A bounds this integrand away from zero and infinity for t<1, so no nonintegrable Bochner default is used on the stated domain.
--   - `conditionalRenyiNumerator`: PDF p.11: s times the source's (unoptimized) conditional Renyi entropy.
--   - `integratedFiberEntropyNats`: PDF p.11: conditional Shannon entropy, natural logarithms; zero letters contribute 0.
--   - `fiberRenyi`: PDF p.11: fiber Renyi entropy, on the s>0 domain of Lemma 7.
--   - `conditionalPhiExponent`: PDF p.11: the new conditional source exponent.
--   - `conditionalHExponent`: PDF p.11: the conditional entropy comparison exponent e_H.
--   - `conditionalTildeExponent`: PDF p.11: the older comparison exponent e_tildeH, with denominator 2.
--   - `conditionalIid`: PDF p.11: actual iid conditional vector, with the product Eve marginal.
--   - `IsENNRealDiscreteLaw`: PDF p.12: a probability law on a countable discrete input alphabet. Nonnegative infinite sums never use the default of a nonsummable real tsum.
--   - `IsDensityChannel`: PDF p.12: classical stochastic channel densities relative to a common output measure. Their nonnegative integral is one; continuous and discrete outputs are allowed.
--   - `classicalOutputDensity`: PDF p.13, (76): actual channel mixture, including countably many inputs.
--   - `gallagerDensityMoment`: PDF p.12: exp(phi), represented before the logarithm. This may be infinite for a countable input at positive t, and is NOT converted to a real integral.
--   - `psiMoment`: PDF p.13, (76): exp(psi); outputs of zero mixture finiteVectorMass contribute zero before any negative power is evaluated.
--   - `wiretapPhiExponent`: PDF p.13: secrecy exponent defined with extended logarithms so an infinite channel renyiPowerSum gives minus infinity, rather than Real.log of a default value.
--   - `wiretapPsiExponent`: PDF p.14, (77): comparison exponent e_psi, with denominator 1+s.
--   - `wiretapTildeExponent`: PDF p.14, (79): Pinsker comparison exponent with denominator 2.
--   - `WiretapCode`: PDF p.12: stochastic encoder distributions and disjoint measurable decoding sets. Uniform messages are included in every performance definition below.
--   - `wiretapDecodingError`: PDF p.12: average Bob error for this actual stochastic code.
--   - `codeEveAverage`: PDF p.12: the actual average Eve output of a uniform message.
--   - `codeLeakage`: PDF p.12: full L1 message–Eve dependence relative to the ACTUAL Eve marginal, not to an independently supplied comparison state. Probability densities are finite a.e.
--   - `blockDensity`: PDF p.13: product channel densities, with no product restriction on code encoders.
--   - `discreteIid`: PDF p.13: only the random-coding input law is tensorized.
--   - `negativeLogRateENN`: PDF p.13: normalized negative log of an actual nonnegative error.
--   - `classicalMutualInformationNats`: PDF p.13: mutual information in nats, via the nonnegative KL generator u log u-u+1. This equals D(p(x)W_x(y) || p(x)W_p(y)); no signed nonintegrable integral or infinity-minus-infinity is used.
--   - `finiteUniformMass`: PDF p.15: uniform law on a finite nonempty alphabet.
--   - `additiveDensity`: PDF pp.14–15: the actual additive noise channel, with z-x in this order.
--   - `generalAdditiveDensity`: PDF p.15, (82): general additive channel, relative to counting on G times the actual marginal measure of side noise E. This includes continuous side noise.
--   - `subgroupUniform`: PDF p.15: uniform law on C1, as a law on the ambient input alphabet.
--   - `SubcodeCondition`: PDF p.15, Condition 4: fixed size L and the paper's L/|C1| collision bound. C1 and W are chosen independently of the seed.
--   - `cosetOutput`: PDF p.15: the actual uniform-coset output for representative x.
--   - `cosetLeakage`: PDF p.15: full L1 coset-key leakage. Averaging representatives with 1/|C1| counts each coset L times and is exactly uniform averaging over |C1|/L keys.
--   - `expectedCosetLeakage`: PDF p.15: averaged leakage includes the public seed as side information.
--   - `CompatibleMarginals`: PDF p.16, (95): two compatible source marginals; all Bob and Eve metrics, including the public mask, depend only on these marginals. Compatibility is exactly that they have the same A-law, and permits gluing them to a joint source.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, https://arxiv.org/abs/1010.1358v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-! Hayashi, arXiv:1010.1358v5. Natural logarithms and FULL L1 distance.
All new models are paper-local. Exact zero errors have infinite exponents.
Compilation is pending the explicitly requested batch handoff. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

-- Exact frozen finite-law predicate; its full body matches PDF p.3.
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: finite subprobability vectors, including the zero vector. -/
def IsSubLaw {A : Type*} [Fintype A] (P : A → ℝ) : Prop :=
  (∀ a, 0 ≤ P a) ∧ ∑ a, P a ≤ 1

/-- PDF p.3, (1): full L1 distance. -/
def l1 {A : Type*} [Fintype A] (P Q : A → ℝ) : ℝ :=
  ∑ a, |P a - Q a|

/-- PDF p.3, (7): the finiteVectorMass of a finite vector. -/
def finiteVectorMass {A : Type*} [Fintype A] (P : A → ℝ) : ℝ := ∑ a, P a

/-- PDF p.3: hash pushforward, summing the whole fiber. -/
def hashFiberMass {A : Type*} [Fintype A] {M : ℕ}
    (P : A → ℝ) (f : A → Fin M) (b : Fin M) : ℝ :=
  ∑ a, if f a = b then P a else 0

/-- PDF p.3, (7): deviation from the finiteVectorMass-scaled uniform output. -/
def extractionError {A : Type*} [Fintype A] {M : ℕ}
    (P : A → ℝ) (f : A → Fin M) : ℝ :=
  ∑ b, |hashFiberMass P f b - finiteVectorMass P / (M : ℝ)|

/-- PDF pp.3–4: the distribution of the random hash itself. Any seed induces this
finite distribution; choosing it before the source keeps the seed independent. -/
structure HashEnsemble (A : Type*) [Fintype A] (M : ℕ) where
  weight : (A → Fin M) → ℝ
  nonnegative : ∀ f, 0 ≤ weight f
  normalized : ∑ f, weight f = 1

/-- PDF p.3, Condition 1: only the collision constraint is imposed. -/
def Universal2 {A : Type*} [Fintype A] {M : ℕ}
    (h : HashEnsemble A M) : Prop :=
  ∀ a a', a ≠ a' →
    (∑ f, if f a = f a' then h.weight f else 0) ≤ 1 / (M : ℝ)

/-- PDF p.4, Condition 3: a uniform hash value independent of the ENTIRE tuple
of all other hash values, expressed by its joint cylinders. -/
def StronglyUniversal2 {A : Type*} [Fintype A] {M : ℕ}
    (h : HashEnsemble A M) : Prop :=
  (∀ a b, (∑ f, if f a = b then h.weight f else 0) = 1 / (M : ℝ)) ∧
  ∀ a b (g : A → Fin M),
    (∑ f, if f a = b ∧ (∀ a', a' ≠ a → f a' = g a') then h.weight f else 0) =
      (1 / (M : ℝ)) *
        ∑ f, if (∀ a', a' ≠ a → f a' = g a') then h.weight f else 0

/-- PDF p.3, (9): expected full L1 error with independent public seed. -/
def expectedError {A : Type*} [Fintype A] {M : ℕ}
    (h : HashEnsemble A M) (P : A → ℝ) : ℝ :=
  ∑ f, h.weight f * extractionError P f

/-- PDF p.3: the Renyi renyiPowerSum of order 1+s; it also handles zero subdistributions. -/
def renyiPowerSum {A : Type*} [Fintype A] (P : A → ℝ) (s : ℝ) : ℝ :=
  ∑ a, (P a) ^ (1 + s)

/-- PDF pp.3–4: s H_(1+s); its continuous endpoint at s=0 is zero for a law. -/
def renyiNumerator {A : Type*} [Fintype A] (P : A → ℝ) (s : ℝ) : ℝ :=
  if s = 0 then 0 else -Real.log (renyiPowerSum P s)

/-- PDF p.6: largest atom; on finite nonempty alphabets this supremum is attained. -/
def peak {A : Type*} [Fintype A] (P : A → ℝ) : ℝ := sSup (Set.range P)

/-- PDF p.4, (18): direct universal2 exponent. The objective is continuous on [0,1]. -/
def directExponent {A : Type*} [Fintype A] (P : A → ℝ) (R : ℝ) : ℝ :=
  sSup ((fun s : ℝ => (renyiNumerator P s - s * R) / (1 + s)) '' Set.Icc 0 1)

/-- PDF p.9, (58): specialized direct exponent; denominator 1+s is absent. -/
def intrinsicExponent {A : Type*} [Fintype A] (P : A → ℝ) (R : ℝ) : ℝ :=
  sSup ((fun s : ℝ => renyiNumerator P s - s * R) '' Set.Icc 0 1)

/-- PDF p.7, (35)–(37): s is unbounded; a supremum need not have a finite optimizer. -/
def smoothExponent {A : Type*} [Fintype A] (P : A → ℝ) (R : ℝ) : ℝ :=
  sSup ((fun s : ℝ => (renyiNumerator P s - s * R) / (1 + 2 * s)) '' Set.Ici 0)

/-- PDF p.7, (36)–(37): compactified objective. At t=1 use H_infinity, at t=0 use 0. -/
def compactSmoothObjective {A : Type*} [Fintype A]
    (P : A → ℝ) (R t : ℝ) : ℝ :=
  if t = 0 then 0 else if t = 1 then (-Real.log (peak P) - R) / 2
  else ((1 - t) * renyiNumerator P (t / (1 - t)) - t * R) / (1 + t)

/-- PDF p.4 onward: product law on n independently sampled letters. -/
def iid {A : Type*} (P : A → ℝ) (n : ℕ) (x : Fin n → A) : ℝ :=
  ∏ i, P (x i)

/-- PDF pp.4,7,9: extended negative logarithmic rate, used at positive blocklengths.
The n=0 convention is irrelevant to every limit at infinity. -/
def negativeLogRate (error : ℝ) (n : ℕ) : EReal :=
  if error = 0 then ⊤ else ((-Real.log error / (n : ℝ) : ℝ) : EReal)

/-- PDF p.7, (37): minimization over all subdistributions, including zero. -/
def smoothingBenchmark {A : Type*} [Fintype A]
    (P : A → ℝ) (R : ℝ) (n : ℕ) : ℝ :=
  sInf {v | ∃ Q : (Fin n → A) → ℝ, IsSubLaw Q ∧
    v = Real.exp ((n : ℝ) * R / 2) * Real.sqrt (peak Q) + 2 * l1 (iid P n) Q}

/-- PDF p.7: all extractors to floor(exp(nR)) outputs, no optimization surrogate. -/
def intrinsicExtractionError {A : Type*} [Fintype A]
    (P : A → ℝ) (R : ℝ) (n : ℕ) : ℝ :=
  sInf (Set.range (fun f : (Fin n → A) → Fin (Nat.floor (Real.exp ((n : ℝ) * R))) =>
    extractionError (iid P n) f))

/-- PDF p.5: a type is the empirical count vector of an actual word. -/
def counts {A : Type*} [DecidableEq A] {n : ℕ} (x : Fin n → A) (a : A) : ℕ :=
  (Finset.univ.filter (fun i => x i = a)).card

/-- PDF pp.5,8: all realized n-types, with no artificial impossible count vectors. -/
def types (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) : Finset (A → ℕ) :=
  Finset.univ.image (fun x : Fin n → A => counts x)

/-- PDF p.5, (22): the common probability of each word of a type, directly as a
product, so zero-support types have probability zero without log(0). -/
def typeAtom {A : Type*} [Fintype A] (P : A → ℝ) (q : A → ℕ) : ℝ :=
  ∏ a, P a ^ (q a)

/-- PDF p.5, (23): actual finiteVectorMass of a type class. -/
def typeMass {A : Type*} [Fintype A] [DecidableEq A]
    (P : A → ℝ) (n : ℕ) (q : A → ℕ) : ℝ :=
  ∑ x : Fin n → A, if counts x = q then iid P n x else 0

/-- PDF p.8, T_n^1[M]: equivalent to D+H >= log M/n at n>0, including
infinite cross-entropy when a positive count falls outside the support of P. -/
def firstTypes {A : Type*} [Fintype A] [DecidableEq A]
    (P : A → ℝ) (n M : ℕ) : Finset (A → ℕ) :=
  (types A n).filter (fun q => typeAtom P q ≤ 1 / (M : ℝ))

/-- PDF p.8, T_n^2[M]: this set need not be disjoint from T_n^1[M]. -/
def secondTypes {A : Type*} [Fintype A] [DecidableEq A]
    (P : A → ℝ) (n M : ℕ) : Finset (A → ℕ) :=
  (types A n).filter (fun q => typeMass P n q < 1 / (M : ℝ))

/-- PDF p.8, (48): empty maximum of nonnegative atom probabilities is zero. -/
def rareTypePeak {A : Type*} [Fintype A] [DecidableEq A]
    (P : A → ℝ) (n M : ℕ) : ℝ :=
  sSup (insert 0 ((fun q => typeAtom P q) '' (↑(secondTypes P n M) : Set (A → ℕ))))

/-- Sanity: the empty-word product is one. -/
example {A : Type*} (P : A → ℝ) (x : Fin 0 → A) : iid P 0 x = 1 := by
  simp [iid]

/-- Sanity: exact extraction has infinite exponent even at positive n. -/
example (n : ℕ) : negativeLogRate 0 n = ⊤ := by simp [negativeLogRate]

/-- Sanity: finiteVectorMass is the unweighted sum, including for a subdistribution. -/
example {A : Type*} [Fintype A] (P : A → ℝ) : finiteVectorMass P = ∑ a, P a := rfl

/-- PDF p.10: a measurable normalized conditional probability vector. Values on
null fibers may be any probability vector; the definitions integrate them out. -/
def IsConditionalLaw {A E : Type*} [Fintype A] [MeasurableSpace E]
    (p : E → A → ℝ) : Prop :=
  (∀ e, IsLaw (p e)) ∧ ∀ a, Measurable (fun e => p e a)

/-- PDF p.10: full conditional L1 leakage against the uniform key and actual Eve marginal. -/
def conditionalLeakage {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) {M : ℕ} (f : A → Fin M) : ℝ :=
  ∫ e, extractionError (p e) f ∂mu

/-- PDF p.10, (66): seed expectation; the seed is independent of (A,E). -/
def expectedConditionalLeakage {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) {M : ℕ} (h : HashEnsemble A M) : ℝ :=
  ∑ f, h.weight f * conditionalLeakage mu p f

/-- PDF p.10, (66): actual joint (key,E,public seed) distance; the factors inside
absolute values are the joint conditional densities relative to mu and counting. -/
def publicSeedLeakage {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) {M : ℕ} (h : HashEnsemble A M) : ℝ :=
  ∫ e, ∑ f, ∑ b : Fin M,
    |h.weight f * hashFiberMass (p e) f b - h.weight f / (M : ℝ)| ∂mu

/-- PDF p.10: conditional phi; finite A bounds this integrand away from zero and infinity
for t<1, so no nonintegrable Bochner default is used on the stated domain. -/
def conditionalPhi {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) (t : ℝ) : ℝ :=
  Real.log (∫ e, (∑ a, (p e a) ^ (1 / (1 - t))) ^ (1 - t) ∂mu)

/-- PDF p.11: s times the source's (unoptimized) conditional Renyi entropy. -/
def conditionalRenyiNumerator {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) (s : ℝ) : ℝ :=
  if s = 0 then 0 else -Real.log (∫ e, renyiPowerSum (p e) s ∂mu)

/-- PDF p.11: conditional Shannon entropy, natural logarithms; zero letters contribute 0. -/
def integratedFiberEntropyNats {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) : ℝ :=
  ∫ e, -(∑ a, p e a * Real.log (p e a)) ∂mu

/-- PDF p.11: fiber Renyi entropy, on the s>0 domain of Lemma 7. -/
def fiberRenyi {A : Type*} [Fintype A] (P : A → ℝ) (s : ℝ) : ℝ :=
  -Real.log (renyiPowerSum P s) / s

/-- PDF p.11: the new conditional source exponent. -/
def conditionalPhiExponent {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) (R : ℝ) : ℝ :=
  sSup ((fun t : ℝ => -conditionalPhi mu p t - t * R) '' Set.Icc 0 (1 / 2))

/-- PDF p.11: the conditional entropy comparison exponent e_H. -/
def conditionalHExponent {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) (R : ℝ) : ℝ :=
  sSup ((fun s : ℝ => (conditionalRenyiNumerator mu p s - s * R) / (1 + s)) '' Set.Icc 0 1)

/-- PDF p.11: the older comparison exponent e_tildeH, with denominator 2. -/
def conditionalTildeExponent {A E : Type*} [Fintype A] [MeasurableSpace E]
    (mu : Measure E) (p : E → A → ℝ) (R : ℝ) : ℝ :=
  sSup ((fun s : ℝ => (conditionalRenyiNumerator mu p s - s * R) / 2) '' Set.Icc 0 1)

/-- PDF p.11: actual iid conditional vector, with the product Eve marginal. -/
def conditionalIid {A E : Type*} (p : E → A → ℝ) (n : ℕ)
    (es : Fin n → E) (x : Fin n → A) : ℝ := ∏ i, p (es i) (x i)

/-- Sanity: tensoring zero copies has one empty-word atom. -/
example {A E : Type*} (p : E → A → ℝ) (es : Fin 0 → E) (x : Fin 0 → A) :
    conditionalIid p 0 es x = 1 := by simp [conditionalIid]

/-- PDF p.12: a probability law on a countable discrete input alphabet.
Nonnegative infinite sums never use the default of a nonsummable real tsum. -/
def IsENNRealDiscreteLaw {X : Type*} (p : X → ℝ≥0∞) : Prop := (∑' x, p x) = 1

/-- PDF p.12: classical stochastic channel densities relative to a common output
measure. Their nonnegative integral is one; continuous and discrete outputs are allowed. -/
def IsDensityChannel {X Y : Type*} [MeasurableSpace Y]
    (mu : Measure Y) (W : X → Y → ℝ≥0∞) : Prop :=
  ∀ x, Measurable (W x) ∧ (∫⁻ y, W x y ∂mu) = 1

/-- PDF p.13, (76): actual channel mixture, including countably many inputs. -/
def classicalOutputDensity {X Y : Type*} (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞)
    (y : Y) : ℝ≥0∞ := ∑' x, p x * W x y

/-- PDF p.12: exp(phi), represented before the logarithm. This may be infinite
for a countable input at positive t, and is NOT converted to a real integral. -/
def gallagerDensityMoment {X Y : Type*} [MeasurableSpace Y] (mu : Measure Y)
    (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, (∑' x, p x * (W x y) ^ (1 / (1 - t))) ^ (1 - t) ∂mu

/-- PDF p.13, (76): exp(psi); outputs of zero mixture finiteVectorMass contribute zero before
any negative power is evaluated. -/
def psiMoment {X Y : Type*} [MeasurableSpace Y] (mu : Measure Y)
    (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, if classicalOutputDensity W p y = 0 then 0 else
    (∑' x, p x * (W x y) ^ (1 + s)) * (classicalOutputDensity W p y) ^ (-s) ∂mu

/-- PDF p.13: secrecy exponent defined with extended logarithms so an infinite
channel renyiPowerSum gives minus infinity, rather than Real.log of a default value. -/
def wiretapPhiExponent {X Y : Type*} [MeasurableSpace Y] (mu : Measure Y)
    (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (R : ℝ) : EReal :=
  sSup ((fun t : ℝ => (t * R : ℝ) - ENNReal.log (gallagerDensityMoment mu W p t)) ''
    Set.Icc 0 (1 / 2))

/-- PDF p.14, (77): comparison exponent e_psi, with denominator 1+s. -/
def wiretapPsiExponent {X Y : Type*} [MeasurableSpace Y] (mu : Measure Y)
    (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (R : ℝ) : EReal :=
  sSup ((fun s : ℝ => ((s * R : ℝ) - ENNReal.log (psiMoment mu W p s)) /
    ((1 + s : ℝ) : EReal)) '' Set.Icc 0 1)

/-- PDF p.14, (79): Pinsker comparison exponent with denominator 2. -/
def wiretapTildeExponent {X Y : Type*} [MeasurableSpace Y] (mu : Measure Y)
    (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) (R : ℝ) : EReal :=
  sSup ((fun s : ℝ => ((s * R : ℝ) - ENNReal.log (psiMoment mu W p s)) /
    (2 : EReal)) '' Set.Icc 0 1)

/-- PDF p.12: stochastic encoder distributions and disjoint measurable decoding
sets. Uniform messages are included in every performance definition below. -/
structure WiretapCode (X Y : Type*) [MeasurableSpace Y] (M : ℕ) where
  encoder : Fin M → X → ℝ≥0∞
  encoderLaw : ∀ i, IsENNRealDiscreteLaw (encoder i)
  decoding : Fin M → Set Y
  decodingMeasurable : ∀ i, MeasurableSet (decoding i)
  decodingDisjoint : Pairwise (fun i j => Disjoint (decoding i) (decoding j))

/-- PDF p.12: average Bob error for this actual stochastic code. -/
def wiretapDecodingError {X Y : Type*} [MeasurableSpace Y] {M : ℕ}
    (mu : Measure Y) (W : X → Y → ℝ≥0∞) (C : WiretapCode X Y M) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ y,
    if y ∈ C.decoding i then 0 else classicalOutputDensity W (C.encoder i) y ∂mu

/-- PDF p.12: the actual average Eve output of a uniform message. -/
def codeEveAverage {X Y E : Type*} [MeasurableSpace Y] {M : ℕ}
    (W : X → E → ℝ≥0∞) (C : WiretapCode X Y M) (e : E) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ i, classicalOutputDensity W (C.encoder i) e

/-- PDF p.12: full L1 message–Eve dependence relative to the ACTUAL Eve marginal,
not to an independently supplied comparison state. Probability densities are finite a.e. -/
def codeLeakage {X Y E : Type*} [MeasurableSpace Y] [MeasurableSpace E] {M : ℕ}
    (mu : Measure E) (W : X → E → ℝ≥0∞) (C : WiretapCode X Y M) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ e,
    ((classicalOutputDensity W (C.encoder i) e - codeEveAverage W C e) +
      (codeEveAverage W C e - classicalOutputDensity W (C.encoder i) e)) ∂mu

/-- PDF p.13: product channel densities, with no product restriction on code encoders. -/
def blockDensity {X Y : Type*} (W : X → Y → ℝ≥0∞) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) : ℝ≥0∞ := ∏ i, W (x i) (y i)

/-- PDF p.13: only the random-coding input law is tensorized. -/
def discreteIid {X : Type*} (p : X → ℝ≥0∞) (n : ℕ) (x : Fin n → X) : ℝ≥0∞ :=
  ∏ i, p (x i)

/-- PDF p.13: normalized negative log of an actual nonnegative error. -/
def negativeLogRateENN (error : ℝ≥0∞) (n : ℕ) : EReal :=
  -ENNReal.log error / (n : EReal)

/-- PDF p.13: mutual information in nats, via the nonnegative KL generator
u log u-u+1. This equals D(p(x)W_x(y) || p(x)W_p(y)); no signed
nonintegrable integral or infinity-minus-infinity is used. -/
def classicalMutualInformationNats {X Y : Type*} [MeasurableSpace Y] (mu : Measure Y)
    (W : X → Y → ℝ≥0∞) (p : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, p x * ∫⁻ y,
    let q := classicalOutputDensity W p y
    let u := (W x y / q).toReal
    q * ENNReal.ofReal (u * Real.log u - u + 1) ∂mu

/-- Sanity: tensoring one channel use does not mix different channel inputs. -/
example {X Y : Type*} (W : X → Y → ℝ≥0∞) (x : Fin 1 → X) (y : Fin 1 → Y) :
    blockDensity W 1 x y = W (x 0) (y 0) := by simp [blockDensity]

/-- PDF p.15: uniform law on a finite nonempty alphabet. -/
def finiteUniformMass (X : Type*) [Fintype X] : X → ℝ≥0∞ :=
  fun _ => (Fintype.card X : ℝ≥0∞)⁻¹

/-- PDF pp.14–15: the actual additive noise channel, with z-x in this order. -/
def additiveDensity {G : Type*} [AddGroup G] (P : G → ℝ) (x z : G) : ℝ≥0∞ :=
  ENNReal.ofReal (P (z - x))

/-- PDF p.15, (82): general additive channel, relative to counting on G times the
actual marginal measure of side noise E. This includes continuous side noise. -/
def generalAdditiveDensity {G E : Type*} [AddGroup G]
    (p : E → G → ℝ) (x : G) (ze : G × E) : ℝ≥0∞ :=
  ENNReal.ofReal (p ze.2 (ze.1 - x))

/-- PDF p.15: uniform law on C1, as a law on the ambient input alphabet. -/
def subgroupUniform {G : Type*} [AddGroup G] [Fintype G]
    (C1 : AddSubgroup G) (x : G) : ℝ≥0∞ :=
  if x ∈ C1 then (Fintype.card C1 : ℝ≥0∞)⁻¹ else 0

/-- PDF p.15, Condition 4: fixed size L and the paper's L/|C1| collision bound.
C1 and W are chosen independently of the seed. -/
def SubcodeCondition {G S : Type*} [AddCommGroup G] [Fintype G] [Fintype S]
    (C1 : AddSubgroup G) (H : S → AddSubgroup C1) (w : S → ℝ) (L : ℕ) : Prop :=
  IsLaw w ∧ (∀ seed, Fintype.card (H seed) = L) ∧
    ∀ x : C1, x ≠ 0 → (∑ seed, if x ∈ H seed then w seed else 0) ≤
      (L : ℝ) / (Fintype.card C1 : ℝ)

/-- PDF p.15: the actual uniform-coset output for representative x. -/
def cosetOutput {G E : Type*} [AddCommGroup G] [Fintype G]
    (W : G → E → ℝ≥0∞) (C1 : AddSubgroup G) (H : AddSubgroup C1)
    (x : C1) (e : E) : ℝ≥0∞ :=
  (Fintype.card H : ℝ≥0∞)⁻¹ * ∑ h : H, W ((x + h.1 : C1) : G) e

/-- PDF p.15: full L1 coset-key leakage. Averaging representatives with 1/|C1|
counts each coset L times and is exactly uniform averaging over |C1|/L keys. -/
def cosetLeakage {G E : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace E]
    (mu : Measure E) (W : G → E → ℝ≥0∞) (C1 : AddSubgroup G)
    (H : AddSubgroup C1) : ℝ≥0∞ :=
  (Fintype.card C1 : ℝ≥0∞)⁻¹ * ∑ x : C1, ∫⁻ e,
    ((cosetOutput W C1 H x e - classicalOutputDensity W (subgroupUniform C1) e) +
      (classicalOutputDensity W (subgroupUniform C1) e - cosetOutput W C1 H x e)) ∂mu

/-- PDF p.15: averaged leakage includes the public seed as side information. -/
def expectedCosetLeakage {G E S : Type*} [AddCommGroup G] [Fintype G]
    [Fintype S] [MeasurableSpace E] (mu : Measure E) (W : G → E → ℝ≥0∞)
    (C1 : AddSubgroup G) (H : S → AddSubgroup C1) (w : S → ℝ) : ℝ≥0∞ :=
  ∑ seed, ENNReal.ofReal (w seed) * cosetLeakage mu W C1 (H seed)

/-- Sanity: the additive channel uses noise at zero when input equals output. -/
example {G : Type*} [AddGroup G] (P : G → ℝ) (x : G) :
    additiveDensity P x x = ENNReal.ofReal (P 0) := by simp [additiveDensity]

/-- PDF p.16, (95): two compatible source marginals; all Bob and Eve metrics,
including the public mask, depend only on these marginals. Compatibility is exactly
that they have the same A-law, and permits gluing them to a joint source. -/
def CompatibleMarginals {A B E : Type*} [Fintype A]
    [MeasurableSpace B] [MeasurableSpace E]
    (muB : Measure B) (pB : B → A → ℝ) (muE : Measure E) (pE : E → A → ℝ) : Prop :=
  IsConditionalLaw pB ∧ IsConditionalLaw pE ∧
    ∀ a, (∫ b, pB b a ∂muB) = ∫ e, pE e a ∂muE

/-- Sanity: zero subdistributions have zero finiteVectorMass-scaled uniformity error. -/
example {A : Type*} [Fintype A] {M : ℕ} (f : A → Fin M) :
    extractionError (fun _ : A => 0) f = 0 := by
  simp [extractionError, hashFiberMass, finiteVectorMass]

/-- Sanity: full L1 distance vanishes at identical vectors. -/
example {A : Type*} [Fintype A] (P : A → ℝ) : l1 P P = 0 := by simp [l1]

/-- Sanity: a singleton discrete input has its full probability finiteVectorMass at its one letter. -/
example : IsENNRealDiscreteLaw (fun _ : Unit => (1 : ℝ≥0∞)) := by simp [IsENNRealDiscreteLaw]

/-- Sanity: a zero count contributes a factor one, even on a zero-probability letter. -/
example {A : Type*} [Fintype A] (P : A → ℝ) : typeAtom P (fun _ => 0) = 1 := by
  simp [typeAtom]

/-- Sanity: trivial side information and a deterministic source give phi(0)=0. -/
example : conditionalPhi (Measure.dirac ()) (fun _ : Unit => fun _ : Unit => (1 : ℝ)) 0 = 0 := by
  simp [conditionalPhi]

/-- Sanity: the one-point classical channel has renyiPowerSum one at t=0. -/
example : gallagerDensityMoment (Measure.dirac ()) (fun _ : Unit => fun _ : Unit => (1 : ℝ≥0∞))
    (fun _ : Unit => (1 : ℝ≥0∞)) 0 = 1 := by
  simp [gallagerDensityMoment]

/-- Sanity: a one-message code has no message--Eve dependence. -/
example {X Y E : Type*} [MeasurableSpace Y] [MeasurableSpace E]
    (mu : Measure E) (W : X → E → ℝ≥0∞) (C : WiretapCode X Y 1) :
    codeLeakage mu W C = 0 := by
  simp [codeLeakage, codeEveAverage]

end QAlgorithms.Papers.Independent.Advance50.P28


