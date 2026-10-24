-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38
-- name    : QAlgorithms_Papers_Independent_Support50_P38
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:54:50.157985+00:00
-- url     : https://prove2.me/theorems/6d4a3e62-ebaa-4240-87d2-3f7fa3c5ab61
-- title:
--   Definitions for Compression of sources of probability distributions and density operators
-- statement:
--   The objects the formalized statements of *Compression of sources of probability distributions and density operators* (arXiv:quant-ph/0208131) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SourceWord`: PDF p.1: a length-n word, with the original letter order retained.
--   - `wordMass`: PDF pp.1–2: the memoryless product probability.
--   - `wordChannel`: PDF p.1: the memoryless conditional output distribution.
--   - `sourceOutputMarginal`: PDF p.3: the output marginal PW.
--   - `sourceConditionalEntropyBits`: PDF p.3: conditional entropy H(W|P), in bits.
--   - `sourceInformationBits`: PDF p.3: I(P;W) = H(PW) - H(W|P).
--   - `tv`: PDF p.1, (4): total variation is half the full l1 distance.
--   - `DistributionCompressionCode`: PDF p.1, (3): visible code, finite nonempty message alphabet, stochastic encoder and stochastic decoder. Their private randomness is independent: composition multiplies kernels.
--   - `DistributionCompressionCode.output`: PDF p.1: the composed output distribution of an ordinary code.
--   - `sourceAverageBlockError`: PDF p.1, (4): P^n-average block total variation, not empirical distortion.
--   - `minimumSize`: PDF p.1: M(n,lambda) is the minimum alphabet cardinality. Exact sending of the label makes this set nonempty for lambda >= 0. Theorems only use that domain.
--   - `sizeRate`: PDF p.3: the positive-blocklength normalized communication cost. Using n+1 gives exactly the same asymptotic limits while excluding division by zero.
--   - `occurrences`: PDF p.3, (8): number of occurrences of a letter in a word.
--   - `VarianceTypicalWord`: PDF p.3, (8): variance-normalized typical words, including zero-probability letters.
--   - `SharedCode`: PDF pp.3–6: the seed law is chosen independently of the input; private kernels factor conditional on it. A single common message alphabet is used for every seed.
--   - `SharedCode.output`: PDF p.3: averaging the composed channels over the independent shared seed.
--   - `SharedCode.Uniform`: PDF p.3: Theorem 9 uses a uniform seed.
--   - `SharedCode.PassiveFeedback`: PDF pp.5–6: passive feedback is an actual output word computed from seed and message. The encoder can recover the receiver's identical word; independent decoder noise is absent.
--   - `QuestionFour`: PDF p.3, Question 4: an assertion, not an assumed answer to the open question.
--   - `QuestionFourPrime`: PDF p.3, Question 4': global all-instance assertion, with a code fixed before every input. It includes the average criterion (4) and the extra typical-word condition.
--   - `ExactType`: PDF p.4: an exact n-type is an integer histogram of total n. Results use n >= 1.
--   - `typeWords`: PDF p.4: the full type class of the histogram, not just an arbitrary support subset.
--   - `typeUniform`: PDF p.4: uniform probability on a type class, zero outside the class.
--   - `ExactType.left`: PDF p.4: the X marginal of a joint type.
--   - `ExactType.right`: PDF p.4: the Y marginal of a joint type.
--   - `JointTypeWordsCompatible`: PDF p.4: membership of the paired word in a joint type class.
--   - `forwardFiber`: PDF p.4: conditional exact type T(x).
--   - `reverseFiber`: PDF p.4: conditional exact type T(y).
--   - `typeForward`: PDF p.4: W_T^n, a uniform channel on each nonempty conditional type class. Its totalized value outside the X type class is zero and never used as a probability law.
--   - `typeReverse`: PDF p.4: V_T^n, uniform on the reverse conditional type class.
--   - `sourceBayesReverse`: PDF p.4: Bayes transpose V on positive output mass. On a zero-mass column use P; this arbitrary stochastic completion never affects positive conditional events.
--   - `positionMarginal`: PDF p.2, (5): the single-position output marginal.
--   - `letterError`: PDF p.7: average of the positionwise total variations, with averaging outside the norm.
--   - `DistributionCompressionCode.Exact`: PDF pp.1,7–8: exact reconstruction for every visible label word.
--   - `DistributionCompressionCode.messageLaw`: PDF pp.1,7–8: distribution of the encoder's message under the source.
--   - `exactEntropy`: PDF pp.1,7: optimized encoder entropy S(n), not minimum log-cardinality. Exact label transmission is feasible and entropy is nonnegative, so this real infimum is nonempty and bounded.
--   - `exactEntropyRate`: PDF pp.1–2,7: Gamma is defined as the infimum of normalized positive-length S(n). The limit identity is a theorem, not a presupposition in this definition.
--   - `FeedbackRates`: PDF p.6: operational rates for simulation on every word, with passive feedback. An asymptotic error bound is allowed; arbitrary positive error and rate slack include the boundary of the region (including vanishing error at error = 0).
--   - `generatedPairs`: PDF pp.8–9: independent local channels applied to one uniform shared seed, with no communication. The resulting law is on pairs of ordered words.
--   - `jointWordLaw`: PDF pp.8–9: the i.i.d. joint law of input and channel output, on paired words.
--   - `VisibleDensityCompressionCode`: PDF p.10, (15): visible quantum encoder and CPTP decoder, without a shared seed.
--   - `quantumWord`: PDF p.10: target tensor product in the original letter order.
--   - `quantumError`: PDF p.10, (16): average half trace norm.
--   - `minimumQuantumSize`: PDF p.10: M is a dimension, not its logarithm; all code dimensions are positive.
--   - `quantumSizeRate`: PDF pp.10–11: normalized log dimension on positive lengths.
--   - `diagonalIn`: PDF p.10: classical law as a diagonal density operator in a common eigenbasis U.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, https://arxiv.org/abs/quant-ph/0208131v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

/-!
Winter, Compression of sources of probability distributions and density operators,
arXiv:quant-ph/0208131v1. Local definitions model this paper only.
Probability laws, stochastic kernels, bit-valued Shannon entropy, and bit-valued
Holevo information reuse the pinned accepted library. Distinct source-compression
objects have specific names to distinguish unrelated accepted objects.
All logarithms and entropies are in bits. Empty alphabets are excluded in results.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate
open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- PDF p.1: a length-n word, with the original letter order retained. -/
abbrev SourceWord (A : Type) (n : ℕ) := Fin n → A

/-- PDF pp.1–2: the memoryless product probability. -/
def wordMass {A : Type} {n : ℕ} (p : A → ℝ) (x : SourceWord A n) : ℝ :=
  ∏ i, p (x i)

/-- PDF p.1: the memoryless conditional output distribution. -/
def wordChannel {A B : Type} {n : ℕ} (w : A → B → ℝ)
    (x : SourceWord A n) (y : SourceWord B n) : ℝ := ∏ i, w (x i) (y i)

/-- PDF p.3: the output marginal PW. -/
def sourceOutputMarginal {A B : Type} [Fintype A] (p : A → ℝ) (w : A → B → ℝ) : B → ℝ :=
  fun b => ∑ a, p a * w a b

/-- PDF p.3: conditional entropy H(W|P), in bits. -/
def sourceConditionalEntropyBits {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (w : A → B → ℝ) : ℝ := ∑ a, p a * shannon (w a)

/-- PDF p.3: I(P;W) = H(PW) - H(W|P). -/
def sourceInformationBits {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (w : A → B → ℝ) : ℝ :=
  shannon (sourceOutputMarginal p w) - sourceConditionalEntropyBits p w

/-- PDF p.1, (4): total variation is half the full l1 distance. -/
def tv {A : Type} [Fintype A] (p q : A → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

/-- PDF p.1, (3): visible code, finite nonempty message alphabet, stochastic encoder and
stochastic decoder. Their private randomness is independent: composition multiplies kernels. -/
structure DistributionCompressionCode (A B : Type) [Fintype B] (n : ℕ) where
  size : ℕ
  size_pos : 0 < size
  enc : SourceWord A n → Fin size → ℝ
  enc_law : IsStochastic enc
  dec : Fin size → SourceWord B n → ℝ
  dec_law : IsStochastic dec

/-- PDF p.1: the composed output distribution of an ordinary code. -/
def DistributionCompressionCode.output {A B : Type} [Fintype B] {n : ℕ} (c : DistributionCompressionCode A B n)
    (x : SourceWord A n) (y : SourceWord B n) : ℝ := ∑ m, c.enc x m * c.dec m y

/-- PDF p.1, (4): P^n-average block total variation, not empirical distortion. -/
def sourceAverageBlockError {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (p : A → ℝ) (w : A → B → ℝ) (v : SourceWord A n → SourceWord B n → ℝ) : ℝ :=
  ∑ x, wordMass p x * tv (wordChannel w x) (v x)

/-- PDF p.1: M(n,lambda) is the minimum alphabet cardinality. Exact sending of the label
makes this set nonempty for lambda >= 0. Theorems only use that domain. -/
def minimumSize {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (w : A → B → ℝ) (n : ℕ) (error : ℝ) : ℕ :=
  sInf {m | ∃ c : DistributionCompressionCode A B n, c.size = m ∧ sourceAverageBlockError p w c.output ≤ error}

/-- PDF p.3: the positive-blocklength normalized communication cost. Using n+1 gives
exactly the same asymptotic limits while excluding division by zero. -/
def sizeRate {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (w : A → B → ℝ) (error : ℝ) (n : ℕ) : ℝ :=
  Real.logb 2 (minimumSize p w (n + 1) error : ℝ) / (n + 1 : ℝ)

/-- PDF p.3, (8): number of occurrences of a letter in a word. -/
def occurrences {A : Type} [DecidableEq A] {n : ℕ} (x : SourceWord A n) (a : A) : ℕ :=
  (Finset.univ.filter fun i => x i = a).card

/-- PDF p.3, (8): variance-normalized typical words, including zero-probability letters. -/
def VarianceTypicalWord {A : Type} [DecidableEq A] {n : ℕ} (p : A → ℝ) (width : ℝ)
    (x : SourceWord A n) : Prop :=
  ∀ a, |(occurrences x a : ℝ) - n * p a| ≤
    width * Real.sqrt n * Real.sqrt (p a * (1 - p a))

/-- PDF pp.3–6: the seed law is chosen independently of the input; private kernels
factor conditional on it. A single common message alphabet is used for every seed. -/
structure SharedCode (A B : Type) [Fintype B] (n : ℕ) where
  size : ℕ
  size_pos : 0 < size
  seeds : ℕ
  seeds_pos : 0 < seeds
  seed : Fin seeds → ℝ
  seed_law : IsLaw seed
  enc : Fin seeds → SourceWord A n → Fin size → ℝ
  enc_law : ∀ s, IsStochastic (enc s)
  dec : Fin seeds → Fin size → SourceWord B n → ℝ
  dec_law : ∀ s, IsStochastic (dec s)

/-- PDF p.3: averaging the composed channels over the independent shared seed. -/
def SharedCode.output {A B : Type} [Fintype B] {n : ℕ}
    (c : SharedCode A B n) (x : SourceWord A n) (y : SourceWord B n) : ℝ :=
  ∑ s, c.seed s * ∑ m, c.enc s x m * c.dec s m y

/-- PDF p.3: Theorem 9 uses a uniform seed. -/
def SharedCode.Uniform {A B : Type} [Fintype B] {n : ℕ} (c : SharedCode A B n) : Prop :=
  ∀ s, c.seed s = 1 / (c.seeds : ℝ)

/-- PDF pp.5–6: passive feedback is an actual output word computed from seed and message.
The encoder can recover the receiver's identical word; independent decoder noise is absent. -/
def SharedCode.PassiveFeedback {A B : Type} [Fintype B] [DecidableEq B] {n : ℕ}
    (c : SharedCode A B n) : Prop :=
  ∃ out : Fin c.seeds → Fin c.size → SourceWord B n,
    ∀ s m y, c.dec s m y = if y = out s m then 1 else 0

/-- PDF p.3, Question 4: an assertion, not an assumed answer to the open question. -/
def QuestionFour : Prop :=
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ (p : Fin a → ℝ) (w : Fin a → Fin b → ℝ), IsLaw p → IsStochastic w →
      ∀ error : ℝ, 0 < error → error < 1 →
        Tendsto (sizeRate p w error) atTop (nhds (sourceInformationBits p w))

/-- PDF p.3, Question 4': global all-instance assertion, with a code fixed before every
input. It includes the average criterion (4) and the extra typical-word condition. -/
def QuestionFourPrime : Prop :=
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∀ (p : Fin a → ℝ) (w : Fin a → Fin b → ℝ), IsLaw p → IsStochastic w →
      ∀ error : ℝ, 0 < error → error < 1 →
        ∀ slack : ℝ, 0 < slack → ∀ width : ℝ, 0 < width →
          ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
            ∃ c : DistributionCompressionCode (Fin a) (Fin b) n,
              Real.logb 2 (c.size : ℝ) / n ≤ sourceInformationBits p w + slack ∧
              sourceAverageBlockError p w c.output ≤ error ∧
              ∀ x, VarianceTypicalWord p width x → tv (wordChannel w x) (c.output x) ≤ error

/-- PDF p.4: an exact n-type is an integer histogram of total n. Results use n >= 1. -/
structure ExactType (A : Type) [Fintype A] (n : ℕ) where
  count : A → ℕ
  total : ∑ a, count a = n

/-- PDF p.4: the full type class of the histogram, not just an arbitrary support subset. -/
def typeWords {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (t : ExactType A n) :
    Finset (SourceWord A n) := Finset.univ.filter fun x => ∀ a, occurrences x a = t.count a

/-- PDF p.4: uniform probability on a type class, zero outside the class. -/
def typeUniform {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}
    (t : ExactType A n) (x : SourceWord A n) : ℝ :=
  if x ∈ typeWords t then 1 / ((typeWords t).card : ℝ) else 0

/-- PDF p.4: the X marginal of a joint type. -/
def ExactType.left {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (t : ExactType (A × B) n) : ExactType A n where
  count a := ∑ b, t.count (a, b)
  total := by simpa only [Fintype.sum_prod_type] using t.total

/-- PDF p.4: the Y marginal of a joint type. -/
def ExactType.right {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (t : ExactType (A × B) n) : ExactType B n where
  count b := ∑ a, t.count (a, b)
  total := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using t.total

/-- PDF p.4: membership of the paired word in a joint type class. -/
def JointTypeWordsCompatible {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (t : ExactType (A × B) n) (x : SourceWord A n) (y : SourceWord B n) : Prop :=
  (fun i => (x i, y i)) ∈ typeWords t

/-- PDF p.4: conditional exact type T(x). -/
def forwardFiber {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (t : ExactType (A × B) n) (x : SourceWord A n) : Finset (SourceWord B n) :=
  Finset.univ.filter fun y => JointTypeWordsCompatible t x y

/-- PDF p.4: conditional exact type T(y). -/
def reverseFiber {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (t : ExactType (A × B) n) (y : SourceWord B n) : Finset (SourceWord A n) :=
  Finset.univ.filter fun x => JointTypeWordsCompatible t x y

/-- PDF p.4: W_T^n, a uniform channel on each nonempty conditional type class.
Its totalized value outside the X type class is zero and never used as a probability law. -/
def typeForward {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (t : ExactType (A × B) n) (x : SourceWord A n) (y : SourceWord B n) : ℝ :=
  if JointTypeWordsCompatible t x y then 1 / ((forwardFiber t x).card : ℝ) else 0

/-- PDF p.4: V_T^n, uniform on the reverse conditional type class. -/
def typeReverse {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (t : ExactType (A × B) n) (y : SourceWord B n) (x : SourceWord A n) : ℝ :=
  if JointTypeWordsCompatible t x y then 1 / ((reverseFiber t y).card : ℝ) else 0

/-- PDF p.4: Bayes transpose V on positive output mass. On a zero-mass column use P;
this arbitrary stochastic completion never affects positive conditional events. -/
def sourceBayesReverse {A B : Type} [Fintype A] (p : A → ℝ) (w : A → B → ℝ) (b : B) (a : A) : ℝ :=
  if 0 < sourceOutputMarginal p w b then p a * w a b / sourceOutputMarginal p w b else p a

/-- PDF p.2, (5): the single-position output marginal. -/
def positionMarginal {B : Type} [Fintype B] [DecidableEq B] {n : ℕ}
    (v : SourceWord B n → ℝ) (i : Fin n) (b : B) : ℝ :=
  ∑ y, if y i = b then v y else 0

/-- PDF p.7: average of the positionwise total variations, with averaging outside the norm. -/
def letterError {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] {n : ℕ}
    (p : A → ℝ) (w : A → B → ℝ) (c : DistributionCompressionCode A B n) : ℝ :=
  ∑ x, wordMass p x * ((∑ i, tv (w (x i)) (positionMarginal (c.output x) i)) / n)

/-- PDF pp.1,7–8: exact reconstruction for every visible label word. -/
def DistributionCompressionCode.Exact {A B : Type} [Fintype B] {n : ℕ} (c : DistributionCompressionCode A B n) (w : A → B → ℝ) : Prop :=
  ∀ x y, c.output x y = wordChannel w x y

/-- PDF pp.1,7–8: distribution of the encoder's message under the source. -/
def DistributionCompressionCode.messageLaw {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (c : DistributionCompressionCode A B n) (p : A → ℝ) (m : Fin c.size) : ℝ := ∑ x, wordMass p x * c.enc x m

/-- PDF pp.1,7: optimized encoder entropy S(n), not minimum log-cardinality. Exact label
transmission is feasible and entropy is nonnegative, so this real infimum is nonempty and bounded. -/
def exactEntropy {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (w : A → B → ℝ) (n : ℕ) : ℝ :=
  sInf {r | ∃ c : DistributionCompressionCode A B n, c.Exact w ∧ shannon (c.messageLaw p) = r}

/-- PDF pp.1–2,7: Gamma is defined as the infimum of normalized positive-length S(n).
The limit identity is a theorem, not a presupposition in this definition. -/
def exactEntropyRate {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (w : A → B → ℝ) : ℝ :=
  sInf {r | ∃ n : ℕ, 0 < n ∧ exactEntropy p w n / n = r}

/-- PDF p.6: operational rates for simulation on every word, with passive feedback.
An asymptotic error bound is allowed; arbitrary positive error and rate slack include the
boundary of the region (including vanishing error at error = 0). -/
def FeedbackRates {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (w : A → B → ℝ) (error communication randomness : ℝ) : Prop :=
  ∀ tolerance > (0 : ℝ), ∀ slack > (0 : ℝ),
    ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
    ∃ c : SharedCode A B n, c.PassiveFeedback ∧
      Real.logb 2 (c.size : ℝ) / n ≤ communication + slack ∧
      Real.logb 2 (c.seeds : ℝ) / n ≤ randomness + slack ∧
      ∀ x, tv (wordChannel w x) (c.output x) ≤ error + tolerance

/-- PDF pp.8–9: independent local channels applied to one uniform shared seed,
with no communication. The resulting law is on pairs of ordered words. -/
def generatedPairs {A B : Type} {n seeds : ℕ}
    (a : Fin seeds → SourceWord A n → ℝ) (b : Fin seeds → SourceWord B n → ℝ)
    (xy : SourceWord A n × SourceWord B n) : ℝ :=
  (∑ s, a s xy.1 * b s xy.2) / seeds

/-- PDF pp.8–9: the i.i.d. joint law of input and channel output, on paired words. -/
def jointWordLaw {A B : Type} {n : ℕ} (p : A → ℝ) (w : A → B → ℝ)
    (xy : SourceWord A n × SourceWord B n) : ℝ := wordMass p xy.1 * wordChannel w xy.1 xy.2

/-- PDF p.10, (15): visible quantum encoder and CPTP decoder, without a shared seed. -/
structure VisibleDensityCompressionCode (A B : Type) [Fintype B] [DecidableEq B] (n : ℕ) where
  size : ℕ
  size_pos : 0 < size
  enc : SourceWord A n → Matrix (Fin size) (Fin size) ℂ
  enc_state : ∀ x, QAlgorithms.IsDensityMatrix (enc x)
  dec : QAlgorithms.Superop (Fin size) (SourceWord B n)
  dec_channel : QAlgorithms.IsChannel dec

/-- PDF p.10: target tensor product in the original letter order. -/
def quantumWord {A B : Type} {n : ℕ} (rho : A → Matrix B B ℂ)
    (x : SourceWord A n) : Matrix (SourceWord B n) (SourceWord B n) ℂ :=
  fun y z => ∏ i, rho (x i) (y i) (z i)

/-- PDF p.10, (16): average half trace norm. -/
def quantumError {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] {n : ℕ}
    (p : A → ℝ) (rho : A → Matrix B B ℂ) (c : VisibleDensityCompressionCode A B n) : ℝ :=
  ∑ x, wordMass p x * (QAlgorithms.traceNorm (quantumWord rho x - c.dec (c.enc x)) / 2)

/-- PDF p.10: M is a dimension, not its logarithm; all code dimensions are positive. -/
def minimumQuantumSize {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (rho : A → Matrix B B ℂ) (n : ℕ) (error : ℝ) : ℕ :=
  sInf {m | ∃ c : VisibleDensityCompressionCode A B n, c.size = m ∧ quantumError p rho c ≤ error}

/-- PDF pp.10–11: normalized log dimension on positive lengths. -/
def quantumSizeRate {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (p : A → ℝ) (rho : A → Matrix B B ℂ) (error : ℝ) (n : ℕ) : ℝ :=
  Real.logb 2 (minimumQuantumSize p rho (n + 1) error : ℝ) / (n + 1 : ℝ)

/-- PDF p.10: classical law as a diagonal density operator in a common eigenbasis U. -/
def diagonalIn {B : Type} [Fintype B] [DecidableEq B]
    (u : Matrix B B ℂ) (p : B → ℝ) : Matrix B B ℂ :=
  u * Matrix.diagonal (fun b => (p b : ℂ)) * uᴴ

/-- Sanity: the empty product is a unit point mass, rather than a zero state. -/
example {A : Type} (p : A → ℝ) (x : SourceWord A 0) : wordMass p x = 1 := by
  simp [wordMass]

/-- Sanity: total variation between identical laws is zero. -/
example {A : Type} [Fintype A] (p : A → ℝ) : tv p p = 0 := by
  simp [tv]

/-- Sanity: a deterministic code on a singleton message/output has a normalized kernel. -/
example : IsStochastic (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) := by
  intro a
  constructor
  · intro b; norm_num
  · simp

/-- Sanity: zero-probability output columns of the Bayes completion return P. -/
example {A B : Type} [Fintype A] (p : A → ℝ) (w : A → B → ℝ) (b : B)
    (h : sourceOutputMarginal p w b = 0) : sourceBayesReverse p w b = p := by
  funext a
  simp [sourceBayesReverse, h]

/-- Sanity: the quantum tensor product of zero letters is the 1-by-1 identity entry. -/
example {A B : Type} (rho : A → Matrix B B ℂ) (x : SourceWord A 0) (y z : SourceWord B 0) :
    quantumWord rho x y z = 1 := by
  simp [quantumWord]

/-- Sanity: a one-symbol law and channel have zero mutual information. -/
example : sourceInformationBits (fun (_ : Unit) => (1 : ℝ))
    (fun (_ _ : Unit) => (1 : ℝ)) = 0 := by
  simp [sourceInformationBits, sourceOutputMarginal, sourceConditionalEntropyBits, shannon]

/-- Sanity: incompatible words have zero conditional-type probability, not a normalized
0/0 probability. -/
example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (t : ExactType (A × B) n) (x : SourceWord A n) (y : SourceWord B n)
    (h : ¬ JointTypeWordsCompatible t x y) : typeForward t x y = 0 := by
  simp [typeForward, h]

/-- Sanity: the corrected optimal-alphabet bound is one at the singleton corner. -/
example : max 1 (Fintype.card Unit * Fintype.card Unit - 1) = 1 := by
  simp

end QAlgorithms.Papers.Independent.Support50.P38


