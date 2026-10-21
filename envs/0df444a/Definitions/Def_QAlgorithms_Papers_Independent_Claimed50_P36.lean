-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36
-- name    : QAlgorithms_Papers_Independent_Claimed50_P36
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:31:16.515434+00:00
-- url     : https://prove2.me/theorems/3b168af3-9fe2-4fae-bb79-10f5509d09f6
-- title:
--   Definitions for Information capacity formula of quantum optical channels
-- statement:
--   The objects the formalized statements of *Information capacity formula of quantum optical channels* (arXiv:quant-ph/0105042) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `coherentOverlap`: PDF pp.3,16,18: exact coherent overlap, conjugate linear in alpha. Its squared modulus is exp(-|alpha-beta|²). No photon cutoff is taken.
--   - `wordGram`: PDF pp.1,3: Gram matrix of product letter codewords.
--   - `IsGramPOVM`: PDF pp.1,3: pullback of an arbitrary collective POVM to the exact codeword span. Positivity plus sum=Gram includes nonorthogonal and dependent codewords and preserves every conditional probability on these words.
--   - `PureCode`: PDF pp.3,7, Eq.(21): pure-letter code with transmitted cost per word. The receiver acts jointly on the entire product word.
--   - `pureError`: PDF pp.1-4: average decoding error for equally likely messages.
--   - `PureAchievable`: PDF pp.2-4,7: an asymptotically achievable rate in nats per mode. The alphabet, overlap, and cost are fixed before block length and messages. L and M are positive wherever logarithms or divisions are used.
--   - `coherentRates`: PDF p.16, Eq.(67): operational continuous coherent-alphabet capacity. All finite codes with arbitrary complex amplitudes and collective POVMs occur.
--   - `coherentCapacity`: PDF pp.7,16: supremum of achievable continuous coherent rates. The theorem establishes boundedness on m≥0 rather than assuming it.
--   - `binaryLetter`: PDF p.16, Eqs.(68)-(69): the two coherent letters, fixed before coding.
--   - `fixedBinaryRates`: PDF pp.16-17: operational capacity for a fixed binary coherent alphabet.
--   - `binaryCollectiveRates`: PDF p.17: a binary alphabet is chosen before block lengths and messages.
--   - `binaryCollectiveCapacity`: PDF p.16, Eq.(68): optimal binary discretization with collective decoding.
--   - `matrixEntropy`: PDF p.5, Eq.(14): finite-state entropy in nats. Hermitian density matrices are used below. This differs from frozen vnEntropy, whose units are bits.
--   - `binaryPrior`: PDF pp.16,18: prior Q for alpha and 1-Q for beta.
--   - `binaryMixtureGram`: PDF pp.5,16: weighted Gram matrix with the same nonzero spectrum as q|alpha><alpha|+(1-q)|beta><beta|, not a cutoff of oscillator energy.
--   - `binaryValue`: PDF p.17, Eq.(70): explicit optimal binary collective rate.
--   - `binaryConditional`: PDF p.4, Eq.(6): conditional probabilities of a binary receiver. No optimal receiver or accessible-information formula is assumed here.
--   - `binaryOutput`: PDF pp.4,17-18: output law of a binary receiver.
--   - `binaryMutualInformation`: PDF p.4, Eq.(6): actual Shannon mutual information in nats. On valid priors and Gram POVMs, zero-probability terms are 0 log 0=0.
--   - `binaryAccessibleValues`: PDF pp.16-18, Eqs.(69),(72): full one-symbol optimization, including all priors, both amplitudes, and every binary POVM on their exact span. The source states that two receiver outcomes suffice for two pure letters.
--   - `binaryAccessibleCapacity`: PDF p.17, Eq.(72): full binary single-symbol accessible-information capacity. This is not the heuristic prior (79).
--   - `thermalLaw`: PDF p.15, Eq.(58): Bose-Einstein photon-number law, including m=0.
--   - `NumberLaw`: PDF pp.7-9,15: probability on the full number alphabet with finite raw first moment bounded by m. HasSum mass=1 excludes an empty or divergent law.
--   - `numberEntropy`: PDF p.15, Eqs.(58)-(63): extended Shannon entropy of a number-diagonal state in nats. The nonnegative series retains infinity rather than totalizing a divergent real tsum to zero.
--   - `lossTransition`: PDF p.15, Eq.(60): eta is photon survival probability, not amplitude k. The guard y≤n is essential because natural subtraction is truncated.
--   - `lossOutput`: PDF p.15, Eq.(62): exact number-diagonal output law on the full oscillator.
--   - `numberHolevo`: PDF p.15, Eq.(63): Holevo difference. Finiteness of both entropy terms and summability of the averaged conditional entropies are conclusions below.
--   - `NumberCode`: PDF pp.3,7,15: number-state product code under transmitter mean cost. Every collective POVM on diagonal output states induces a stochastic decoder on the full number-word basis; all such decoders are included.
--   - `numberError`: PDF pp.3,15: average code error through the memoryless binomial channel. For each input word, loss has finite support, so this real tsum converges.
--   - `NumberAchievable`: PDF pp.3,7,15: vanishing-error product-number-code rates in nats per mode.
--   - `numberRates`: PDF p.15: operational capacity with number letters and no added noise.
--   - `numberCapacity`: PDF p.15, Eqs.(59),(63): supremum of operational number-code rates.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, https://arxiv.org/abs/quant-ph/0105042v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

/-!
Sohma and Hirota, arXiv:quant-ph/0105042v1.
All optical rates below use natural logarithms. Full number alphabets are ℕ.
For pure coherent codewords, the Gram representation is the exact span of the
physical oscillator codewords, not a photon cutoff: B_j = S† Π_j S is positive
and sums to S†S. Conversely these matrices specify every POVM on the span,
including singular Gram matrices and coincident letters. The coherent kernel
is the full oscillator overlap. Number outputs are diagonal on the complete
number basis, so all POVMs induce precisely stochastic decoders on that basis.
The operational definitions use product codewords, arbitrary collective
receivers, a transmitted energy bound on each codeword, and vanishing average
error. The Gaussian mixed-output interfaces are deferred, not replaced by
covariance-only capacities. Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter
open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.
open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)
open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF pp.3,16,18: exact coherent overlap, conjugate linear in alpha.
Its squared modulus is exp(-|alpha-beta|²). No photon cutoff is taken. -/
def coherentOverlap (alpha beta : ℂ) : ℂ :=
  Complex.exp (((-(Complex.normSq alpha + Complex.normSq beta) / 2 : ℝ) : ℂ) +
    star alpha * beta)

/-- PDF pp.1,3: Gram matrix of product letter codewords. -/
def wordGram {A : Type*} {L M : ℕ} (K : A → A → ℂ)
    (letters : Fin M → Fin L → A) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => ∏ t, K (letters i t) (letters j t)

/-- PDF pp.1,3: pullback of an arbitrary collective POVM to the exact
codeword span. Positivity plus sum=Gram includes nonorthogonal and dependent
codewords and preserves every conditional probability on these words. -/
def IsGramPOVM {I O : Type*} [Fintype I] [Fintype O]
    (G : Matrix I I ℂ) (B : O → Matrix I I ℂ) : Prop :=
  (∀ o, (B o).PosSemidef) ∧ ∑ o, B o = G

/-- PDF pp.3,7, Eq.(21): pure-letter code with transmitted cost per word.
The receiver acts jointly on the entire product word. -/
structure PureCode {A : Type*} (K : A → A → ℂ) (cost : A → ℝ)
    (budget : ℝ) (L M : ℕ) where
  letters : Fin M → Fin L → A
  energy : ∀ i, ∑ t, cost (letters i t) ≤ (L : ℝ) * budget
  detection : Fin M → Matrix (Fin M) (Fin M) ℂ
  receiver : IsGramPOVM (wordGram K letters) detection

/-- PDF pp.1-4: average decoding error for equally likely messages. -/
def pureError {A : Type*} {K : A → A → ℂ} {cost : A → ℝ}
    {budget : ℝ} {L M : ℕ} (code : PureCode K cost budget L M) : ℝ :=
  1 - (∑ i, (code.detection i i i).re) / (M : ℝ)

/-- PDF pp.2-4,7: an asymptotically achievable rate in nats per mode.
The alphabet, overlap, and cost are fixed before block length and messages.
L and M are positive wherever logarithms or divisions are used. -/
def PureAchievable {A : Type*} (K : A → A → ℂ) (cost : A → ℝ)
    (budget rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∀ eps : ℝ, 0 < eps → ∃ L0 : ℕ, 0 < L0 ∧
    ∀ L : ℕ, L0 ≤ L → ∃ M : ℕ, 0 < M ∧
      ∃ code : PureCode K cost budget L M,
        pureError code ≤ eps ∧ rate - eps ≤ Real.log (M : ℝ) / (L : ℝ)

/-- PDF p.16, Eq.(67): operational continuous coherent-alphabet capacity.
All finite codes with arbitrary complex amplitudes and collective POVMs occur. -/
def coherentRates (m : ℝ) : Set ℝ :=
  {rate | PureAchievable coherentOverlap Complex.normSq m rate}

/-- PDF pp.7,16: supremum of achievable continuous coherent rates.
The theorem establishes boundedness on m≥0 rather than assuming it. -/
def coherentCapacity (m : ℝ) : ℝ := sSup (coherentRates m)

/-- PDF p.16, Eqs.(68)-(69): the two coherent letters, fixed before coding. -/
def binaryLetter (alpha beta : ℂ) (i : Bool) : ℂ :=
  if i then beta else alpha

/-- PDF pp.16-17: operational capacity for a fixed binary coherent alphabet. -/
def fixedBinaryRates (alpha beta : ℂ) (m : ℝ) : Set ℝ :=
  {rate | PureAchievable
    (fun i j => coherentOverlap (binaryLetter alpha beta i) (binaryLetter alpha beta j))
    (fun i => Complex.normSq (binaryLetter alpha beta i)) m rate}

/-- PDF p.17: a binary alphabet is chosen before block lengths and messages. -/
def binaryCollectiveRates (m : ℝ) : Set ℝ :=
  {rate | ∃ alpha beta : ℂ, rate ∈ fixedBinaryRates alpha beta m}

/-- PDF p.16, Eq.(68): optimal binary discretization with collective decoding. -/
def binaryCollectiveCapacity (m : ℝ) : ℝ := sSup (binaryCollectiveRates m)

/-- PDF p.5, Eq.(14): finite-state entropy in nats. Hermitian density matrices
are used below. This differs from frozen vnEntropy, whose units are bits. -/
def matrixEntropy {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.log x) rho).trace.re

/-- PDF pp.16,18: prior Q for alpha and 1-Q for beta. -/
def binaryPrior (q : ℝ) (i : Bool) : ℝ := if i then 1 - q else q

/-- PDF pp.5,16: weighted Gram matrix with the same nonzero spectrum as
q|alpha><alpha|+(1-q)|beta><beta|, not a cutoff of oscillator energy. -/
def binaryMixtureGram (alpha beta : ℂ) (q : ℝ) : Matrix Bool Bool ℂ :=
  fun i j => (Real.sqrt (binaryPrior q i) : ℂ) *
    coherentOverlap (binaryLetter alpha beta i) (binaryLetter alpha beta j) *
    (Real.sqrt (binaryPrior q j) : ℂ)

/-- PDF p.17, Eq.(70): explicit optimal binary collective rate. -/
def binaryValue (m : ℝ) : ℝ :=
  (binaryEntropy ((1 - Real.exp (-2 * m)) / 2)).toReal

/-- PDF p.4, Eq.(6): conditional probabilities of a binary receiver.
No optimal receiver or accessible-information formula is assumed here. -/
def binaryConditional (B : Bool → Matrix Bool Bool ℂ) (o i : Bool) : ℝ :=
  (B o i i).re

/-- PDF pp.4,17-18: output law of a binary receiver. -/
def binaryOutput (q : ℝ) (B : Bool → Matrix Bool Bool ℂ) (o : Bool) : ℝ :=
  ∑ i, binaryPrior q i * binaryConditional B o i

/-- PDF p.4, Eq.(6): actual Shannon mutual information in nats.
On valid priors and Gram POVMs, zero-probability terms are 0 log 0=0. -/
def binaryMutualInformation (q : ℝ) (B : Bool → Matrix Bool Bool ℂ) : ℝ :=
  ∑ i, ∑ o, binaryPrior q i * binaryConditional B o i *
    Real.log (binaryConditional B o i / binaryOutput q B o)

/-- PDF pp.16-18, Eqs.(69),(72): full one-symbol optimization, including
all priors, both amplitudes, and every binary POVM on their exact span.
The source states that two receiver outcomes suffice for two pure letters. -/
def binaryAccessibleValues (m : ℝ) : Set ℝ :=
  {value | ∃ alpha beta : ℂ, ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
    q * Complex.normSq alpha + (1 - q) * Complex.normSq beta ≤ m ∧
    ∃ B : Bool → Matrix Bool Bool ℂ,
      IsGramPOVM (fun i j => coherentOverlap
        (binaryLetter alpha beta i) (binaryLetter alpha beta j)) B ∧
      value = binaryMutualInformation q B}

/-- PDF p.17, Eq.(72): full binary single-symbol accessible-information capacity.
This is not the heuristic prior (79). -/
def binaryAccessibleCapacity (m : ℝ) : ℝ := sSup (binaryAccessibleValues m)

/-- PDF p.15, Eq.(58): Bose-Einstein photon-number law, including m=0. -/
def thermalLaw (m : ℝ) (n : ℕ) : ℝ :=
  1 / (1 + m) * (m / (1 + m)) ^ n

/-- PDF pp.7-9,15: probability on the full number alphabet with finite raw
first moment bounded by m. HasSum mass=1 excludes an empty or divergent law. -/
def NumberLaw (m : ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ HasSum p 1 ∧
    Summable (fun n : ℕ => (n : ℝ) * p n) ∧ (∑' n : ℕ, (n : ℝ) * p n) ≤ m

/-- PDF p.15, Eqs.(58)-(63): extended Shannon entropy of a number-diagonal
state in nats. The nonnegative series retains infinity rather than totalizing
a divergent real tsum to zero. -/
def numberEntropy (p : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (-p n * Real.log (p n))

/-- PDF p.15, Eq.(60): eta is photon survival probability, not amplitude k.
The guard y≤n is essential because natural subtraction is truncated. -/
def lossTransition (eta : ℝ) (n y : ℕ) : ℝ :=
  if y ≤ n then (Nat.choose n y : ℝ) * eta ^ y * (1 - eta) ^ (n - y) else 0

/-- PDF p.15, Eq.(62): exact number-diagonal output law on the full oscillator. -/
def lossOutput (eta : ℝ) (p : ℕ → ℝ) (y : ℕ) : ℝ :=
  ∑' n, p n * lossTransition eta n y

/-- PDF p.15, Eq.(63): Holevo difference. Finiteness of both entropy terms
and summability of the averaged conditional entropies are conclusions below. -/
def numberHolevo (eta : ℝ) (p : ℕ → ℝ) : ℝ :=
  (numberEntropy (lossOutput eta p)).toReal -
    ∑' n, p n * (numberEntropy (lossTransition eta n)).toReal

/-- PDF pp.3,7,15: number-state product code under transmitter mean cost.
Every collective POVM on diagonal output states induces a stochastic decoder
on the full number-word basis; all such decoders are included. -/
structure NumberCode (eta budget : ℝ) (L M : ℕ) where
  letters : Fin M → Fin L → ℕ
  energy : ∀ i, (∑ t, (letters i t : ℝ)) ≤ (L : ℝ) * budget
  decode : (Fin L → ℕ) → Fin M → ℝ
  decode_nonneg : ∀ y i, 0 ≤ decode y i
  decode_total : ∀ y, ∑ i, decode y i = 1

/-- PDF pp.3,15: average code error through the memoryless binomial channel.
For each input word, loss has finite support, so this real tsum converges. -/
def numberError {eta budget : ℝ} {L M : ℕ}
    (code : NumberCode eta budget L M) : ℝ :=
  1 - (∑ i, ∑' y : Fin L → ℕ,
    (∏ t, lossTransition eta (code.letters i t) (y t)) * code.decode y i) / (M : ℝ)

/-- PDF pp.3,7,15: vanishing-error product-number-code rates in nats per mode. -/
def NumberAchievable (eta budget rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∀ eps : ℝ, 0 < eps → ∃ L0 : ℕ, 0 < L0 ∧
    ∀ L : ℕ, L0 ≤ L → ∃ M : ℕ, 0 < M ∧
      ∃ code : NumberCode eta budget L M,
        numberError code ≤ eps ∧ rate - eps ≤ Real.log (M : ℝ) / (L : ℝ)

/-- PDF p.15: operational capacity with number letters and no added noise. -/
def numberRates (eta m : ℝ) : Set ℝ := {rate | NumberAchievable eta m rate}

/-- PDF p.15, Eqs.(59),(63): supremum of operational number-code rates. -/
def numberCapacity (eta m : ℝ) : ℝ := sSup (numberRates eta m)

/-! Small normalization and boundary checks for the new definitions. -/

example : Real.log 2 * bosonicEntropy 0 = 0 := by simp [bosonicEntropy]

example : (binaryEntropy 0).toReal = 0 := by simp [binaryEntropy]

example : coherentOverlap 0 0 = 1 := by simp [coherentOverlap]

example {A : Type*} (K : A → A → ℂ) {M : ℕ}
    (letters : Fin M → Fin 0 → A) (i j : Fin M) : wordGram K letters i j = 1 := by
  simp [wordGram]

example : thermalLaw 0 0 = 1 := by simp [thermalLaw]

example (n : ℕ) : thermalLaw 0 (n + 1) = 0 := by simp [thermalLaw]

example (eta : ℝ) : lossTransition eta 0 0 = 1 := by simp [lossTransition]

example (eta : ℝ) : lossTransition eta 0 1 = 0 := by simp [lossTransition]

example : binaryLetter 0 0 false = 0 := rfl

example : IsGramPOVM (1 : Matrix Unit Unit ℂ)
    (fun _ : Unit => (1 : Matrix Unit Unit ℂ)) :=
  ⟨fun _ => Matrix.PosSemidef.one, by simp⟩

example (eta : ℝ) : Nonempty (NumberCode eta 0 1 1) := by
  refine ⟨{ letters := fun _ _ => 0
            energy := ?_
            decode := fun _ _ => 1
            decode_nonneg := ?_
            decode_total := ?_ }⟩
  all_goals simp

end QAlgorithms.Papers.Independent.Claimed50.P36


