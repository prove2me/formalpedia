-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23
-- name    : QAlgorithms_Papers_Independent_Advance50_P23
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:18:49.501871+00:00
-- url     : https://prove2.me/theorems/48b81581-d8d7-4808-be9c-ecb407c45bef
-- title:
--   Definitions for Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information
-- statement:
--   The objects the formalized statements of *Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information* (arXiv:1202.0325) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `hayashiIsCQ`: PDF p.2: normalized finite cq outputs.
--   - `hayashiIsStochastic`: PDF p.2: a classical stochastic encoder.
--   - `hayashiCompose`: PDF p.2: actual composition of a cq channel and a stochastic matrix.
--   - `cqJoint`: PDF pp.2,4: the cq matrix in quantum-then-classical tensor order.
--   - `cqReference`: PDF p.4: reference sigma tensor the classical law, in the same tensor order.
--   - `hayashiPetzD`: PDF pp.2–3, (3): shifted-order Petz divergence, with the Umegaki branch at zero. Negative-order zero overlap uses extended log(0)=-infinity; support failure at positive s gives +infinity. At s=-1 the numerator power is the support projection.
--   - `underlinedD`: PDF p.2, (2): the paper's underlined divergence. The logarithm is extended spectrally: a nonzero rho weight on the kernel of B gives -infinity, rather than silently replacing log(0) by zero. This is not Umegaki or sandwiched divergence.
--   - `starMoment`: PDF p.2, (4): positive-parameter starred trace moment, without a sandwiched power of rho. Only 0<s<=1 is used below.
--   - `petzInfo`: PDF pp.4–5, (23),(39): Petz cq information. Its zero value is the Holevo information; for normalized finite cq data the displayed trace is strictly positive.
--   - `referenceInfo`: PDF p.4, (29): Petz information relative to a specified normalized state.
--   - `powerAverage`: PDF pp.4–5, (32): the weighted power average A_s.
--   - `gallagerTrace`: PDF p.5, Lemma 3: concrete Gallager trace functional, including s=0.
--   - `gallagerInfo`: PDF pp.4–5, (32)–(33): Gallager information with its continuous zero branch.
--   - `renyiOptimizer`: PDF p.5, Lemma 1: constructed attaining reference, not a free optimizer.
--   - `hayashiShannon`: PDF p.2: natural Shannon entropy, with zero-weight terms contributing zero.
--   - `hayashiRenyiEntropy`: PDF pp.2,13: classical order-1+s Renyi entropy, including the Shannon limit. All uses have s>=0 and IsLaw P, so the power sum is positive.
--   - `eigenCount`: PDF p.3: number of DISTINCT spectral values, including zero if present.
--   - `spectralSpread`: PDF p.10: log spectral spread on the positive output support. Normalization by trace cancels in this difference. Never include ambient zero eigenvalues.
--   - `hayashiMu`: PDF p.10, (71): the two spectral branches; the square root includes the ceiling.
--   - `traceCorrelation`: PDF p.6: full trace-norm correlation of a cq ensemble at input P.
--   - `Imix`: PDF pp.6,9: uniform-message Holevo leakage.
--   - `Imax`: PDF pp.6,9: source-universal Holevo leakage over all normalized input laws. For density outputs on nonempty finite alphabets this is a nonempty bounded supremum.
--   - `d1mix`: PDF pp.6,9: uniform-message full trace-norm leakage, without a factor 1/2.
--   - `d1max`: PDF pp.6,9: source-universal full trace-norm leakage. Its defining value set is nonempty and bounded by two for normalized finite cq data.
--   - `WiretapCode`: PDF p.9: a genuine M-message code with stochastic encoder and normalized POVM.
--   - `tableEncoder`: PDF p.10, (62): pushforward of the SOLE runtime auxiliary random variable.
--   - `UsesLaw`: PDF pp.9–10: no extra runtime mixing source is allowed. The deterministic table is selected before communication and does not depend on the sampled l or m.
--   - `messageError`: PDF p.9: probability of error on one specified message; fixes printed free i to m.
--   - `hayashiCodeError`: PDF p.9: average error for a uniform message.
--   - `maxError`: PDF p.9: worst-message error, over the nonempty finite message set.
--   - `hayashiReliability`: PDF pp.9–10, (69): hayashiReliability objective, with continuous value one at t=0.
--   - `secrecy`: PDF p.10, (70): secrecy objective, used only for 0<s<=1.
--   - `traceBound`: PDF p.10, (71): Gallager full trace-norm objective.
--   - `mapOutput`: PDF p.7: a deterministic map pushes PA into the actual output mixture.
--   - `PairwiseMap`: PDF p.7: pairwise independent map coordinates, all with the prescribed marginal. These are hypotheses on the random map law, not assertions about a selected map.
--   - `expectE`: PDF pp.7–8: finite expectation of an extended quantity; zero-weight samples contribute zero even if the integrand is infinite.
--   - `expectExp`: PDF pp.7–8: exponential moments preserve exp(-infinity)=0 and exp(+infinity)=infinity.
--   - `bookLaw`: PDF p.9: iid codebook law. The table is sampled once before communication.
--   - `exponentR`: PDF p.14: the two optimized exponents, including the attained zero objective at s=0.
--   - `exponentG`: PDF p.14: Gallager exponent, with the same closed-interval convention.
--   - `IsAdditiveCQ`: PDF pp.7,29: additive cq means an actual projective unitary orbit.
--   - `Universal2`: PDF p.30, Condition 3: universal2 under a finite seed law.
--   - `hayashiBalanced`: PDF p.30: balanced fibres, expressed without truncated natural division.
--   - `Condition1`: PDF p.8, Condition 1: fixed submodule size and the nonzero-membership bound.
--   - `Condition2`: PDF p.8, Condition 2: actual injective linear maps, constrained only at nonzero inputs and outputs. For singleton G the guarded denominator is never used.
--   - `cosetOutput`: PDF p.8: output of a uniformly sampled affine coset, with actual submodule cardinality. It is nonzero because a submodule contains zero.
--   - `shiftExpect`: PDF p.8: independent uniform ambient translation, averaged AFTER the seed.
--   - `shiftExpectE`: PDF pp.8–9: same joint law for extended divergence expectations.
--   - `shiftExpectExp`: PDF pp.8–9: exponential moment under independent uniform translation.
--   - `toeplitz`: PDF p.9: Toeplitz diagonal index i-j represented without negative naturals. Empty-height/width matrices use their genuine matrix type.
--   - `systematicSubmodule`: PDF p.9: systematic image {(a,Za)}. It is a submodule, not an arbitrary assigned-cost code. All r+l-1 diagonal seeds are independent uniform field elements.
--   - `uniformMomentBound`: PDF pp.21–22: moment RHS using an L-point uniform auxiliary law.
--   - `uniformTraceBound`: PDF pp.21–22: uniform linear-code trace-norm objective before its factor two.
--   - `NestedPair`: PDF p.19: actual nested submodules, prescribed sizes, and a complete, unique set of quotient representatives. The representatives merely label the messages.
--   - `pairOutput`: PDF p.19: uniform mixture on the indicated coset, with ambient translation y.
--   - `pairEncoder`: PDF p.19: the actual stochastic coset encoder on the physical input alphabet.
--   - `GroupedDecoder`: PDF p.19: a quotient decoder groups the underlying NORMALIZED codeword POVM. The latter acts on C1+y, labeled by x in C1. This predicate constructs no error bound.
--   - `AffinePair`: PDF pp.22–23: nonuniform linear encoding data, with all quotient cosets represented exactly once. The auxiliary law is supplied independently.
--   - `affinePairOutput`: PDF pp.22–23: actual nonuniform output states; no quotient symmetry is assumed.
--   - `matrixTensor`: PDF p.13: physical tensor powers, including the one-dimensional zeroth power.
--   - `hayashiProductLaw`: PDF p.13: the iid input law. No independence is imposed on general encoders.
--   - `blockMu`: PDF p.13, (85): block prefactor keeps the exact tensor spectral count and n lambda.
--   - `CodeSequence`: PDF pp.13,16: a sequence of actual codes on the physical n-fold channel. Every size is positive. Block zero is harmless and never used for a finite-block bound.
--   - `ReliableRate`: PDF p.16: asymptotic rate and vanishing average decoding error.
--   - `wiretapCapacity`: PDF p.13: operational private capacity over UNRESTRICTED stochastic encoders. The complete extended lattice avoids empty or unbounded real supremum defaults.
--   - `leakedRate`: PDF p.16: operational minimum leakage rate, using precisely the sequences whose ordinary normalized-leakage limits exist. Empty infimum is +infinity.
--   - `receiverCapacity`: PDF p.17: receiver capacity, with a bounded nonempty value set on normalized finite cq data. The theorem's feasibility hypothesis excludes rates above this value.
--   - `constrainedPrivate`: PDF pp.16–17, (100): constrained, normalized private information over every finite auxiliary and every stochastic preprocessing. Empty optimization is -infinity.
--   - `equivocationFunction`: PDF pp.16–17: H(R) via the liminf explicitly identified with the limit on p.17. Convergence is theorem content, never a field imposed on a supplied optimizer.
--   - `ensembleInfo`: PDF p.13: actual ensemble leakage for a sampled iid codebook.
--   - `ensembleTrace`: PDF p.13: actual ensemble full trace-norm leakage.
--   - `lowerExponent`: PDF p.13: corrected lower-asymptotic decay rate, with +infinity at zero leakage. The value at n=0 is irrelevant to liminf as n tends to infinity.
--   - `phaseAmplitude`: PDF p.25, (153): explicit phase-error cq vector, with omega=exp(2 pi i/d). This is a mathematical cq family, not the disputed complement of printed (151).
--   - `phaseCQ`: PDF p.25, (152)–(153): the explicit cq family with arbitrary correlated classical law PZ(z) P(x|z); output basis is (x,z).
--   - `hayashiConditionalRenyi`: PDF p.25: averaged-power conditional Renyi entropy, NOT Arimoto conditional entropy. At order zero only positive conditional probabilities are counted.
--   - `classicalRenyi`: PDF p.26: unconditional Renyi entropy at arbitrary order, with Shannon limit and the order-zero support convention, rather than assigning 0^0=1.
--   - `phasePure`: PDF p.26, (162): reduced pure-state channel in the independent-error case.
--   - `previousExponent`: PDF p.15: the earlier book's exponent objective, including its zero endpoint.
--   - `hashedDistance`: PDF pp.6,30: actual full trace distance from uniform and independent hashed output; hashed blocks are subnormalized and the comparison marginal is common.
--   - `conditionalRenyiReference`: PDF p.4, (25), extended to a specified reference as immediately below (29). The classical reference is identity, not the classical probability law.
--   - `decodedConditionalEntropy`: PDF pp.18–19: Shannon conditional entropy H(M|Mhat) from the actual decoded joint law and its output marginal. Reuse Support50.P07.decodedJoint with the identity receiver dilation and a one-dimensional environment, then read its diagonal. The normalization guard only supplies the frozen KeyCode's proof field; it holds for every normalized cq channel and stochastic encoder used in the theorem below. Outside this physical domain the conditional entropy is assigned zero.
--   - `operationalEquivocationRate`: PDF p.17, corrected operational equivocation: SUPREMUM of the existing conditional-entropy rates of actual reliable codes. Empty supremum is -infinity. The printed infimum is corrected because p.2 calls this the maximum and the identity H(M|E)=log M-I(M;E) reverses the leakage infimum.
-- source:
--   Quantum wiretap channel with non-uniform random number and its exponent and equivocation rate of leaked information, arXiv:1202.0325v3, https://arxiv.org/abs/1202.0325v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07

/-!
Hayashi, arXiv:1202.0325v3. Finite classical alphabets and finite complex matrix
systems; natural logarithms and full trace norm. Definitions are paper-local.
Theorems deliberately have no proofs. Deferred nodes and source discrepancies
are recorded in the assigned unit's HARD.md and GAPS.json. Compilation pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P23

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal
open Filter
open QAlgorithms.Papers.Independent.Information100.P56
  (IsLaw entropy average holevo uniform ProjectiveRep orbit productOutput)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch logNonnegativeExtended)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A Z B E : Type} [Fintype X] [Fintype A] [Fintype Z]
  [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- PDF p.2: normalized finite cq outputs. -/
def hayashiIsCQ (W : X → Matrix E E ℂ) : Prop := ∀ x, IsDensityMatrix (W x)

/-- PDF p.2: a classical stochastic encoder. -/
def hayashiIsStochastic (G : A → X → ℝ) : Prop := ∀ a, IsLaw (G a)

/-- PDF p.2: actual composition of a cq channel and a stochastic matrix. -/
def hayashiCompose (W : X → Matrix E E ℂ) (G : A → X → ℝ) : A → Matrix E E ℂ :=
  fun a => average W (G a)

/-- PDF pp.2,4: the cq matrix in quantum-then-classical tensor order. -/
def cqJoint (W : X → Matrix E E ℂ) (P : X → ℝ) : Matrix (E × X) (E × X) ℂ :=
  fun i j => if i.2 = j.2 then (P i.2 : ℂ) * W i.2 i.1 j.1 else 0

/-- PDF p.4: reference sigma tensor the classical law, in the same tensor order. -/
def cqReference (sigma : Matrix E E ℂ) (P : X → ℝ) : Matrix (E × X) (E × X) ℂ :=
  fun i j => if i.2 = j.2 then (P i.2 : ℂ) * sigma i.1 j.1 else 0

/-- PDF pp.2–3, (3): shifted-order Petz divergence, with the Umegaki branch at zero.
Negative-order zero overlap uses extended log(0)=-infinity; support failure at positive
s gives +infinity. At s=-1 the numerator power is the support projection. -/
def hayashiPetzD (s : ℝ) (rho sigma : Matrix E E ℂ) : EReal :=
  if s = 0 then relativeEntropy rho sigma
  else if 0 < s ∧ ¬ IsSupported rho sigma then ⊤
  else ((s⁻¹ : ℝ) : EReal) *
    logNonnegativeExtended ((supportPower rho (1 + s) * supportPower sigma (-s)).trace.re)

/-- PDF p.2, (2): the paper's underlined divergence. The logarithm is extended
spectrally: a nonzero rho weight on the kernel of B gives -infinity, rather than
silently replacing log(0) by zero. This is not Umegaki or sandwiched divergence. -/
def underlinedD (rho sigma : Matrix E E ℂ) : EReal :=
  let S := supportPower sigma (-(1 / 2 : ℝ))
  let T := S * rho * S
  if IsSupported rho T then ((rho * cfc Real.log T).trace.re : EReal) else ⊥

/-- PDF p.2, (4): positive-parameter starred trace moment, without a sandwiched
power of rho. Only 0<s<=1 is used below. -/
def starMoment (s : ℝ) (rho sigma : Matrix E E ℂ) : ℝ :=
  let S := supportPower sigma (-(1 / 2 : ℝ))
  (rho * supportPower (S * rho * S) s).trace.re

/-- PDF pp.4–5, (23),(39): Petz cq information. Its zero value is the Holevo
information; for normalized finite cq data the displayed trace is strictly positive. -/
def petzInfo (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  if s = 0 then holevo P W else
    Real.log ((∑ x, (P x : ℂ) •
      (supportPower (W x) (1 + s) * supportPower (average W P) (-s))).trace.re) / s

/-- PDF p.4, (29): Petz information relative to a specified normalized state. -/
def referenceInfo (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ)
    (sigma : Matrix E E ℂ) : EReal := hayashiPetzD s (cqJoint W P) (cqReference sigma P)

/-- PDF pp.4–5, (32): the weighted power average A_s. -/
def powerAverage (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : Matrix E E ℂ :=
  ∑ x, (P x : ℂ) • supportPower (W x) (1 + s)

/-- PDF p.5, Lemma 3: concrete Gallager trace functional, including s=0. -/
def gallagerTrace (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  (supportPower (powerAverage s W P) (1 / (1 + s))).trace.re

/-- PDF pp.4–5, (32)–(33): Gallager information with its continuous zero branch. -/
def gallagerInfo (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  if s = 0 then holevo P W else (1 + s) / s * Real.log (gallagerTrace s W P)

/-- PDF p.5, Lemma 1: constructed attaining reference, not a free optimizer. -/
def renyiOptimizer (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : Matrix E E ℂ :=
  (gallagerTrace s W P : ℂ)⁻¹ • supportPower (powerAverage s W P) (1 / (1 + s))

/-- PDF p.2: natural Shannon entropy, with zero-weight terms contributing zero. -/
def hayashiShannon (P : A → ℝ) : ℝ := -∑ a, P a * Real.log (P a)

/-- PDF pp.2,13: classical order-1+s Renyi entropy, including the Shannon limit.
All uses have s>=0 and IsLaw P, so the power sum is positive. -/
def hayashiRenyiEntropy (s : ℝ) (P : A → ℝ) : ℝ :=
  if s = 0 then hayashiShannon P else -Real.log (∑ a, Real.rpow (P a) (1 + s)) / s

/-- PDF p.3: number of DISTINCT spectral values, including zero if present. -/
def eigenCount (sigma : Matrix E E ℂ) : ℕ :=
  (Finset.univ.image (ascEigenvalues sigma)).card

/-- PDF p.10: log spectral spread on the positive output support. Normalization
by trace cancels in this difference. Never include ambient zero eigenvalues. -/
def spectralSpread (sigma : Matrix E E ℂ) : ℝ :=
  let vals := Finset.univ.image (ascEigenvalues sigma)
  if h : vals.Nonempty then Real.log (vals.max' h) - Real.log (minPositiveEigenvalue sigma)
  else 0

/-- PDF p.10, (71): the two spectral branches; the square root includes the ceiling. -/
def hayashiMu (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  min (4 + Real.sqrt (eigenCount (powerAverage s W P)))
    ((4 + Real.sqrt (Int.ceil (spectralSpread (powerAverage s W P)))) * Real.exp (s / 2))

/-- PDF p.6: full trace-norm correlation of a cq ensemble at input P. -/
def traceCorrelation (P : X → ℝ) (W : X → Matrix E E ℂ) : ℝ :=
  ∑ x, P x * traceNorm (W x - average W P)

/-- PDF pp.6,9: uniform-message Holevo leakage. -/
def Imix (W : X → Matrix E E ℂ) : ℝ := holevo uniform W

/-- PDF pp.6,9: source-universal Holevo leakage over all normalized input laws.
For density outputs on nonempty finite alphabets this is a nonempty bounded supremum. -/
def Imax (W : X → Matrix E E ℂ) : ℝ :=
  sSup {y : ℝ | ∃ P : X → ℝ, IsLaw P ∧ y = holevo P W}

/-- PDF pp.6,9: uniform-message full trace-norm leakage, without a factor 1/2. -/
def d1mix (W : X → Matrix E E ℂ) : ℝ := traceCorrelation uniform W

/-- PDF pp.6,9: source-universal full trace-norm leakage. Its defining value set
is nonempty and bounded by two for normalized finite cq data. -/
def d1max (W : X → Matrix E E ℂ) : ℝ :=
  sSup {y : ℝ | ∃ P : X → ℝ, IsLaw P ∧ y = traceCorrelation P W}

/-- PDF p.9: a genuine M-message code with stochastic encoder and normalized POVM. -/
structure WiretapCode (X B : Type) [Fintype X] [Fintype B] [DecidableEq B] (M : ℕ) where
  positive : 0 < M
  encoder : Fin M → X → ℝ
  encoder_law : hayashiIsStochastic encoder
  decoder : Fin M → Matrix B B ℂ
  decoder_povm : IsPOVM decoder

/-- PDF p.10, (62): pushforward of the SOLE runtime auxiliary random variable. -/
def tableEncoder {M L : ℕ} (P : Fin L → ℝ) (c : Fin L → Fin M → X) : Fin M → X → ℝ :=
  fun m x => ∑ l, if c l m = x then P l else 0

/-- PDF pp.9–10: no extra runtime mixing source is allowed. The deterministic
table is selected before communication and does not depend on the sampled l or m. -/
def UsesLaw {M L : ℕ} (P : Fin L → ℝ) (C : WiretapCode X B M) : Prop :=
  ∃ c : Fin L → Fin M → X, C.encoder = tableEncoder P c

/-- PDF p.9: probability of error on one specified message; fixes printed free i to m. -/
def messageError {M : ℕ} (W : X → Matrix B B ℂ) (C : WiretapCode X B M) (m : Fin M) : ℝ :=
  1 - effectProb (C.decoder m) (hayashiCompose W C.encoder m)

/-- PDF p.9: average error for a uniform message. -/
def hayashiCodeError {M : ℕ} (W : X → Matrix B B ℂ) (C : WiretapCode X B M) : ℝ :=
  ∑ m, (M : ℝ)⁻¹ * messageError W C m

/-- PDF p.9: worst-message error, over the nonempty finite message set. -/
def maxError {M : ℕ} (W : X → Matrix B B ℂ) (C : WiretapCode X B M) : ℝ :=
  sSup (Set.range (messageError W C))

/-- PDF pp.9–10, (69): hayashiReliability objective, with continuous value one at t=0. -/
def hayashiReliability (M L : ℕ) (t : ℝ) (W : X → Matrix B B ℂ) (P : X → ℝ) : ℝ :=
  if t = 0 then 1 else Real.rpow (M * L : ℕ) t * Real.exp (-t * petzInfo (-t) W P)

/-- PDF p.10, (70): secrecy objective, used only for 0<s<=1. -/
def secrecy (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) (PA : A → ℝ) : ℝ :=
  Real.rpow (eigenCount (average W P)) s / s *
    Real.exp (-s * hayashiRenyiEntropy s PA + s * petzInfo s W P)

/-- PDF p.10, (71): Gallager full trace-norm objective. -/
def traceBound (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) (PA : A → ℝ) : ℝ :=
  hayashiMu s W P * Real.exp (s / 2 * (gallagerInfo s W P - hayashiRenyiEntropy s PA))

/-- PDF p.7: a deterministic map pushes PA into the actual output mixture. -/
def mapOutput (W : X → Matrix E E ℂ) (f : A → X) (PA : A → ℝ) : Matrix E E ℂ :=
  ∑ a, (PA a : ℂ) • W (f a)

/-- PDF p.7: pairwise independent map coordinates, all with the prescribed marginal.
These are hypotheses on the random map law, not assertions about a selected map. -/
def PairwiseMap (PZ : Z → ℝ) (f : Z → A → X) (PX : X → ℝ) : Prop :=
  IsLaw PZ ∧ (∀ a x, (∑ z, if f z a = x then PZ z else 0) = PX x) ∧
  ∀ a b, a ≠ b → ∀ x y,
    (∑ z, if f z a = x ∧ f z b = y then PZ z else 0) = PX x * PX y

/-- PDF pp.7–8: finite expectation of an extended quantity; zero-weight samples
contribute zero even if the integrand is infinite. -/
def expectE (PZ : Z → ℝ) (f : Z → EReal) : EReal := ∑ z, (PZ z : EReal) * f z

/-- PDF pp.7–8: exponential moments preserve exp(-infinity)=0 and exp(+infinity)=infinity. -/
def expectExp (PZ : Z → ℝ) (s : ℝ) (f : Z → EReal) : ℝ≥0∞ :=
  ∑ z, ENNReal.ofReal (PZ z) * EReal.exp ((s : EReal) * f z)

/-- PDF p.9: iid codebook law. The table is sampled once before communication. -/
def bookLaw {M L : ℕ} (PX : X → ℝ) (c : Fin L → Fin M → X) : ℝ :=
  ∏ l, ∏ m, PX (c l m)

/-- PDF p.14: the two optimized exponents, including the attained zero objective at s=0. -/
def exponentR (R : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ s ∈ Set.Icc (0 : ℝ) 1, y = s * (R - petzInfo s W P)}

/-- PDF p.14: Gallager exponent, with the same closed-interval convention. -/
def exponentG (R : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ s ∈ Set.Icc (0 : ℝ) 1, y = s / 2 * (R - gallagerInfo s W P)}

/-- PDF pp.7,29: additive cq means an actual projective unitary orbit. -/
def IsAdditiveCQ {G : Type} [AddCommGroup G] (W : G → Matrix E E ℂ) : Prop :=
  ∃ U : ProjectiveRep (Multiplicative G) E, ∃ rho : Matrix E E ℂ,
    IsDensityMatrix rho ∧ ∀ x, W x = orbit U rho (Multiplicative.ofAdd x)

/-- PDF p.30, Condition 3: universal2 under a finite seed law. -/
def Universal2 {D : Type} [Fintype D] (PZ : Z → ℝ) (f : Z → A → D) : Prop :=
  ∀ a b, a ≠ b → (∑ z, if f z a = f z b then PZ z else 0) ≤ (Fintype.card D : ℝ)⁻¹

/-- PDF p.30: balanced fibres, expressed without truncated natural division. -/
def hayashiBalanced {D : Type} [Fintype D] (f : A → D) : Prop :=
  ∀ d, (Finset.univ.filter (fun a => f a = d)).card * Fintype.card D = Fintype.card A

/-- PDF p.8, Condition 1: fixed submodule size and the nonzero-membership bound. -/
def Condition1 {K G : Type} [Ring K] [AddCommGroup G] [Module K G] [Fintype G]
    (PZ : Z → ℝ) (C : Z → Submodule K G) (L : ℕ) : Prop :=
  IsLaw PZ ∧ (∀ z, Fintype.card (C z) = L) ∧
    ∀ x : G, x ≠ 0 → (∑ z, if x ∈ C z then PZ z else 0) ≤ L / (Fintype.card G : ℝ)

/-- PDF p.8, Condition 2: actual injective linear maps, constrained only at nonzero
inputs and outputs. For singleton G the guarded denominator is never used. -/
def Condition2 {K D G : Type} [Ring K] [AddCommGroup D] [AddCommGroup G]
    [Module K D] [Module K G] [Fintype G]
    (PZ : Z → ℝ) (f : Z → D →ₗ[K] G) : Prop :=
  IsLaw PZ ∧ (∀ z, Function.Injective (f z)) ∧
    ∀ a : D, a ≠ 0 → ∀ x : G, x ≠ 0 → 1 < Fintype.card G →
      (∑ z, if f z a = x then PZ z else 0) ≤ ((Fintype.card G : ℝ) - 1)⁻¹

/-- PDF p.8: output of a uniformly sampled affine coset, with actual submodule
cardinality. It is nonzero because a submodule contains zero. -/
def cosetOutput {K G : Type} [Ring K] [AddCommGroup G] [Module K G] [Fintype G]
    (W : G → Matrix E E ℂ) (C : Submodule K G) (y : G) : Matrix E E ℂ :=
  ∑ x : C, ((Fintype.card C : ℝ)⁻¹ : ℂ) • W (x.1 + y)

/-- PDF p.8: independent uniform ambient translation, averaged AFTER the seed. -/
def shiftExpect {G : Type} [Fintype G] (PZ : Z → ℝ) (f : Z → G → ℝ) : ℝ :=
  ∑ z, PZ z * ∑ y, (Fintype.card G : ℝ)⁻¹ * f z y

/-- PDF pp.8–9: same joint law for extended divergence expectations. -/
def shiftExpectE {G : Type} [Fintype G] (PZ : Z → ℝ) (f : Z → G → EReal) : EReal :=
  ∑ z, (PZ z : EReal) * ∑ y, (((Fintype.card G : ℝ)⁻¹ : ℝ) : EReal) * f z y

/-- PDF pp.8–9: exponential moment under independent uniform translation. -/
def shiftExpectExp {G : Type} [Fintype G] (PZ : Z → ℝ) (s : ℝ)
    (f : Z → G → EReal) : ℝ≥0∞ :=
  ∑ z, ENNReal.ofReal (PZ z) * ∑ y,
    ENNReal.ofReal ((Fintype.card G : ℝ)⁻¹) * EReal.exp ((s : EReal) * f z y)

/-- PDF p.9: Toeplitz diagonal index i-j represented without negative naturals.
Empty-height/width matrices use their genuine matrix type. -/
def toeplitz {K : Type} (r l : ℕ) (z : Fin (r + l - 1) → K) : Matrix (Fin r) (Fin l) K :=
  fun i j => z ⟨i.val + (l - 1 - j.val), by omega⟩

/-- PDF p.9: systematic image {(a,Za)}. It is a submodule, not an arbitrary
assigned-cost code. All r+l-1 diagonal seeds are independent uniform field elements. -/
def systematicSubmodule {K : Type} [Field K] (r l : ℕ) (z : Fin (r + l - 1) → K) :
    Submodule K ((Fin l → K) × (Fin r → K)) where
  carrier := {v | ∀ i, v.2 i = ∑ j, toeplitz r l z i j * v.1 j}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb i
    change a.2 i + b.2 i = ∑ j, toeplitz r l z i j * (a.1 j + b.1 j)
    rw [ha i, hb i]
    simp [mul_add, Finset.sum_add_distrib]
  smul_mem' := by
    intro c a ha i
    change c * a.2 i = ∑ j, toeplitz r l z i j * (c * a.1 j)
    rw [ha i]
    simp [Finset.mul_sum, mul_left_comm]

/-- PDF pp.21–22: moment RHS using an L-point uniform auxiliary law. -/
def uniformMomentBound (L : ℕ) (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  Real.rpow (eigenCount (average W P)) s *
    (1 + Real.exp (s * petzInfo s W P) / Real.rpow L s)

/-- PDF pp.21–22: uniform linear-code trace-norm objective before its factor two. -/
def uniformTraceBound (L : ℕ) (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  hayashiMu s W P * Real.exp (s / 2 * gallagerInfo s W P) / Real.rpow L (s / 2)

/-- PDF p.19: actual nested submodules, prescribed sizes, and a complete, unique
set of quotient representatives. The representatives merely label the messages. -/
structure NestedPair (K G : Type) [Ring K] [AddCommGroup G] [Module K G]
    [Fintype G] (M L : ℕ) where
  outer : Submodule K G
  inner : Submodule K G
  nested : inner ≤ outer
  inner_size : Fintype.card inner = L
  outer_size : Fintype.card outer = M * L
  representative : Fin M → G
  representative_mem : ∀ m, representative m ∈ outer
  quotient_complete : ∀ x : G, x ∈ outer → ∃! m : Fin M, x - representative m ∈ inner

/-- PDF p.19: uniform mixture on the indicated coset, with ambient translation y. -/
def pairOutput {K G : Type} [Ring K] [AddCommGroup G] [Module K G] [Fintype G]
    {M L : ℕ} (W : G → Matrix E E ℂ) (C : NestedPair K G M L) (y : G) :
    Fin M → Matrix E E ℂ := fun m => cosetOutput W C.inner (C.representative m + y)

/-- PDF p.19: the actual stochastic coset encoder on the physical input alphabet. -/
def pairEncoder {K G : Type} [Ring K] [AddCommGroup G] [Module K G] [Fintype G]
    {M L : ℕ} (C : NestedPair K G M L) (y : G) : Fin M → G → ℝ :=
  fun m x => if x - (C.representative m + y) ∈ C.inner then (L : ℝ)⁻¹ else 0

/-- PDF p.19: a quotient decoder groups the underlying NORMALIZED codeword POVM.
The latter acts on C1+y, labeled by x in C1. This predicate constructs no error bound. -/
def GroupedDecoder {K G : Type} [Ring K] [AddCommGroup G] [Module K G] [Fintype G]
    {M L : ℕ} (C : NestedPair K G M L) (y : G) (D : WiretapCode G B M) : Prop :=
  D.encoder = pairEncoder C y ∧ ∃ word : C.outer → Matrix B B ℂ,
    IsPOVM word ∧ ∀ m, D.decoder m =
      ∑ x : C.outer, if x.1 - C.representative m ∈ C.inner then word x else 0

/-- PDF pp.22–23: nonuniform linear encoding data, with all quotient cosets
represented exactly once. The auxiliary law is supplied independently. -/
structure AffinePair (K D G : Type) [Ring K] [AddCommGroup D] [AddCommGroup G]
    [Module K D] [Module K G] [Fintype G] (M : ℕ) where
  outer : Submodule K G
  linear : D →ₗ[K] G
  injective : Function.Injective linear
  image_mem : ∀ a, linear a ∈ outer
  representative : Fin M → G
  representative_mem : ∀ m, representative m ∈ outer
  quotient_complete : ∀ x : G, x ∈ outer →
    ∃! m : Fin M, ∃ a : D, x = linear a + representative m

/-- PDF pp.22–23: actual nonuniform output states; no quotient symmetry is assumed. -/
def affinePairOutput {K D G : Type} [Ring K] [AddCommGroup D] [AddCommGroup G]
    [Module K D] [Module K G] [Fintype D] [Fintype G] {M : ℕ}
    (W : G → Matrix E E ℂ) (PA : D → ℝ) (C : AffinePair K D G M) (y : G) :
    Fin M → Matrix E E ℂ :=
  fun m => mapOutput W (fun a => C.linear a + (C.representative m + y)) PA

/-- PDF p.13: physical tensor powers, including the one-dimensional zeroth power. -/
def matrixTensor (n : ℕ) (sigma : Matrix E E ℂ) : Matrix (Fin n → E) (Fin n → E) ℂ :=
  fun i j => ∏ k, sigma (i k) (j k)

/-- PDF p.13: the iid input law. No independence is imposed on general encoders. -/
def hayashiProductLaw (n : ℕ) (P : X → ℝ) : (Fin n → X) → ℝ := fun x => ∏ i, P (x i)

/-- PDF p.13, (85): block prefactor keeps the exact tensor spectral count and n lambda. -/
def blockMu (n : ℕ) (s : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  min (4 + Real.sqrt (eigenCount (matrixTensor n (powerAverage s W P))))
    ((4 + Real.sqrt (Int.ceil (n * spectralSpread (powerAverage s W P)))) * Real.exp (s / 2))

/-- PDF pp.13,16: a sequence of actual codes on the physical n-fold channel.
Every size is positive. Block zero is harmless and never used for a finite-block bound. -/
structure CodeSequence (X B : Type) [Fintype X] [Fintype B] [DecidableEq B] where
  size : ℕ → ℕ
  code : (n : ℕ) → WiretapCode (Fin n → X) (Fin n → B) (size n)

/-- PDF p.16: asymptotic rate and vanishing average decoding error. -/
def ReliableRate (WB : X → Matrix B B ℂ) (R : ℝ) (S : CodeSequence X B) : Prop :=
  0 ≤ R ∧ Tendsto (fun n => Real.log (S.size n) / n) atTop (nhds R) ∧
    Tendsto (fun n => hayashiCodeError (productOutput n WB) (S.code n)) atTop (nhds 0)

/-- PDF p.13: operational private capacity over UNRESTRICTED stochastic encoders.
The complete extended lattice avoids empty or unbounded real supremum defaults. -/
def wiretapCapacity (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) : EReal :=
  sSup {r : EReal | ∃ R : ℝ, ∃ S : CodeSequence X B, r = (R : EReal) ∧
    ReliableRate WB R S ∧
    Tendsto (fun n => Imix (hayashiCompose (productOutput n WE) (S.code n).encoder)) atTop (nhds 0)}

/-- PDF p.16: operational minimum leakage rate, using precisely the sequences
whose ordinary normalized-leakage limits exist. Empty infimum is +infinity. -/
def leakedRate (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (R : ℝ) : EReal :=
  sInf {r : EReal | ∃ l : ℝ, ∃ S : CodeSequence X B, r = (l : EReal) ∧ ReliableRate WB R S ∧
    Tendsto (fun n => Imix (hayashiCompose (productOutput n WE) (S.code n).encoder) / n) atTop (nhds l)}

/-- PDF p.17: receiver capacity, with a bounded nonempty value set on normalized
finite cq data. The theorem's feasibility hypothesis excludes rates above this value. -/
def receiverCapacity (WB : X → Matrix B B ℂ) : ℝ :=
  sSup {y : ℝ | ∃ P : X → ℝ, IsLaw P ∧ y = holevo P WB}

/-- PDF pp.16–17, (100): constrained, normalized private information over every
finite auxiliary and every stochastic preprocessing. Empty optimization is -infinity. -/
def constrainedPrivate (n : ℕ) (R : ℝ) (WB : X → Matrix B B ℂ)
    (WE : X → Matrix E E ℂ) : EReal :=
  sSup {y : EReal | ∃ C : QAlgorithms.Papers.Independent.Information100.P56.Encoder (Fin n → X),
    n * R ≤ holevo C.outer (hayashiCompose (productOutput n WB) C.conditional) ∧
    y = ((QAlgorithms.Papers.Independent.Information100.P56.encoderValue
      (productOutput n WB) (productOutput n WE) C / n : ℝ) : EReal)}

/-- PDF pp.16–17: H(R) via the liminf explicitly identified with the limit on p.17.
Convergence is theorem content, never a field imposed on a supplied optimizer. -/
def equivocationFunction (R : ℝ) (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) : EReal :=
  Filter.liminf (fun n => constrainedPrivate n R WB WE) atTop

/-- PDF p.13: actual ensemble leakage for a sampled iid codebook. -/
def ensembleInfo (M L : ℕ) (W : X → Matrix E E ℂ) (PX : X → ℝ) (PL : Fin L → ℝ) : ℝ :=
  ∑ c : Fin L → Fin M → X, bookLaw PX c * Imix (hayashiCompose W (tableEncoder PL c))

/-- PDF p.13: actual ensemble full trace-norm leakage. -/
def ensembleTrace (M L : ℕ) (W : X → Matrix E E ℂ) (PX : X → ℝ) (PL : Fin L → ℝ) : ℝ :=
  ∑ c : Fin L → Fin M → X, bookLaw PX c * d1mix (hayashiCompose W (tableEncoder PL c))

/-- PDF p.13: corrected lower-asymptotic decay rate, with +infinity at zero
leakage. The value at n=0 is irrelevant to liminf as n tends to infinity. -/
def lowerExponent (f : ℕ → ℝ) : EReal :=
  Filter.liminf (fun n : ℕ => -(((n : ℝ)⁻¹ : ℝ) : EReal) * logNonnegativeExtended (f n)) atTop

/-- PDF p.25, (153): explicit phase-error cq vector, with omega=exp(2 pi i/d).
This is a mathematical cq family, not the disputed complement of printed (151). -/
def phaseAmplitude (d : ℕ) [NeZero d] (P : ZMod d → ℝ) (j x : ZMod d) : ℂ :=
  Complex.exp (((2 * Real.pi * j.val * x.val / d : ℝ) : ℂ) * Complex.I) *
    (Real.sqrt (P x) : ℂ)

/-- PDF p.25, (152)–(153): the explicit cq family with arbitrary correlated
classical law PZ(z) P(x|z); output basis is (x,z). -/
def phaseCQ (d : ℕ) [NeZero d] (PZ : ZMod d → ℝ) (P : ZMod d → ZMod d → ℝ)
    (j : ZMod d) : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
  fun u v => if u.2 = v.2 then (PZ u.2 : ℂ) *
    phaseAmplitude d (P u.2) j u.1 * conj (phaseAmplitude d (P u.2) j v.1) else 0

/-- PDF p.25: averaged-power conditional Renyi entropy, NOT Arimoto conditional
entropy. At order zero only positive conditional probabilities are counted. -/
def hayashiConditionalRenyi {D F : Type} [Fintype D] [Fintype F]
    (alpha : ℝ) (PZ : F → ℝ) (P : F → D → ℝ) : ℝ :=
  if alpha = 1 then ∑ z, PZ z * hayashiShannon (P z) else
    Real.log (∑ z, PZ z * ∑ x, if P z x = 0 then 0 else Real.rpow (P z x) alpha) / (1 - alpha)

/-- PDF p.26: unconditional Renyi entropy at arbitrary order, with Shannon limit
and the order-zero support convention, rather than assigning 0^0=1. -/
def classicalRenyi (alpha : ℝ) (P : A → ℝ) : ℝ :=
  if alpha = 1 then hayashiShannon P else
    Real.log (∑ a, if P a = 0 then 0 else Real.rpow (P a) alpha) / (1 - alpha)

/-- PDF p.26, (162): reduced pure-state channel in the independent-error case. -/
def phasePure (d : ℕ) [NeZero d] (P : ZMod d → ℝ) (j : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  fun x y => phaseAmplitude d P j x * conj (phaseAmplitude d P j y)

/-! Sanity checks pin endpoint branches, tensor order, and deterministic runtime mixing. -/

example (rho sigma : Matrix E E ℂ) : hayashiPetzD 0 rho sigma = relativeEntropy rho sigma := by
  simp [hayashiPetzD]

example (W : X → Matrix E E ℂ) (P : X → ℝ) : petzInfo 0 W P = holevo P W := by
  simp [petzInfo]

example (W : X → Matrix E E ℂ) (P : X → ℝ) : gallagerInfo 0 W P = holevo P W := by
  simp [gallagerInfo]

example (P : A → ℝ) : hayashiRenyiEntropy 0 P = hayashiShannon P := by simp [hayashiRenyiEntropy]

example (M L : ℕ) (W : X → Matrix B B ℂ) (P : X → ℝ) : hayashiReliability M L 0 W P = 1 := by
  simp [hayashiReliability]

example (W : X → Matrix E E ℂ) (P : X → ℝ) (e eprime : E) (x : X) :
    cqJoint W P (e, x) (eprime, x) = (P x : ℂ) * W x e eprime := by simp [cqJoint]

example (x : X) : tableEncoder (fun _ : Fin 1 => (1 : ℝ)) (fun _ _ : Fin 1 => x) 0 x = 1 := by
  simp [tableEncoder]

example (P : Z → ℝ) (s : ℝ) : expectE P (fun _ => (0 : EReal)) = 0 := by simp [expectE]

example {K G : Type} [Ring K] [AddCommGroup G] [Module K G] [Fintype G]
    (PZ : Z → ℝ) (W : G → Matrix E E ℂ) :
    cosetOutput W (⊥ : Submodule K G) 0 = W 0 := by
  simp [cosetOutput]
  exact congrArg W ((Submodule.mem_bot K).mp
    (default : (⊥ : Submodule K G)).property)

example (sigma : Matrix E E ℂ) (i j : Fin 0 → E) : matrixTensor 0 sigma i j = 1 := by
  simp [matrixTensor]

example (P : X → ℝ) (x : Fin 0 → X) : hayashiProductLaw 0 P x = 1 := by simp [hayashiProductLaw]

example (P : A → ℝ) : classicalRenyi 1 P = hayashiShannon P := by simp [classicalRenyi]

example {D F : Type} [Fintype D] [Fintype F] (PZ : F → ℝ) (P : F → D → ℝ) :
    hayashiConditionalRenyi 1 PZ P = ∑ z, PZ z * hayashiShannon (P z) := by simp [hayashiConditionalRenyi]

example (d : ℕ) [NeZero d] (P : ZMod d → ℝ) (x : ZMod d) :
    phaseAmplitude d P 0 x = (Real.sqrt (P x) : ℂ) := by simp [phaseAmplitude]

example (s : ℝ) (sigma : Matrix E E ℂ) : starMoment s (0 : Matrix E E ℂ) sigma = 0 := by
  simp [starMoment]

example (s : ℝ) (W : X → Matrix E E ℂ) : powerAverage s W (fun _ => 0) = 0 := by
  simp [powerAverage]

/-- PDF p.15: the earlier book's exponent objective, including its zero endpoint. -/
def previousExponent (R : ℝ) (W : X → Matrix E E ℂ) (P : X → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ s ∈ Set.Icc (0 : ℝ) 1,
    y = s * (R - petzInfo s W P) / (2 * (1 + s))}

/-- PDF pp.6,30: actual full trace distance from uniform and independent hashed
output; hashed blocks are subnormalized and the comparison marginal is common. -/
def hashedDistance {D : Type} [Fintype D]
    (W : A → Matrix E E ℂ) (PA : A → ℝ) (f : A → D) : ℝ :=
  ∑ d : D, traceNorm ((∑ a, if f a = d then (PA a : ℂ) • W a else 0) -
    (((Fintype.card D : ℝ)⁻¹ : ℂ) • average W PA))

/-- PDF p.4, (25), extended to a specified reference as immediately below (29).
The classical reference is identity, not the classical probability law. -/
def conditionalRenyiReference (s : ℝ) (W : A → Matrix E E ℂ) (PA : A → ℝ)
    (sigma : Matrix E E ℂ) : EReal :=
  -hayashiPetzD s (cqJoint W PA) (cqReference sigma (fun _ : A => 1))

/-- PDF pp.18–19: Shannon conditional entropy H(M|Mhat) from the actual decoded
joint law and its output marginal. Reuse Support50.P07.decodedJoint with the
identity receiver dilation and a one-dimensional environment, then read its diagonal.
The normalization guard only supplies the frozen KeyCode's proof field; it holds
for every normalized cq channel and stochastic encoder used in the theorem below.
Outside this physical domain the conditional entropy is assigned zero. -/
def decodedConditionalEntropy {M : ℕ} (W : X → Matrix B B ℂ) (C : WiretapCode X B M) : ℝ :=
  if h : ∀ m, IsDensityMatrix (hayashiCompose W C.encoder m) then
    let code : QAlgorithms.Papers.Independent.Support50.P07.KeyCode B B :=
      { messages := M
        positive := C.positive
        inputs := hayashiCompose W C.encoder
        normalized := h
        measurement := C.decoder
        povm := C.decoder_povm }
    let U : Matrix (B × Unit) B ℂ := fun i j => if i.1 = j then 1 else 0
    let omega := QAlgorithms.Papers.Independent.Support50.P07.decodedJoint U code
    let P : (Fin M × Fin M) → ℝ :=
      fun i => (omega (i.1, (i.2, ())) (i.1, (i.2, ()))).re
    hayashiShannon P - hayashiShannon (fun j : Fin M => ∑ i : Fin M, P (i,j))
  else 0

example {D : Type} [Fintype D] (W : A → Matrix E E ℂ) (PA : A → ℝ) (f : A → D) :
    hashedDistance W (fun _ : A => 0) f = 0 := by
  simp [hashedDistance, average, traceNorm, cfc_zero]

example (W : A → Matrix E E ℂ) (PA : A → ℝ) (sigma : Matrix E E ℂ) :
    conditionalRenyiReference 0 W PA sigma =
      -relativeEntropy (cqJoint W PA) (cqReference sigma (fun _ : A => 1)) := by
  simp [conditionalRenyiReference, hayashiPetzD]

/-- PDF p.17, corrected operational equivocation: SUPREMUM of the existing
conditional-entropy rates of actual reliable codes. Empty supremum is -infinity.
The printed infimum is corrected because p.2 calls this the maximum and the
identity H(M|E)=log M-I(M;E) reverses the leakage infimum. -/
def operationalEquivocationRate (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ)
    (R : ℝ) : EReal :=
  sSup {r : EReal | ∃ l : ℝ, ∃ S : CodeSequence X B,
    r = (l : EReal) ∧ ReliableRate WB R S ∧
    Tendsto (fun n => (Real.log (S.size n) -
      Imix (hayashiCompose (productOutput n WE) (S.code n).encoder)) / n)
      atTop (nhds l)}

end QAlgorithms.Papers.Independent.Advance50.P23


