-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P80
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:21:18.195021+00:00
-- url     : https://prove2.me/theorems/f9568732-fe24-40e1-85fa-a2446c4b3b79
-- title:
--   Definitions for The statistical strength of nonlocality proofs
-- statement:
--   The objects the formalized statements of *The statistical strength of nonlocality proofs* (arXiv:quant-ph/0307125) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BellExperiment`: PDF pp.4,16: nonempty finite parties, settings, and setting-dependent outcomes.
--   - `Settings`
--   - `MeasuredOutcomes`
--   - `Potential`
--   - `Table`
--   - `Sigma`
--   - `PiLocal`
--   - `potentialAtSetting`: PDF pp.5,16: measuring a setting selects coordinates of ONE potential assignment.
--   - `localTable`: PDF pp.5,16: the measured marginal of a full potential-outcome law.
--   - `localTensorEffect`: PDF p.16: coefficient tensor product of the local measurement effects.
--   - `QuantumGenerated`: PDF pp.4–5,16: a fixed finite quantum realization, with normalized shared density matrix and local POVMs. This witnesses quantum generation; it is never optimized in a strength.
--   - `MarginalConsistency`: PDF pp.5,31: every subset marginal is independent of the other parties' settings. Natural coordinate values allow comparison across dependent outcome alphabets.
--   - `NonlocalityProof`: PDF pp.4–5,16,31: quantum table with its probability and no-signalling invariants exposed. Properness is a separate predicate, so local quantum tables remain admissible.
--   - `Proper`: PDF pp.5,16: no single local potential-outcome law reproduces every setting.
--   - `uniformSettings`: PDF p.8: computed uniform setting weights. All setting alphabets are nonempty.
--   - `Uncorrelated`: PDF pp.5,8: products of normalized local setting laws, including point masses.
--   - `PositiveCoordinates`: PDF pp.12,33: relative simplex interior, not ambient interior.
--   - `kl`: PDF p.6: finite KL in bits with explicit support guard. Zero-Q terms, including 0/0, are zero. Individual signed contributions are summed BEFORE taking the nonnegative part.
--   - `BellTrial`
--   - `trialJointLaw`: PDF pp.5–6: the SAME independently chosen setting law for quantum and local theories.
--   - `statisticalPayoff`: PDF p.12, equation (13): U is defined by JOINT KL; the average identity is a conclusion.
--   - `lowerValue`: PDF p.12, equation (14): infimum over all local theories.
--   - `uniformStrength`: PDF p.8, equation (8).
--   - `uncorrelatedStrength`: PDF p.8, equation (9): supremum over PRODUCT settings followed by infimum over Pi.
--   - `correlatedStrength`: PDF p.8, equation (10): potentially correlated settings.
--   - `upperValue`: PDF pp.13–14: the reverse optimization, kept distinct from the maximin.
--   - `minimax`: PDF pp.13–14: inf-sup, not defined to equal sup-inf.
--   - `productSettings`
--   - `Saddle`: PDF pp.13–14 and proof p.35 (102)–(107): saddle orientation. The printed display on p.13 is already correct, contrary to the supplied plan notes.
--   - `minimizers`: PDF p.14, equations (25)–(26).
--   - `Equalizer`: PDF p.14: constant statisticalPayoff against EVERY potentially correlated setting law.
--   - `DominatesQuantum`: PDF p.12: Q is supported by the measured marginals at every setting.
--   - `optimizerScore`: PDF p.12, equations (15)–(16): zero-Q contributions are zero, even if their denominator vanishes. The optimizer characterization separately requires DominatesQuantum.
--   - `NontrivialTable`: PDF p.12: nontriviality in Theorem 1(3a).
--   - `TwoByTwo`: PDF pp.12,14,31: two parties, two settings each; outcomes remain arbitrary finite sets.
--   - `binaryScenario`: PDF pp.18,21: homogeneous binary experimental scenarios.
--   - `BellScenario`
--   - `MerminScenario`
--   - `GHZScenario`
--   - `rotatedBellPairLaw`: PDF pp.18,21: pair law of the fixed (00+11)/sqrt(2) state at rotation angles A,B.
--   - `originalBell`: PDF p.18, Appendix III-A: Bell's ORIGINAL fixed experiment.
--   - `optimizedBell`: PDF p.20, Table VIII (exact rationals), the optimized Bell experiment.
--   - `chshTable`: PDF pp.6,18,21: exact CHSH probabilities, not the rounded decimal table.
--   - `chshLocal`: PDF p.14, equation (27): the specified eight potential assignments each get mass 1/8.
--   - `hardyAlpha`: PDF p.21: Hardy's exact alpha; radical checked in the PDF.
--   - `hardyBeta`
--   - `hardyVector`: PDF p.21, (38)–(39): T vector; F is its real orthogonal complement.
--   - `hardy`: PDF p.21: Born probabilities for alpha|00> - beta|11>, with the stated local bases.
--   - `mermin`: PDF p.23, Table XXII: Mermin's fixed three-setting experiment.
--   - `ghzConstrained`: PDF pp.17,24, (35) and Table XXVIII: 111,122,212,221 in one-based notation.
--   - `ghzAllowed`: PDF p.24, Table XXVIII: parity is odd at 111 and even at 122,212,221.
--   - `ghzTable`: PDF pp.21,24: exact GHZ conditional law.
--   - `ghzLocalTable`: PDF p.24, Table XXIX: exact best-local conditional table; realization is a conclusion.
--   - `ghzCorrelatedSettings`: PDF p.24: corrected from Table XXVIII and (35). The prose prints 0.125 instead of 0.25 and says even, instead of odd, number of setting-1 measurements.
--   - `trialMeasure`: PDF p.25: one-trial law as a finite atomic measure.
--   - `iidLaw`: PDF p.25: infinite IID law on the product sigma algebra. Under NonlocalityProof and s in Sigma, trialMeasure is a probability measure, so infinitePi's zero fallback is not used.
--   - `sampleLikelihood`: PDF pp.25,29: an n-sample likelihood, including the empty product at n=0.
--   - `simplexVolume`: PDF p.29: intrinsic simplex measure in affine dimension |potential assignments|-1. Hausdorff measure for the coordinate norm differs from affine Lebesgue volume only by a fixed positive factor, absorbed into the normalized density. Ambient volume would be zero.
--   - `AdmissiblePrior`: PDF p.29: the source's continuous density, normalized for intrinsic volume, and bounded strictly away from zero. Integrability is a conclusion below, rather than a default integral.
--   - `bayesMarginal`: PDF p.29, equation (64): actual Bayesian marginal over the same local family.
--   - `posteriorOdds`: PDF p.29, (68): posterior odds with fixed 0<h<1 prior probability of QM.
--   - `initialTrials`: First n trials of an infinite sequence.
--   - `idealLength`: PDF pp.26–27: ideal codelength in bits, infinite at impossible words.
--   - `IsPrefixCode`: Actual binary words form a prefix code on the indicated alphabet/support.
--   - `shannonBefore`: Canonical Shannon ordering: decreasing probability, ties broken by a fixed finite index.
--   - `shannonCumulative`: Left end of the Shannon interval for x in the probability-sorted alphabet.
--   - `shannonSize`: PDF p.31: actual integer Shannon ceiling length; used only at p(x)>0.
--   - `shannonWord`: PDF p.31: explicit Shannon words: the first ceil(-log2 p(x)) binary digits of the cumulative probability in decreasing-probability order. Zero-mass words are excluded from its coding alphabet; singleton support has the empty word.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, https://arxiv.org/abs/quant-ph/0307125v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Information

/-!
Statements from van Dam, Gill and Grunwald, quant-ph/0307125v2.
All new definitions are confined to this paper. Indices are zero based; outcome 1 is T.
Distinct names separate this paper's experimental tables and likelihoods from unrelated
accepted channel/operator definitions. Base-two logs reuse Mathlib Real.logb directly.
The saddle inequalities agree with Definition 4 on PDF p.13 and its proof on p.35.
The plan incorrectly described the displayed minimizer inequality as reversed.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Filter

/-- PDF pp.4,16: nonempty finite parties, settings, and setting-dependent outcomes. -/
structure BellExperiment where
  parties : ℕ
  parties_pos : 0 < parties
  settings : Fin parties → ℕ
  settings_pos : ∀ i, 0 < settings i
  outcomes : (i : Fin parties) → Fin (settings i) → ℕ
  outcomes_pos : ∀ i a, 0 < outcomes i a

abbrev Settings (S : BellExperiment) := (i : Fin S.parties) → Fin (S.settings i)

abbrev MeasuredOutcomes (S : BellExperiment) (s : Settings S) :=
  (i : Fin S.parties) → Fin (S.outcomes i (s i))

abbrev Potential (S : BellExperiment) :=
  (i : Fin S.parties) → (a : Fin (S.settings i)) → Fin (S.outcomes i a)

abbrev Table (S : BellExperiment) := (s : Settings S) → MeasuredOutcomes S s → ℝ

abbrev Sigma (S : BellExperiment) := stdSimplex ℝ (Settings S)

abbrev PiLocal (S : BellExperiment) := stdSimplex ℝ (Potential S)

/-- PDF pp.5,16: measuring a setting selects coordinates of ONE potential assignment. -/
def potentialAtSetting {S : BellExperiment} (v : Potential S) (s : Settings S) : MeasuredOutcomes S s :=
  fun i => v i (s i)

/-- PDF pp.5,16: the measured marginal of a full potential-outcome law. -/
def localTable {S : BellExperiment} (p : Potential S → ℝ) : Table S :=
  fun s x => ∑ v, if potentialAtSetting v s = x then p v else 0

/-- PDF p.16: coefficient tensor product of the local measurement effects. -/
def localTensorEffect {S : BellExperiment} (d : Fin S.parties → ℕ)
    (M : (i : Fin S.parties) → (a : Fin (S.settings i)) →
      Fin (S.outcomes i a) → Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (s : Settings S) (x : MeasuredOutcomes S s) :
    Matrix ((i : Fin S.parties) → Fin (d i)) ((i : Fin S.parties) → Fin (d i)) ℂ :=
  Matrix.of fun u v => ∏ i, M i (s i) (x i) (u i) (v i)

/-- PDF pp.4–5,16: a fixed finite quantum realization, with normalized shared density matrix
and local POVMs. This witnesses quantum generation; it is never optimized in a strength. -/
def QuantumGenerated {S : BellExperiment} (Q : Table S) : Prop :=
  ∃ (d : Fin S.parties → ℕ), (∀ i, 0 < d i) ∧
    ∃ (rho : Matrix ((i : Fin S.parties) → Fin (d i))
        ((i : Fin S.parties) → Fin (d i)) ℂ)
      (M : (i : Fin S.parties) → (a : Fin (S.settings i)) →
        Fin (S.outcomes i a) → Matrix (Fin (d i)) (Fin (d i)) ℂ),
      QAlgorithms.IsDensityMatrix rho ∧ (∀ i a, QAlgorithms.IsPOVM (M i a)) ∧
      ∀ s x, Q s x = QAlgorithms.effectProb (localTensorEffect d M s x) rho

/-- PDF pp.5,31: every subset marginal is independent of the other parties' settings.
Natural coordinate values allow comparison across dependent outcome alphabets. -/
def MarginalConsistency {S : BellExperiment} (Q : Table S) : Prop :=
  ∀ (J : Finset (Fin S.parties)) (s t : Settings S),
    (∀ i ∈ J, s i = t i) → ∀ v : Potential S,
    (∑ x, if ∀ i ∈ J, (x i).val = (v i (s i)).val then Q s x else 0) =
    (∑ x, if ∀ i ∈ J, (x i).val = (v i (t i)).val then Q t x else 0)

/-- PDF pp.4–5,16,31: quantum table with its probability and no-signalling invariants exposed.
Properness is a separate predicate, so local quantum tables remain admissible. -/
def NonlocalityProof {S : BellExperiment} (Q : Table S) : Prop :=
  (∀ s, Q s ∈ stdSimplex ℝ (MeasuredOutcomes S s)) ∧ MarginalConsistency Q ∧ QuantumGenerated Q

/-- PDF pp.5,16: no single local potential-outcome law reproduces every setting. -/
def Proper {S : BellExperiment} (Q : Table S) : Prop :=
  ¬ ∃ p : PiLocal S, localTable p.1 = Q

/-- PDF p.8: computed uniform setting weights. All setting alphabets are nonempty. -/
def uniformSettings (S : BellExperiment) : Settings S → ℝ :=
  fun _ => (Fintype.card (Settings S) : ℝ)⁻¹

/-- PDF pp.5,8: products of normalized local setting laws, including point masses. -/
def Uncorrelated {S : BellExperiment} (s : Settings S → ℝ) : Prop :=
  ∃ p : (i : Fin S.parties) → stdSimplex ℝ (Fin (S.settings i)),
    ∀ a, s a = ∏ i, (p i).1 (a i)

/-- PDF pp.12,33: relative simplex interior, not ambient interior. -/
def PositiveCoordinates {I : Type*} (p : I → ℝ) : Prop := ∀ i, 0 < p i

/-- PDF p.6: finite KL in bits with explicit support guard. Zero-Q terms, including 0/0,
are zero. Individual signed contributions are summed BEFORE taking the nonnegative part. -/
def kl {I : Type*} [Fintype I] (q p : I → ℝ) : ℝ≥0∞ :=
  if ∃ x, 0 < q x ∧ p x = 0 then ⊤ else
    ENNReal.ofReal (∑ x, if q x = 0 then 0 else q x * Real.logb 2 (q x / p x))

abbrev BellTrial (S : BellExperiment) := (s : Settings S) × MeasuredOutcomes S s

/-- PDF pp.5–6: the SAME independently chosen setting law for quantum and local theories. -/
def trialJointLaw {S : BellExperiment} (Q : Table S) (s : Settings S → ℝ) : BellTrial S → ℝ :=
  fun z => s z.1 * Q z.1 z.2

/-- PDF p.12, equation (13): U is defined by JOINT KL; the average identity is a conclusion. -/
def statisticalPayoff {S : BellExperiment} (Q : Table S) (s : Settings S → ℝ)
    (p : Potential S → ℝ) : ℝ≥0∞ := kl (trialJointLaw Q s) (trialJointLaw (localTable p) s)

/-- PDF p.12, equation (14): infimum over all local theories. -/
def lowerValue {S : BellExperiment} (Q : Table S) (s : Settings S → ℝ) : ℝ≥0∞ :=
  ⨅ p : PiLocal S, statisticalPayoff Q s p.1

/-- PDF p.8, equation (8). -/
def uniformStrength {S : BellExperiment} (Q : Table S) : ℝ≥0∞ :=
  lowerValue Q (uniformSettings S)

/-- PDF p.8, equation (9): supremum over PRODUCT settings followed by infimum over Pi. -/
def uncorrelatedStrength {S : BellExperiment} (Q : Table S) : ℝ≥0∞ :=
  ⨆ s : {s : Sigma S // Uncorrelated s.1}, lowerValue Q s.1.1

/-- PDF p.8, equation (10): potentially correlated settings. -/
def correlatedStrength {S : BellExperiment} (Q : Table S) : ℝ≥0∞ :=
  ⨆ s : Sigma S, lowerValue Q s.1

/-- PDF pp.13–14: the reverse optimization, kept distinct from the maximin. -/
def upperValue {S : BellExperiment} (Q : Table S) (A : Set (Settings S → ℝ))
    (p : Potential S → ℝ) : ℝ≥0∞ := ⨆ s : A, statisticalPayoff Q s.1 p

/-- PDF pp.13–14: inf-sup, not defined to equal sup-inf. -/
def minimax {S : BellExperiment} (Q : Table S) (A : Set (Settings S → ℝ)) : ℝ≥0∞ :=
  ⨅ p : PiLocal S, upperValue Q A p.1

def productSettings (S : BellExperiment) : Set (Settings S → ℝ) :=
  {s | s ∈ stdSimplex ℝ (Settings S) ∧ Uncorrelated s}

/-- PDF pp.13–14 and proof p.35 (102)–(107): saddle orientation.
The printed display on p.13 is already correct, contrary to the supplied plan notes. -/
def Saddle {S : BellExperiment} (Q : Table S) (A : Set (Settings S → ℝ))
    (s : Settings S → ℝ) (p : Potential S → ℝ) : Prop :=
  s ∈ A ∧ p ∈ stdSimplex ℝ (Potential S) ∧
    (∀ t ∈ A, statisticalPayoff Q t p ≤ statisticalPayoff Q s p) ∧
    (∀ r ∈ stdSimplex ℝ (Potential S), statisticalPayoff Q s p ≤ statisticalPayoff Q s r)

/-- PDF p.14, equations (25)–(26). -/
def minimizers {S : BellExperiment} (Q : Table S) (A : Set (Settings S → ℝ)) :
    Set (Potential S → ℝ) :=
  {p | p ∈ stdSimplex ℝ (Potential S) ∧ upperValue Q A p = minimax Q A}

/-- PDF p.14: constant statisticalPayoff against EVERY potentially correlated setting law. -/
def Equalizer {S : BellExperiment} (Q : Table S) (p : Potential S → ℝ) : Prop :=
  ∃ K : ℝ≥0∞, ∀ s : Sigma S, statisticalPayoff Q s.1 p = K

/-- PDF p.12: Q is supported by the measured marginals at every setting. -/
def DominatesQuantum {S : BellExperiment} (Q : Table S) (p : Potential S → ℝ) : Prop :=
  ∀ s x, 0 < Q s x → 0 < localTable p s x

/-- PDF p.12, equations (15)–(16): zero-Q contributions are zero, even if their denominator
vanishes. The optimizer characterization separately requires DominatesQuantum. -/
def optimizerScore {S : BellExperiment} (Q : Table S) (s : Settings S → ℝ)
    (p : Potential S → ℝ) (v : Potential S) : ℝ :=
  ∑ a, if Q a (potentialAtSetting v a) = 0 then 0 else
    s a * Q a (potentialAtSetting v a) / localTable p a (potentialAtSetting v a)

/-- PDF p.12: nontriviality in Theorem 1(3a). -/
def NontrivialTable {S : BellExperiment} (Q : Table S) : Prop :=
  ∃ a x, 0 < Q a x ∧ Q a x < 1

/-- PDF pp.12,14,31: two parties, two settings each; outcomes remain arbitrary finite sets. -/
def TwoByTwo (S : BellExperiment) : Prop := S.parties = 2 ∧ ∀ i, S.settings i = 2

/-- PDF pp.18,21: homogeneous binary experimental scenarios. -/
abbrev binaryScenario (k m : ℕ) (hk : 0 < k) (hm : 0 < m) : BellExperiment where
  parties := k
  parties_pos := hk
  settings := fun _ => m
  settings_pos := fun _ => hm
  outcomes := fun _ _ => 2
  outcomes_pos := fun _ _ => by decide

abbrev BellScenario := binaryScenario 2 2 (by decide) (by decide)

abbrev MerminScenario := binaryScenario 2 3 (by decide) (by decide)

abbrev GHZScenario := binaryScenario 3 2 (by decide) (by decide)

/-- PDF pp.18,21: pair law of the fixed (00+11)/sqrt(2) state at rotation angles A,B. -/
def rotatedBellPairLaw (A B : ℝ) (x y : Fin 2) : ℝ :=
  if x = y then (Real.cos (A - B)) ^ 2 / 2 else (Real.sin (A - B)) ^ 2 / 2

/-- PDF p.18, Appendix III-A: Bell's ORIGINAL fixed experiment. -/
def originalBell : Table BellScenario := fun s x =>
  rotatedBellPairLaw (if s 0 = 0 then 0 else Real.pi / 8)
    (if s 1 = 0 then Real.pi / 8 else Real.pi / 4) (x 0) (x 1)

/-- PDF p.20, Table VIII (exact rationals), the optimized Bell experiment. -/
def optimizedBell : Table BellScenario := fun s x =>
  if s 0 = 0 ∧ s 1 = 0 then (if x 0 = x 1 then 1 / 2 else 0)
  else if s 0 = 0 ∧ s 1 = 1 then (if x 0 = x 1 then 1 / 8 else 3 / 8)
  else (if x 0 = x 1 then 3 / 8 else 1 / 8)

/-- PDF pp.6,18,21: exact CHSH probabilities, not the rounded decimal table. -/
def chshTable : Table BellScenario := fun s x =>
  if (x 0 ≠ x 1) ↔ (s 0 = 1 ∧ s 1 = 1)
  then 1 / 4 + Real.sqrt 2 / 8 else 1 / 4 - Real.sqrt 2 / 8

/-- PDF p.14, equation (27): the specified eight potential assignments each get mass 1/8. -/
def chshLocal : Potential BellScenario → ℝ := fun v =>
  if (v 0 0, v 0 1, v 1 0, v 1 1) ∈
      ({(0,0,0,0), (1,1,1,1), (0,0,0,1), (1,1,1,0),
        (0,0,1,0), (1,1,0,1), (1,0,0,1), (0,1,1,0)} :
        Finset (Fin 2 × Fin 2 × Fin 2 × Fin 2))
  then 1 / 8 else 0

/-- PDF p.21: Hardy's exact alpha; radical checked in the PDF. -/
def hardyAlpha : ℝ := Real.sqrt (2 + 2 * Real.sqrt (-13 + 6 * Real.sqrt 5)) / 2

def hardyBeta : ℝ := Real.sqrt (1 - hardyAlpha ^ 2)

/-- PDF p.21, (38)–(39): T vector; F is its real orthogonal complement. -/
def hardyVector (a x j : Fin 2) : ℝ :=
  let u := if a = 0 then Real.sqrt (hardyBeta / (hardyAlpha + hardyBeta))
    else -Real.sqrt (hardyBeta ^ 3 / (hardyAlpha ^ 3 + hardyBeta ^ 3))
  let v := if a = 0 then Real.sqrt (hardyAlpha / (hardyAlpha + hardyBeta))
    else Real.sqrt (hardyAlpha ^ 3 / (hardyAlpha ^ 3 + hardyBeta ^ 3))
  if x = 1 then (if j = 0 then u else v) else (if j = 0 then -v else u)

/-- PDF p.21: Born probabilities for alpha|00> - beta|11>, with the stated local bases. -/
def hardy : Table BellScenario := fun s x =>
  (hardyAlpha * hardyVector (s 0) (x 0) 0 * hardyVector (s 1) (x 1) 0 -
    hardyBeta * hardyVector (s 0) (x 0) 1 * hardyVector (s 1) (x 1) 1) ^ 2

/-- PDF p.23, Table XXII: Mermin's fixed three-setting experiment. -/
def mermin : Table MerminScenario := fun s x =>
  if s 0 = s 1 then (if x 0 = x 1 then 1 / 2 else 0)
  else (if x 0 = x 1 then 1 / 8 else 3 / 8)

/-- PDF pp.17,24, (35) and Table XXVIII: 111,122,212,221 in one-based notation. -/
def ghzConstrained (s : Settings GHZScenario) : Prop :=
  (s 0).val + (s 1).val + (s 2).val = 0 ∨
    (s 0).val + (s 1).val + (s 2).val = 2

/-- PDF p.24, Table XXVIII: parity is odd at 111 and even at 122,212,221. -/
def ghzAllowed (s : Settings GHZScenario) (x : MeasuredOutcomes GHZScenario s) : Prop :=
  ((x 0).val + (x 1).val + (x 2).val) % 2 =
    if s 0 = 0 ∧ s 1 = 0 ∧ s 2 = 0 then 1 else 0

/-- PDF pp.21,24: exact GHZ conditional law. -/
def ghzTable : Table GHZScenario := fun s x =>
  if ghzConstrained s then (if ghzAllowed s x then 1 / 4 else 0) else 1 / 8

/-- PDF p.24, Table XXIX: exact best-local conditional table; realization is a conclusion. -/
def ghzLocalTable : Table GHZScenario := fun s x =>
  if ghzConstrained s then (if ghzAllowed s x then 3 / 16 else 1 / 16) else 1 / 8

/-- PDF p.24: corrected from Table XXVIII and (35). The prose prints 0.125 instead of 0.25
and says even, instead of odd, number of setting-1 measurements. -/
def ghzCorrelatedSettings : Settings GHZScenario → ℝ := fun s =>
  if ghzConstrained s then 1 / 4 else 0

section ProbabilityCoding

/-- Finite trial alphabet carries the discrete sigma algebra. -/
instance trialMeasurableSpace (S : BellExperiment) : MeasurableSpace (BellTrial S) := ⊤

/-- PDF p.25: one-trial law as a finite atomic measure. -/
def trialMeasure {S : BellExperiment} (Q : Table S) (s : Settings S → ℝ) : Measure (BellTrial S) :=
  ∑ z, ENNReal.ofReal (trialJointLaw Q s z) • Measure.dirac z

/-- PDF p.25: infinite IID law on the product sigma algebra. Under NonlocalityProof and
s in Sigma, trialMeasure is a probability measure, so infinitePi's zero fallback is not used. -/
def iidLaw {S : BellExperiment} (Q : Table S) (s : Settings S → ℝ) : Measure (ℕ → BellTrial S) :=
  Measure.infinitePi (fun _ : ℕ => trialMeasure Q s)

/-- PDF pp.25,29: an n-sample likelihood, including the empty product at n=0. -/
def sampleLikelihood {Z : Type*} (p : Z → ℝ) {n : ℕ} (z : Fin n → Z) : ℝ := ∏ i, p (z i)

/-- PDF p.29: intrinsic simplex measure in affine dimension |potential assignments|-1.
Hausdorff measure for the coordinate norm differs from affine Lebesgue volume only by a
fixed positive factor, absorbed into the normalized density. Ambient volume would be zero. -/
def simplexVolume (S : BellExperiment) : Measure (Potential S → ℝ) :=
  (Measure.hausdorffMeasure ((Fintype.card (Potential S) - 1 : ℕ) : ℝ)).restrict
    (stdSimplex ℝ (Potential S))

/-- PDF p.29: the source's continuous density, normalized for intrinsic volume, and bounded
strictly away from zero. Integrability is a conclusion below, rather than a default integral. -/
def AdmissiblePrior {S : BellExperiment} (w : (Potential S → ℝ) → ℝ) : Prop :=
  ContinuousOn w (stdSimplex ℝ (Potential S)) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ p ∈ stdSimplex ℝ (Potential S), c < w p) ∧
  (∫ p, w p ∂simplexVolume S) = 1

/-- PDF p.29, equation (64): actual Bayesian marginal over the same local family. -/
def bayesMarginal {S : BellExperiment} (s : Settings S → ℝ)
    (w : (Potential S → ℝ) → ℝ) {n : ℕ} (z : Fin n → BellTrial S) : ℝ :=
  ∫ p, w p * sampleLikelihood (trialJointLaw (localTable p) s) z ∂simplexVolume S

/-- PDF p.29, (68): posterior odds with fixed 0<h<1 prior probability of QM. -/
def posteriorOdds {S : BellExperiment} (Q : Table S) (s : Settings S → ℝ)
    (w : (Potential S → ℝ) → ℝ) (h : ℝ) {n : ℕ} (z : Fin n → BellTrial S) : ℝ :=
  (h / (1 - h)) * sampleLikelihood (trialJointLaw Q s) z / bayesMarginal s w z

/-- First n trials of an infinite sequence. -/
def initialTrials {Z : Type*} (z : ℕ → Z) (n : ℕ) : Fin n → Z := fun i => z i.val

/-- PDF pp.26–27: ideal codelength in bits, infinite at impossible words. -/
def idealLength {Z : Type*} (p : Z → ℝ) {n : ℕ} (z : Fin n → Z) : ℝ≥0∞ :=
  if sampleLikelihood p z = 0 then ⊤ else ENNReal.ofReal (-Real.logb 2 (sampleLikelihood p z))

/-- Actual binary words form a prefix code on the indicated alphabet/support. -/
def IsPrefixCode {Z : Type*} (C : Z → List Bool) : Prop :=
  ∀ x y, (C x).IsPrefix (C y) → x = y

/-- Canonical Shannon ordering: decreasing probability, ties broken by a fixed finite index. -/
def shannonBefore {Z : Type*} [Fintype Z] (p : Z → ℝ) (x y : Z) : Prop :=
  p y < p x ∨ (p x = p y ∧ (Fintype.equivFin Z x).val < (Fintype.equivFin Z y).val)

/-- Left end of the Shannon interval for x in the probability-sorted alphabet. -/
def shannonCumulative {Z : Type*} [Fintype Z] (p : Z → ℝ) (x : Z) : ℝ :=
  ∑ y, if shannonBefore p y x then p y else 0

/-- PDF p.31: actual integer Shannon ceiling length; used only at p(x)>0. -/
def shannonSize {Z : Type*} (p : Z → ℝ) (x : Z) : ℕ := ⌈-Real.logb 2 (p x)⌉₊

/-- PDF p.31: explicit Shannon words: the first ceil(-log2 p(x)) binary digits of the
cumulative probability in decreasing-probability order. Zero-mass words are excluded from
its coding alphabet; singleton support has the empty word. -/
def shannonWord {Z : Type*} [Fintype Z] (p : Z → ℝ) (x : Z) : List Bool :=
  List.ofFn fun j : Fin (shannonSize p x) =>
    decide ((⌊(2 : ℝ) ^ (j.val + 1) * shannonCumulative p x⌋₊) % 2 = 1)

end ProbabilityCoding

section DefinitionSanity

example : (0 : Fin BellScenario.parties).val = 0 := rfl

example {S : BellExperiment} (v : Potential S) (s : Settings S) (i : Fin S.parties) :
    potentialAtSetting v s i = v i (s i) := rfl

example {I : Type*} [Fintype I] (p : I → ℝ) : kl (fun _ => 0) p = 0 := by
  simp [kl]

example : kl (fun _ : Unit => (1 : ℝ)) (fun _ => 0) = ⊤ := by
  simp [kl]

example {Z : Type*} (p : Z → ℝ) (z : Fin 0 → Z) : sampleLikelihood p z = 1 := by
  simp [sampleLikelihood]

example {Z : Type*} [Fintype Z] (p : Z → ℝ) (x : Z) :
    (shannonWord p x).length = shannonSize p x := by
  simp [shannonWord]

example : ghzConstrained (fun _ => 0) := by
  exact Or.inl rfl

end DefinitionSanity

end QAlgorithms.Papers.Independent.Intakethird100.P80


