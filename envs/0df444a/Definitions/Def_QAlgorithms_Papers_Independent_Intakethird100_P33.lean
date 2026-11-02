-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P33
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P33
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:47:47.063661+00:00
-- url     : https://prove2.me/theorems/d33e0679-33bb-4a45-830a-5513869115f1
-- title:
--   Definitions for Towards practical and fast Quantum Cryptography
-- statement:
--   The objects the formalized statements of *Towards practical and fast Quantum Cryptography* (arXiv:quant-ph/0411022) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `dataState`: PDF p.2, (4)-(5): perfect blocking and a common zero phase, after attenuation. False is logical zero, with the occupied early bin.
--   - `OpticalPOVM`: PDF p.2, II.B: reuse the accepted full-Fock finite-outcome POVM. Positive finite coefficient forms and their identity sum make every effect a bounded positive contraction on the full oscillator Hilbert space.
--   - `Unambiguous`: PDF p.2: outcomes 0,1 are conclusive; outcome 2 is inconclusive.
--   - `discriminationSuccess`: PDF pp.2-3: success averaged over the two equal conditional bit priors.
--   - `countingOutcome`: PDF p.2: number counting, with vacuum and double-occupied sectors assigned inconclusive. The latter sector has zero weight on both source bit states.
--   - `monitoringOutput`: PDF p.2, (6)-(7): the coherent output at the selected interference time. The other times of the delayed interferometer are not identified with these modes.
--   - `opticalClick`: PDF p.2: ideal threshold click in one monitoring output, without dark counts.
--   - `sourceOccupation`: PDF pp.1-3: source symbols 0,1,2 mean logical 0, logical 1, and decoy. The Bool coordinate is false for the early bin and true for the late bin.
--   - `substitutedWord`: PDF p.3, II.D: the actual normalized number-basis vector after substitution.
--   - `splitCoefficients`: PDF pp.4-5, Fig.2: vacuum splitting on all number sectors. The output is indexed by Bob's two occupations and Eve's two occupations, in that order. The accepted vacuumAmplitude supplies the normalized multinomial coefficients; its NNReal port weights agree with t and 1-t on the theorem's domain.
--   - `splitState`: PDF pp.4-5: full Hilbert-space splitting. The theorem concludes Memℓp, normalization, and every coefficient, excluding the total fallback on source inputs.
--   - `splitBobDensity`: PDF p.5, (15): Bob's reduced density after basic splitting.
--   - `eveReadout`: PDF pp.4-5: Eve's ideal time-bin readout, with no claim of information optimality. No-click and double-occupied sectors have no conclusive bit label.
--   - `eveClickProbability`: PDF pp.4-5: exact ideal conclusive click probability from the retained state.
--   - `bobDistribution`: PDF p.5, (15): Bob's finite data readout, including independent trusted noise. K depends only on Bob's photon counts, never on Eve's result.
--   - `aliceBobJoint`: PDF p.5: uniform nondecoy Alice bit jointly with Bob's readout.
--   - `clickJoint`: PDF p.5, (15): actual joint distribution of Bob's output and Eve's inferred bit conditional on her click. Defined from the full split Born law, not by the claimed conditional independence. The theorem guards the denominator.
--   - `ratePolynomial`: PDF p.5, (16): only the displayed polynomial, not an exact secure key rate.
--   - `trainDensity`: PDF pp.1-3: the full product coherent source density in n two-bin blocks.
--   - `resendWeight`: PDF p.5, III.C.2: ideal detection followed by a localized single-photon resend. Each nonvacuum input detection is replaced by |1>, not by the incident coherent pulse.
--   - `interceptResend`: PDF p.5, Fig.3: the resulting localized-number mixture on the full train.
--   - `boundaryLeft`: PDF pp.5-6, Fig.3: the earlier source block of cross-boundary pair k.
--   - `boundaryRight`: PDF pp.5-6, Fig.3: the later source block of cross-boundary pair k.
--   - `boundaryTotal`: PDF pp.5-6: one nondemolition TOTAL-number measurement on the late/early pair. This does not measure the individual occupations.
--   - `crossCounting`: PDF pp.5-6, Fig.3 and endnote [13]: all successive disjoint cross-boundary pairs are counted. Only coherences between different total-number outcomes are removed. Unpaired outer endpoint bins are left untouched.
--   - `numberTerm`: PDF p.2, II.C: mean input photon number, only used with summability certified.
--   - `coherenceTerm`: PDF pp.2,5-6: the normally ordered coherence <a_i^dagger a_j>. The guard on p_j prevents truncated subtraction from creating a vacuum term.
--   - `FinitePairMoments`: PDF pp.2,5-6: convergence of the means and cross term used by the monitor.
--   - `monitorFlux`: PDF p.2, (6)-(7): intrinsic mean output flux at the selected interference slot. The divisor 4 is the square of the amplitude divisor 2.
--   - `opticalVisibility`: PDF pp.5-6, (21),(23): intrinsic optical contrast, used only at positive summed flux. It is not a raw dark-count click fraction.
--   - `printedSignal`: PDF p.7, endnote [6]: the eight signal coefficients in the PRINTED table. Pattern order is 00,01,10,11; the two port columns are DM1,DM2.
--   - `printedCount`: PDF pp.4,7: first-order table count, not an exact coherent click law.
-- source:
--   Towards practical and fast Quantum Cryptography, arXiv:quant-ph/0411022v1, https://arxiv.org/abs/quant-ph/0411022v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

/-!
Gisin et al., arXiv:quant-ph/0411022v1. Full number bases, no photon cutoff.
The exact optical assertions and the displayed polynomial calculation are separate
from the operational security claims deferred in HARD.md. Photon flux visibility
is intrinsic optical contrast, with no dark-count contribution. Equal conditional
bit priors apply after decoy removal. Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P33

open scoped BigOperators ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)
open QAlgorithms.Papers.Independent.Support50.P48 (vacuumAmplitude)
open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM realFockTracePair)
open QAlgorithms.Papers.Independent.Dependency50.P34
  (TwoModeFock fockKet photonMean)
open QAlgorithms.Papers.Independent.Frontier18.P14
  (coherentPair coherentPairCoefficients)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.2, (4)-(5): perfect blocking and a common zero phase, after attenuation.
False is logical zero, with the occupied early bin. -/
def dataState (x : ℝ) (bit : Bool) : TwoModeFock :=
  if bit then coherentPair 0 (Real.sqrt x : ℂ)
  else coherentPair (Real.sqrt x : ℂ) 0

/-- PDF p.2, II.B: reuse the accepted full-Fock finite-outcome POVM.
Positive finite coefficient forms and their identity sum make every effect a
bounded positive contraction on the full oscillator Hilbert space. -/
abbrev OpticalPOVM (O : Type) [Fintype O] := FockPOVM (ℕ × ℕ) O

/-- PDF p.2: outcomes 0,1 are conclusive; outcome 2 is inconclusive. -/
def Unambiguous (M : OpticalPOVM (Fin 3)) (x : ℝ) : Prop :=
  realFockTracePair (rankOne (dataState x false)) (M.effect 1) = 0 ∧ realFockTracePair (rankOne (dataState x true)) (M.effect 0) = 0

/-- PDF pp.2-3: success averaged over the two equal conditional bit priors. -/
def discriminationSuccess (M : OpticalPOVM (Fin 3)) (x : ℝ) : ℝ :=
  (realFockTracePair (rankOne (dataState x false)) (M.effect 0) + realFockTracePair (rankOne (dataState x true)) (M.effect 1)) / 2

/-- PDF p.2: number counting, with vacuum and double-occupied sectors assigned
inconclusive. The latter sector has zero weight on both source bit states. -/
def countingOutcome (nm : ℕ × ℕ) : Fin 3 :=
  if 0 < nm.1 ∧ nm.2 = 0 then 0
  else if nm.1 = 0 ∧ 0 < nm.2 then 1 else 2

example : countingOutcome (0, 0) = 2 := by simp [countingOutcome]

example : countingOutcome (1, 0) = 0 := by simp [countingOutcome]

/-- PDF p.2, (6)-(7): the coherent output at the selected interference time.
The other times of the delayed interferometer are not identified with these modes. -/
def monitoringOutput (a b : ℂ) : TwoModeFock :=
  coherentPair (Complex.I * (a + b) / 2) ((-a + b) / 2)

/-- PDF p.2: ideal threshold click in one monitoring output, without dark counts. -/
def opticalClick (v : TwoModeFock) (port : Fin 2) : ℝ :=
  ∑' nm : ℕ × ℕ,
    if 0 < (if port = 0 then nm.1 else nm.2) then Complex.normSq (v nm) else 0

/-- PDF pp.1-3: source symbols 0,1,2 mean logical 0, logical 1, and decoy.
The Bool coordinate is false for the early bin and true for the late bin. -/
def sourceOccupation {n : ℕ} (w : Fin n → Fin 3) (j : Fin n × Bool) : ℕ :=
  if w j.1 = 0 then (if j.2 then 0 else 1)
  else if w j.1 = 1 then (if j.2 then 1 else 0) else 1

/-- PDF p.3, II.D: the actual normalized number-basis vector after substitution. -/
def substitutedWord {n : ℕ} (w : Fin n → Fin 3) : Hilbert ((Fin n × Bool) → ℕ) :=
  lp.single 2 (sourceOccupation w) 1

example : sourceOccupation (fun _ : Fin 1 => (0 : Fin 3)) (0, false) = 1 := by
  simp [sourceOccupation]

example : sourceOccupation (fun _ : Fin 1 => (0 : Fin 3)) (0, true) = 0 := by
  simp [sourceOccupation]

/-- PDF pp.4-5, Fig.2: vacuum splitting on all number sectors. The output is
indexed by Bob's two occupations and Eve's two occupations, in that order.
The accepted vacuumAmplitude supplies the normalized multinomial coefficients;
its NNReal port weights agree with t and 1-t on the theorem's domain. -/
def splitCoefficients (t : ℝ) (v : TwoModeFock)
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℂ :=
  v (z.1.1 + z.2.1, z.1.2 + z.2.2) *
    (vacuumAmplitude (fun b : Bool => Real.toNNReal (if b then 1 - t else t))
      (fun b : Bool => if b then z.2.1 else z.1.1) (z.1.1 + z.2.1) : ℂ) *
    (vacuumAmplitude (fun b : Bool => Real.toNNReal (if b then 1 - t else t))
      (fun b : Bool => if b then z.2.2 else z.1.2) (z.1.2 + z.2.2) : ℂ)

/-- PDF pp.4-5: full Hilbert-space splitting. The theorem concludes Memℓp,
normalization, and every coefficient, excluding the total fallback on source inputs. -/
def splitState (t : ℝ) (v : TwoModeFock) : Hilbert ((ℕ × ℕ) × (ℕ × ℕ)) :=
  if h : Memℓp (splitCoefficients t v) 2 then ⟨splitCoefficients t v, h⟩ else 0

/-- PDF p.5, (15): Bob's reduced density after basic splitting. -/
def splitBobDensity (t : ℝ) (v : TwoModeFock) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun p q => ∑' e : ℕ × ℕ, splitState t v (p, e) * star (splitState t v (q, e))

/-- PDF pp.4-5: Eve's ideal time-bin readout, with no claim of information
optimality. No-click and double-occupied sectors have no conclusive bit label. -/
def eveReadout (nm : ℕ × ℕ) : Option Bool :=
  if 0 < nm.1 ∧ nm.2 = 0 then some false
  else if nm.1 = 0 ∧ 0 < nm.2 then some true else none

/-- PDF pp.4-5: exact ideal conclusive click probability from the retained state. -/
def eveClickProbability (mu t : ℝ) : ℝ :=
  ∑' e : ℕ × ℕ, if eveReadout e = some false then
    Complex.normSq (dataState (mu * (1 - t)) false e) else 0

/-- PDF p.5, (15): Bob's finite data readout, including independent trusted noise.
K depends only on Bob's photon counts, never on Eve's result. -/
def bobDistribution {O : Type} (K : (ℕ × ℕ) → O → ℝ)
    (mu t : ℝ) (bit : Bool) (o : O) : ℝ :=
  ∑' p : ℕ × ℕ, Complex.normSq (dataState (mu * t) bit p) * K p o

/-- PDF p.5: uniform nondecoy Alice bit jointly with Bob's readout. -/
def aliceBobJoint {O : Type} (K : (ℕ × ℕ) → O → ℝ)
    (mu t : ℝ) (o : O) (bit : Bool) : ℝ := bobDistribution K mu t bit o / 2

/-- PDF p.5, (15): actual joint distribution of Bob's output and Eve's inferred
bit conditional on her click. Defined from the full split Born law, not by the
claimed conditional independence. The theorem guards the denominator. -/
def clickJoint {O : Type} (K : (ℕ × ℕ) → O → ℝ)
    (mu t : ℝ) (o : O) (e : Bool) : ℝ :=
  (∑ bit : Bool, ∑' z : (ℕ × ℕ) × (ℕ × ℕ),
    if eveReadout z.2 = some e then
      Complex.normSq (splitState t (dataState mu bit) z) * K z.1 o else 0) /
    (2 * eveClickProbability mu t)

example : eveReadout (0, 0) = none := by simp [eveReadout]

example : splitCoefficients 1 (fockKet 1 0) ((1, 0), (0, 0)) = 1 := by
  norm_num [splitCoefficients, vacuumAmplitude, fockKet]

/-- PDF p.5, (16): only the displayed polynomial, not an exact secure key rate. -/
def ratePolynomial (t tB eta f mu : ℝ) : ℝ :=
  mu * t * tB * eta * (1 - f) * (1 - mu * (1 - t))

example (tB eta f mu : ℝ) : ratePolynomial 0 tB eta f mu = 0 := by
  simp [ratePolynomial]

/-- PDF pp.1-3: the full product coherent source density in n two-bin blocks. -/
def trainDensity {n : ℕ} (w : Fin n → Fin 3) (x : ℝ) :
    Matrix ((Fin n × Bool) → ℕ) ((Fin n × Bool) → ℕ) ℂ :=
  fun p q =>
    (∏ j : Fin n × Bool,
      coherentCoefficient (if sourceOccupation w j = 0 then 0 else (Real.sqrt x : ℂ)) (p j)) *
    star (∏ j : Fin n × Bool,
      coherentCoefficient (if sourceOccupation w j = 0 then 0 else (Real.sqrt x : ℂ)) (q j))

/-- PDF p.5, III.C.2: ideal detection followed by a localized single-photon resend.
Each nonvacuum input detection is replaced by |1>, not by the incident coherent pulse. -/
def resendWeight (x : ℝ) (occupied : Bool) (m : ℕ) : ℝ :=
  let z := if occupied then x else 0
  if m = 0 then Real.exp (-z) else if m = 1 then 1 - Real.exp (-z) else 0

/-- PDF p.5, Fig.3: the resulting localized-number mixture on the full train. -/
def interceptResend {n : ℕ} (w : Fin n → Fin 3) (x : ℝ) :
    Matrix ((Fin n × Bool) → ℕ) ((Fin n × Bool) → ℕ) ℂ :=
  fun p q => if p = q then
    (∏ j : Fin n × Bool, resendWeight x (decide (sourceOccupation w j = 1)) (p j) : ℝ)
    else 0

/-- PDF pp.5-6, Fig.3: the earlier source block of cross-boundary pair k. -/
def boundaryLeft {n : ℕ} (k : Fin (n - 1)) : Fin n := ⟨k.val, by omega⟩

/-- PDF pp.5-6, Fig.3: the later source block of cross-boundary pair k. -/
def boundaryRight {n : ℕ} (k : Fin (n - 1)) : Fin n := ⟨k.val + 1, by omega⟩

/-- PDF pp.5-6: one nondemolition TOTAL-number measurement on the late/early pair.
This does not measure the individual occupations. -/
def boundaryTotal {n : ℕ} (p : (Fin n × Bool) → ℕ) (k : Fin (n - 1)) : ℕ :=
  p (boundaryLeft k, true) + p (boundaryRight k, false)

/-- PDF pp.5-6, Fig.3 and endnote [13]: all successive disjoint cross-boundary
pairs are counted. Only coherences between different total-number outcomes are
removed. Unpaired outer endpoint bins are left untouched. -/
def crossCounting {n : ℕ} (w : Fin n → Fin 3) (x : ℝ) :
    Matrix ((Fin n × Bool) → ℕ) ((Fin n × Bool) → ℕ) ℂ :=
  fun p q => if ∀ k : Fin (n - 1), boundaryTotal p k = boundaryTotal q k then
    trainDensity w x p q else 0

/-- PDF p.2, II.C: mean input photon number, only used with summability certified. -/
def numberTerm {J : Type} (rho : Matrix (J → ℕ) (J → ℕ) ℂ) (i : J)
    (p : J → ℕ) : ℝ := (p i : ℝ) * (rho p p).re

/-- PDF pp.2,5-6: the normally ordered coherence <a_i^dagger a_j>.
The guard on p_j prevents truncated subtraction from creating a vacuum term. -/
def coherenceTerm {J : Type} [DecidableEq J]
    (rho : Matrix (J → ℕ) (J → ℕ) ℂ) (i j : J) (p : J → ℕ) : ℂ :=
  if i = j then (p i : ℂ) * rho p p else if p j = 0 then 0 else
    (Real.sqrt (((p i : ℝ) + 1) * (p j : ℝ)) : ℂ) *
      rho p (Function.update (Function.update p i (p i + 1)) j (p j - 1))

/-- PDF pp.2,5-6: convergence of the means and cross term used by the monitor. -/
def FinitePairMoments {J : Type} [DecidableEq J]
    (rho : Matrix (J → ℕ) (J → ℕ) ℂ) (i j : J) : Prop :=
  Summable (numberTerm rho i) ∧ Summable (numberTerm rho j) ∧
    Summable (coherenceTerm rho i j)

/-- PDF p.2, (6)-(7): intrinsic mean output flux at the selected interference
slot. The divisor 4 is the square of the amplitude divisor 2. -/
def monitorFlux {J : Type} [DecidableEq J]
    (rho : Matrix (J → ℕ) (J → ℕ) ℂ) (i j : J) (port : Fin 2) : ℝ :=
  ((∑' p, numberTerm rho i p) + (∑' p, numberTerm rho j p) +
    (if port = 0 then 2 else -2) * (∑' p, coherenceTerm rho i j p).re) / 4

/-- PDF pp.5-6, (21),(23): intrinsic optical contrast, used only at positive
summed flux. It is not a raw dark-count click fraction. -/
def opticalVisibility {J : Type} [DecidableEq J]
    (rho : Matrix (J → ℕ) (J → ℕ) ℂ) (i j : J) : ℝ :=
  (monitorFlux rho i j 0 - monitorFlux rho i j 1) /
    (monitorFlux rho i j 0 + monitorFlux rho i j 1)

example {n : ℕ} (w : Fin n → Fin 3) (x : ℝ) (p : (Fin n × Bool) → ℕ) :
    crossCounting w x p p = trainDensity w x p p := by simp [crossCounting]

example (x : ℝ) : resendWeight x false 1 = 0 := by simp [resendWeight]

/-- PDF p.7, endnote [6]: the eight signal coefficients in the PRINTED table.
Pattern order is 00,01,10,11; the two port columns are DM1,DM2. -/
def printedSignal (x : ℝ) (pattern : Fin 4) (port : Fin 2) : ℝ :=
  if pattern = 2 then (if port = 0 then x else 0)
  else if pattern = 1 then 0 else x / 4

/-- PDF pp.4,7: first-order table count, not an exact coherent click law. -/
def printedCount (x pd f : ℝ) (pattern : Fin 4) (port : Fin 2) : ℝ :=
  (printedSignal x pattern port + (1 - printedSignal x pattern port) * pd) * (1 - f) / 4

example (x : ℝ) : printedSignal x 0 0 = x / 4 := by simp [printedSignal]

/-! Definitional sanity checks. These do not prove any of the source results. -/

example (x : ℝ) : dataState x false = coherentPair (Real.sqrt x : ℂ) 0 := rfl

example (M : OpticalPOVM (Fin 3)) (x : ℝ) :
    Unambiguous M x ↔
      realFockTracePair (rankOne (dataState x false)) (M.effect 1) = 0 ∧ realFockTracePair (rankOne (dataState x true)) (M.effect 0) = 0 := Iff.rfl

example (M : OpticalPOVM (Fin 3)) (x : ℝ) :
    discriminationSuccess M x =
      (realFockTracePair (rankOne (dataState x false)) (M.effect 0) + realFockTracePair (rankOne (dataState x true)) (M.effect 1)) / 2 := rfl

example (a : ℂ) : monitoringOutput a a = coherentPair (Complex.I * (a + a) / 2) 0 := by
  simp [monitoringOutput]

example (port : Fin 2) : opticalClick 0 port = 0 := by simp [opticalClick]

example {n : ℕ} (w : Fin n → Fin 3) :
    substitutedWord w (sourceOccupation w) = 1 := by simp [substitutedWord]

example (t : ℝ) : splitState t 0 = 0 := by
  have h : splitCoefficients t 0 = 0 := by ext z; simp [splitCoefficients]
  unfold splitState
  split_ifs with hm
  · apply lp.ext
    funext z
    change splitCoefficients t 0 z = 0
    exact congrFun h z
  · rfl

example (t : ℝ) : splitBobDensity t 0 = 0 := by
  have h : splitState t 0 = 0 := by
    have hc : splitCoefficients t 0 = 0 := by ext z; simp [splitCoefficients]
    unfold splitState
    split_ifs with hm
    · apply lp.ext
      funext z
      change splitCoefficients t 0 z = 0
      exact congrFun hc z
    · rfl
  ext p q
  simp [splitBobDensity, h]

example {O : Type} (mu t : ℝ) (b : Bool) (o : O) :
    bobDistribution (fun (_ : ℕ × ℕ) (_ : O) => (0 : ℝ)) mu t b o = 0 := by
  simp [bobDistribution]

example {O : Type} [Fintype O] :
    QAlgorithms.mutualInfoBits (fun _ : O × Bool => 0) = 0 := by
  simp [QAlgorithms.mutualInfoBits]

example (x : ℝ) : resendWeight x true 2 = 0 := by simp [resendWeight]

example {n : ℕ} (k : Fin (n - 1)) : boundaryTotal (fun _ => 0) k = 0 := by
  simp [boundaryTotal]

example {J : Type} (i : J) (p : J → ℕ) :
    numberTerm (0 : Matrix (J → ℕ) (J → ℕ) ℂ) i p = 0 := by simp [numberTerm]

example {J : Type} [DecidableEq J] (i j : J) (p : J → ℕ) :
    coherenceTerm (0 : Matrix (J → ℕ) (J → ℕ) ℂ) i j p = 0 := by
  simp [coherenceTerm]

example {J : Type} [DecidableEq J] (i j : J) :
    FinitePairMoments (0 : Matrix (J → ℕ) (J → ℕ) ℂ) i j := by
  have hn (k : J) :
      numberTerm (0 : Matrix (J → ℕ) (J → ℕ) ℂ) k = (fun _ => 0) := by
    funext p
    simp [numberTerm]
  have hc : coherenceTerm (0 : Matrix (J → ℕ) (J → ℕ) ℂ) i j = (fun _ => 0) := by
    funext p
    simp [coherenceTerm]
  unfold FinitePairMoments
  rw [hn i, hn j, hc]
  exact ⟨summable_zero, summable_zero, summable_zero⟩

example (x pd : ℝ) (pattern : Fin 4) (port : Fin 2) :
    printedCount x pd 1 pattern port = 0 := by simp [printedCount]

end QAlgorithms.Papers.Independent.Intakethird100.P33


