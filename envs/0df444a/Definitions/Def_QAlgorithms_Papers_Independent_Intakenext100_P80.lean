-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P80
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P80
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:57:33.632915+00:00
-- url     : https://prove2.me/theorems/2aea3a93-a185-49da-b2d9-5d68a8d5b54d
-- title:
--   Definitions for Proof of security of quantum key distribution with two-way classical communications
-- statement:
--   The objects the formalized statements of *Proof of security of quantum key distribution with two-way classical communications* (arXiv:quant-ph/0105121) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PauliRates`: PDF p.9, Definition 5: three nonidentity Pauli error probabilities. Validity is separately required by `IsPauliRates`.
--   - `IsPauliRates`: PDF p.9, Definition 5: exactly the probability-simplex conditions.
--   - `identityRate`: PDF pp.9,22, Eq.(22): probability of no Pauli error.
--   - `BellError`: PDF pp.10--11: Bell labels (bit,phase); no scalar Pauli phase is retained.
--   - `errorMass`: PDF pp.9--11: the normalized Bell-diagonal mixture's four weights.
--   - `eprBellAmplitude`: PDF pp.5,10: amplitude of (I tensor X^x Z^z)|Psi+>. The frozen Hadamard supplies the factor 1/sqrt(2) and the phase (-1)^(za).
--   - `eprBellProjectionWeight`: PDF p.22: Born weight of a (possibly subnormalized) surviving pair in the Bell state specified by `e`. Branches remain subnormalized.
--   - `bBranchAmplitude`: PDF pp.13,16: B-step branch on two independent input Bell states. Bilateral CNOT uses pair 1 as control; s,t are the two Z measurement outcomes on pair 2. The surviving pair has computational coordinates a,b.
--   - `bOutputMass`: PDF pp.16,22: joint probability of B acceptance and output Bell label. Only equal local target outcomes are retained; no polynomial update is used.
--   - `bSurvival`: PDF p.22, Eq.(18): survival probability per two-pair candidate block, computed by summing its accepted output probabilities.
--   - `pCorrection`: PDF pp.16,18, Figure 6: both relative X syndromes disagree exactly when Bob applies the phase correction to the surviving pair.
--   - `pBranchAmplitude`: PDF pp.16,18--19, Figure 6: P-step branch amplitude on three independent Bell states. The two CNOT controls are pairs 2,3 and their common target is pair 1; pairs 2,3 are then measured in X. The four Hadamard entries implement those measurements. Bob's conditional Z is included. There is no rejection based on either phase syndrome.
--   - `pOutputMass`: PDF pp.16,22: P-step output probability, summing every pair of local phase syndromes. The product of three weights enforces independent input pairs. The syndrome is discarded after correction, as on p.17.
--   - `bStep`: PDF pp.16,22: actual conditional B-step Pauli rates. On the probability simplex, survival is (1-b)^2+b^2 >= 1/2, where b=qX+qY.
--   - `pStep`: PDF pp.16,22: P-step rates. One pair survives each triple, with no phase-syndrome postselection or conditional normalization.
--   - `bitError`: PDF p.22, Eq.(23): measured bit-error probability pZ.
--   - `phaseError`: PDF p.22, Eq.(24): phase-error probability pX.
--   - `pauliErrorDifference`: PDF p.22, Eq.(25): Delta=qZ-qY.
--   - `PurificationStep`: PDF pp.16--17,22: the two possible purification rounds.
--   - `runSteps`: PDF pp.22--23: chronological finite step word, evaluated on the conditional Pauli distribution after each round; the empty word does nothing.
--   - `bb84Rates`: PDF pp.17,22: the full BB84-compatible IID family, with qY=a.
-- source:
--   Proof of security of quantum key distribution with two-way classical communications, arXiv:quant-ph/0105121v2, https://arxiv.org/abs/quant-ph/0105121v2

import Definitions.Def_QAlgorithms_Defs_Gates

/-!
Gottesman--Lo, arXiv:quant-ph/0105121v2, PDF pp.16,18,22--23.
Only the two statements listed in items.json are drafted here. Operational
QKD/security and asymmetric-CSS completion nodes are explicitly deferred.

The B/P maps below are evaluated from circuit amplitudes and the Born rule;
the closed error-rate polynomials are conclusions, not definitions. The Bell
label is (bit flip, phase flip), so I=(0,0), X=(1,0), Y=(1,1), Z=(0,1).
The Y representative differs from Y by an irrelevant scalar phase.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P80

open scoped ComplexConjugate

/-- PDF p.9, Definition 5: three nonidentity Pauli error probabilities.
Validity is separately required by `IsPauliRates`. -/
structure PauliRates where
  qX : ℝ
  qY : ℝ
  qZ : ℝ

/-- PDF p.9, Definition 5: exactly the probability-simplex conditions. -/
def IsPauliRates (q : PauliRates) : Prop :=
  0 ≤ q.qX ∧ 0 ≤ q.qY ∧ 0 ≤ q.qZ ∧ q.qX + q.qY + q.qZ ≤ 1

/-- PDF pp.9,22, Eq.(22): probability of no Pauli error. -/
def identityRate (q : PauliRates) : ℝ :=
  1 - q.qX - q.qY - q.qZ

/-- PDF pp.10--11: Bell labels (bit,phase); no scalar Pauli phase is retained. -/
abbrev BellError := Bool × Bool

/-- PDF pp.9--11: the normalized Bell-diagonal mixture's four weights. -/
def errorMass (q : PauliRates) (e : BellError) : ℝ :=
  if e.1 then (if e.2 then q.qY else q.qX)
  else (if e.2 then q.qZ else identityRate q)

/-- PDF pp.5,10: amplitude of (I tensor X^x Z^z)|Psi+>.
The frozen Hadamard supplies the factor 1/sqrt(2) and the phase (-1)^(za). -/
def eprBellAmplitude (e : BellError) (a b : Bool) : ℂ :=
  if b = xor a e.1 then hadamard e.2 a else 0

/-- PDF p.22: Born weight of a (possibly subnormalized) surviving pair
in the Bell state specified by `e`. Branches remain subnormalized. -/
def eprBellProjectionWeight (v : Bool → Bool → ℂ) (e : BellError) : ℝ :=
  Complex.normSq (∑ a : Bool, ∑ b : Bool,
    conj (eprBellAmplitude e a b) * v a b)

/-- PDF pp.13,16: B-step branch on two independent input Bell states.
Bilateral CNOT uses pair 1 as control; s,t are the two Z measurement
outcomes on pair 2. The surviving pair has computational coordinates a,b. -/
def bBranchAmplitude (e f : BellError) (s t a b : Bool) : ℂ :=
  eprBellAmplitude e a b * eprBellAmplitude f (xor s a) (xor t b)

/-- PDF pp.16,22: joint probability of B acceptance and output Bell label.
Only equal local target outcomes are retained; no polynomial update is used. -/
def bOutputMass (q : PauliRates) (o : BellError) : ℝ :=
  ∑ e : BellError, ∑ f : BellError,
    errorMass q e * errorMass q f *
      ∑ s : Bool, eprBellProjectionWeight (fun a b => bBranchAmplitude e f s s a b) o

/-- PDF p.22, Eq.(18): survival probability per two-pair candidate block,
computed by summing its accepted output probabilities. -/
def bSurvival (q : PauliRates) : ℝ :=
  ∑ o : BellError, bOutputMass q o

/-- PDF pp.16,18, Figure 6: both relative X syndromes disagree exactly
when Bob applies the phase correction to the surviving pair. -/
def pCorrection (s t : Bool × Bool) : Bool :=
  xor s.1 t.1 && xor s.2 t.2

/-- PDF pp.16,18--19, Figure 6: P-step branch amplitude on three independent
Bell states. The two CNOT controls are pairs 2,3 and their common target
is pair 1; pairs 2,3 are then measured in X. The four Hadamard entries
implement those measurements. Bob's conditional Z is included. There is
no rejection based on either phase syndrome. -/
def pBranchAmplitude (e f g : BellError) (s t : Bool × Bool) (a b : Bool) : ℂ :=
  (if pCorrection s t && b then (-1 : ℂ) else 1) *
    ∑ a2 : Bool, ∑ a3 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
      hadamard s.1 a2 * hadamard s.2 a3 *
        hadamard t.1 b2 * hadamard t.2 b3 *
        eprBellAmplitude e (xor (xor a a2) a3) (xor (xor b b2) b3) *
        eprBellAmplitude f a2 b2 * eprBellAmplitude g a3 b3

/-- PDF pp.16,22: P-step output probability, summing every pair of local
phase syndromes. The product of three weights enforces independent input
pairs. The syndrome is discarded after correction, as on p.17. -/
def pOutputMass (q : PauliRates) (o : BellError) : ℝ :=
  ∑ e : BellError, ∑ f : BellError, ∑ g : BellError,
    errorMass q e * errorMass q f * errorMass q g *
      ∑ s : Bool × Bool, ∑ t : Bool × Bool,
        eprBellProjectionWeight (pBranchAmplitude e f g s t) o

/-- PDF pp.16,22: actual conditional B-step Pauli rates. On the probability
simplex, survival is (1-b)^2+b^2 >= 1/2, where b=qX+qY. -/
def bStep (q : PauliRates) : PauliRates :=
  ⟨bOutputMass q (true, false) / bSurvival q,
   bOutputMass q (true, true) / bSurvival q,
   bOutputMass q (false, true) / bSurvival q⟩

/-- PDF pp.16,22: P-step rates. One pair survives each triple, with no
phase-syndrome postselection or conditional normalization. -/
def pStep (q : PauliRates) : PauliRates :=
  ⟨pOutputMass q (true, false), pOutputMass q (true, true),
   pOutputMass q (false, true)⟩

/-- PDF p.22, Eq.(23): measured bit-error probability pZ. -/
def bitError (q : PauliRates) : ℝ :=
  q.qX + q.qY

/-- PDF p.22, Eq.(24): phase-error probability pX. -/
def phaseError (q : PauliRates) : ℝ :=
  q.qY + q.qZ

/-- PDF p.22, Eq.(25): Delta=qZ-qY. -/
def pauliErrorDifference (q : PauliRates) : ℝ :=
  q.qZ - q.qY

/-- PDF pp.16--17,22: the two possible purification rounds. -/
inductive PurificationStep where
  | B
  | P
  deriving DecidableEq

/-- PDF pp.22--23: chronological finite step word, evaluated on the
conditional Pauli distribution after each round; the empty word does nothing. -/
def runSteps (steps : List PurificationStep) (q : PauliRates) : PauliRates :=
  steps.foldl (fun r s => match s with
    | .B => bStep r
    | .P => pStep r) q

/-- PDF pp.17,22: the full BB84-compatible IID family, with qY=a. -/
def bb84Rates (p a : ℝ) : PauliRates :=
  ⟨p - a, a, p - a⟩

/-- Sanity: no-error Bell state has zero amplitude on |01>. -/
example : eprBellAmplitude (false, false) false true = 0 := by
  simp [eprBellAmplitude]

/-- Sanity: its |00> amplitude is the normalized 1/sqrt(2). -/
example : eprBellAmplitude (false, false) false false = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rfl

/-- Sanity: noiseless B inputs cannot give unequal target outcomes when
the surviving computational coordinates are 00. -/
example : bBranchAmplitude (false, false) (false, false) false true false false = 0 := by
  simp [bBranchAmplitude, eprBellAmplitude]

/-- Sanity: a single phase syndrome disagreement never triggers correction. -/
example : pCorrection (false, false) (true, false) = false := by
  rfl

/-- Sanity: two phase syndrome disagreements trigger the surviving-pair Z. -/
example : pCorrection (false, false) (true, true) = true := by
  rfl

/-- Sanity: a word with zero rounds leaves every input distribution unchanged. -/
example (q : PauliRates) : runSteps [] q = q := by
  rfl

end QAlgorithms.Papers.Independent.Intakenext100.P80


