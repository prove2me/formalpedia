-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P14
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P14
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T00:17:40.927752+00:00
-- url     : https://prove2.me/theorems/5e32ef6b-01de-4689-ac56-080cf59a6ca4
-- title:
--   Definitions for Secure Identification and QKD in the Bounded-Quantum-Storage Model
-- statement:
--   The objects the formalized statements of *Secure Identification and QKD in the Bounded-Quantum-Storage Model* (arXiv:0708.2557) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pushMass`: PDF p.6: push forward a possibly subnormalized classical law.
--   - `guessingMass`: PDF p.6: average guessing probability, the sum of maxima of JOINT masses. The finite, nonempty maximum has no empty/unbounded-supremum default.
--   - `IsRetained`: PDF p.6: retained event mass, with fractional conditional event probabilities allowed. The event is deleted without renormalizing.
--   - `smoothGuess`: PDF p.6: minimum retained guessing probability. For epsilon >= 0 and normalized p the feasible set is nonempty and compact, so its infimum is attained. For epsilon >= 1 zero retention is feasible and the value is zero (entropy +infinity).
--   - `conditionMass`: PDF p.6: conditioning an actual probability law on an event. The zero-event branch is zero and is used only in identities with zero weight; all entropy uses below have positive conditioning probability.
--   - `blockMass`: PDF p.5: the classical probability of a CQ block.
--   - `cqPush`: PDF p.5: relabel classical registers and take their marginal.
--   - `markov`: PDF pp.5-6: Markov reconstruction, keeping the actual classical joint law. Zero-mass fibers contribute zero, including for subnormalized event blocks.
--   - `cqCondition`: PDF p.5: event conditioning with an arbitrary original-state version at mass zero.
--   - `andPassword`: PDF p.3: prescribed private-input maps for the passive AND reduction.
--   - `PassiveExecution`: PDF p.3: an honest identification execution's local views, including its common publicly announced decision. This is an execution kernel, not a security assumption on an arbitrary replacement functionality.
--   - `PassiveEqualitySecurity`: PDF p.3: passive equality identification correctness and statistical privacy. Privacy compares unequal passwords for the other party at a fixed own input; accept/reject is retained in both views.
--   - `packedRestriction`: PDF p.10: pack a restriction in increasing coordinate order, then right-pad with zeros.
--   - `xorTag`: PDF p.10: xor of the two ell-bit tags.
--   - `StrongUniversal`: PDF p.7: strong universal-2, with an independent uniform seed.
--   - `QIDParameters`: PDF p.10: public Q-ID parameters. Code distance is a guaranteed minimum; seed alphabets are finite nonempty types supplied at use sites.
--   - `qidTag`: PDF p.10, steps 3-6: the exact tag computed from the packed restriction.
--   - `bb84Probability`: PDF pp.4,10: Born probability for measuring an encoded product state.
--   - `honestAcceptance`: PDF p.10, complete honest execution of steps 1-6. Uniform independent x,theta,f,g are averaged; xprime is drawn using the Born measurement law.
--   - `ServerAttack`: PDF p.10, Prop.3.4: arbitrary password-independent server strategy. Only the checkpoint quantum register is bounded. Classical Y, final E, and all computation are unrestricted; the post-revelation map chooses g adaptively.
--   - `serverOutput`: PDF pp.10-11: actual Q-ID output against this server, retaining the full classical history (theta,f,y,g,z). No map has the unknown password as an input.
--   - `markovRight`: PDF pp.5-6,8: Markov reconstruction with the transcript H in the quantum observer's side of the partition. The transcript is NOT discarded.
--   - `IsGuessExtension`: PDF p.8: a classical guess extension of the actual output, with independence of the password; every register and quantum block is preserved when the extra guess is discarded.
--   - `GuessSecrecy`: PDF p.8, Definitions 3.2/3.3: compare the conditioned actual state to its OWN Markov reconstruction, retaining the final announced decision.
--   - `HasIndependentGuess`: PDF p.8, Definition 3.2: the existential independent-guess witness is an extension of the actual protocol output, not a new assumed output law.
--   - `qidUncertaintyExponent`: PDF p.7: the corrected, PDF-verified uncertainty exponent. Only the source's security range 0 < lambda < 1/4 is used below.
--   - `UserAttack`: PDF pp.10-12: all operations before receiving g can be represented by a password-independent CQ ensemble of the transmitted register and retained R. The response instrument chooses an arbitrary tag or abort (none), after seeing g. A final channel may depend on the announced decision. There is no quantum-storage bound on R or E.
--   - `measuredResidual`: PDF p.10 step 2: unnormalized residual state on R after the honest server's actual measurement in the password code basis.
--   - `UserHistory`: PDF p.10: user attack transcript includes the final announced decision. The optional tag none is an abort and is always rejected.
--   - `userOutput`: PDF pp.10-12: complete original Q-ID execution against an arbitrary user. The honest server measures in c(w) before theta,f are revealed, and chooses g uniformly and independently. The user can process its state after receiving the announced decision. All attack operations are password independent.
--   - `ServerSecurity`: PDF p.8, Definition 3.3: the same independent guess supplies exact acceptance on equality, bounded acceptance on mismatch, and postdecision secrecy. The acceptance conditions use weighted events, so a zero-mass equality event adds no positivity assumption. Mismatch has mass at least 1/2 in Prop.3.5.
--   - `affineTag`: PDF p.15: the fixed binary coordinates of GF(2^N), followed by projection onto the first ell coordinates; the tag alphabet's additive group is GF(2^ell). Only its addition is used, so binary coordinate vectors give exactly that group.
--   - `keyMass`: PDF p.15: uniform independent key, with exactly field-degree N rather than the unrelated transmitted-qubit count.
--   - `classicalTagLaw`: PDF p.15: actual classical tag/key/side-information distribution.
--   - `classicalIdealTagLaw`: PDF p.15: ideal independent uniform tag, preserving the same key and Z law.
--   - `quantumTagLaw`: PDF p.15: the actual CQ tag/key/Z/E state. E depends only on X,Z, while the key is independent and uniform.
--   - `quantumIdealTagLaw`: PDF p.15: I/2^ell tensor rho_K tensor rho_ZE, with actual marginals.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, https://arxiv.org/abs/0708.2557v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P31
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05

/-!
Damgard, Fehr, Salvail and Schaffner, arXiv:0708.2557v3.
Accepted primitives supply finite classical laws, CQ blocks, BB84 vectors, and
rectangular instruments. Local definitions implement event-deletion smoothing,
CQ Markov reconstruction, and the six-step ideal-channel Q-ID execution.
All basis strings use false = computational, true = Hadamard.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P14

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)
open QAlgorithms.Papers.Independent.Gap48.P11 (blockMatrix cqDistance)
open QAlgorithms.Papers.Independent.Claimed50.P31 (bb84Vector)
open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.6: push forward a possibly subnormalized classical law. -/
def pushMass {S A : Type*} [Fintype S] (p : S → ℝ) (X : S → A) (a : A) : ℝ :=
  ∑ s, if X s = a then p s else 0

/-- PDF p.6: average guessing probability, the sum of maxima of JOINT masses.
The finite, nonempty maximum has no empty/unbounded-supremum default. -/
def guessingMass {S A B : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [Fintype B] (p : S → ℝ) (X : S → A) (Y : S → B) : ℝ :=
  ∑ b, Finset.univ.sup' Finset.univ_nonempty
    (fun a => pushMass p (fun s => (X s, Y s)) (a, b))

/-- PDF p.6: retained event mass, with fractional conditional event probabilities
allowed. The event is deleted without renormalizing. -/
def IsRetained {S : Type*} [Fintype S] (p r : S → ℝ) (epsilon : ℝ) : Prop :=
  (∀ s, 0 ≤ r s ∧ r s ≤ p s) ∧ 1 - epsilon ≤ ∑ s, r s

/-- PDF p.6: minimum retained guessing probability. For epsilon >= 0 and
normalized p the feasible set is nonempty and compact, so its infimum is attained.
For epsilon >= 1 zero retention is feasible and the value is zero (entropy +infinity). -/
def smoothGuess {S A B : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [Fintype B] (p : S → ℝ) (X : S → A) (Y : S → B) (epsilon : ℝ) : ℝ :=
  sInf {g : ℝ | ∃ r : S → ℝ, IsRetained p r epsilon ∧ g = guessingMass r X Y}

/-- PDF p.6: conditioning an actual probability law on an event.
The zero-event branch is zero and is used only in identities with zero weight;
all entropy uses below have positive conditioning probability. -/
def conditionMass {S : Type*} [Fintype S] (p : S → ℝ) (event : S → Prop) : S → ℝ :=
  fun s => if event s then p s / (∑ t, if event t then p t else 0) else 0

/-- PDF p.5: the classical probability of a CQ block. -/
def blockMass {C E : Type*} [Fintype E] (r : C → Matrix E E ℂ) (c : C) : ℝ :=
  (r c).trace.re

/-- PDF p.5: relabel classical registers and take their marginal. -/
def cqPush {C D E : Type*} [Fintype C] (r : C → Matrix E E ℂ) (f : C → D) :
    D → Matrix E E ℂ :=
  fun d => ∑ c, if f c = d then r c else 0

/-- PDF pp.5-6: Markov reconstruction, keeping the actual classical joint law.
Zero-mass fibers contribute zero, including for subnormalized event blocks. -/
def markov {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E]
    (r : (X × Y) → Matrix E E ℂ) : (X × Y) → Matrix E E ℂ :=
  fun xy => ((blockMass r xy / blockMass (cqPush r Prod.snd) xy.2 : ℝ) : ℂ) •
    cqPush r Prod.snd xy.2

/-- PDF p.5: event conditioning with an arbitrary original-state version at mass zero. -/
def cqCondition {C E : Type*} [Fintype C] [Fintype E]
    (r : C → Matrix E E ℂ) (event : C → Prop) : C → Matrix E E ℂ :=
  let p := ∑ c, if event c then blockMass r c else 0
  if 0 < p then fun c => if event c then ((p⁻¹ : ℝ) : ℂ) • r c else 0 else r

/-- Positive list length and inhabited fibers supply the tagged union's inhabitant.
This derived instance adds no hypothesis to Lemma 2.2. -/
local instance {m : ℕ} [NeZero m] {A : Fin m → Type*}
    [∀ i, Nonempty (A i)] : Nonempty (Sigma A) :=
  ⟨⟨0, Classical.choice (inferInstance : Nonempty (A 0))⟩⟩

/-- PDF p.3: prescribed private-input maps for the passive AND reduction. -/
def andPassword {W : Type*} (wzero wone : W) (b : Bool) : W :=
  if b then wone else wzero

/-- PDF p.3: an honest identification execution's local views, including
its common publicly announced decision. This is an execution kernel, not a
security assumption on an arbitrary replacement functionality. -/
structure PassiveExecution (W EA EB : Type*) where
  alice : W → W → (Bool → Matrix EA EA ℂ)
  bob : W → W → (Bool → Matrix EB EB ℂ)

/-- PDF p.3: passive equality identification correctness and statistical privacy.
Privacy compares unequal passwords for the other party at a fixed own input;
accept/reject is retained in both views. -/
def PassiveEqualitySecurity {W EA EB : Type*} [Fintype EA] [Fintype EB]
    (P : PassiveExecution W EA EB) (delta epsilon : ℝ) : Prop :=
  0 ≤ delta ∧ 0 ≤ epsilon ∧
  (∀ a b, QAlgorithms.IsDensityMatrix (blockMatrix (P.alice a b)) ∧
    QAlgorithms.IsDensityMatrix (blockMatrix (P.bob a b)) ∧
    (∀ t, blockMass (P.alice a b) t = blockMass (P.bob a b) t) ∧
    blockMass (P.bob a b) (decide (a = b)) ≥ 1 - delta) ∧
  (∀ a b c, b ≠ a → c ≠ a → cqDistance (P.alice a b) (P.alice a c) ≤ epsilon) ∧
  (∀ b a c, a ≠ b → c ≠ b → cqDistance (P.bob a b) (P.bob c b) ≤ epsilon)

/-- PDF p.10: pack a restriction in increasing coordinate order, then right-pad with zeros. -/
def packedRestriction {n : ℕ} (x theta c : QAlgorithms.Qubits n) : QAlgorithms.Qubits n :=
  fun j => (((List.finRange n).filter (fun i => theta i == c i)).map x).getD j.val false

/-- PDF p.10: xor of the two ell-bit tags. -/
def xorTag {ell : ℕ} (a b : QAlgorithms.Qubits ell) : QAlgorithms.Qubits ell :=
  fun i => xor (a i) (b i)

/-- PDF p.7: strong universal-2, with an independent uniform seed. -/
def StrongUniversal {I A B : Type*} [Fintype I] [Fintype B]
    (f : I → A → B) : Prop :=
  ∀ x y, x ≠ y → ∀ u v,
    ((Finset.univ.filter (fun i => f i x = u ∧ f i y = v)).card : ℝ) /
      Fintype.card I = ((Fintype.card B : ℝ) ^ 2)⁻¹

/-- PDF p.10: public Q-ID parameters. Code distance is a guaranteed minimum;
seed alphabets are finite nonempty types supplied at use sites. -/
structure QIDParameters (n ell m d : ℕ) (F G : Type*) [Fintype F] [Fintype G] where
  code : Fin m → QAlgorithms.Qubits n
  injective : Function.Injective code
  distance : ∀ a b, a ≠ b → d ≤ hammingDist (code a) (code b)
  hashF : F → QAlgorithms.Qubits n → QAlgorithms.Qubits ell
  hashG : G → Fin m → QAlgorithms.Qubits ell
  strongF : StrongUniversal hashF
  strongG : StrongUniversal hashG

/-- PDF p.10, steps 3-6: the exact tag computed from the packed restriction. -/
def qidTag {n ell m d : ℕ} {F G : Type*} [Fintype F] [Fintype G]
    (P : QIDParameters n ell m d F G) (w : Fin m)
    (x theta : QAlgorithms.Qubits n) (f : F) (g : G) : QAlgorithms.Qubits ell :=
  xorTag (P.hashF f (packedRestriction x theta (P.code w))) (P.hashG g w)

/-- PDF pp.4,10: Born probability for measuring an encoded product state. -/
def bb84Probability {n : ℕ} (x theta y c : QAlgorithms.Qubits n) : ℝ :=
  Complex.normSq (∑ t, conj (bb84Vector y c t) * bb84Vector x theta t)

/-- PDF p.10, complete honest execution of steps 1-6. Uniform independent
x,theta,f,g are averaged; xprime is drawn using the Born measurement law. -/
def honestAcceptance {n ell m d : ℕ} {F G : Type*} [Fintype F] [Fintype G]
    (P : QIDParameters n ell m d F G) (w : Fin m) : ℝ :=
  ((Fintype.card (QAlgorithms.Qubits n) : ℝ) ^ 2 * Fintype.card F * Fintype.card G)⁻¹ *
    ∑ x, ∑ theta, ∑ f, ∑ g, ∑ y,
      bb84Probability x theta y (P.code w) *
        (if qidTag P w x theta f g = qidTag P w y theta f g then 1 else 0)

/-- PDF p.10, Prop.3.4: arbitrary password-independent server strategy.
Only the checkpoint quantum register is bounded. Classical Y, final E, and
all computation are unrestricted; the post-revelation map chooses g adaptively. -/
structure ServerAttack (n ell q : ℕ) (F : Type*) (G Y E : Type)
    [Fintype F] [Fintype G] [Fintype Y] [Fintype E] where
  checkpoint : RectangularInstrument (QAlgorithms.Qubits n) (QAlgorithms.Qubits q) Y
  chooseG : QAlgorithms.Qubits n → F → Y → RectangularInstrument (QAlgorithms.Qubits q) E G
  finish : QAlgorithms.Qubits n → F → Y → G → QAlgorithms.Qubits ell →
    QAlgorithms.Superop E E
  finish_channel : ∀ theta f y g z, QAlgorithms.IsChannel (finish theta f y g z)

/-- PDF pp.10-11: actual Q-ID output against this server, retaining the full
classical history (theta,f,y,g,z). No map has the unknown password as an input. -/
def serverOutput {n ell m d q : ℕ} {F : Type*} {G Y E : Type}
    [Fintype F] [Fintype G] [Fintype Y] [Fintype E]
    (P : QIDParameters n ell m d F G) (W : Law (Fin m))
    (A : ServerAttack n ell q F G Y E) :
    (Fin m × (QAlgorithms.Qubits n × F × Y × G × QAlgorithms.Qubits ell)) → Matrix E E ℂ :=
  fun wh =>
    let w := wh.1
    let theta := wh.2.1
    let f := wh.2.2.1
    let y := wh.2.2.2.1
    let g := wh.2.2.2.2.1
    let z := wh.2.2.2.2.2
    ((W.prob w / ((Fintype.card (QAlgorithms.Qubits n) : ℝ) ^ 2 * Fintype.card F) : ℝ) : ℂ) •
      ∑ x, if z = qidTag P w x theta f g then
        A.finish theta f y g z
          (RectangularInstrument.branch (A.chooseG theta f y) g
            (RectangularInstrument.branch A.checkpoint y (QAlgorithms.pureDensity (bb84Vector x theta))))
      else 0

/-- PDF pp.5-6,8: Markov reconstruction with the transcript H in the
quantum observer's side of the partition. The transcript is NOT discarded. -/
def markovRight {W J H E : Type*} [Fintype W] [Fintype J]
    [Fintype H] [Fintype E] (r : ((W × J) × H) → Matrix E E ℂ) :
    ((W × J) × H) → Matrix E E ℂ :=
  fun c =>
    ((blockMass (cqPush r Prod.fst) c.1 /
      blockMass (cqPush r (fun c => c.1.2)) c.1.2 : ℝ) : ℂ) •
        cqPush r (fun c => (c.1.2, c.2)) (c.1.2, c.2)

/-- PDF p.8: a classical guess extension of the actual output, with
independence of the password; every register and quantum block is preserved
when the extra guess is discarded. -/
def IsGuessExtension {W J H E : Type*} [Fintype W] [Fintype J]
    [Fintype H] [Fintype E] (rho : (W × H) → Matrix E E ℂ)
    (ext : ((W × J) × H) → Matrix E E ℂ) : Prop :=
  QAlgorithms.IsDensityMatrix (blockMatrix ext) ∧
  cqPush ext (fun c => (c.1.1, c.2)) = rho ∧
  ∀ w j, blockMass (cqPush ext Prod.fst) (w, j) =
    blockMass (cqPush rho Prod.fst) w *
      blockMass (cqPush ext (fun c => c.1.2)) j

/-- PDF p.8, Definitions 3.2/3.3: compare the conditioned actual state
to its OWN Markov reconstruction, retaining the final announced decision. -/
def GuessSecrecy {W J H E : Type*} [Fintype W] [Fintype J]
    [Fintype H] [Fintype E] (ext : ((W × J) × H) → Matrix E E ℂ)
    (guessValue : J → Option W) (epsilon : ℝ) : Prop :=
  let r := cqCondition ext (fun c => some c.1.1 ≠ guessValue c.1.2)
  cqDistance r (markovRight r) ≤ epsilon

/-- PDF p.8, Definition 3.2: the existential independent-guess witness
is an extension of the actual protocol output, not a new assumed output law. -/
def HasIndependentGuess {W H E J : Type*} [Fintype W] [Fintype H]
    [Fintype E] [Fintype J] (rho : (W × H) → Matrix E E ℂ)
    (guessValue : J → Option W) (epsilon : ℝ) : Prop :=
  ∃ ext : ((W × J) × H) → Matrix E E ℂ,
    IsGuessExtension rho ext ∧ GuessSecrecy ext guessValue epsilon

/-- PDF p.7: the corrected, PDF-verified uncertainty exponent.
Only the source's security range 0 < lambda < 1/4 is used below. -/
def qidUncertaintyExponent (lambda : ℝ) : ℝ :=
  lambda ^ 2 * Real.logb 2 (Real.exp 1) / (32 * (2 - Real.logb 2 lambda) ^ 2)

/-- PDF pp.10-12: all operations before receiving g can be represented
by a password-independent CQ ensemble of the transmitted register and retained R.
The response instrument chooses an arbitrary tag or abort (none), after seeing g.
A final channel may depend on the announced decision. There is no
quantum-storage bound on R or E. -/
structure UserAttack (n ell : ℕ) (F G : Type*) (R E : Type)
    [Fintype F] [Fintype G] [Fintype R] [Fintype E] where
  prepared : (QAlgorithms.Qubits n × F) →
    Matrix (QAlgorithms.Qubits n × R) (QAlgorithms.Qubits n × R) ℂ
  normalized : QAlgorithms.IsDensityMatrix (blockMatrix prepared)
  respond : QAlgorithms.Qubits n → F → G →
    RectangularInstrument R E (Option (QAlgorithms.Qubits ell))
  finish : QAlgorithms.Qubits n → F → G → Option (QAlgorithms.Qubits ell) →
    Bool → QAlgorithms.Superop E E
  finish_channel : ∀ theta f g z accepted,
    QAlgorithms.IsChannel (finish theta f g z accepted)

/-- PDF p.10 step 2: unnormalized residual state on R after the honest
server's actual measurement in the password code basis. -/
def measuredResidual {n : ℕ} {R : Type*} (rho :
    Matrix (QAlgorithms.Qubits n × R) (QAlgorithms.Qubits n × R) ℂ)
    (y c : QAlgorithms.Qubits n) : Matrix R R ℂ :=
  fun r s => ∑ i, ∑ j,
    conj (bb84Vector y c i) * rho (i, r) (j, s) * bb84Vector y c j

/-- PDF p.10: user attack transcript includes the final announced decision.
The optional tag none is an abort and is always rejected. -/
abbrev UserHistory (n ell : ℕ) (F G : Type*) :=
  QAlgorithms.Qubits n × F × G × Option (QAlgorithms.Qubits ell) × Bool

/-- PDF pp.10-12: complete original Q-ID execution against an arbitrary user.
The honest server measures in c(w) before theta,f are revealed, and chooses g
uniformly and independently. The user can process its state after receiving the
announced decision. All attack operations are password independent. -/
def userOutput {n ell m d : ℕ} {F G : Type*} {R E : Type}
    [Fintype F] [Fintype G] [Fintype R] [Fintype E]
    (P : QIDParameters n ell m d F G) (W : Law (Fin m))
    (A : UserAttack n ell F G R E) :
    (Fin m × UserHistory n ell F G) → Matrix E E ℂ :=
  fun wh =>
    let w := wh.1
    let theta := wh.2.1
    let f := wh.2.2.1
    let g := wh.2.2.2.1
    let z := wh.2.2.2.2.1
    let accepted := wh.2.2.2.2.2
    ((W.prob w / Fintype.card G : ℝ) : ℂ) • ∑ y,
      if decide (z = some (qidTag P w y theta f g)) = accepted then
        A.finish theta f g z accepted
          (RectangularInstrument.branch (A.respond theta f g) z
            (measuredResidual (A.prepared (theta, f)) y (P.code w)))
      else 0

/-- PDF p.8, Definition 3.3: the same independent guess supplies exact
acceptance on equality, bounded acceptance on mismatch, and postdecision secrecy.
The acceptance conditions use weighted events, so a zero-mass equality event
adds no positivity assumption. Mismatch has mass at least 1/2 in Prop.3.5. -/
def ServerSecurity {n ell m : ℕ} {F G E : Type*}
    [Fintype F] [Fintype G] [Fintype E]
    (rho : (Fin m × UserHistory n ell F G) → Matrix E E ℂ) (epsilon : ℝ) : Prop :=
  ∃ ext : (((Fin m) × Option (Fin m)) × UserHistory n ell F G) → Matrix E E ℂ,
    IsGuessExtension rho ext ∧ GuessSecrecy ext id epsilon ∧
    (∑ c, if some c.1.1 = c.1.2 ∧ c.2.2.2.2.2 = false
      then blockMass ext c else 0) = 0 ∧
    (∑ c, if some c.1.1 ≠ c.1.2 ∧ c.2.2.2.2.2 = true
      then blockMass ext c else 0) ≤
      epsilon * (∑ c, if some c.1.1 ≠ c.1.2 then blockMass ext c else 0)

/-- PDF p.15: the fixed binary coordinates of GF(2^N), followed by projection
onto the first ell coordinates; the tag alphabet's additive group is GF(2^ell).
Only its addition is used, so binary coordinate vectors give exactly that group. -/
def affineTag {K : Type*} [Field K] [Algebra (ZMod 2) K] {N ell : ℕ}
    (coordinates : K ≃ₗ[ZMod 2] (Fin N → ZMod 2)) (hell : ell ≤ N)
    (key : K × (Fin ell → ZMod 2)) (x : K) : Fin ell → ZMod 2 :=
  fun i => coordinates (key.1 * x) (Fin.castLE hell i) + key.2 i

/-- PDF p.15: uniform independent key, with exactly field-degree N rather
than the unrelated transmitted-qubit count. -/
def keyMass {K : Type*} [Fintype K] (ell : ℕ) : ℝ :=
  ((Fintype.card K : ℝ) * (2 : ℝ) ^ ell)⁻¹

/-- PDF p.15: actual classical tag/key/side-information distribution. -/
def classicalTagLaw {K : Type*} {S : Type} {Z : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    [Fintype S] {N ell : ℕ}
    (coordinates : K ≃ₗ[ZMod 2] (Fin N → ZMod 2)) (hell : ell ≤ N)
    (p : Law S) (X : S → K) (z : S → Z) :
    ((Fin ell → ZMod 2) × (K × (Fin ell → ZMod 2)) × Z) → ℝ :=
  fun t => keyMass (K := K) ell * ∑ s,
    if t.1 = affineTag coordinates hell t.2.1 (X s) ∧ t.2.2 = z s then p.prob s else 0

/-- PDF p.15: ideal independent uniform tag, preserving the same key and Z law. -/
def classicalIdealTagLaw {K : Type*} {S : Type} {Z : Type*} [Fintype K] [Fintype S] (ell : ℕ)
    (p : Law S) (z : S → Z) :
    ((Fin ell → ZMod 2) × (K × (Fin ell → ZMod 2)) × Z) → ℝ :=
  fun t => ((2 : ℝ) ^ ell)⁻¹ * keyMass (K := K) ell * pushMass p.prob z t.2.2

/-- PDF p.15: the actual CQ tag/key/Z/E state. E depends only on X,Z,
while the key is independent and uniform. -/
def quantumTagLaw {K : Type*} {S : Type} {Z : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    [Fintype S] {N ell q : ℕ}
    (coordinates : K ≃ₗ[ZMod 2] (Fin N → ZMod 2)) (hell : ell ≤ N)
    (p : Law S) (X : S → K) (z : S → Z)
    (rho : K → Z → Matrix (QAlgorithms.Qubits q) (QAlgorithms.Qubits q) ℂ) :
    ((Fin ell → ZMod 2) × (K × (Fin ell → ZMod 2)) × Z) →
      Matrix (QAlgorithms.Qubits q) (QAlgorithms.Qubits q) ℂ :=
  fun t => ((keyMass (K := K) ell : ℝ) : ℂ) • ∑ s,
    if t.1 = affineTag coordinates hell t.2.1 (X s) ∧ t.2.2 = z s
    then (p.prob s : ℂ) • rho (X s) (z s) else 0

/-- PDF p.15: I/2^ell tensor rho_K tensor rho_ZE, with actual marginals. -/
def quantumIdealTagLaw {K : Type*} {S : Type} {Z : Type*} [Fintype K] [Fintype S] (ell : ℕ) {q : ℕ}
    (p : Law S) (X : S → K) (z : S → Z)
    (rho : K → Z → Matrix (QAlgorithms.Qubits q) (QAlgorithms.Qubits q) ℂ) :
    ((Fin ell → ZMod 2) × (K × (Fin ell → ZMod 2)) × Z) →
      Matrix (QAlgorithms.Qubits q) (QAlgorithms.Qubits q) ℂ :=
  fun t => ((((2 : ℝ) ^ ell)⁻¹ * keyMass (K := K) ell : ℝ) : ℂ) • ∑ s,
    if z s = t.2.2 then (p.prob s : ℂ) • rho (X s) (z s) else 0

example (a b : Bool) : andPassword a b true = b := rfl

/-- Retaining the full event is feasible at every nonnegative smoothing level. -/
example {S : Type} [Fintype S] (p : Law S)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) : IsRetained p.prob p.prob epsilon := by
  constructor
  · intro s
    exact ⟨p.nonneg s, le_rfl⟩
  · rw [p.total]
    linarith

/-- A zero event block has zero weighted Markov reconstruction. -/
example {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] :
    markov (0 : (X × Y) → Matrix E E ℂ) = 0 := by
  funext xy
  simp [markov, blockMass, cqPush]

example {C E : Type*} (r : C → Matrix E E ℂ) (c : C) (i j : E) :
    blockMatrix r (c, i) (c, j) = r c i j := by simp [blockMatrix]

example {S : Type*} [Fintype S] (p : S → ℝ) :
    conditionMass p (fun _ => False) = 0 := by
  funext s
  simp [conditionMass]

example (x theta : QAlgorithms.Qubits 0) : bb84Vector x theta (fun i => Fin.elim0 i) = 1 := by
  simp [bb84Vector]

example {K : Type*} [Field K] [Algebra (ZMod 2) K] {N ell : ℕ}
    (coordinates : K ≃ₗ[ZMod 2] (Fin N → ZMod 2)) (hell : ell ≤ N)
    (a : K) (b : Fin ell → ZMod 2) : affineTag coordinates hell (a, b) 0 = b := by
  funext i
  simp [affineTag]

example : Law Unit where
  prob := fun _ => 1
  nonneg := by intro a; norm_num
  total := by simp

example {I O J : Type} [Fintype I] [Fintype O] [Fintype J]
    (M : RectangularInstrument I J O) (o : O) : RectangularInstrument.branch M o 0 = 0 := by
  simp [RectangularInstrument.branch, QAlgorithms.krausApply]

example (x theta y : QAlgorithms.Qubits 1) :
    bb84Vector x theta y =
      if theta 0 then QAlgorithms.hadamard (y 0) (x 0)
      else if y 0 = x 0 then 1 else 0 := by
  simp [bb84Vector]

example {n : ℕ} (x theta c : QAlgorithms.Qubits n)
    (hnomatch : ∀ i, theta i ≠ c i) : packedRestriction x theta c = fun _ => false := by
  funext j
  have hempty : (List.finRange n).filter (fun i => theta i == c i) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    simp [hnomatch i]
  simp [packedRestriction, hempty]

end QAlgorithms.Papers.Independent.Intakenext100.P14


