-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41
-- name    : QAlgorithms_Papers_Independent_Intake100_P41
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:16:53.105783+00:00
-- url     : https://prove2.me/theorems/b2f96e68-9470-4d35-a917-747ae6574112
-- title:
--   Definitions for Key recycling in authentication
-- statement:
--   The objects the formalized statements of *Key recycling in authentication* (arXiv:1202.1229) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Tag`: PDF p.4, Definition 2: the m-bit tag alphabet, including the empty word.
--   - `uniformAverage`: PDF p.4: expectation under the uniform distribution on a finite seed set. Theorems require that the seed set be nonempty.
--   - `uniformProbability`: PDF p.4: probability of an event under a uniform finite seed.
--   - `authConditionedSeedAverage`: PDF p.8: uniform conditioning for the standard simulator. An impossible conditioning event falls back to the original uniform law; its real branch has zero probability. This also makes the simulator total at epsilon >= 1.
--   - `IsASU2`: PDF p.4, Definition 1: pair bound only, without marginal uniformity.
--   - `IsAXU2`: PDF p.4, Definition 2: the source's XOR universality convention.
--   - `paddedTag`: PDF pp.4,10--11: an actual tag with an independent OTP.
--   - `CausalTest`: PDF pp.7--9: all causal, terminating binary tests of an interactive system. There is no computational restriction or finite-alphabet restriction. Every finite observation prefix can be tested; private randomized tests are mixtures of these after their private randomness is fixed.
--   - `testValue`: PDF pp.7--9: deterministic execution of a causal test against a resource.
--   - `AuthInput`: PDF pp.7,10--16: the externally chosen input actions. For an asynchronous resource timeout is an inert action, conveying no synchronized event.
--   - `AuthOutput`: PDF pp.10--16: observations at all three interfaces. An empty deliveries list means no response; a list entry `none` is a rejection. Keys are emitted only on release, with Alice's and Bob's releases distinguished.
--   - `silent`: PDF pp.7,16: a step with no output is observably different from rejection.
--   - `AuthState`: PDF pp.10--16: send and submission orders have separate counters. The first submitted pair is retained for the standard simulator's rejection conditioning.
--   - `authInitialState`: PDF pp.7,10--16: initial protocol state; no message has yet been supplied.
--   - `authMachineStep`: PDF pp.10--16, Figures 7--11: explicit input/output scheduling. Submission i checks pad i even if send i has not occurred. Bob releases after n verifications or final timeout; Alice only at final timeout. Timeout emits one rejection per missing delivery and closes both interfaces. With recycling disabled it does nothing, so withholding an asynchronous message never creates a rejection. Excess calls to an already-used port are inert.
--   - `padAt`: PDF pp.13--14: the input reserve contains one hash key and exactly n pads. Out-of-range lookup returns the zero word; authMachineStep never uses that branch.
--   - `paddedStep`: PDF pp.10--16: real padded protocol, or authentic ideal channel with the fixed Figure 8 simulator. In the ideal execution tags are independent uniform pad-seed entries, and only an exact previously sent pair can be delivered. The simulator never uses the ideal hash key to choose its tags or decisions. The key is nevertheless visible to a test at the specified release steps.
--   - `HonestInput`: PDF p.8, Definition 4(i): honest users can choose messages and the final synchronization event, but have no malicious-channel submission interface.
--   - `honestStep`: PDF pp.8,11,14: attach the honest forwarding filter and hide Eve's tag port. The ideal version is the authentic channel's allow-delivery filter: its internal simulated tag is hidden and exactly forwarded, so no simulator output is exposed.
--   - `PaddedConstructionSecure`: PDF p.8, Definition 4, instantiated on the explicit padded executions. First clause: honest filtered distance zero. Second: the same fixed simulator works for every causal test, including tests that learn Bob's released key and then choose Alice's later inputs. A uniform seed in K × (Fin n → Tag m) is one uniform hash key and n mutually independent fresh pads, also independent of the test. Both clauses compare full executions, not just forgery probabilities.
--   - `standardStep`: PDF pp.7--9,17--18: standard authentication has one unpadded tag and exports no key. The ideal decision is exact pair equality, with impersonation rejected.
--   - `standardIdealValue`: PDF p.8: the one fixed standard-authentication simulator. At the first send it samples its own uniform hash key. If a submission was already rejected, it instead samples uniformly among keys rejecting that pair. Empty conditioning sets use the explicit harmless fallback in authConditionedSeedAverage. All other steps use exact-match delivery, and never leak the simulator's key.
--   - `StandardConstructionSecure`: PDF p.8, Definition 4, and pp.17--18, Lemma 9: full resource security for the actual unpadded execution and the fixed rejection-conditioned simulator. Honest filtered executions agree exactly; every adversarial causal test is bounded.
--   - `RoundView`: PDF pp.16--17: complete public transcript of one attempted substitution.
--   - `AdaptiveAttack`: PDF pp.16--17: a chosen-message attacker uses only public earlier rounds, including feedback, and the current intercepted pair. It has no secret-key argument. An existential attack is chosen before the uniform execution seed.
--   - `attackTrace`: PDF pp.16--17: execute n sequential chosen-message rounds with the same hash key and independent pads; append all messages, tags and verification bits.
--   - `corrupts`: PDF p.16: success means accepting a changed message in at least one round.
--   - `posteriorKey`: PDF pp.16--17: posterior law of the retained hash index, under a uniform joint key/pad seed. At any actually observed z its denominator is positive. Unobserved fibers have Lean's total value zero and contribute no entropy.
--   - `conditionalKeyEntropy`: PDF pp.16--17: classical conditional Shannon entropy in bits. Averaging fiber entropy over the original finite seed avoids requiring a finite message alphabet or a Fintype on all possible transcript values. The entropy is of K, not of the OTP seed P. The zero-mass convention is 0 log 0 = 0.
--   - `leakageBound`: PDF pp.16--17, Theorem 8: the second term is zero at n = |T|, as given by its zero-probability branch in the proof. It is not a logarithm of a sum.
--   - `prematureReleaseView`: PDF pp.3,10: the allowed subsequent application reveals k before Bob verifies the pending pair. The attacker gets the revealed key and intercepted pair, but not the OTP. This is a concrete known-key context for premature reuse.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, https://arxiv.org/abs/1202.1229v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

/-!
Portmann, arXiv:1202.1229v3. Concrete finite-randomness executions of the
classical authentication resources. Tests have unrestricted computation and
choose each input after seeing all preceding outputs. Fixing a test's private
coins gives such a deterministic causal test, so the universal bounds include
randomized environments by averaging. Prefix tests include stopping, suppressing
messages, and ignoring interfaces. The ideal executions include one fixed
simulator, defined before tests, rather than a security assumption in a record.
All new definitions are local to this paper. QKD reserve composition is deferred.
Compilation is pending the separate mechanical stage.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Definition 2: the m-bit tag alphabet, including the empty word. -/
abbrev Tag (m : ℕ) := Fin m → Bool

/-- PDF p.4: expectation under the uniform distribution on a finite seed set.
Theorems require that the seed set be nonempty. -/
def uniformAverage {S : Type*} [Fintype S] (f : S → ℝ) : ℝ :=
  (∑ s, f s) / (Fintype.card S : ℝ)

/-- PDF p.4: probability of an event under a uniform finite seed. -/
def uniformProbability {S : Type*} [Fintype S] (p : S → Prop) : ℝ :=
  ((Finset.univ.filter p).card : ℝ) / (Fintype.card S : ℝ)

/-- PDF p.8: uniform conditioning for the standard simulator. An impossible
conditioning event falls back to the original uniform law; its real branch has
zero probability. This also makes the simulator total at epsilon >= 1. -/
def authConditionedSeedAverage {S : Type*} [Fintype S] (p : S → Prop) (f : S → ℝ) : ℝ :=
  if (Finset.univ.filter p).Nonempty then
    (∑ s ∈ Finset.univ.filter p, f s) / ((Finset.univ.filter p).card : ℝ)
  else uniformAverage f

/-- PDF p.4, Definition 1: pair bound only, without marginal uniformity. -/
def IsASU2 {K X T : Type*} [Fintype K] [Fintype T]
    (h : K → X → T) (epsilon : ℝ) : Prop :=
  ∀ x y, x ≠ y → ∀ a b,
    uniformProbability (fun k => h k x = a ∧ h k y = b) ≤
      epsilon / (Fintype.card T : ℝ)

/-- PDF p.4, Definition 2: the source's XOR universality convention. -/
def IsAXU2 {K X : Type*} [Fintype K] {m : ℕ}
    (h : K → X → Tag m) (epsilon : ℝ) : Prop :=
  ∀ x y, x ≠ y → ∀ c,
    uniformProbability (fun k => xorWord (h k x) (h k y) = c) ≤ epsilon

/-- PDF pp.4,10--11: an actual tag with an independent OTP. -/
def paddedTag {K X : Type*} {m : ℕ} (h : K → X → Tag m)
    (k : K) (pad : Tag m) (x : X) : Tag m :=
  xorWord (h k x) pad

/-- PDF pp.7--9: all causal, terminating binary tests of an interactive system.
There is no computational restriction or finite-alphabet restriction. Every
finite observation prefix can be tested; private randomized tests are mixtures
of these after their private randomness is fixed. -/
inductive CausalTest (I O : Type*) where
  | stop : Bool → CausalTest I O
  | step : I → (O → CausalTest I O) → CausalTest I O

/-- PDF pp.7--9: deterministic execution of a causal test against a resource. -/
def testValue {S I O : Type*} (step : S → I → S × O) (s : S) :
    CausalTest I O → ℝ
  | .stop b => if b then 1 else 0
  | .step a next =>
    let result := step s a
    testValue step result.1 (next result.2)

/-- PDF pp.7,10--16: the externally chosen input actions. For an asynchronous
resource timeout is an inert action, conveying no synchronized event. -/
inductive AuthInput (X T : Type*) where
  | send : X → AuthInput X T
  | submit : X × T → AuthInput X T
  | timeout : AuthInput X T

/-- PDF pp.10--16: observations at all three interfaces. An empty deliveries
list means no response; a list entry `none` is a rejection. Keys are emitted
only on release, with Alice's and Bob's releases distinguished. -/
structure AuthOutput (K X T : Type*) where
  tag : Option (X × T)
  deliveries : List (Option X)
  aliceKey : Option K
  bobKey : Option K

/-- PDF pp.7,16: a step with no output is observably different from rejection. -/
def silent {K X T : Type*} : AuthOutput K X T :=
  ⟨none, [], none, none⟩

/-- PDF pp.10--16: send and submission orders have separate counters. The first
submitted pair is retained for the standard simulator's rejection conditioning. -/
structure AuthState (X T : Type*) where
  sent : List (X × T)
  received : ℕ
  firstSubmitted : Option (X × T)
  closed : Bool

/-- PDF pp.7,10--16: initial protocol state; no message has yet been supplied. -/
def authInitialState {X T : Type*} : AuthState X T :=
  ⟨[], 0, none, false⟩

/-- PDF pp.10--16, Figures 7--11: explicit input/output scheduling. Submission i
checks pad i even if send i has not occurred. Bob releases after n verifications
or final timeout; Alice only at final timeout. Timeout emits one rejection per
missing delivery and closes both interfaces. With recycling disabled it does
nothing, so withholding an asynchronous message never creates a rejection.
Excess calls to an already-used port are inert. -/
def authMachineStep {K X T : Type*} (n : ℕ) (recycle : Bool) (k : K)
    (makeTag : ℕ → X → T)
    (valid : AuthState X T → ℕ → X × T → Bool)
    (s : AuthState X T) (input : AuthInput X T) :
    AuthState X T × AuthOutput K X T :=
  if s.closed then (s, silent) else
  match input with
  | .send x =>
    if s.sent.length < n then
      let pair := (x, makeTag s.sent.length x)
      ({s with sent := s.sent ++ [pair]}, {(silent : AuthOutput K X T) with tag := some pair})
    else (s, silent)
  | .submit pair =>
    if s.received < n then
      let y := if valid s s.received pair then some pair.1 else none
      let released := if recycle = true ∧ s.received + 1 = n then some k else none
      ({ s with
          received := s.received + 1
          firstSubmitted := if s.received = 0 then some pair else s.firstSubmitted },
        { (silent : AuthOutput K X T) with
          deliveries := [y]
          bobKey := released })
    else (s, silent)
  | .timeout =>
    if recycle then
      ({ s with
          closed := true
          received := n },
        { (silent : AuthOutput K X T) with
          deliveries := List.replicate (n - s.received) none
          aliceKey := some k
          bobKey := if s.received < n then some k else none })
    else (s, silent)

/-- PDF pp.13--14: the input reserve contains one hash key and exactly n pads.
Out-of-range lookup returns the zero word; authMachineStep never uses that branch. -/
def padAt {m n : ℕ} (pads : Fin n → Tag m) (i : ℕ) : Tag m :=
  if hi : i < n then pads ⟨i, hi⟩ else fun _ => false

/-- PDF pp.10--16: real padded protocol, or authentic ideal channel with the
fixed Figure 8 simulator. In the ideal execution tags are independent uniform
pad-seed entries, and only an exact previously sent pair can be delivered.
The simulator never uses the ideal hash key to choose its tags or decisions.
The key is nevertheless visible to a test at the specified release steps. -/
def paddedStep {K X : Type*} {m n : ℕ} (ideal recycle : Bool)
    (h : K → X → Tag m) (k : K) (pads : Fin n → Tag m) :=
  authMachineStep n recycle k
    (fun i x => if ideal then padAt pads i else paddedTag h k (padAt pads i) x)
    (fun s i pair => if ideal then decide (s.sent[i]? = some pair)
      else decide (pair.2 = paddedTag h k (padAt pads i) pair.1))

/-- PDF p.8, Definition 4(i): honest users can choose messages and the final
synchronization event, but have no malicious-channel submission interface. -/
inductive HonestInput (X : Type*) where
  | send : X → HonestInput X
  | timeout : HonestInput X

/-- PDF pp.8,11,14: attach the honest forwarding filter and hide Eve's tag port.
The ideal version is the authentic channel's allow-delivery filter: its internal
simulated tag is hidden and exactly forwarded, so no simulator output is exposed. -/
def honestStep {K X T : Type*}
    (step : AuthState X T → AuthInput X T → AuthState X T × AuthOutput K X T)
    (s : AuthState X T) (input : HonestInput X) :
    AuthState X T × AuthOutput K X T :=
  match input with
  | .timeout => step s .timeout
  | .send x =>
    let first := step s (.send x)
    match first.2.tag with
    | none => first
    | some pair =>
      let second := step first.1 (.submit pair)
      (second.1, {second.2 with tag := none})

/-- PDF p.8, Definition 4, instantiated on the explicit padded executions.
First clause: honest filtered distance zero. Second: the same fixed simulator
works for every causal test, including tests that learn Bob's released key and
then choose Alice's later inputs. A uniform seed in K × (Fin n → Tag m) is one
uniform hash key and n mutually independent fresh pads, also independent of the
test. Both clauses compare full executions, not just forgery probabilities. -/
def PaddedConstructionSecure {K X : Type*} [Fintype K] {m n : ℕ}
    (h : K → X → Tag m) (recycle : Bool) (epsilon : ℝ) : Prop :=
  (∀ d : CausalTest (HonestInput X) (AuthOutput K X (Tag m)),
    uniformAverage (fun seed : K × (Fin n → Tag m) =>
      testValue (honestStep (paddedStep false recycle h seed.1 seed.2)) authInitialState d) =
    uniformAverage (fun seed : K × (Fin n → Tag m) =>
      testValue (honestStep (paddedStep true recycle h seed.1 seed.2)) authInitialState d)) ∧
  ∀ d : CausalTest (AuthInput X (Tag m)) (AuthOutput K X (Tag m)),
    |uniformAverage (fun seed : K × (Fin n → Tag m) =>
      testValue (paddedStep false recycle h seed.1 seed.2) authInitialState d) -
     uniformAverage (fun seed : K × (Fin n → Tag m) =>
      testValue (paddedStep true recycle h seed.1 seed.2) authInitialState d)| ≤ epsilon

/-- PDF pp.7--9,17--18: standard authentication has one unpadded tag and exports
no key. The ideal decision is exact pair equality, with impersonation rejected. -/
def standardStep {K X T : Type*} (ideal : Bool) (h : K → X → T) (k : K) :=
  authMachineStep 1 false k (fun _ x => h k x)
    (fun s i pair => if ideal then decide (s.sent[i]? = some pair)
      else decide (verifyTag h k pair = some pair.1))

/-- PDF p.8: the one fixed standard-authentication simulator. At the first send
it samples its own uniform hash key. If a submission was already rejected, it
instead samples uniformly among keys rejecting that pair. Empty conditioning
sets use the explicit harmless fallback in authConditionedSeedAverage. All other steps
use exact-match delivery, and never leak the simulator's key. -/
def standardIdealValue {K X T : Type*} [Fintype K] [Nonempty K]
    (h : K → X → T) (s : AuthState X T) :
    CausalTest (AuthInput X T) (AuthOutput K X T) → ℝ
  | .stop b => if b then 1 else 0
  | .step input next =>
    match input with
    | .send x =>
      if s.closed = false ∧ s.sent.length < 1 then
        authConditionedSeedAverage
          (fun k => match s.firstSubmitted with
            | none => True
            | some pair => h k pair.1 ≠ pair.2)
          (fun k =>
            let result := standardStep true h k s (.send x)
            standardIdealValue h result.1 (next result.2))
      else
        let result := standardStep true h (Classical.choice inferInstance) s input
        standardIdealValue h result.1 (next result.2)
    | _ =>
      let result := standardStep true h (Classical.choice inferInstance) s input
      standardIdealValue h result.1 (next result.2)

/-- PDF p.8, Definition 4, and pp.17--18, Lemma 9: full resource security for the
actual unpadded execution and the fixed rejection-conditioned simulator. Honest
filtered executions agree exactly; every adversarial causal test is bounded. -/
def StandardConstructionSecure {K X T : Type*} [Fintype K] [Nonempty K]
    (h : K → X → T) (epsilon : ℝ) : Prop :=
  (∀ d : CausalTest (HonestInput X) (AuthOutput K X T),
    uniformAverage (fun k : K => testValue (honestStep (standardStep false h k)) authInitialState d) =
    uniformAverage (fun k : K => testValue (honestStep (standardStep true h k)) authInitialState d)) ∧
  ∀ d : CausalTest (AuthInput X T) (AuthOutput K X T),
    |uniformAverage (fun k : K => testValue (standardStep false h k) authInitialState d) -
      standardIdealValue h authInitialState d| ≤ epsilon

/-- PDF pp.16--17: complete public transcript of one attempted substitution. -/
structure RoundView (X T : Type*) where
  message : X
  tag : T
  submitted : X × T
  accepted : Bool

/-- PDF pp.16--17: a chosen-message attacker uses only public earlier rounds,
including feedback, and the current intercepted pair. It has no secret-key
argument. An existential attack is chosen before the uniform execution seed. -/
structure AdaptiveAttack (X T : Type*) where
  message : List (RoundView X T) → X
  substitute : List (RoundView X T) → X × T → X × T

/-- PDF pp.16--17: execute n sequential chosen-message rounds with the same
hash key and independent pads; append all messages, tags and verification bits. -/
def attackTrace {K X : Type*} {m n : ℕ} (h : K → X → Tag m)
    (a : AdaptiveAttack X (Tag m)) (k : K) (pads : Fin n → Tag m) :
    List (RoundView X (Tag m)) :=
  (List.finRange n).foldl (fun history i =>
    let x := a.message history
    let t := paddedTag h k (pads i) x
    let pair := a.substitute history (x, t)
    history ++ [⟨x, t, pair, decide (pair.2 = paddedTag h k (pads i) pair.1)⟩]) []

/-- PDF p.16: success means accepting a changed message in at least one round. -/
def corrupts {X T : Type*} (z : List (RoundView X T)) : Prop :=
  ∃ r ∈ z, r.accepted = true ∧ r.submitted.1 ≠ r.message

/-- PDF pp.16--17: posterior law of the retained hash index, under a uniform
joint key/pad seed. At any actually observed z its denominator is positive.
Unobserved fibers have Lean's total value zero and contribute no entropy. -/
def posteriorKey {K P Z : Type*} [Fintype K] [Fintype P]
    (observe : K × P → Z) (z : Z) (k : K) : ℝ :=
  uniformProbability (fun seed : K × P => seed.1 = k ∧ observe seed = z) /
    uniformProbability (fun seed : K × P => observe seed = z)

/-- PDF pp.16--17: classical conditional Shannon entropy in bits. Averaging
fiber entropy over the original finite seed avoids requiring a finite message
alphabet or a Fintype on all possible transcript values. The entropy is of K,
not of the OTP seed P. The zero-mass convention is 0 log 0 = 0. -/
def conditionalKeyEntropy {K P Z : Type*} [Fintype K] [Fintype P]
    (observe : K × P → Z) : ℝ :=
  uniformAverage (fun seed : K × P =>
    -∑ k : K, posteriorKey observe (observe seed) k *
      Real.logb 2 (posteriorKey observe (observe seed) k))

/-- PDF pp.16--17, Theorem 8: the second term is zero at n = |T|, as given by
its zero-probability branch in the proof. It is not a logarithm of a sum. -/
def leakageBound (K : Type*) [Fintype K] (m n : ℕ) : ℝ :=
  Real.logb 2 ((Fintype.card K : ℝ) / (Fintype.card (Tag m) : ℝ)) +
    if n = Fintype.card (Tag m) then 0 else
      (1 - (n : ℝ) / (Fintype.card (Tag m) : ℝ)) *
        Real.logb 2 ((Fintype.card (Tag m) : ℝ) - (n : ℝ))

/-- PDF pp.3,10: the allowed subsequent application reveals k before Bob
verifies the pending pair. The attacker gets the revealed key and intercepted
pair, but not the OTP. This is a concrete known-key context for premature reuse. -/
def prematureReleaseView {K X : Type*} {m : ℕ} (h : K → X → Tag m)
    (a : K → X × Tag m → X × Tag m) (k : K) (pad : Tag m) (x : X) :
    K × RoundView X (Tag m) :=
  let t := paddedTag h k pad x
  let leakedKey := k
  let pair := a leakedKey (x, t)
  (leakedKey, ⟨x, t, pair, decide (pair.2 = paddedTag h k pad pair.1)⟩)

/-! Definition sanity checks only; no source theorem is proved here. -/

example (r : ℝ) : uniformAverage (fun _ : Unit => r) = r := by
  simp [uniformAverage]

example : uniformProbability (fun _ : Unit => True) = 1 := by
  simp [uniformProbability]

example (f : Unit → ℝ) : authConditionedSeedAverage (fun _ : Unit => False) f =
    uniformAverage f := by
  simp [authConditionedSeedAverage]

example : IsASU2 (fun (_ : Unit) (_ : Bool) => ()) 1 := by
  intro x y hxy a b
  have ha : () = a := Subsingleton.elim _ _
  have hb : () = b := Subsingleton.elim _ _
  simp [uniformProbability, ha, hb]

example : IsAXU2 (fun (_ : Unit) (_ : Bool) (_ : Fin 0) => false) 1 := by
  intro x y hxy c
  have hc : xorWord (fun _ : Fin 0 => false) (fun _ => false) = c :=
    Subsingleton.elim _ _
  simp [uniformProbability, hc]

example : paddedTag (fun (_ : Unit) (_ : Unit) (_ : Fin 1) => true)
    () (fun _ => false) () = (fun _ => true) := rfl

example {K X T : Type*} : (silent : AuthOutput K X T).deliveries = [] := rfl

example {X T : Type*} : (authInitialState : AuthState X T).received = 0 := rfl

example {S I O : Type*} (step : S → I → S × O) (s : S) :
    testValue step s (.stop true) = 1 := rfl

example {K X T : Type*} (n : ℕ) (recycle : Bool) (k : K)
    (makeTag : ℕ → X → T) (valid : AuthState X T → ℕ → X × T → Bool)
    (s : AuthState X T) (hs : s.closed = true) (i : AuthInput X T) :
    authMachineStep n recycle k makeTag valid s i = (s, silent) := by
  simp [authMachineStep, hs]

example {K X : Type*} {m : ℕ} (h : K → X → Tag m) (k : K)
    (pads : Fin 1 → Tag m) :
    (paddedStep false false h k pads authInitialState .timeout).2.deliveries = [] := rfl

example {K X T : Type*} [Fintype K] [Nonempty K] (h : K → X → T) :
    standardIdealValue h authInitialState (.stop false) = 0 := rfl

example {K X T : Type*} (h : K → X → T) (k : K) (x : X) :
    (standardStep false h k authInitialState (.submit (x, h k x))).2.deliveries = [some x] := by
  simp [standardStep, authMachineStep, authInitialState, silent, verifyTag]

example {K X T : Type*} (h : K → X → T) (k : K) (x : X) (t : T) :
    (standardStep true h k authInitialState (.submit (x, t))).2.deliveries = [none] := by
  simp [standardStep, authMachineStep, authInitialState, silent]

example {K X : Type*} {m : ℕ} (h : K → X → Tag m) (k : K) (pad : Tag m) (x : X) :
    (prematureReleaseView h (fun _ pair => pair) k pad x).2.accepted = true := by
  simp [prematureReleaseView]

example {K X : Type*} {m : ℕ} (h : K → X → Tag m)
    (a : AdaptiveAttack X (Tag m)) (k : K) (pads : Fin 0 → Tag m) :
    attackTrace h a k pads = [] := by
  simp [attackTrace, List.finRange]

example : conditionalKeyEntropy (fun _ : Unit × Unit => ()) = 0 := by
  simp [conditionalKeyEntropy, posteriorKey, uniformProbability, uniformAverage]

example (K : Type*) [Fintype K] (m : ℕ) :
    leakageBound K m (Fintype.card (Tag m)) =
      Real.logb 2 ((Fintype.card K : ℝ) / (Fintype.card (Tag m) : ℝ)) := by
  simp [leakageBound]

end QAlgorithms.Papers.Independent.Intake100.P41


