-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P76
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:06:55.163215+00:00
-- url     : https://prove2.me/theorems/0973c56b-e09e-4f32-9989-3a65df3331da
-- title:
--   Definitions for The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents
-- statement:
--   The objects the formalized statements of *The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents* (arXiv:1107.4148) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `observationEntropyBits`: PDF pp.3--4: entropy of a finite observation. The fiber formula avoids counting duplicate values; zero masses contribute zero (0 log 0 = 0).
--   - `condEntropy`: PDF p.3: conditional Shannon entropy in bits.
--   - `observationMutualInfoBits`: PDF p.3: mutual information under the actual joint law.
--   - `condInfo`: PDF p.4: conditional mutual information in bits.
--   - `renyiBits`: PDF p.16, (84): Renyi entropy of order 1+alpha, used for alpha>0.
--   - `DMBC`: PDF p.3, Section II-A: normalized discrete memoryless broadcast channel.
--   - `excitationJointMass`: PDF p.4, (10): the (S,X,Y,Z) law is fixed by p(s) and the channel.
--   - `obsS`: PDF p.3: sounding-symbol observation.
--   - `obsX`: PDF p.3: Alice's channel observation.
--   - `obsY`: PDF p.3: Bob's channel observation.
--   - `obsZ`: PDF p.3: Eve's channel observation.
--   - `AdmissibleCost`: PDF p.3: admissible positive cost, including implicit feasibility.
--   - `CostFeasibleInput`: PDF p.4: feasible single-letter input law.
--   - `SenderExcitedCode`: PDF pp.2--4: forward code with stochastic excitation and public fixed maps. Finite positive sizes include singleton message, public-message and key alphabets.
--   - `BlockSample`: PDF p.3: sample before applying the public and key functions.
--   - `blockMass`: PDF p.3: uniform M, stochastic encoder, then the product DMBC law.
--   - `keyA`: PDF p.3: Alice's key is computed from M and X^n only.
--   - `eveView`: PDF p.3: Eve observes Z^n and the public message.
--   - `keyDisagreementProbability`: PDF p.3, (2): error probability of the actual code.
--   - `publicKeyLeakage`: PDF p.3, (3): realized-public-code leakage, without annealed mixing.
--   - `generatedKeyEntropy`: PDF p.3, (4): actual key entropy; exact uniformity is not assumed.
--   - `CodeCost`: PDF p.3, (1): almost-sure cost on encoder support. None is the no-cost regime.
--   - `BoundedRanges`: PDF pp.3--4: exact ceiling convention for message, public and key alphabets. The key alphabet has the claimed rate R, as clarified on p.4 and in (58), rather than an unrelated existential rate. EntropyRate supplies near uniformity.
--   - `EntropyRate`: PDF p.3, (4): liminf entropy-rate bound in epsilon form.
--   - `WeakAchievable`: PDF pp.3--4, Definition 1: ONE sequence meets all three conditions.
--   - `senderExcitedCapacity`: PDF p.3, Definition 2: extended supremum avoids real-supremum defaults. The theorem identifies it with a finite, attained single-letter value.
--   - `logRate`: PDF p.4, (6)--(7): normalized negative log, with +infinity at zero.
--   - `TripleAchievable`: PDF p.4, Definition 3: the SAME sequence supplies entropy and BOTH exponents.
--   - `region`: PDF p.4, Definition 4: closure of operationally achievable triples.
--   - `StrongAchievable`: PDF p.4, Definition 5: strictly positive reliability AND secrecy exponents.
--   - `StrongAchievableAt`: PDF pp.3--4 and pp.8--9: strong achievability at specified public and excitation rates. One code sequence has exactly the three prescribed ceiling alphabet sizes and supplies the entropy condition and both positive exponents. Keeping RP and RM here is necessary for the rate-limited conclusions.
--   - `strongCapacity`: PDF p.8: supremal strongly achievable rate.
--   - `SenderExcitedDegraded`: PDF p.4, Definition 6: stochastic degradation preserves BOTH (S,X,Y) and (S,X,Z). The alternative coupling is p(x,y|s)d(z|y).
--   - `advantage`: PDF p.5, (12): information difference for Alice's pair (X,S).
--   - `upperObjective`: PDF p.5, (11): conditional-information upper-bound objective.
--   - `channelRate`: PDF p.5, (16): channel portion, not forced nonnegative.
--   - `residualSourceRate`: PDF p.5, (17): source portion, not forced nonnegative.
--   - `Aux`: PDF p.4, (10): normalized auxiliary kernels.
--   - `auxMass`: PDF p.4, (10): constructed joint law, with the fixed DMBC marginal.
--   - `auxObjective`: PDF p.4, (8): auxiliary conditional-information difference.
--   - `auxValues`: PDF p.4: feasible values over all finite auxiliary alphabets.
--   - `InteractiveCode`: PDF p.5: finite sequential discussion after excitation. All talk and key maps are fixed and public. Each message depends on the sender's observation, private seed and PRECEDING transcript only. A common finite alphabet and fixed schedule cover arbitrary finite discussions by padding with dummy messages. The base code supplies excitation and sizes; its forward maps are unused.
--   - `InteractiveSample`: PDF p.5: independent uniform Bob seed and the original excitation sample.
--   - `transcript`: PDF p.5: the full public transcript, constructed in temporal order.
--   - `interactiveMass`: PDF p.5: interactive sample law; Bob's private seed is independent.
--   - `interactiveKeyA`: PDF p.5: interactive Alice key.
--   - `interactiveError`: PDF p.5: key disagreement after the whole discussion.
--   - `interactiveLeakage`: PDF p.5: Eve sees Z^n and EVERY public message.
--   - `interactiveEntropy`: PDF p.5: the same entropy criterion for an interactive key.
--   - `InteractiveAchievable`: PDF p.5: weak achievability with multi-way public discussion. The key and excitation ranges remain exponentially bounded; the finite discussion itself is unrestricted, as in the stated multi-way upper bound.
--   - `interactiveCapacity`: PDF p.5: multi-way capacity uses its own operational protocol class.
--   - `xyMass`: PDF p.6: conditional X,Y mass given S.
--   - `yMass`: PDF p.6: conditional Y mass given S.
--   - `xzMass`: PDF p.6, (22): conditional X,Z mass given S.
--   - `reliabilityOne`: C18: printed (18), p.6, has an inner sum over (s,x) despite fixing s in the outer sum. Changed to sum only over x, exactly as (66), p.13, because this is the conditional-source moment given (y,s). Null rows have zero weight.
--   - `reliabilityTwo`: PDF pp.6,7,13, (19),(30),(67), corrected C19: sum first over output (X,Y), then input S inside the power. The printed reversed order conflicts with the expressly described channel S->(X,Y) and derivative in (30).
--   - `reliabilityThree`: PDF p.6, (20): hybrid joint-decoding event.
--   - `reliabilityExponent`: PDF p.6, (21): maximize separately, then take the minimum of three.
--   - `secrecyTrial`: PDF p.6, (22): omit null Z fibers explicitly.
--   - `secrecyExponent`: PDF p.6, (23): supremum over 0<alpha≤1.
--   - `innerRegion`: PDF p.6, (24): inner region for one common p(s) and auxiliary rate pair.
--   - `optimizedReliability`: PDF pp.9--10, (41): optimized reliability value.
--   - `inputOptimizedSecrecyExponent`: PDF p.10, (42): independently optimized secrecy value.
-- source:
--   The Sender-Excited Secret Key Agreement Model: Capacity, Reliability and Secrecy Exponents, arXiv:1107.4148v4, https://arxiv.org/abs/1107.4148v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

/-!
Statements from Chou--Tan--Draper, arXiv:1107.4148v4. Information is in bits.
All new definitions are paper-local, with complete bodies. Blocks have length n+1.
C18 and C19 are source corrections independently audited in moderation round 1.
Round 2 links the rate-limited code conclusions to their specified rates.
These repairs require fresh blind readbacks and a subsequent no-edit round.
Deferred nodes have no theorem. Compilation is pending batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P76

noncomputable section

open scoped BigOperators
open Filter Set

attribute [local instance] Classical.propDecidable

-- Exact pinned primitives, inspected at their definitions before reuse.
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

/-- PDF pp.3--4: entropy of a finite observation. The fiber formula avoids
counting duplicate values; zero masses contribute zero (0 log 0 = 0). -/
def observationEntropyBits {O A : Type*} [Fintype O] (p : O → ℝ) (a : O → A) : ℝ := by
  classical
  exact -∑ o, p o * Real.logb 2 (∑ t, if a t = a o then p t else 0)

/-- PDF p.3: conditional Shannon entropy in bits. -/
def condEntropy {O A B : Type*} [Fintype O] (p : O → ℝ)
    (a : O → A) (b : O → B) : ℝ :=
  observationEntropyBits p (fun o => (a o, b o)) - observationEntropyBits p b

/-- PDF p.3: mutual information under the actual joint law. -/
def observationMutualInfoBits {O A B : Type*} [Fintype O] (p : O → ℝ)
    (a : O → A) (b : O → B) : ℝ :=
  observationEntropyBits p a + observationEntropyBits p b - observationEntropyBits p (fun o => (a o, b o))

/-- PDF p.4: conditional mutual information in bits. -/
def condInfo {O A B C : Type*} [Fintype O] (p : O → ℝ)
    (a : O → A) (b : O → B) (c : O → C) : ℝ :=
  condEntropy p a c - condEntropy p a (fun o => (b o, c o))

/-- PDF p.16, (84): Renyi entropy of order 1+alpha, used for alpha>0. -/
def renyiBits {A : Type*} [Fintype A] (p : A → ℝ) (alpha : ℝ) : ℝ :=
  -(Real.logb 2 (∑ a, (p a) ^ (1 + alpha))) / alpha

/-- A one-point observation has zero entropy. -/
example : observationEntropyBits (fun _ : Unit => (1 : ℝ)) id = 0 := by
  simp [observationEntropyBits]

/-- A point mass has zero Renyi entropy. -/
example (alpha : ℝ) : renyiBits (fun _ : Unit => (1 : ℝ)) alpha = 0 := by
  simp [renyiBits]

variable {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
  [Nonempty S] [Nonempty X] [Nonempty Y] [Nonempty Z]

variable {n u w : ℕ}

/-- PDF p.3, Section II-A: normalized discrete memoryless broadcast channel. -/
structure DMBC (S X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z] where
  s_nonempty : Nonempty S
  x_nonempty : Nonempty X
  y_nonempty : Nonempty Y
  z_nonempty : Nonempty Z
  w : S → (X × Y × Z) → ℝ
  stochastic : IsStochastic w

/-- PDF p.4, (10): the (S,X,Y,Z) law is fixed by p(s) and the channel. -/
def excitationJointMass (W : DMBC S X Y Z) (p : S → ℝ) : (S × X × Y × Z) → ℝ :=
  fun o => p o.1 * W.w o.1 o.2

/-- PDF p.3: sounding-symbol observation. -/
def obsS (o : S × X × Y × Z) : S := o.1

/-- PDF p.3: Alice's channel observation. -/
def obsX (o : S × X × Y × Z) : X := o.2.1

/-- PDF p.3: Bob's channel observation. -/
def obsY (o : S × X × Y × Z) : Y := o.2.2.1

/-- PDF p.3: Eve's channel observation. -/
def obsZ (o : S × X × Y × Z) : Z := o.2.2.2

/-- PDF p.3: admissible positive cost, including implicit feasibility. -/
def AdmissibleCost (cost : S → ℝ) (Gamma : ℝ) : Prop :=
  0 < Gamma ∧ (∃ L : ℝ, ∀ s, 0 ≤ cost s ∧ cost s ≤ L) ∧
    ∃ p : S → ℝ, IsLaw p ∧ ∑ s, p s * cost s ≤ Gamma

/-- PDF p.4: feasible single-letter input law. -/
def CostFeasibleInput (cost : S → ℝ) (Gamma : ℝ) (p : S → ℝ) : Prop :=
  IsLaw p ∧ ∑ s, p s * cost s ≤ Gamma

/-- PDF pp.2--4: forward code with stochastic excitation and public fixed maps.
Finite positive sizes include singleton message, public-message and key alphabets. -/
structure SenderExcitedCode (S X Y : Type) [Fintype S] (n : ℕ) where
  messages : ℕ
  publicSize : ℕ
  keys : ℕ
  messages_pos : 0 < messages
  public_pos : 0 < publicSize
  keys_pos : 0 < keys
  encoder : Fin messages → (Fin n → S) → ℝ
  encoder_law : IsStochastic encoder
  publicMap : Fin messages → (Fin n → X) → Fin publicSize
  aliceKey : Fin messages → (Fin n → X) → Fin keys
  bobKey : (Fin n → Y) → Fin publicSize → Fin keys

/-- PDF p.3: sample before applying the public and key functions. -/
abbrev BlockSample (C : SenderExcitedCode S X Y n) :=
  Fin C.messages × (Fin n → S) × (Fin n → X) × (Fin n → Y) × (Fin n → Z)

/-- PDF p.3: uniform M, stochastic encoder, then the product DMBC law. -/
def blockMass (W : DMBC S X Y Z) (C : SenderExcitedCode S X Y n) :
    BlockSample (Z := Z) C → ℝ :=
  fun o => (C.messages : ℝ)⁻¹ * C.encoder o.1 o.2.1 *
    ∏ i, W.w (o.2.1 i) (o.2.2.1 i, o.2.2.2.1 i, o.2.2.2.2 i)

/-- PDF p.3: Alice's key is computed from M and X^n only. -/
def keyA (C : SenderExcitedCode S X Y n) (o : BlockSample (Z := Z) C) :=
  C.aliceKey o.1 o.2.2.1

/-- PDF p.3: Eve observes Z^n and the public message. -/
def eveView (C : SenderExcitedCode S X Y n) (o : BlockSample (Z := Z) C) :=
  (o.2.2.2.2, C.publicMap o.1 o.2.2.1)

/-- PDF p.3, (2): error probability of the actual code. -/
def keyDisagreementProbability (W : DMBC S X Y Z) (C : SenderExcitedCode S X Y n) : ℝ := by
  classical
  exact ∑ o, if keyA C o ≠ C.bobKey o.2.2.2.1 (C.publicMap o.1 o.2.2.1)
    then blockMass W C o else 0

/-- PDF p.3, (3): realized-public-code leakage, without annealed mixing. -/
def publicKeyLeakage (W : DMBC S X Y Z) (C : SenderExcitedCode S X Y n) : ℝ :=
  observationMutualInfoBits (blockMass W C) (keyA C) (eveView C)

/-- PDF p.3, (4): actual key entropy; exact uniformity is not assumed. -/
def generatedKeyEntropy (W : DMBC S X Y Z) (C : SenderExcitedCode S X Y n) : ℝ :=
  observationEntropyBits (blockMass W C) (keyA C)

/-- PDF p.3, (1): almost-sure cost on encoder support. None is the no-cost regime. -/
def CodeCost (cost : S → ℝ) (Gamma : Option ℝ) (C : SenderExcitedCode S X Y n) : Prop :=
  match Gamma with
  | none => True
  | some g => ∀ m s, 0 < C.encoder m s → (∑ i, cost (s i)) ≤ (n : ℝ) * g

/-- PDF pp.3--4: exact ceiling convention for message, public and key alphabets.
The key alphabet has the claimed rate R, as clarified on p.4 and in (58),
rather than an unrelated existential rate. EntropyRate supplies near uniformity. -/
def BoundedRanges (C : (n : ℕ) → SenderExcitedCode S X Y (n + 1)) (R : ℝ) : Prop :=
  ∃ rM rP : ℝ, 0 ≤ rM ∧ 0 ≤ rP ∧ ∀ n,
    (C n).messages = 2 ^ ⌈(n + 1 : ℝ) * rM⌉₊ ∧
    (C n).publicSize = 2 ^ ⌈(n + 1 : ℝ) * rP⌉₊ ∧
    (C n).keys = 2 ^ ⌈(n + 1 : ℝ) * R⌉₊

/-- PDF p.3, (4): liminf entropy-rate bound in epsilon form. -/
def EntropyRate (W : DMBC S X Y Z) (C : (n : ℕ) → SenderExcitedCode S X Y (n + 1))
    (R : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
    R - eps ≤ generatedKeyEntropy W (C n) / (n + 1 : ℕ)

/-- PDF pp.3--4, Definition 1: ONE sequence meets all three conditions. -/
def WeakAchievable (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma : Option ℝ)
    (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ C : (n : ℕ) → SenderExcitedCode S X Y (n + 1),
    BoundedRanges C R ∧ (∀ n, CodeCost cost Gamma (C n)) ∧ EntropyRate W C R ∧
    Tendsto (fun n => keyDisagreementProbability W (C n)) atTop (nhds 0) ∧
    Tendsto (fun n => publicKeyLeakage W (C n) / (n + 1 : ℕ)) atTop (nhds 0)

/-- PDF p.3, Definition 2: extended supremum avoids real-supremum defaults.
The theorem identifies it with a finite, attained single-letter value. -/
def senderExcitedCapacity (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma : Option ℝ) : EReal :=
  sSup {v | ∃ R : ℝ, WeakAchievable W cost Gamma R ∧ v = (R : EReal)}

/-- PDF p.4, (6)--(7): normalized negative log, with +infinity at zero. -/
def logRate (n : ℕ) (t : ℝ) : EReal :=
  if t = 0 then ⊤ else ((-Real.logb 2 t / (n + 1 : ℕ) : ℝ) : EReal)

/-- Zero error or leakage has infinite decay exponent. -/
example (n : ℕ) : logRate n 0 = ⊤ := by
  simp [logRate]

/-- PDF p.4, Definition 3: the SAME sequence supplies entropy and BOTH exponents. -/
def TripleAchievable (W : DMBC S X Y Z) (v : ℝ × ℝ × ℝ) : Prop :=
  0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧
    ∃ C : (n : ℕ) → SenderExcitedCode S X Y (n + 1), BoundedRanges C v.1 ∧
      EntropyRate W C v.1 ∧
      (v.2.1 : EReal) ≤ Filter.liminf (fun n => logRate n (keyDisagreementProbability W (C n))) atTop ∧
      (v.2.2 : EReal) ≤ Filter.liminf (fun n => logRate n (publicKeyLeakage W (C n))) atTop

/-- PDF p.4, Definition 4: closure of operationally achievable triples. -/
def region (W : DMBC S X Y Z) : Set (ℝ × ℝ × ℝ) :=
  closure {v | TripleAchievable W v}

/-- PDF p.4, Definition 5: strictly positive reliability AND secrecy exponents. -/
def StrongAchievable (W : DMBC S X Y Z) (R : ℝ) : Prop :=
  ∃ E F : ℝ, 0 < E ∧ 0 < F ∧ TripleAchievable W (R, E, F)

/-- PDF pp.3--4 and pp.8--9: strong achievability at specified public and
excitation rates. One code sequence has exactly the three prescribed ceiling
alphabet sizes and supplies the entropy condition and both positive exponents.
Keeping RP and RM here is necessary for the rate-limited conclusions. -/
def StrongAchievableAt (W : DMBC S X Y Z) (RK RP RM : ℝ) : Prop :=
  ∃ E F : ℝ, 0 < E ∧ 0 < F ∧ 0 ≤ RK ∧ 0 ≤ RP ∧ 0 ≤ RM ∧
    ∃ C : (n : ℕ) → SenderExcitedCode S X Y (n + 1),
      (∀ n, (C n).messages = 2 ^ ⌈(n + 1 : ℝ) * RM⌉₊ ∧
        (C n).publicSize = 2 ^ ⌈(n + 1 : ℝ) * RP⌉₊ ∧
        (C n).keys = 2 ^ ⌈(n + 1 : ℝ) * RK⌉₊) ∧
      EntropyRate W C RK ∧
      (E : EReal) ≤ Filter.liminf (fun n => logRate n (keyDisagreementProbability W (C n))) atTop ∧
      (F : EReal) ≤ Filter.liminf (fun n => logRate n (publicKeyLeakage W (C n))) atTop

/-- Forgetting the prescribed discussion and excitation rates preserves strong
achievability, using exactly the same code sequence and exponents. -/
example (W : DMBC S X Y Z) (RK RP RM : ℝ)
    (h : StrongAchievableAt W RK RP RM) : StrongAchievable W RK := by
  rcases h with ⟨E, F, hE, hF, hK, hP, hM, C, hsizes, hEntropy, he, hl⟩
  exact ⟨E, F, hE, hF, hK, le_of_lt hE, le_of_lt hF, C,
    ⟨RM, RP, hM, hP, hsizes⟩, hEntropy, he, hl⟩

/-- PDF p.8: supremal strongly achievable rate. -/
def strongCapacity (W : DMBC S X Y Z) : EReal :=
  sSup {v | ∃ R : ℝ, StrongAchievable W R ∧ v = (R : EReal)}

/-- PDF p.4, Definition 6: stochastic degradation preserves BOTH (S,X,Y)
and (S,X,Z). The alternative coupling is p(x,y|s)d(z|y). -/
def SenderExcitedDegraded (W : DMBC S X Y Z) : Prop :=
  ∃ d : Y → Z → ℝ, IsStochastic d ∧ ∀ s x z,
    (∑ y, W.w s (x, y, z)) = ∑ y, (∑ t, W.w s (x, y, t)) * d y z

/-- PDF p.5, (12): information difference for Alice's pair (X,S). -/
def advantage (W : DMBC S X Y Z) (p : S → ℝ) : ℝ :=
  observationMutualInfoBits (excitationJointMass W p) (fun o => (obsX o, obsS o)) obsY -
    observationMutualInfoBits (excitationJointMass W p) (fun o => (obsX o, obsS o)) obsZ

/-- PDF p.5, (11): conditional-information upper-bound objective. -/
def upperObjective (W : DMBC S X Y Z) (p : S → ℝ) : ℝ :=
  condInfo (excitationJointMass W p) (fun o => (obsX o, obsS o)) obsY obsZ

/-- PDF p.5, (16): channel portion, not forced nonnegative. -/
def channelRate (W : DMBC S X Y Z) (p : S → ℝ) : ℝ :=
  observationMutualInfoBits (excitationJointMass W p) obsS obsY - observationMutualInfoBits (excitationJointMass W p) obsS obsZ

/-- PDF p.5, (17): source portion, not forced nonnegative. -/
def residualSourceRate (W : DMBC S X Y Z) (p : S → ℝ) : ℝ :=
  condInfo (excitationJointMass W p) obsX obsY obsS - condInfo (excitationJointMass W p) obsX obsZ obsS

/-- PDF p.4, (10): normalized auxiliary kernels. -/
structure Aux (S X : Type) (u w : ℕ) [Fintype S] [Fintype X] where
  input : S → ℝ
  input_law : IsLaw input
  uKernel : (X × S) → Fin u → ℝ
  u_law : IsStochastic uKernel
  wKernel : Fin u → Fin w → ℝ
  w_law : IsStochastic wKernel

/-- PDF p.4, (10): constructed joint law, with the fixed DMBC marginal. -/
def auxMass (W : DMBC S X Y Z) (A : Aux S X u w) :
    (Fin w × Fin u × S × X × Y × Z) → ℝ :=
  fun o => A.wKernel o.2.1 o.1 * A.uKernel (o.2.2.2.1, o.2.2.1) o.2.1 *
    excitationJointMass W A.input o.2.2

/-- PDF p.4, (8): auxiliary conditional-information difference. -/
def auxObjective (W : DMBC S X Y Z) (A : Aux S X u w) : ℝ :=
  condInfo (auxMass W A) (fun o => o.2.1) (fun o => o.2.2.2.2.1) (fun o => o.1) -
    condInfo (auxMass W A) (fun o => o.2.1) (fun o => o.2.2.2.2.2) (fun o => o.1)

/-- PDF p.4: feasible values over all finite auxiliary alphabets. -/
def auxValues (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma : ℝ) : Set ℝ :=
  {v | ∃ u w : ℕ, 0 < u ∧ 0 < w ∧ ∃ A : Aux S X u w,
    CostFeasibleInput cost Gamma A.input ∧ v = auxObjective W A}

/-- PDF p.5: finite sequential discussion after excitation. All talk and key
maps are fixed and public. Each message depends on the sender's observation,
private seed and PRECEDING transcript only. A common finite alphabet and fixed
schedule cover arbitrary finite discussions by padding with dummy messages.
The base code supplies excitation and sizes; its forward maps are unused. -/
structure InteractiveCode (S X Y : Type) [Fintype S] (n : ℕ) where
  base : SenderExcitedCode S X Y n
  bobSeeds : ℕ
  bobSeeds_pos : 0 < bobSeeds
  rounds : ℕ
  symbols : ℕ
  symbols_pos : 0 < symbols
  sender : ℕ → Bool
  aliceTalk : Fin base.messages → (Fin n → X) → List (Fin symbols) → Fin symbols
  bobTalk : Fin bobSeeds → (Fin n → Y) → List (Fin symbols) → Fin symbols
  finalAlice : Fin base.messages → (Fin n → X) → List (Fin symbols) → Fin base.keys
  finalBob : Fin bobSeeds → (Fin n → Y) → List (Fin symbols) → Fin base.keys

/-- PDF p.5: independent uniform Bob seed and the original excitation sample. -/
abbrev InteractiveSample (C : InteractiveCode S X Y n) :=
  BlockSample (Z := Z) C.base × Fin C.bobSeeds

/-- PDF p.5: the full public transcript, constructed in temporal order. -/
def transcript (C : InteractiveCode S X Y n) (o : InteractiveSample (Z := Z) C) :=
  (List.range C.rounds).foldl (fun t i => t ++
    [if C.sender i then C.aliceTalk o.1.1 o.1.2.2.1 t
      else C.bobTalk o.2 o.1.2.2.2.1 t]) []

/-- PDF p.5: interactive sample law; Bob's private seed is independent. -/
def interactiveMass (W : DMBC S X Y Z) (C : InteractiveCode S X Y n) :
    InteractiveSample (Z := Z) C → ℝ :=
  fun o => blockMass W C.base o.1 / C.bobSeeds

/-- PDF p.5: interactive Alice key. -/
def interactiveKeyA (C : InteractiveCode S X Y n) (o : InteractiveSample (Z := Z) C) :=
  C.finalAlice o.1.1 o.1.2.2.1 (transcript C o)

/-- PDF p.5: key disagreement after the whole discussion. -/
def interactiveError (W : DMBC S X Y Z) (C : InteractiveCode S X Y n) : ℝ := by
  classical
  exact ∑ o, if interactiveKeyA C o ≠
    C.finalBob o.2 o.1.2.2.2.1 (transcript C o) then interactiveMass W C o else 0

/-- PDF p.5: Eve sees Z^n and EVERY public message. -/
def interactiveLeakage (W : DMBC S X Y Z) (C : InteractiveCode S X Y n) : ℝ :=
  observationMutualInfoBits (interactiveMass W C) (interactiveKeyA C)
    (fun o => (o.1.2.2.2.2, transcript C o))

/-- PDF p.5: the same entropy criterion for an interactive key. -/
def interactiveEntropy (W : DMBC S X Y Z) (C : InteractiveCode S X Y n) : ℝ :=
  observationEntropyBits (interactiveMass W C) (interactiveKeyA C)

/-- PDF p.5: weak achievability with multi-way public discussion. The key and
excitation ranges remain exponentially bounded; the finite discussion itself
is unrestricted, as in the stated multi-way upper bound. -/
def InteractiveAchievable (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ C : (n : ℕ) → InteractiveCode S X Y (n + 1),
    BoundedRanges (fun n => (C n).base) R ∧
    (∀ n, CodeCost cost (some Gamma) (C n).base) ∧
    (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
      R - eps ≤ interactiveEntropy W (C n) / (n + 1 : ℕ)) ∧
    Tendsto (fun n => interactiveError W (C n)) atTop (nhds 0) ∧
    Tendsto (fun n => interactiveLeakage W (C n) / (n + 1 : ℕ)) atTop (nhds 0)

/-- PDF p.5: multi-way capacity uses its own operational protocol class. -/
def interactiveCapacity (W : DMBC S X Y Z) (cost : S → ℝ) (Gamma : ℝ) : EReal :=
  sSup {v | ∃ R : ℝ, InteractiveAchievable W cost Gamma R ∧ v = (R : EReal)}

/-- A discussion with zero rounds has an empty public transcript. -/
example (C : InteractiveCode S X Y n) (h : C.rounds = 0)
    (o : InteractiveSample (Z := Z) C) : transcript C o = [] := by
  simp [transcript, h]

/-- PDF p.6: conditional X,Y mass given S. -/
def xyMass (W : DMBC S X Y Z) (s : S) (x : X) (y : Y) : ℝ :=
  ∑ z, W.w s (x, y, z)

/-- PDF p.6: conditional Y mass given S. -/
def yMass (W : DMBC S X Y Z) (s : S) (y : Y) : ℝ :=
  ∑ x, xyMass W s x y

/-- PDF p.6, (22): conditional X,Z mass given S. -/
def xzMass (W : DMBC S X Y Z) (s : S) (x : X) (z : Z) : ℝ :=
  ∑ y, W.w s (x, y, z)

/-- C18: printed (18), p.6, has an inner sum over (s,x) despite fixing s
in the outer sum. Changed to sum only over x, exactly as (66), p.13, because
this is the conditional-source moment given (y,s). Null rows have zero weight. -/
def reliabilityOne (W : DMBC S X Y Z) (p : S → ℝ) (rho RP : ℝ) : ℝ :=
  rho * RP - Real.logb 2 (∑ s, ∑ y, p s * yMass W s y *
    (∑ x, (xyMass W s x y / yMass W s y) ^ (1 / (1 + rho))) ^ (1 + rho))

/-- PDF pp.6,7,13, (19),(30),(67), corrected C19: sum first over output
(X,Y), then input S inside the power. The printed reversed order conflicts
with the expressly described channel S->(X,Y) and derivative in (30). -/
def reliabilityTwo (W : DMBC S X Y Z) (p : S → ℝ) (rho RP RM : ℝ) : ℝ :=
  rho * (RP - RM) - Real.logb 2 (∑ x, ∑ y,
    (∑ s, p s * (xyMass W s x y) ^ (1 / (1 + rho))) ^ (1 + rho))

/-- PDF p.6, (20): hybrid joint-decoding event. -/
def reliabilityThree (W : DMBC S X Y Z) (p : S → ℝ) (rho RP RM : ℝ) : ℝ :=
  rho * (RP - RM) - Real.logb 2 (∑ y,
    (∑ s, ∑ x, p s * (xyMass W s x y) ^ (1 / (1 + rho))) ^ (1 + rho))

/-- PDF p.6, (21): maximize separately, then take the minimum of three. -/
def reliabilityExponent (W : DMBC S X Y Z) (p : S → ℝ) (RP RM : ℝ) : EReal :=
  min (⨆ rho ∈ Icc (0 : ℝ) 1, (reliabilityOne W p rho RP : EReal))
    (min (⨆ rho ∈ Icc (0 : ℝ) 1, (reliabilityTwo W p rho RP RM : EReal))
      (⨆ rho ∈ Icc (0 : ℝ) 1, (reliabilityThree W p rho RP RM : EReal)))

/-- PDF p.6, (22): omit null Z fibers explicitly. -/
def secrecyTrial (W : DMBC S X Y Z) (p : S → ℝ) (alpha RK RP RM : ℝ) : ℝ :=
  -alpha * (RK + RP - RM) - Real.logb 2
    (∑ z, let pz := ∑ s, ∑ x, p s * xzMass W s x z
          if pz = 0 then 0 else
            ∑ s, ∑ x, p s * xzMass W s x z * (xzMass W s x z / pz) ^ alpha)

/-- PDF p.6, (23): supremum over 0<alpha≤1. -/
def secrecyExponent (W : DMBC S X Y Z) (p : S → ℝ) (RK RP RM : ℝ) : EReal :=
  ⨆ alpha ∈ Ioc (0 : ℝ) 1, (secrecyTrial W p alpha RK RP RM : EReal)

/-- PDF p.6, (24): inner region for one common p(s) and auxiliary rate pair. -/
def innerRegion (W : DMBC S X Y Z) (p : S → ℝ) (RP RM : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {v | 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧
    (v.2.1 : EReal) ≤ reliabilityExponent W p RP RM ∧
    (v.2.2 : EReal) ≤ secrecyExponent W p v.1 RP RM}

/-- PDF pp.9--10, (41): optimized reliability value. -/
def optimizedReliability (W : DMBC S X Y Z) (RP RM : ℝ) : EReal :=
  ⨆ (p : S → ℝ) (_ : IsLaw p), reliabilityExponent W p RP RM

/-- PDF p.10, (42): independently optimized secrecy value. -/
def inputOptimizedSecrecyExponent (W : DMBC S X Y Z) (RK RP RM : ℝ) : EReal :=
  ⨆ (p : S → ℝ) (_ : IsLaw p), secrecyExponent W p RK RP RM

end

end QAlgorithms.Papers.Independent.Intakethird100.P76


