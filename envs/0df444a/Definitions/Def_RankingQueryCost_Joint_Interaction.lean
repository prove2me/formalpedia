-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Interaction
-- name    : RankingQueryCost_Joint_Interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:39.520337+00:00
-- url     : https://prove2.me/theorems/830d4715-db7e-4e70-9b03-fabb04ba8e9f
-- title:
--   Causal partial-online comparisons and operational optimal budgets
-- statement:
--   A world fixes a true order and at most $a$ initial faulty identities before the private tape. On the first query of any other identity, its strategy may designate it faulty while fewer than $h$ additional identities have been designated. It sees the public past, current query and public messages, and its own designations. Every later read returns the cached first answer. A protocol's next action and real output depend only on public history and its private fair-bit tape.
--
--   $$\Pr[L_r(q)\le\theta]\ge3/4,\qquad
--   \Pr[\text{emission}\ \land\ L_r(q)\le\theta]\ge3/4.$$
--
--   Actual success requires a returned estimate in $Q$. Safety bounds every returned estimate by $\beta_n$ in every compatible order on every path. Dual accuracy requires a sound public verifier, an accepted certificate on every emitted result, and $q^0$ on refusal. Hard budgets bound distinct acquired identities at every execution prefix, including divergent and refusal paths. The three optima are infima of operationally attainable natural budgets in $\mathbb N\cup\{+\infty\}$, so an empty task cannot acquire a zero optimum.
--
--   **Formalization Note** Logical rereads remain visible and cost no new identity. Divergence never contributes to success. Independent randomized adversaries are covered by conditioning on their independent seeds and averaging these uniform deterministic-strategy guarantees. The verifier's mathematical decision takes no private tape.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.1, pp. 3–4, PDF pp. 4–5; §6.3, p. 31, PDF p. 32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Transcript

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

abbrev PrivateTape := ℕ → Bool

instance listNatMeasurableSpace : MeasurableSpace (List ℕ) := ⊤
instance requestMeasurableSpace (n : ℕ) : MeasurableSpace (Option (Option (Pair n))) := ⊤

/-- Mathlib's product law of independent fair private bits. -/
def privateLaw : MeasureTheory.Measure PrivateTape :=
  MeasureTheory.Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

/-- Finite public messages allow, for example, revealing a reference set before its first star.
The actual correction mask need not be revealed. Replies always concern an acquired pair. -/
abbrev PublicHistory (n : ℕ) := List (List ℕ × Pair n × Bool)

/-- Lower-bound policies may use arbitrary real outputs and arbitrary measurable private rules.
All logical requests, including rereads, appear in the public history. -/
structure QueryPolicy (n : ℕ) where
  request : PrivateTape → PublicHistory n → Option (Option (Pair n))
  message : PrivateTape → PublicHistory n → List ℕ
  estimate : PrivateTape → PublicHistory n → (Fin n → ℝ)
  emission : PrivateTape → PublicHistory n → Bool
  certificate : PrivateTape → PublicHistory n → List ℕ
  request_measurable : ∀ H, Measurable fun ω => request ω H
  message_measurable : ∀ H, Measurable fun ω => message ω H
  estimate_measurable : ∀ H, Measurable fun ω => estimate ω H
  emission_measurable : ∀ H, Measurable fun ω => emission ω H
  certificate_measurable : ∀ H, Measurable fun ω => certificate ω H

/-- An initially fixed order and support; online decisions see the public past and current query,
but receive no private tape. Extra independent adversarial randomness is a mixture of these rules. -/
structure ComparisonWorld (n : ℕ) where
  rank : Rank n
  initial : Finset (Pair n)
  firstReply : PublicHistory n → Finset (Pair n) → List ℕ → Pair n → Bool × Bool

structure InteractionState (n : ℕ) where
  ledger : Transcript n
  history : PublicHistory n
  online : Finset (Pair n)

def initialState (n : ℕ) : InteractionState n := ⟨emptyTranscript n, [], ∅⟩

/-- One ledger read. A cached identity cannot be redesignated or have its answer changed.
The first component of the strategy's choice requests a new online designation. -/
def readIdentity {n : ℕ} (h : ℕ) (W : ComparisonWorld n) (S : InteractionState n)
    (msg : List ℕ) (e : Pair n) : Bool × InteractionState n :=
  match S.ledger e with
  | some b => (b, { S with history := S.history ++ [(msg, e, b)] })
  | none =>
    let choice := W.firstReply S.history S.online msg e
    let newlyFaulty := e ∉ W.initial ∧ choice.1 = true ∧ S.online.card < h
    let F := if newlyFaulty then insert e S.online else S.online
    let b := if e ∈ W.initial ∨ newlyFaulty then choice.2 else truthful W.rank e
    (b, ⟨Function.update S.ledger e (some b), S.history ++ [(msg, e, b)], F⟩)

structure InteractionResult (n : ℕ) where
  state : InteractionState n
  estimate : Fin n → ℝ
  emission : Bool
  certificate : List ℕ

/-- A running computation, a halted result, or an explicit divergence between requests.
The latter allows unrestricted lower-bound protocols; successful paths must actually terminate. -/
inductive Execution (n : ℕ) where
  | running (state : InteractionState n)
  | halted (result : InteractionResult n)
  | diverged (state : InteractionState n)

/-- `none` is divergence; `some none` is termination; `some (some e)` is a logical request. -/
def advance {n : ℕ} (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ)
    (ω : PrivateTape) : Execution n → Execution n
  | .halted o => .halted o
  | .diverged S => .diverged S
  | .running S =>
    match A.request ω S.history with
    | none => .diverged S
    | some none => .halted ⟨S, A.estimate ω S.history, A.emission ω S.history,
        A.certificate ω S.history⟩
    | some (some e) => .running (readIdentity h W S (A.message ω S.history) e).2

def executionPrefix {n : ℕ} (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ)
    (ω : PrivateTape) : ℕ → Execution n
  | 0 => .running (initialState n)
  | t + 1 => advance A W h ω (executionPrefix A W h ω t)

def executionState {n : ℕ} : Execution n → InteractionState n
  | .running S => S
  | .halted o => o.state
  | .diverged S => S

def Returns {n : ℕ} (A : QueryPolicy n) (W : ComparisonWorld n) (h : ℕ)
    (ω : PrivateTape) (o : InteractionResult n) : Prop :=
  ∃ t, executionPrefix A W h ω t = .halted o

def LegalWorld {n : ℕ} (a : ℕ) (W : ComparisonWorld n) : Prop := W.initial.card ≤ a

/-- The cap holds on every tape and at every finite executionPrefix, including divergent paths. -/
def HardBudget {n : ℕ} (a h B : ℕ) (A : QueryPolicy n) : Prop :=
  ∀ W, LegalWorld a W → ∀ ω t,
    (acquired (executionState (executionPrefix A W h ω t)).ledger).card ≤ B

/-- A public verifier has only the record, the claimed output and finite witness. -/
abbrev PublicVerifier (n : ℕ) := Transcript n → (Fin n → ℝ) → List ℕ → Bool

def VerifierSound {n : ℕ} (s : ℕ) (τ : ℝ) (V : PublicVerifier n) : Prop :=
  ∀ T q c, q ∈ estimateSet n → V T q c = true →
    ∀ r ∈ compatible s T, loss q r ≤ τ

/-- Every returned output is in Q, and actual success includes termination. -/
def Actual {n : ℕ} (a h : ℕ) (θ : ℝ) (A : QueryPolicy n) : Prop :=
  (∀ W, LegalWorld a W → ∀ ω o, Returns A W h ω o → o.estimate ∈ estimateSet n) ∧
  ∀ W, LegalWorld a W →
    (3 / 4 : ENNReal) ≤ privateLaw {ω | ∃ o, Returns A W h ω o ∧ loss o.estimate W.rank ≤ θ}

def Safe {n : ℕ} (a h : ℕ) (θ : ℝ) (A : QueryPolicy n) : Prop :=
  Actual a h θ A ∧ ∀ W, LegalWorld a W → ∀ ω o, Returns A W h ω o →
    ∀ r ∈ compatible (a + h) o.state.ledger, loss o.estimate r ≤ baseline n

/-- Successful emission and actual accuracy are a joint event. Every refused result is q⁰. -/
def Dual {n : ℕ} (a h : ℕ) (θ τ : ℝ) (A : QueryPolicy n) (V : PublicVerifier n) : Prop :=
  VerifierSound (a + h) τ V ∧
  (∀ W, LegalWorld a W → ∀ ω o, Returns A W h ω o →
    o.estimate ∈ estimateSet n ∧
    (o.emission = true → V o.state.ledger o.estimate o.certificate = true) ∧
    (o.emission = false → o.estimate = fallback n)) ∧
  ∀ W, LegalWorld a W →
    (3 / 4 : ENNReal) ≤ privateLaw {ω | ∃ o, Returns A W h ω o ∧
      o.emission = true ∧ loss o.estimate W.rank ≤ θ}

/-- Sets of attainable natural hard budgets, with no target rate included. -/
def actualBudgets (n a h : ℕ) (θ : ℝ) : Set ℕ :=
  {B | ∃ A : QueryPolicy n, HardBudget a h B A ∧ Actual a h θ A}

def safeBudgets (n a h : ℕ) (θ : ℝ) : Set ℕ :=
  {B | ∃ A : QueryPolicy n, HardBudget a h B A ∧ Safe a h θ A}

def dualBudgets (n a h : ℕ) (θ τ : ℝ) : Set ℕ :=
  {B | ∃ (A : QueryPolicy n) (V : PublicVerifier n),
    HardBudget a h B A ∧ Dual a h θ τ A V}

/-- An empty feasible set has optimum +∞, never the natural-number infimum's default 0. -/
def optimalBudget (S : Set ℕ) : ℕ∞ := sInf ((fun B : ℕ => (B : ℕ∞)) '' S)

end RankingQueryCost.Joint


