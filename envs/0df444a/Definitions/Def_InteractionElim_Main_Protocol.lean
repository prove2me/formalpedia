-- Prove2me | Definitions.Def_InteractionElim_Main_Protocol
-- name    : InteractionElim_Main_Protocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:07.402987+00:00
-- url     : https://prove2.me/theorems/ca1446a6-974d-4fcc-bf84-164b2adbb41d
-- title:
--   The two-party protocol model of §2: execution law, fee (2.1), reliability, admissibility, the classes of Definition 2.1 and $C_{ad}$, $C_{pre}$, $C_{lin}$
-- statement:
--   A **world** is a pair $(x,u)$ with $x\in\mathbb F_2^R$ and a bit $u$. The **expert** initially knows only its record $Ax$; the **agent** knows $u$. A **public history** $H$ lists paid bits and complete submissions with their (implicit, successful) feedback. A **protocol** consists of
--
--   1. a **public parser**: functions of $H$ giving the next paid-bit speaker (agent, expert, or none = parser leaf) and a phase flag;
--   2. an **agent strategy**: from its private tape, $u$ and its whole private view (the interleaved list of public events and of its own private query indices and responses), the next action: query a coordinate of the current block, emit its paid bit, submit a value $(v,u')$ for the current block, *yield* to the designated expert, or abandon;
--   3. an **expert strategy**: from its private tape, $Ax$ and $H$, its paid bit, and separately whether to abandon at $H$.
--
--   Private tapes are independent infinite fair-coin sequences; there is no shared tape. **Execution** in world $(x,u)$: a query on $i\in B_j$ (current stage $j$) returns $x_i\oplus Z$ with fresh $Z\sim\mathrm{Bernoulli}(p_i)$ (the $n$-th call on $i$ reads entry $n$ of an independent noise array); a paid bit is published only by the designated speaker (the agent's own bit, or the expert's bit when the agent yields); the agent may submit at any time, also when the expert is designated; a correct submission $(x_{B_j},u)$ opens the next stage and the last one is full success; a wrong submission, an abandonment by either party, or an illegal move is absorbing failure. After each public event (and at the start) the expert may abandon.
--
--   With $C$ the number of transmitted paid bits and $N_i$ the number of calls on $i$, the **fee** (2.1) is
--   $$
--   \sup_{x,u}\ \mathbb E_{x,u}\Big[\gamma C+w\sum_i N_i\Big].
--   $$
--   A protocol is **reliable** if every world has failure probability at most $\delta$, and **admissible** if its strategies are measurable and it terminates almost surely in every world. It is **initial teaching** if all paid bits occur in one initial phase (flagged by the parser) before any query or submission, and **fixed-linear teaching** if moreover the expert's bits use the record only through $Sx$ for a public fixed $S$ with $\operatorname{row}S\subseteq\operatorname{row}A$ and at every normally completed initial lesson the agent can recover $Sx$ from the paid transcript, its original tape and $u$ (expert abandonment may still use all of $Ax$). Then (Definition 2.1)
--   $$
--   C_{ad}=\inf_{\text{reliable, admissible}}\mathrm{fee},\qquad C_{pre}=\inf_{\ldots,\ \text{initial teaching}}\mathrm{fee},\qquad C_{lin}=\inf_{\ldots,\ \text{fixed-linear}}\mathrm{fee}.
--   $$
--   The module also defines the paid-bit/ordered-marker **signature** of a history (§B.1) and the event of full success with a given signature.
--
--   **Formalization Note** Strategies are deterministic functions of the party's tape and view; fair-coin tapes realize any private randomization. The expert never sees query indices, responses, counts or timing. Fees and values live in $[0,\infty]$ (`ℝ≥0∞`); the expectation is a lower Lebesgue integral of the path cost $\sup_t(\gamma\cdot\text{bits}_t+w\sum_i\text{calls}_{t,i})$, so infinite-fee protocols are allowed. Reliability bounds the probability of the event *some failure occurs*, not a success probability. The law is `Measure.infinitePi` of fair coins and $\mathrm{Bernoulli}(p_i)$ coins.
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 4, §2 (sequential workflow; communication, parsing, and admissibility; risk, fees, and protocol classes; Eq. (2.1); Definition 2.1 and the following paragraph); p. 22, §B.1 (signatures)

import Mathlib
import Definitions.Def_InteractionElim_Main_Instance

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Matrix

namespace InteractionElim.Main

/-!
# The two-party protocol model of §2, its execution law, the fee (2.1), reliability,
# admissibility, the classes of Definition 2.1 and the values `C_ad`, `C_pre`, `C_lin`

Source: Jin, Zang, Xu, Li, *Eliminating Ongoing Interaction in Long-Running Verification Agents*,
STOC 2027 submission (manuscript sha256 44f6d829…), §2, p. 4 ("sequential workflow",
"Communication, parsing, and admissibility", "Risk, fees, and protocol classes",
Definition 2.1 and the paragraph after it); signatures from §B.1, p. 22.

**Model.** A world is a pair `(x, u)` with `x ∈ F_2^R` and a bit `u`. The expert knows only
`A x`; the agent knows `u`. A *public history* is the list of public events: paid bits and
complete submissions (a submission carries the current block's value, zero elsewhere, and the
submitted bit; a submission recorded in a running history was correct, so its feedback is
implicit). A *public parser* assigns to every public history the next paid-bit speaker
(`none` = no paid bit can follow) and a phase flag. The agent's strategy maps its private tape,
`u`, and its whole private view (the interleaved list of public events and its own private
query responses) to an action: query a coordinate, emit its paid bit, submit, *yield* (let the
designated expert emit its bit), or abandon. The expert's strategy maps its private tape, its
record `A x` and the public history to a paid bit, and, separately, to the decision to abandon
at that public history. Private tapes are infinite fair-coin sequences (any randomization of a
party is a measurable function of such a tape). Strategies are deterministic functions of
their tape and view.

**Execution** in world `(x, u)` is driven by `ω`: the agent's tape, the expert's tape, and for
every coordinate `i` an infinite array of independent `Bernoulli(p_i)` noise bits, the `n`-th
call on `i` reading entry `n` (fresh noise per call). One step is one agent action:
* `query i` with `i` in the current block returns `x_i ⊕ Z` privately (a query outside the
  current block is unavailable and counts as abandonment);
* `bit b` publishes `b` if the parser designates the agent, `yield` publishes the expert's bit
  if the parser designates the expert (otherwise either is an illegal move = abandonment);
* `submit` publishes the submission; a correct one (`x_{B_j}` and `u`) opens the next stage, the
  last correct one is full success, an incorrect one is absorbing failure. The agent may submit
  at any time, also when the parser designates the expert (preemption);
* `abandon` is absorbing failure.
After every public event (and at the empty history) the expert may privately abandon
(absorbing failure). The expert never sees queries, responses, counts or time.
-/

/-- A public event: a paid bit, or a complete submission (current-block value, zero elsewhere,
and the submitted bit `u`). -/
inductive Event (R : ℕ) where
  | bit (b : Bool)
  | submit (v : Fin R → ZMod 2) (ub : ZMod 2)

/-- A public history `H`. -/
abbrev History (R : ℕ) := List (Event R)

/-- The two parties. -/
inductive Party where
  | agent
  | expert
  deriving DecidableEq

/-- A public parser: the next paid-bit speaker (`none` = parser leaf, no paid bit follows) and
the phase flag (`true` = inside the initial discussion), both functions of the public history.
Message boundaries are further functions of `H`, available to both parties. -/
structure Parser (R : ℕ) where
  speaker : History R → Option Party
  phase : History R → Bool

/-- An entry of the agent's private view: a public event, or one of its own private tool calls
with the response. -/
inductive AgentObs (R : ℕ) where
  | pub (e : Event R)
  | obs (i : Fin R) (resp : ZMod 2)

/-- An agent action. -/
inductive AgentAct (R : ℕ) where
  | query (i : Fin R)
  | bit (b : Bool)
  | submit (v : Fin R → ZMod 2) (ub : ZMod 2)
  | yield
  | abandon

/-- Actions carry the discrete σ-algebra. -/
instance (R : ℕ) : MeasurableSpace (AgentAct R) := ⊤

/-- A private tape: an infinite sequence of fair coins. -/
abbrev Tape := ℕ → Bool

/-- A protocol for the instance `I`. -/
structure Protocol (I : Instance) where
  /-- The public parser. -/
  parser : Parser I.R
  /-- The agent: private tape, its bit `u`, its private view ↦ next action. -/
  agent : Tape → ZMod 2 → List (AgentObs I.R) → AgentAct I.R
  /-- The expert's paid bit: private tape, record `A x`, public history ↦ bit. -/
  expertBit : Tape → (Fin I.nrows → ZMod 2) → History I.R → Bool
  /-- The expert's private abandonment at a public history. -/
  expertAbandon : Tape → (Fin I.nrows → ZMod 2) → History I.R → Bool

/-- Sources of randomness: the two private tapes and the per-coordinate noise arrays. -/
inductive Src (R : ℕ) where
  | agentTape (n : ℕ)
  | expertTape (n : ℕ)
  | noise (i : Fin R) (n : ℕ)

/-- The sample space. -/
abbrev Ω (R : ℕ) := Src R → Bool

/-- A coin that is `true` with probability `q` (clamped to `[0, 1]`). -/
noncomputable def coin (q : ℝ) : Measure Bool :=
  bernoulliMeasure true false (Set.projIcc (0 : ℝ) 1 zero_le_one q)

/-- The execution law: all sources independent, tapes fair, `noise i n ∼ Bernoulli(p_i)`. -/
noncomputable def law (I : Instance) : Measure (Ω I.R) :=
  Measure.infinitePi fun s : Src I.R =>
    match s with
    | .agentTape _ => coin (1 / 2)
    | .expertTape _ => coin (1 / 2)
    | .noise i _ => coin (I.p i)

/-- The agent's tape inside `ω`. -/
def agentTape {R : ℕ} (ω : Ω R) : Tape := fun n => ω (.agentTape n)

/-- The expert's tape inside `ω`. -/
def expertTape {R : ℕ} (ω : Ω R) : Tape := fun n => ω (.expertTape n)

/-- Run status. -/
inductive Status where
  | running
  | success
  | failure
  deriving DecidableEq

/-- The execution state: the agent's view, the public history, the current (0-based) stage,
the per-coordinate call counts, the number of paid bits transmitted, and the status. -/
structure State (R : ℕ) where
  log : List (AgentObs R)
  hist : History R
  stage : ℕ
  calls : Fin R → ℕ
  bits : ℕ
  status : Status

section Execution

variable {I : Instance}

open Classical in
/-- Append a public event and let the expert decide whether to abandon at the new history. -/
noncomputable def publish (pr : Protocol I) (x : Fin I.R → ZMod 2) (ω : Ω I.R)
    (st : State I.R) (e : Event I.R) : State I.R :=
  let st' : State I.R := { st with hist := st.hist ++ [e], log := st.log ++ [.pub e] }
  if pr.expertAbandon (expertTape ω) (I.A *ᵥ x) st'.hist then { st' with status := .failure }
  else st'

open Classical in
/-- One execution step in world `(x, u)` with randomness `ω`. -/
noncomputable def step (pr : Protocol I) (x : Fin I.R → ZMod 2) (u : ZMod 2) (ω : Ω I.R)
    (st : State I.R) : State I.R :=
  if st.status ≠ .running then st else
  match pr.agent (agentTape ω) u st.log with
  | .query i =>
      if ((I.block i : ℕ) = st.stage) then
        { st with
          calls := Function.update st.calls i (st.calls i + 1)
          log := st.log ++
            [.obs i (x i + (if ω (.noise i (st.calls i)) then (1 : ZMod 2) else 0))] }
      else { st with status := .failure }
  | .bit b =>
      if pr.parser.speaker st.hist = some .agent then
        publish pr x ω { st with bits := st.bits + 1 } (.bit b)
      else { st with status := .failure }
  | .yield =>
      if pr.parser.speaker st.hist = some .expert then
        publish pr x ω { st with bits := st.bits + 1 }
          (.bit (pr.expertBit (expertTape ω) (I.A *ᵥ x) st.hist))
      else { st with status := .failure }
  | .submit v ub =>
      let e : Event I.R := .submit (fun i => if (I.block i : ℕ) = st.stage then v i else 0) ub
      if (∀ i, (I.block i : ℕ) = st.stage → v i = x i) ∧ ub = u then
        if st.stage + 1 = I.m then
          { st with hist := st.hist ++ [e], log := st.log ++ [.pub e], stage := st.stage + 1,
                    status := .success }
        else publish pr x ω { st with stage := st.stage + 1 } e
      else { st with hist := st.hist ++ [e], log := st.log ++ [.pub e], status := .failure }
  | .abandon => { st with status := .failure }

open Classical in
/-- The initial state (the expert may abandon at the empty history). -/
noncomputable def initState (pr : Protocol I) (x : Fin I.R → ZMod 2) (ω : Ω I.R) :
    State I.R :=
  { log := [], hist := [], stage := 0, calls := fun _ => 0, bits := 0,
    status := if pr.expertAbandon (expertTape ω) (I.A *ᵥ x) [] then .failure else .running }

/-- The state after `t` steps. -/
noncomputable def run (pr : Protocol I) (x : Fin I.R → ZMod 2) (u : ZMod 2) (ω : Ω I.R)
    (t : ℕ) : State I.R :=
  (step pr x u ω)^[t] (initState pr x ω)

/-- The execution terminates (success or failure). -/
def Terminates (pr : Protocol I) (x : Fin I.R → ZMod 2) (u : ZMod 2) (ω : Ω I.R) : Prop := ∃ t, (run pr x u ω t).status ≠ .running

/-- Some failure occurs in the chain. -/
def Fails (pr : Protocol I) (x : Fin I.R → ZMod 2) (u : ZMod 2) (ω : Ω I.R) : Prop := ∃ t, (run pr x u ω t).status = .failure

/-- Full success. -/
def Succeeds (pr : Protocol I) (x : Fin I.R → ZMod 2) (u : ZMod 2) (ω : Ω I.R) : Prop := ∃ t, (run pr x u ω t).status = .success

/-- The cost incurred up to a state: `γ · (paid bits) + w · ∑_i (calls on i)`. -/
noncomputable def costOf (st : State I.R) : ℝ≥0∞ :=
  ENNReal.ofReal (I.γ : ℝ) * (st.bits : ℝ≥0∞) + ENNReal.ofReal (I.w : ℝ) * ∑ i, (st.calls i : ℝ≥0∞)

/-- The actual cost of a whole execution path, `γ C + w ∑_i N_i` (possibly `∞`). -/
noncomputable def pathCost (pr : Protocol I) (x : Fin I.R → ZMod 2) (u : ZMod 2) (ω : Ω I.R) :
    ℝ≥0∞ := ⨆ t, costOf (run pr x u ω t)

end Execution

section Values

variable {I : Instance}

/-- The fee (2.1): `sup_{x,u} E_{x,u}[γ C + w ∑_i N_i]`. -/
noncomputable def fee (pr : Protocol I) : ℝ≥0∞ :=
  ⨆ (x : Fin I.R → ZMod 2) (u : ZMod 2), ∫⁻ ω, pathCost pr x u ω ∂(law I)

/-- Both parties' strategies are measurable functions of their tapes. -/
def StrategiesMeasurable (pr : Protocol I) : Prop :=
  (∀ u l, Measurable fun ρ : Tape => pr.agent ρ u l) ∧
    (∀ y H, Measurable fun ρ : Tape => pr.expertBit ρ y H) ∧
    (∀ y H, Measurable fun ρ : Tape => pr.expertAbandon ρ y H)

/-- Admissible: measurable strategies, and termination almost surely in every world. -/
def Admissible (pr : Protocol I) : Prop :=
  StrategiesMeasurable pr ∧
    ∀ (x : Fin I.R → ZMod 2) (u : ZMod 2), law I {ω | ¬ Terminates pr x u ω} = 0

/-- Reliable: in every world `(x, u)` the probability of any failure in the chain is at most
`δ`. -/
def Reliable (pr : Protocol I) : Prop :=
  ∀ (x : Fin I.R → ZMod 2) (u : ZMod 2), law I {ω | Fails pr x u ω} ≤ ENNReal.ofReal (I.δ : ℝ)

/-- The public history of an agent view. -/
def pubHist {R : ℕ} (l : List (AgentObs R)) : History R :=
  l.filterMap fun o => match o with
    | .pub e => some e
    | .obs _ _ => none

/-- The paid bits of a public history, in order. -/
def bitsOf {R : ℕ} (H : History R) : List Bool :=
  H.filterMap fun e => match e with
    | .bit b => some b
    | .submit _ _ => none

/-- The paid-bit/ordered-marker signature of a history (§B.1): every paid bit, and one marker
`none` per submission, omitting the submitted values. -/
def signature {R : ℕ} (H : History R) : List (Option Bool) :=
  H.map fun e => match e with
    | .bit b => some b
    | .submit _ _ => none

/-- Full success with paid-bit/ordered-marker signature `s` (the event `{Γ, S = s}` of §B.2). -/
def SucceedsWith {I : Instance} (pr : Protocol I) (x : Fin I.R → ZMod 2) (u : ZMod 2) (ω : Ω I.R)
    (s : List (Option Bool)) : Prop :=
  ∃ t, (run pr x u ω t).status = .success ∧ signature (run pr x u ω t).hist = s

/-- Initial teaching (the class of `C_pre`): discussion is one initial phase, flagged by the
parser, before any tool call or submission; once the flag is off it stays off and no paid bit
can follow. -/
def InitialTeaching (pr : Protocol I) : Prop :=
  (∀ H, pr.parser.phase H = false → pr.parser.speaker H = none) ∧
    (∀ H e, pr.parser.phase H = false → pr.parser.phase (H ++ [e]) = false) ∧
    ∀ ρ u l, pr.parser.phase (pubHist l) = true →
      (∀ i, pr.agent ρ u l ≠ .query i) ∧ ∀ v ub, pr.agent ρ u l ≠ .submit v ub

/-- Fixed-linear teaching (the class of `C_lin`): initial teaching whose expert bits use only
`S x` (with public data and the original tapes) for a public fixed matrix `S` with
`row S ⊆ row A`. At a normally completed initial phase the agent can recover `S x`
from the paid transcript, its own original tape and `u`. Failed paths are not completed
lessons (Appendix E, (E.4)); expert abandonment may still depend on the full record `A x`. -/
def LinearTeaching (pr : Protocol I) : Prop :=
  InitialTeaching pr ∧
    ∃ (s : ℕ) (S : Matrix (Fin s) (Fin I.R) (ZMod 2)),
      (∃ M : Matrix (Fin s) (Fin I.nrows) (ZMod 2), S = M * I.A) ∧
      (∀ ρ x x' H, S *ᵥ x = S *ᵥ x' → pr.expertBit ρ (I.A *ᵥ x) H = pr.expertBit ρ (I.A *ᵥ x') H) ∧
      ∃ decode : Tape → ZMod 2 → List Bool → (Fin s → ZMod 2),
        ∀ x u ω t,
          pr.parser.phase (run pr x u ω t).hist = false →
          (run pr x u ω t).status ≠ .failure →
          decode (agentTape ω) u (bitsOf (run pr x u ω t).hist) = S *ᵥ x

/-- `C_ad`: the infimum of the fee over all reliable admissible protocols. -/
noncomputable def Cad (I : Instance) : ℝ≥0∞ :=
  ⨅ (pr : Protocol I) (_ : Reliable pr ∧ Admissible pr), fee pr

/-- `C_pre`: the infimum over reliable admissible initial-teaching protocols. -/
noncomputable def Cpre (I : Instance) : ℝ≥0∞ :=
  ⨅ (pr : Protocol I) (_ : Reliable pr ∧ Admissible pr ∧ InitialTeaching pr), fee pr

/-- `C_lin`: the infimum over reliable admissible fixed-linear-teaching protocols. -/
noncomputable def Clin (I : Instance) : ℝ≥0∞ :=
  ⨅ (pr : Protocol I) (_ : Reliable pr ∧ Admissible pr ∧ LinearTeaching pr), fee pr

end Values

end InteractionElim.Main


