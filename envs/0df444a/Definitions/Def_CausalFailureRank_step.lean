-- Prove2me | Definitions.Def_CausalFailureRank_step
-- name    : CausalFailureRank_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:40.164385+00:00
-- url     : https://prove2.me/theorems/b8c03d34-3d66-495f-8953-efc2cdc1df8a
-- title:
--   Execution semantics: state, legal steps, runs, success and bill
-- statement:
--   A run follows the timeline: fresh fact, noisy reviews, ordinary write, exact report, allocation and advance. The state records the stage, the phase, the reviews bought at the stage, the unused tools, committed unexecuted corrections, the currently incorrect stages, the calls used, a halted flag and the history.
--
--   1. A **review** returns the next entry of the stage's tape; it needs an open port, quota and a call.
--   2. A **write** charges the stage's normal calls, closes the ports and reveals the fact. A correct write advances; an erroneous one creates the handle.
--   3. A **commit** needs that handle and an unused compatible tool, consumes the tool irrevocably and advances. Under the immediate contract it also executes the correction.
--   4. A **decline** advances and leaves the stage permanently wrong.
--   5. An **execute** of a committed correction needs a call and repairs that output only.
--   6. **Stop** and every illegal action halt the run, which is abandonment.
--
--   **Success** means that the run reaches the end with no incorrect output. The **bill** $C=\sum_i c_iT_i+\sum f_{ir}$ is the supremum over time of the accumulated charges, so failed paths are charged. Healthy entry states record that all earlier allocations are resolved.
--
--   **Formalization Note** A blind overwrite does not exist, and allocations cannot be made after a stage's window, so this is contract $I$ and not the retained contract. The bill takes values in $[0,\infty]$, and a run with unbounded reviews fails with infinite bill.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, pp.4–5

import Mathlib
import Definitions.Def_CausalFailureRank_Instance
import Definitions.Def_CausalFailureRank_tapeLaw
import Definitions.Def_CausalFailureRank_Event

namespace CausalFailureRank

variable {N q : ℕ}

/-- `reviewing`: the stage's review and write ports are open. `allocating`: an actual error has been
reported, its handle exists, and the allocation is due before advancing. -/
inductive Phase
  | reviewing
  | allocating
  deriving DecidableEq

/-- The state of an execution (§2, pp.4–5). `pending j = some r` is a correction committed to tool `r`
and not yet executed; `wrong` is the set of stages whose output is currently not correct. -/
structure State (I : Instance N q) where
  /-- The current stage; `N` is terminal. -/
  stage : ℕ
  /-- The phase of the current stage. -/
  phase : Phase
  /-- The reviews bought at the current stage. -/
  reviews : ℕ
  /-- The unused tools. -/
  unused : Finset (Fin q)
  /-- The committed, not yet executed, corrections. -/
  pending : Fin N → Option (Fin q)
  /-- The stages whose output is currently incorrect. -/
  wrong : Finset (Fin N)
  /-- The cumulative calls used. -/
  calls : ℕ
  /-- Whether the run has halted (stopped, or tried an illegal action). -/
  halted : Bool
  /-- The visible history. -/
  history : History I

/-- Halt: abandonment. Nothing changes afterwards. -/
def State.halt {I : Instance N q} (st : State I) : State I := { st with halted := true }

/-- Advance to the next stage, with fresh review ports. -/
def State.advance {I : Instance N q} (st : State I) : State I :=
  { st with stage := st.stage + 1, phase := .reviewing, reviews := 0 }

/-- Continue at the current stage if it is not terminal, otherwise halt. -/
def State.atStage {I : Instance N q} (st : State I) (k : Fin N → State I) : State I :=
  if h : st.stage < N then k ⟨st.stage, h⟩ else st.halt

open scoped Classical in
/-- **One step of an execution, given the joint sample `ω`.** Zang, Li, Jin, Xu, *Causal Failure Rank
Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256
721c8b0d…), §2, pp.4–5, early reports and contract I.

* `review`: returns the next tape entry; needs an open port, quota and a call.
* `write b`: charges the stage's normal calls and closes the ports. The report reveals the fact. On
  a correct write the run advances; on an error the handle exists, phase `allocating`.
* `commit r`: only in phase `allocating`, with `r ∈ S i` unused; consumes `r` irrevocably and advances.
  Under `current` the correction becomes pending; under `currentPay` it is executed at once (one
  call, or the action is illegal).
* `decline`: only in phase `allocating`; the stage stays wrong for good and the run advances.
* `execute j`: needs a pending correction and a call; it adds no information.
* `stop` halts, and **any illegal action halts**, which is abandonment. Nothing else changes an output.

**Formalization Note.** Corrections fix the output (`wrong.erase`) and no other output. A correction's
allocation cannot be made after the stage's window (`commit` applies only to the current stage), so
this is contract I, not the retained contract R. `H` caps the cumulative `calls`, counting
normal calls, reviews and corrections. -/
def step (I : Instance N q) (κ : Contract) (caps : Caps N) (ω : Sample I) (st : State I)
    (a : Action N q) : State I :=
  if st.halted then st else
  match a with
  | .stop => st.halt
  | .review => st.atStage fun i =>
      if st.phase = .reviewing ∧ (st.reviews : ℕ∞) < caps.Q i ∧ ((st.calls + 1 : ℕ) : ℕ∞) ≤ caps.H then
        { st with
          reviews := st.reviews + 1
          calls := st.calls + 1
          history := st.history ++ [.obs i ((ω i).2 st.reviews)] }
      else st.halt
  | .write b => st.atStage fun i =>
      if st.phase = .reviewing ∧ ((st.calls + I.normalCalls i : ℕ) : ℕ∞) ≤ caps.H then
        let st' : State I :=
          { st with
            calls := st.calls + I.normalCalls i
            history := st.history ++ [.wrote i b, .report i (ω i).1] }
        if b = (ω i).1 then st'.advance
        else { st' with phase := .allocating, wrong := insert i st.wrong }
      else st.halt
  | .commit r => st.atStage fun i =>
      if st.phase = .allocating ∧ r ∈ I.S i ∧ r ∈ st.unused then
        let st' : State I :=
          { st with
            unused := st.unused.erase r
            history := st.history ++ [.committed i r] }
        match κ with
        | .current => { st' with pending := Function.update st.pending i (some r) }.advance
        | .currentPay =>
            if ((st.calls + 1 : ℕ) : ℕ∞) ≤ caps.H then
              { st' with
                calls := st.calls + 1
                wrong := st.wrong.erase i
                history := st'.history ++ [Event.executed i r] }.advance
            else st.halt
      else st.halt
  | .decline => st.atStage fun i =>
      if st.phase = .allocating then
        { st with history := st.history ++ [Event.declined i] }.advance
      else st.halt
  | .execute j =>
      match st.pending j with
      | some r =>
          if ((st.calls + 1 : ℕ) : ℕ∞) ≤ caps.H then
            { st with
              pending := Function.update st.pending j none
              wrong := st.wrong.erase j
              calls := st.calls + 1
              history := st.history ++ [.executed j r] }
          else st.halt
      | none => st.halt

/-- The state at the start of an execution of the whole task with all tools unused. -/
def initState (I : Instance N q) : State I :=
  { stage := 0, phase := .reviewing, reviews := 0, unused := Finset.univ, pending := fun _ => none,
    wrong := ∅, calls := 0, halted := false, history := [] }

/-- The state after `n` steps from `st₀`, under a policy whose seed is fixed. -/
def runFrom (I : Instance N q) (κ : Contract) (caps : Caps N) (π : History I → Action N q)
    (st₀ : State I) (ω : Sample I) : ℕ → State I
  | 0 => st₀
  | n + 1 =>
      let st := runFrom I κ caps π st₀ ω n
      step I κ caps ω st (π st.history)

/-- **Success from `st₀`**, §2, p.5: all outputs final and truly correct. **Formalization Note.**
Abandonment, a run that never terminates and an unrepaired or unexecuted error are failures. -/
def SuccessFrom (I : Instance N q) (κ : Contract) (caps : Caps N) (π : History I → Action N q)
    (st₀ : State I) (ω : Sample I) : Prop :=
  ∃ n, (runFrom I κ caps π st₀ ω n).stage = N ∧ (runFrom I κ caps π st₀ ω n).wrong = ∅

/-- **The bill** `C = Σ c_i T_i + Σ f_ir`, §2, p.5, of a run from `st₀`, counting the charges of the
events after `st₀`.

**Formalization Note.** Valued in `ℝ≥0∞`, so a run with unbounded reviews has an infinite bill. All
failed-path charges count. -/
noncomputable def billFrom (I : Instance N q) (κ : Contract) (caps : Caps N)
    (π : History I → Action N q) (st₀ : State I) (ω : Sample I) : ENNReal :=
  ⨆ n, ENNReal.ofReal
    (((runFrom I κ caps π st₀ ω n).history.map Event.charge).sum - (st₀.history.map Event.charge).sum)

/-- The future observation charges of a run from `st₀`: the part of the bill of its reviews. -/
noncomputable def obsBillFrom (I : Instance N q) (κ : Contract) (caps : Caps N)
    (π : History I → Action N q) (st₀ : State I) (ω : Sample I) : ENNReal :=
  ⨆ n, ENNReal.ofReal
    (((runFrom I κ caps π st₀ ω n).history.map Event.obsCharge).sum -
      (st₀.history.map Event.obsCharge).sum)

/-- **A healthy state at the first entry to stage `i` with unused tools `R`**, App. E.2, p.35–36: no
current observations; every earlier error has a committed tool (possibly not yet executed), and only
earlier stages are pending. -/
def IsHealthyEntry (I : Instance N q) (st : State I) (i : ℕ) (R : Finset (Fin q)) : Prop :=
  st.stage = i ∧ st.phase = .reviewing ∧ st.reviews = 0 ∧ st.unused = R ∧ st.halted = false ∧
    (∀ j ∈ st.wrong, j.val < i ∧ (st.pending j).isSome) ∧
    ∀ j, (st.pending j).isSome → j.val < i

end CausalFailureRank


