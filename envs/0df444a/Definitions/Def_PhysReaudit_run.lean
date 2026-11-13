-- Prove2me | Definitions.Def_PhysReaudit_run
-- name    : PhysReaudit_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:44:04.071612+00:00
-- url     : https://prove2.me/theorems/1c436f9a-26f0-4176-aeae-fd00e410450d
-- title:
--   The run of an audit, its physical cost $C$ and target count $N$
-- statement:
--   Fix a depth $d$. Given a rule $R$ and an outcome $(w,\text{nav},\text{tgt})$, the **run** is the sequence of states produced by applying $R$'s decisions to the access model of §4: each episode starts with a root setup; at depth $i<d$ an attempt is a navigation transition that reads the next unused navigation-tape entry, moving to depth $i+1$ on success and ending the episode on failure; at depth $d$ an attempt is the target transition, which reads the next unused target-tape entry and ends the episode. An attempt issued with no active episode acts as a root setup. A halted run does not move.
--
--   From the run the module defines:
--
--   1. the **physical cost** $C\in\mathbb N\cup\{\infty\}$, the total number of root setups, navigation attempts and target attempts;
--   2. the **target count** $N\in\mathbb N\cup\{\infty\}$, the number of target attempts;
--   3. the events **accepts** (the rule halts with accept after finitely many decisions) and **stops** (it halts after finitely many decisions, with or without a certificate).
--
--   A rule that never stops never accepts; if it keeps acting its cost is infinite.
--
--   **Formalization Note** Every costly action appends one observation, so $C$ is the supremum over time of the history length.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), §4, p.2 (PDF p.3), access model: "Each episode costs one root setup, then attempts at most d navigation transitions, each succeeding with probability a. Failure terminates the episode. … Every attempted transition costs one interaction."; p.3 (PDF p.4): "Write C for new physical cost and N for target observations"

import Mathlib
import Definitions.Def_PhysReaudit_Rule

namespace PhysReaudit

/-- The state of an audit after some number of decisions: the fresh history (most recent observation
first), the current depth in the active episode (`none` if no episode is active), the number of navigation
and target tape entries consumed, and whether the audit has halted (`some true` = accepted,
`some false` = stopped without a certificate). -/
structure Cfg where
  hist : List Obs
  pos : Option ℕ
  navUsed : ℕ
  tgtUsed : ℕ
  halted : Option Bool

/-- The initial state: no observation, no active episode, nothing consumed, not halted. -/
def Cfg.init : Cfg := ⟨[], none, 0, 0, none⟩

/-- One transition of the access model (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.2 (PDF p.3)): "Each episode costs one root setup,
then attempts at most d navigation transitions, each succeeding with probability a. Failure terminates the
episode. Reaching the target permits one Bernoulli(q) transition, after which the episode terminates
regardless of its outcome."

At depth `i < d` an attempt is a navigation transition and reads the next unused entry of the navigation
tape `navT`: success moves to depth `i + 1`, failure ends the episode. At depth `d` an attempt is the target
transition and reads the next unused entry of the target tape `tgtT`; the episode then ends. A halted audit
does not move.

**Formalization Note** An `attempt` issued while no episode is active acts as a root setup (it is recorded
as `started` and costs one); it never produces a free observation. -/
def step (d : ℕ) (navT tgtT : ℕ → Bool) (act : Action) (c : Cfg) : Cfg :=
  match c.halted with
  | some _ => c
  | none =>
    match act with
    | .accept => { c with halted := some true }
    | .stop => { c with halted := some false }
    | .setup => { c with hist := .started :: c.hist, pos := some 0 }
    | .attempt =>
      match c.pos with
      | none => { c with hist := .started :: c.hist, pos := some 0 }
      | some i =>
        if i < d then
          { c with hist := .nav (navT c.navUsed) :: c.hist,
                   pos := if navT c.navUsed then some (i + 1) else none,
                   navUsed := c.navUsed + 1 }
        else
          { c with hist := .target (tgtT c.tgtUsed) :: c.hist,
                   pos := none,
                   tgtUsed := c.tgtUsed + 1 }

/-- The run of rule `R` at depth `d` on the outcome `ω = (w, navT, tgtT)`: the state after `n` decisions.
The `k`-th navigation attempt overall reads `navT k` and the `j`-th target attempt reads `tgtT j`
(0-based). -/
def run {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) : ℕ → Cfg
  | 0 => Cfg.init
  | n + 1 => step d ω.2.1 ω.2.2 (R.decide ω.1 (run R d ω n).hist) (run R d ω n)

/-- The new physical cost `C` (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4)): the number of root setups plus navigation
attempts plus target attempts, i.e. the number of costly actions taken. It is `⊤` if the rule never stops
and keeps acting.

**Formalization Note** Every costly action appends exactly one observation, so `C` is the supremum over
time of the history length. -/
noncomputable def cost {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) : ℕ∞ :=
  ⨆ n, ((run R d ω n).hist.length : ℕ∞)

/-- The number `N` of target observations (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4)), valued in `ℕ∞`. -/
noncomputable def targetCount {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) : ℕ∞ :=
  ⨆ n, ((run R d ω n).tgtUsed : ℕ∞)

/-- The rule accepts: it halts with `accept` after finitely many decisions. A run that never stops never
accepts. -/
def accepts {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) : Prop :=
  ∃ n, (run R d ω n).halted = some true

/-- The rule stops (with or without a certificate) after finitely many decisions. -/
def stops {W : Type} [MeasurableSpace W] (R : Rule W) (d : ℕ) (ω : Omega W) : Prop :=
  ∃ n, (run R d ω n).halted ≠ none

end PhysReaudit


