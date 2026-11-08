-- Prove2me | Definitions.Def_CausalFailureRank_refController
-- name    : CausalFailureRank_refController
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:14:42.166235+00:00
-- url     : https://prove2.me/theorems/3b53864c-b473-4258-80f1-8e0bf6bf3541
-- title:
--   The reference controller and its truncation
-- statement:
--   Let $B_1(r)=\lceil\log_2(1/r)\rceil$, $B_{j+1}(r)=\lceil\log_2(2+B_j(r))\rceil$ and $p_j(r)=1/(4(1+B_j(r)))$. At a healthy state with risk parameter $r$ the **reference controller** applies:
--
--   1. If $\rho=\infty$: no observations, a blind write, and after an actual error a tool of maximal bad-child rank.
--   2. If $d_b=0$: the SPRT of target $r/2$ and a MAP write; after a correct report continue with $r/2$; after an error abandon.
--   3. Otherwise: the SPRT of target $p_{d_b}(r)$ and a MAP write; after a correct report continue with $r/2$; after an error correct with a tool of maximal bad-child rank and continue with $r'=\min\{1/4,r/(2p)\}$.
--
--   The **truncated** variant also abandons the task when a test exhausts its given quota without stopping.
--
--   **Formalization Note** The tie among maximal tools is an arbitrary selection, so the results quantify over all selections. The controller reads its memory off the visible history. Real risk parameters are allowed.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4, pp.17–18; App. B.5, p.19

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_step
import Definitions.Def_CausalFailureRank_J

namespace CausalFailureRank

variable {N q : ℕ}

/-- `B_1(r) = ⌈log₂(1/r)⌉`, `B_{j+1}(r) = ⌈log₂(2 + B_j(r))⌉`, App. B.4, p.17. The paper's indices start
at `1`; `B 0` is not used. -/
noncomputable def B : ℕ → ℝ → ℕ
  | 0, _ => 0
  | 1, r => ⌈Real.logb 2 (1 / r)⌉₊
  | j + 2, r => ⌈Real.logb 2 (2 + (B (j + 1) r : ℝ))⌉₊

/-- `p_j(r) = 1 / (4 (1 + B_j(r)))`, App. B.4, p.17. -/
noncomputable def pj (j : ℕ) (r : ℝ) : ℝ := 1 / (4 * (1 + (B j r : ℝ)))

/-- `sel` picks, at every state with an available tool, "any tool maximizing the bad-child rank", p.18. -/
def IsBadChildSelection (I : Instance N q) (sel : Fin N → Finset (Fin q) → Option (Fin q)) : Prop :=
  ∀ i R, (I.S i ∩ R).Nonempty → ∃ r, sel i R = some r ∧ r ∈ I.S i ∩ R ∧
    rank I (i.val + 1) (R.erase r) = db I i R

/-- What the reference controller tracks: the stage, the unused tools and the risk parameter. -/
structure RefMemory (q : ℕ) where
  /-- The current stage. -/
  stage : ℕ
  /-- The unused tools. -/
  R : Finset (Fin q)
  /-- The current risk parameter `r`. -/
  r : ℝ
  /-- The bit written at the current stage, once it has been written. -/
  written : Option Bool
  /-- Whether an actual error at the current stage awaits its allocation. -/
  awaiting : Bool

open scoped Classical in
/-- The target of the local test at state `(i, R)` with risk `r`: `r / 2` if `d_b = 0` (rule 2), else
`p_{d_b}(r)` (rule 3), App. B.4, pp.17–18. Infinite-rank states take no test. -/
noncomputable def target (I : Instance N q) (i : Fin N) (R : Finset (Fin q)) (r : ℝ) : ℝ :=
  if db I i R = 0 then r / 2 else pj (db I i R).toNat r

open scoped Classical in
/-- The memory update of the reference controller on one visible event. A correct report continues
with risk `r / 2` (rules 2, 3); a commitment continues with `r' = min {1/4, r / (2 p)}` (rule 3).
Infinite-rank states keep their (irrelevant) parameter. -/
noncomputable def refUpdate (I : Instance N q) (m : RefMemory q) : Event I → RefMemory q
  | .wrote _ b => { m with written := some b }
  | .report i x =>
      if m.written = some x then
        { m with
          stage := m.stage + 1
          r := if rank I i.val m.R = ⊤ then m.r else m.r / 2
          written := none }
      else { m with awaiting := true }
  | .committed i t =>
      { m with
        stage := m.stage + 1
        R := m.R.erase t
        r := if rank I i.val m.R = ⊤ then m.r else min (1 / 4) (m.r / (2 * target I i m.R m.r))
        written := none
        awaiting := false }
  | _ => m

/-- The observations of stage `i` in a history, oldest first. -/
def obsAt (I : Instance N q) (i : Fin N) : History I → List (I.α i)
  | [] => []
  | .obs j y :: h => if hj : j = i then (hj ▸ y) :: obsAt I i h else obsAt I i h
  | _ :: h => obsAt I i h

open scoped Classical in
/-- **The reference controller and its truncation.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines
Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4,
pp.17–18, and App. B.5, p.19, started at stage `i₀`, unused tools `R₀`, risk `r₀`.

1. If `ρ = ∞`: no observations, a blind write; after an actual error, the selected tool.
2. If `d_b = 0`: the SPRT at target `r / 2`, write MAP; after an error, abandon.
3. Otherwise: the SPRT at target `p_{d_b}(r)`, write MAP; after an error, the selected tool.

`cap = some Q̂` is the truncated variant: "If a test exhausts Q̂_i without stopping, abandon the entire
task"; `cap = none` is the untruncated reference controller. After the last stage it stops.

**Formalization Note.** `commit` under contract `currentPay` executes immediately, as the paper's
controllers do. The blind write is `false`, an arbitrary choice. -/
noncomputable def refAction (I : Instance N q) (sel : Fin N → Finset (Fin q) → Option (Fin q))
    (cap : Option (Fin N → ℕ)) (i₀ : ℕ) (R₀ : Finset (Fin q)) (r₀ : ℝ) (h : History I) : Action N q :=
  let m := h.foldl (refUpdate I) { stage := i₀, R := R₀, r := r₀, written := none, awaiting := false }
  if hi : m.stage < N then
    let i : Fin N := ⟨m.stage, hi⟩
    if m.awaiting then
      if db I i m.R = 0 then .stop
      else
        match sel i m.R with
        | some t => .commit t
        | none => .stop
    else if rank I i m.R = ⊤ then .write false
    else
      match sprtRule I i (target I i m.R m.r) (obsAt I i h) with
      | some b => .write b
      | none =>
          match cap with
          | some Q => if (obsAt I i h).length < Q i then .review else .stop
          | none => .review
  else .stop

/-- The healthy state at the first entry to stage `i` with unused tools `R`, nothing pending and no
history. -/
def entryState (I : Instance N q) (i : ℕ) (R : Finset (Fin q)) : State I :=
  { stage := i, phase := .reviewing, reviews := 0, unused := R, pending := fun _ => none,
    wrong := ∅, calls := 0, halted := false, history := [] }

/-- No caps at all: the reference controller's untruncated world. -/
def noCaps (N : ℕ) : Caps N := { Q := fun _ => ⊤, H := ⊤ }

end CausalFailureRank


