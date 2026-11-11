-- Prove2me | Definitions.Def_DenseLanguageGeneration_PatientScope_algorithm
-- name    : DenseLanguageGeneration_PatientScope_algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:47:26.596499+00:00
-- url     : https://prove2.me/theorems/5fa3d703-f346-46a7-8e95-34c18e956f8f
-- title:
--   Operational patient-scope generator and old-chain backtracking
-- statement:
--   For a known indexed family $\mathcal L$ of infinite positive-integer languages, define the deterministic patient-scope generator $G_{\mathcal L}$ by replaying its finite received input history from the initial state. The state stores inputs, earlier outputs, scope size $s$, focus-change count $\tau$, and the number $w$ of completed rounds with the current indexed focus. Initially
--
--   $$
--   s=1,\qquad \tau=1,\qquad w=0.
--   $$
--
--   Each round receives its input before selecting an output. Recompute consistency and criticality. If the old focus is inconsistent, increment $\tau$ and backtrack to the largest index in the inherited scope that is critical both before and after this input. If none survives, use the least currently consistent index in that scope. If the scope has no consistent language, enlarge it to the first consistent index.
--
--   If the old focus survives and $w\ge2^\tau$, enlarge the scope by exactly one. Increment $\tau$ only when the indexed focus changes. Output the smallest member of the resulting focus absent from all inputs through this round and every earlier output. A changed focus has $w=1$ after this response; otherwise increase $w$ by one.
--
--   This is an operational definition: no validity, density, or charging property is a field or a transition assumption. The generator closes over the family before the unknown target and enumeration are chosen.
--
--   **Formalization Note** Scope sizes count zero-based indices, so backtracking to index $i$ sets $s=i+1$. The exponential timer tests previous completed rounds. With a surviving initial focus, the first expansion is in round 3. A globally inconsistent illegal history uses a fixed total default; no such history is used by the theorem statements. Output 1 on empty replay is not a game response. All selection predicates are classical, imposing no effective presentation or decidable-membership restriction.
-- source:
--   Cai, Li, Shen, Wang and Zhang, STOC 2027 submission #335 (October 2026), §3.2, boxed patient-scope and backtracking algorithms, printed pp.13–14 (PDF pp.15–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_criticalChain

set_option autoImplicit false
open ActiveLanguageGeneration.Hierarchy

namespace DenseLanguageGeneration.PatientScope

/-- A positive integer from its zero-based position. -/
def positive (n : ℕ) : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩

/-- §3.2 (printed pp.13--14 / PDF pp.15--16). All fields are operational data.
`age` counts completed output rounds with the current indexed focus. -/
structure State where
  inputs : List ℕ+
  outputs : List ℕ+
  scope : ℕ
  tau : ℕ
  age : ℕ
  lastOutput : ℕ+

/-- Paper time zero: no output has occurred; lastOutput is an unused total default. -/
def initial : State := ⟨[], [], 1, 1, 0, 1⟩

/-- Backtrack on the OLD critical chain. If the inherited scope has no consistent
language, search up to the first consistent index. The fixed default on globally
inconsistent histories is immaterial on legal enumerations and never uses K. -/
noncomputable def backtrackScope (L : Family) (oldh newh : List ℕ+) (s : ℕ) : ℕ := by
  classical
  let cs := (Finset.range s).filter (Consistent L newh)
  let surviving := criticalIndices L oldh s ∩ criticalIndices L newh s
  exact if hc : cs.Nonempty then
    if hs : surviving.Nonempty then surviving.max' hs + 1 else cs.min' hc + 1
  else if he : ∃ i, Consistent L newh i then Nat.find he + 1 else s

/-- Smallest focus element absent from all received inputs and all prior outputs.
One is used only if no available element exists (unreachable on legal runs). -/
noncomputable def leastFresh (F : Set ℕ+) (h b : List ℕ+) : ℕ+ := by
  classical
  exact if he : ∃ n, positive n ∈ F ∧ positive n ∉ h ∧ positive n ∉ b
    then positive (Nat.find he) else 1

/-- The boxed algorithm, with input before response. Test the exponential waiting
threshold against PREVIOUS completed rounds. An unchanged focus does not reset age
or increase tau merely because the scope expands. A new focus's first output counts
as one completed round at the end of this step. -/
noncomputable def step (L : Family) (st : State) (x : ℕ+) : State := by
  classical
  let h := st.inputs ++ [x]
  let old := focusIndex L st.inputs st.scope
  let control : ℕ × ℕ :=
    if (∃ i, old = some i ∧ Consistent L h i) then
      if 2 ^ st.tau ≤ st.age then
        let s := st.scope + 1
        (s, if focusIndex L h s = old then st.tau else st.tau + 1)
      else (st.scope, st.tau)
    else (backtrackScope L st.inputs h st.scope, st.tau + 1)
  let f := focusIndex L h control.1
  let y := leastFresh (focusSet L h control.1) h st.outputs
  exact ⟨h, st.outputs ++ [y], control.1, control.2,
    (if f = old then st.age + 1 else 1), y⟩

/-- Deterministic replay from the empty state, using only the given finite history. -/
noncomputable def replay (L : Family) (h : List ℕ+) : State :=
  h.foldl (step L) initial

/-- The family is known before play; target identity and future inputs are absent.
The response to [] is a total default and is never a game round. -/
noncomputable def generator (L : Family) : Generator ℕ+ :=
  fun h => (replay L h).lastOutput

/-- End of paper time t, with the initial state at t=0. -/
noncomputable def stateAt (L : Family) (a : ℕ → ℕ+) (t : ℕ) : State :=
  replay L (history a t)

/-- End-of-round focus, also defined at the initial time zero. -/
noncomputable def focusAt (L : Family) (a : ℕ → ℕ+) (t : ℕ) : Set ℕ+ :=
  focusSet L (history a t) (stateAt L a t).scope

end DenseLanguageGeneration.PatientScope


