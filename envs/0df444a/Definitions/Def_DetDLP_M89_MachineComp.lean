-- Prove2me | Definitions.Def_DetDLP_M89_MachineComp
-- name    : DetDLP_M89_MachineComp
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T17:22:02.914577+00:00
-- url     : https://prove2.me/theorems/e95dafb5-80d7-4410-9903-0faee9f41d20
-- title:
--   Bounded deterministic machine composition with preserved tapes
-- statement:
--   Framed oracle calls preserve unrelated tapes and account for both visited-cell histories and elapsed time. Sequential and repeated calls are represented by finite control on the same primitive multitape model.
-- source:
--   Local verified MachineComposition module; bounded-computation infrastructure for Liu, Zhang, and Ren, Section 3.3, Proposition 3.3.

import Definitions.Def_DetDLP_Machine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.MachineComposition

/-! Execution lemmas for the exact primitive machine and visited-cell semantics used by
`DetDLP.RunsWithin`.  No target theorem is imported. -/

namespace Trace

universe u v
variable {α : Type u} {β : Type v} {step : α → Option α}

theorem zero_iff {a b : α} : Computation.Trace step 0 a b ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .refl _

theorem append {a b c : α} {m n : ℕ}
    (h₁ : Computation.Trace step m a b) (h₂ : Computation.Trace step n b c) :
    Computation.Trace step (m + n) a c := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons m a b c hs ht ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Computation.Trace.cons hs (ih h₂))

theorem split {a c : α} {m n : ℕ}
    (h : Computation.Trace step (m + n) a c) :
    ∃ b, Computation.Trace step m a b ∧ Computation.Trace step n b c := by
  induction m generalizing a with
  | zero => exact ⟨a, .refl _, by simpa using h⟩
  | succ m ih =>
    have hh : Computation.Trace step ((m + n) + 1) a c := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    cases hh with
    | @cons _ _ b _ hs ht =>
      rcases ih ht with ⟨d, hd, he⟩
      exact ⟨d, .cons hs hd, he⟩

theorem endpoint_unique {a b c : α} {n : ℕ}
    (h₁ : Computation.Trace step n a b) (h₂ : Computation.Trace step n a c) : b = c := by
  induction h₁ generalizing c with
  | refl => cases h₂; rfl
  | @cons n a b d hs ht ih =>
    cases h₂ with
    | @cons _ _ e _ hs' ht' =>
      have : b = e := Option.some.inj (hs.symm.trans hs')
      subst e
      exact ih ht'

theorem take_prefix {a c : α} {n k : ℕ} (h : Computation.Trace step n a c) (hk : k ≤ n) :
    ∃ b, Computation.Trace step k a b ∧ Computation.Trace step (n-k) b c := by
  exact split (by simpa [Nat.add_sub_of_le hk] using h)

theorem map {step' : β → Option β} (f : α → β)
    (hsim : ∀ a b, step a = some b → step' (f a) = some (f b))
    {a b : α} {n : ℕ} (h : Computation.Trace step n a b) :
    Computation.Trace step' n (f a) (f b) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact .cons (hsim _ _ hs) ih

/-- Every prefix of a simulated terminating trace comes from a source prefix.
This includes prefix zero, as required by `RunsWithin`. -/
theorem prefix_of_map {step' : β → Option β} (f : α → β)
    (hsim : ∀ a b, step a = some b → step' (f a) = some (f b))
    {a b : α} {n k : ℕ} (h : Computation.Trace step n a b) (hk : k ≤ n)
    {c : β} (hc : Computation.Trace step' k (f a) c) :
    ∃ d, Computation.Trace step k a d ∧ c = f d := by
  rcases take_prefix h hk with ⟨d, hd, _⟩
  exact ⟨d, hd, endpoint_unique hc (map f hsim hd)⟩

end Trace

/-- A machine segment with a bound on every execution prefix; it does not require
its initial state to be the global start state, or its final state to halt. -/
def Segment (A : PrimitiveMachine) (a b : LocatedCfg A) (n : ℕ) (σ : ℝ) : Prop :=
  Computation.Trace (locatedStep A) n a b ∧
  ∀ k c, k ≤ n → Computation.Trace (locatedStep A) k a c → (visitedSpace c : ℝ) ≤ σ

namespace Segment

variable {A : PrimitiveMachine} {a b c : LocatedCfg A} {m n : ℕ} {σ ρ : ℝ}

theorem refl (h : (visitedSpace a : ℝ) ≤ σ) : Segment A a a 0 σ := by
  refine ⟨.refl _, ?_⟩
  intro k c hk hc
  have : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  cases hc
  exact h

theorem mono (h : Segment A a b n σ) (hσ : σ ≤ ρ) : Segment A a b n ρ :=
  ⟨h.1, fun k c hk hc => (h.2 k c hk hc).trans hσ⟩

/-- Sequential composition retains the maximum of the two visited-space bounds.
The time is exactly the sum of the two segment lengths. -/
theorem append (h₁ : Segment A a b m σ) (h₂ : Segment A b c n ρ) :
    Segment A a c (m+n) (max σ ρ) := by
  refine ⟨Trace.append h₁.1 h₂.1, ?_⟩
  intro k d hk hd
  by_cases hkm : k ≤ m
  · exact (h₁.2 k d hkm hd).trans (le_max_left _ _)
  · have hmk : m ≤ k := by omega
    have hsplit : Computation.Trace (locatedStep A) (m + (k-m)) a d := by
      simpa [Nat.add_sub_of_le hmk] using hd
    rcases Trace.split hsplit with ⟨e, he, hed⟩
    have heq := Trace.endpoint_unique h₁.1 he
    subst e
    exact (h₂.2 (k-m) d (by omega) hed).trans (le_max_right _ _)

end Segment

/-- `RunsWithin` is precisely a bounded segment from the initialized configuration,
with a halting endpoint and the designated output tape. -/
theorem runsWithin_iff_segment (A : PrimitiveMachine) (out : Fin A.tapeCount)
    (input output : List Bool) (τ σ : ℝ) :
    RunsWithin A out input output τ σ ↔
      ∃ n c, Segment A (locatedInit A input) c n σ ∧
        (∃ b : Bool, c.config.state = Sum.inl b) ∧
        c.config.tapes out = Turing.Tape.mk₁ (output.map some) ∧ (n : ℝ) ≤ τ := by
  constructor
  · rintro ⟨n, c, ht, hh, ho, hn, hs⟩
    exact ⟨n, c, ⟨ht, hs⟩, hh, ho, hn⟩
  · rintro ⟨n, c, ⟨ht, hs⟩, hh, ho, hn⟩
    exact ⟨n, c, ht, hh, ho, hn, hs⟩

theorem runsWithin_mono {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ σ τ' σ' : ℝ}
    (h : RunsWithin A out input output τ σ) (ht : τ ≤ τ') (hs : σ ≤ σ') :
    RunsWithin A out input output τ' σ' := by
  rcases h with ⟨n, c, hc, hh, ho, hn, hspace⟩
  exact ⟨n, c, hc, hh, ho, hn.trans ht,
    fun k d hk hd => (hspace k d hk hd).trans hs⟩

/-- Add `r` unused work tapes.  The finite control and each primitive action remain
unchanged; only the scanned tape index is embedded into the larger tape set. -/
def addTapes (A : PrimitiveMachine) (r : ℕ) : PrimitiveMachine where
  tapeCount := A.tapeCount + r
  stateCount := A.stateCount
  inputTape := Fin.castAdd r A.inputTape
  start := A.start
  scan q := Fin.castAdd r (A.scan q)
  transition := A.transition

def addTapesCfg (A : PrimitiveMachine) (r : ℕ) (c : A.Cfg) : (addTapes A r).Cfg where
  state := c.state
  tapes := Fin.append c.tapes (fun _ : Fin r => Turing.Tape.mk₁ [])

def addTapesLocated (A : PrimitiveMachine) (r : ℕ) (c : LocatedCfg A) :
    LocatedCfg (addTapes A r) where
  config := addTapesCfg A r c.config
  position := Fin.append c.position (fun _ : Fin r => 0)
  lower := Fin.append c.lower (fun _ : Fin r => 0)
  upper := Fin.append c.upper (fun _ : Fin r => 0)

private theorem natAdd_ne_castAdd {m r : ℕ} (i : Fin r) (j : Fin m) :
    Fin.natAdd m i ≠ Fin.castAdd r j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

private theorem append_update {α : Type*} {m r : ℕ} (f : Fin m → α)
    (g : Fin r → α) (i : Fin m) (a : α) :
    Function.update (Fin.append f g) (Fin.castAdd r i) a =
      Fin.append (Function.update f i a) g := by
  funext j
  induction j using Fin.addCases with
  | left j => simp [Function.update_apply, Fin.castAdd_inj]
  | right j => simp [natAdd_ne_castAdd]

@[simp] theorem addTapesCfg_step (A : PrimitiveMachine) (r : ℕ) (c : A.Cfg) :
    (addTapes A r).step (addTapesCfg A r c) =
      (A.step c).map (addTapesCfg A r) := by
  rcases c with ⟨state, tapes⟩
  cases state with
  | inl b => rfl
  | inr q =>
    simp only [PrimitiveMachine.step, addTapesCfg, addTapes, Fin.append_left]
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨q', action⟩
      cases action <;> simp [Option.map, addTapesCfg, append_update]

@[simp] theorem addTapesLocated_monitor (A : PrimitiveMachine) (r : ℕ)
    (c : LocatedCfg A) (c' : A.Cfg) :
    (addTapesLocated A r c).monitor (addTapesCfg A r c') =
      addTapesLocated A r (c.monitor c') := by
  rcases c with ⟨⟨state, tapes⟩, position, lower, upper⟩
  cases state with
  | inl b => rfl
  | inr q =>
    simp only [LocatedCfg.monitor, addTapesLocated, addTapesCfg, addTapes,
      Sum.elim_inr, Fin.append_left]
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨q', action⟩
      simp [append_update]

@[simp] theorem addTapesLocated_step (A : PrimitiveMachine) (r : ℕ)
    (c : LocatedCfg A) :
    locatedStep (addTapes A r) (addTapesLocated A r c) =
      (locatedStep A c).map (addTapesLocated A r) := by
  unfold locatedStep
  rw [show (addTapesLocated A r c).config = addTapesCfg A r c.config from rfl,
    addTapesCfg_step]
  cases hs : A.step c.config <;> simp

private theorem locatedCfg_ext {A : PrimitiveMachine} {c d : LocatedCfg A}
    (hc : c.config = d.config) (hp : c.position = d.position)
    (hl : c.lower = d.lower) (hu : c.upper = d.upper) : c = d := by
  cases c; cases d; simp_all

private theorem cfg_ext {A : PrimitiveMachine} {c d : A.Cfg}
    (hs : c.state = d.state) (ht : c.tapes = d.tapes) : c = d := by
  cases c; cases d; simp_all

@[simp] theorem addTapesLocated_init (A : PrimitiveMachine) (r : ℕ) (input : List Bool) :
    locatedInit (addTapes A r) input = addTapesLocated A r (locatedInit A input) := by
  apply locatedCfg_ext
  · apply cfg_ext
    · rfl
    · funext i
      induction i using Fin.addCases with
      | left i => simp [locatedInit, PrimitiveMachine.init, addTapesLocated,
          addTapesCfg, addTapes, Fin.castAdd_inj]
      | right i => simp [locatedInit, PrimitiveMachine.init, addTapesLocated,
          addTapesCfg, addTapes, natAdd_ne_castAdd]
  · funext i; induction i using Fin.addCases <;> simp [locatedInit, addTapesLocated]
  · funext i; induction i using Fin.addCases <;> simp [locatedInit, addTapesLocated]
  · funext i
    induction i using Fin.addCases with
    | left i => simp [locatedInit, addTapesLocated, addTapes, Fin.castAdd_inj]
    | right i => simp [locatedInit, addTapesLocated, addTapes, natAdd_ne_castAdd]

/-- Each additional blank tape contributes exactly one visited cell. -/
@[simp] theorem addTapesLocated_space (A : PrimitiveMachine) (r : ℕ) (c : LocatedCfg A) :
    visitedSpace (addTapesLocated A r c) = visitedSpace c + r := by
  change (∑ i : Fin (A.tapeCount + r),
    (Fin.append c.upper (fun _ : Fin r => 0) i -
      Fin.append c.lower (fun _ : Fin r => 0) i + 1).toNat) = visitedSpace c + r
  rw [Fin.sum_univ_add]
  simp [visitedSpace]

/-- An exact run transfers to a machine with extra work tapes with no time overhead.
All prefix configurations are accounted for, including the initial configuration. -/
theorem runsWithin_addTapes {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ σ : ℝ} (r : ℕ)
    (h : RunsWithin A out input output τ σ) :
    RunsWithin (addTapes A r) (Fin.castAdd r out) input output τ (σ + r) := by
  rcases h with ⟨n, c, hc, hh, ho, hn, hs⟩
  have hsim : ∀ a b, locatedStep A a = some b →
      locatedStep (addTapes A r) (addTapesLocated A r a) =
        some (addTapesLocated A r b) := by
    intro a b hab
    simp [hab]
  refine ⟨n, addTapesLocated A r c, ?_, hh, ?_, hn, ?_⟩
  · rw [addTapesLocated_init]
    exact Trace.map _ hsim hc
  · simpa [addTapesLocated, addTapesCfg] using ho
  · intro k d hk hd
    rw [addTapesLocated_init] at hd
    rcases Trace.prefix_of_map _ hsim hc hk hd with ⟨e, he, rfl⟩
    rw [addTapesLocated_space, Nat.cast_add]
    linarith [hs k e hk he]

/-- The current head belongs to the recorded visited interval on every tape. -/
def LocatedWellFormed {A : PrimitiveMachine} (c : LocatedCfg A) : Prop :=
  ∀ i, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i

@[simp] theorem locatedWellFormed_init (A : PrimitiveMachine) (input : List Bool) :
    LocatedWellFormed (locatedInit A input) := by
  intro i
  simp only [locatedInit, le_refl, true_and]
  split
  · exact Int.natCast_nonneg _
  · exact le_refl _

/-- Monitoring any primitive action preserves the head/visited-interval invariant. -/
theorem locatedWellFormed_monitor {A : PrimitiveMachine} {c : LocatedCfg A}
    (h : LocatedWellFormed c) (c' : A.Cfg) : LocatedWellFormed (c.monitor c') := by
  intro i
  unfold LocatedCfg.monitor
  cases hs : c.config.state with
  | inl b => exact h i
  | inr q =>
    simp only [Sum.elim_inr]
    cases ht : A.transition q (c.config.tapes (A.scan q)).head with
    | inl b => exact h i
    | inr qa =>
      rcases qa with ⟨q', action⟩
      by_cases hi : i = A.scan q
      · subst i; simp
      · simpa [Function.update_of_ne hi] using h i

theorem locatedWellFormed_step {A : PrimitiveMachine} {c d : LocatedCfg A}
    (h : LocatedWellFormed c) (hs : locatedStep A c = some d) : LocatedWellFormed d := by
  unfold locatedStep at hs
  cases ht : A.step c.config with
  | none => simp [ht] at hs
  | some d' =>
    have : c.monitor d' = d := by simpa [ht] using hs
    subst d
    exact locatedWellFormed_monitor h _

theorem locatedWellFormed_trace {A : PrimitiveMachine} {a b : LocatedCfg A} {n : ℕ}
    (h : LocatedWellFormed a) (ht : Computation.Trace (locatedStep A) n a b) :
    LocatedWellFormed b := by
  induction ht with
  | refl => exact h
  | cons hs ht ih => exact ih (locatedWellFormed_step h hs)

theorem locatedWellFormed_reachable {A : PrimitiveMachine} {input : List Bool}
    {b : LocatedCfg A} {n : ℕ}
    (ht : Computation.Trace (locatedStep A) n (locatedInit A input) b) :
    LocatedWellFormed b :=
  locatedWellFormed_trace (locatedWellFormed_init A input) ht

/-- Replacing a halting transition by a control-flow jump implemented as a write of
the scanned symbol leaves the tape and visited interval unchanged. -/
theorem monitor_noop {A : PrimitiveMachine} {c : LocatedCfg A} {q q' : Fin A.stateCount}
    (hw : LocatedWellFormed c) (hq : c.config.state = Sum.inr q)
    (ht : A.transition q (c.config.tapes (A.scan q)).head =
      Sum.inr (q', .write (c.config.tapes (A.scan q)).head)) :
    locatedStep A c = some { c with config := { c.config with state := Sum.inr q' } } := by
  have hl : Function.update c.lower (A.scan q)
      (min (c.lower (A.scan q)) (c.position (A.scan q))) = c.lower := by
    simp [min_eq_left (hw _).1]
  have hu : Function.update c.upper (A.scan q)
      (max (c.upper (A.scan q)) (c.position (A.scan q))) = c.upper := by
    simp [max_eq_left (hw _).2]
  simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, hq, ht,
    headDisplacement, hl, hu]

/-- Finite control over a fixed collection of tapes. This permits two programs to
share the same working tapes without casts between unrelated `Fin` types. -/
structure Program (tapes : ℕ) where
  stateCount : ℕ
  start : Fin stateCount
  scan : Fin stateCount → Fin tapes
  transition : Fin stateCount → Option Bool →
    Bool ⊕ (Fin stateCount × Turing.TM0.Stmt (Option Bool))

def Program.ofMachine (A : PrimitiveMachine) : Program A.tapeCount where
  stateCount := A.stateCount
  start := A.start
  scan := A.scan
  transition := A.transition

def Program.machine {tapes : ℕ} (P : Program tapes) (input : Fin tapes) : PrimitiveMachine where
  tapeCount := tapes
  stateCount := P.stateCount
  inputTape := input
  start := P.start
  scan := P.scan
  transition := P.transition

/-- Actual sequential finite control. A halting transition of `A` becomes a jump
to `B.start`, writing back the currently scanned symbol. Thus a call has no extra
primitive steps compared with the original halting run of `A`. -/
def thenMachine (A : PrimitiveMachine) (B : Program A.tapeCount) : PrimitiveMachine where
  tapeCount := A.tapeCount
  stateCount := A.stateCount + B.stateCount
  inputTape := A.inputTape
  start := Fin.castAdd B.stateCount A.start
  scan := Fin.append A.scan B.scan
  transition := Fin.append
    (fun q symbol => match A.transition q symbol with
      | .inl _ => .inr (Fin.natAdd A.stateCount B.start, .write symbol)
      | .inr (q', action) => .inr (Fin.castAdd B.stateCount q', action))
    (fun q symbol => match B.transition q symbol with
      | .inl answer => .inl answer
      | .inr (q', action) => .inr (Fin.natAdd A.stateCount q', action))

def leftCfg (A : PrimitiveMachine) (B : Program A.tapeCount) (c : LocatedCfg A) :
    LocatedCfg (thenMachine A B) where
  config := ⟨c.config.state.elim
    (fun _ => .inr (Fin.natAdd A.stateCount B.start))
    (fun q => .inr (Fin.castAdd B.stateCount q)), c.config.tapes⟩
  position := c.position
  lower := c.lower
  upper := c.upper

def rightCfg (A : PrimitiveMachine) (B : Program A.tapeCount)
    (c : LocatedCfg (B.machine A.inputTape)) : LocatedCfg (thenMachine A B) where
  config := ⟨c.config.state.elim Sum.inl (fun q => .inr (Fin.natAdd A.stateCount q)),
    c.config.tapes⟩
  position := c.position
  lower := c.lower
  upper := c.upper

/-- Entry into the continuation preserves both the tapes and all visited intervals.
In particular, space used by earlier phases is never forgotten. -/
def restartCfg (A : PrimitiveMachine) (B : Program A.tapeCount) (c : LocatedCfg A) :
    LocatedCfg (B.machine A.inputTape) where
  config := ⟨.inr B.start, c.config.tapes⟩
  position := c.position
  lower := c.lower
  upper := c.upper

@[simp] theorem leftCfg_space (A : PrimitiveMachine) (B : Program A.tapeCount)
    (c : LocatedCfg A) : visitedSpace (leftCfg A B c) = visitedSpace c := rfl

@[simp] theorem rightCfg_space (A : PrimitiveMachine) (B : Program A.tapeCount)
    (c : LocatedCfg (B.machine A.inputTape)) : visitedSpace (rightCfg A B c) = visitedSpace c := rfl

@[simp] theorem leftCfg_init (A : PrimitiveMachine) (B : Program A.tapeCount)
    (input : List Bool) : leftCfg A B (locatedInit A input) =
      locatedInit (thenMachine A B) input := rfl

theorem leftCfg_halt (A : PrimitiveMachine) (B : Program A.tapeCount)
    {c : LocatedCfg A} (h : ∃ b, c.config.state = Sum.inl b) :
    leftCfg A B c = rightCfg A B (restartCfg A B c) := by
  rcases h with ⟨b, hb⟩
  unfold leftCfg rightCfg restartCfg
  simp [hb]

/-- Every primitive source step is one primitive step of the first phase.
The well-formedness premise justifies the no-op write on return. -/
theorem thenMachine_left_step (A : PrimitiveMachine) (B : Program A.tapeCount)
    {c d : LocatedCfg A} (hw : LocatedWellFormed c) (h : locatedStep A c = some d) :
    locatedStep (thenMachine A B) (leftCfg A B c) = some (leftCfg A B d) := by
  rcases c with ⟨⟨state, tapes⟩, position, lower, upper⟩
  cases state with
  | inl b => simp [locatedStep, PrimitiveMachine.step] at h
  | inr q =>
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b =>
      have hd : d = ⟨⟨Sum.inl b, tapes⟩, position, lower, upper⟩ := by
        simpa [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, ht] using h.symm
      subst d
      have hl : min (lower (A.scan q)) (position (A.scan q)) = lower (A.scan q) :=
        min_eq_left (hw _).1
      have hu : max (upper (A.scan q)) (position (A.scan q)) = upper (A.scan q) :=
        max_eq_left (hw _).2
      simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, leftCfg,
        thenMachine, ht, headDisplacement, hl, hu]
    | inr qa =>
      rcases qa with ⟨q', action⟩
      cases action <;>
        simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, ht,
          headDisplacement] at h <;>
        subst d <;>
        simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, leftCfg,
          thenMachine, ht, headDisplacement]

/-- The continuation is embedded step-for-step, including its final halt. -/
theorem thenMachine_right_step (A : PrimitiveMachine) (B : Program A.tapeCount)
    {c d : LocatedCfg (B.machine A.inputTape)} (h : locatedStep (B.machine A.inputTape) c = some d) :
    locatedStep (thenMachine A B) (rightCfg A B c) = some (rightCfg A B d) := by
  rcases c with ⟨⟨state, tapes⟩, position, lower, upper⟩
  cases state with
  | inl b => simp [locatedStep, PrimitiveMachine.step] at h
  | inr q =>
    cases ht : B.transition q (tapes (B.scan q)).head with
    | inl b =>
      have hd : d = ⟨⟨Sum.inl b, tapes⟩, position, lower, upper⟩ := by
        simpa [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor,
          Program.machine, ht] using h.symm
      subst d
      simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, rightCfg,
        thenMachine, Program.machine, ht]
    | inr qa =>
      rcases qa with ⟨q', action⟩
      cases action <;>
        simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, Program.machine,
          ht, headDisplacement] at h <;>
        subst d <;>
        simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, rightCfg,
          thenMachine, Program.machine, ht, headDisplacement]

theorem thenMachine_left_trace (A : PrimitiveMachine) (B : Program A.tapeCount)
    {c d : LocatedCfg A} {n : ℕ} (hw : LocatedWellFormed c)
    (h : Computation.Trace (locatedStep A) n c d) :
    Computation.Trace (locatedStep (thenMachine A B)) n (leftCfg A B c) (leftCfg A B d) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih =>
    exact .cons (thenMachine_left_step A B hw hs) (ih (locatedWellFormed_step hw hs))

theorem thenMachine_left_segment (A : PrimitiveMachine) (B : Program A.tapeCount)
    {c d : LocatedCfg A} {n : ℕ} {σ : ℝ} (hw : LocatedWellFormed c)
    (h : Segment A c d n σ) :
    Segment (thenMachine A B) (leftCfg A B c) (leftCfg A B d) n σ := by
  refine ⟨thenMachine_left_trace A B hw h.1, ?_⟩
  intro k e hk he
  rcases Trace.take_prefix h.1 hk with ⟨f, hf, _⟩
  have heq := Trace.endpoint_unique he (thenMachine_left_trace A B hw hf)
  subst e
  exact h.2 k f hk hf

theorem thenMachine_right_segment (A : PrimitiveMachine) (B : Program A.tapeCount)
    {c d : LocatedCfg (B.machine A.inputTape)} {n : ℕ} {σ : ℝ}
    (h : Segment (B.machine A.inputTape) c d n σ) :
    Segment (thenMachine A B) (rightCfg A B c) (rightCfg A B d) n σ := by
  have hsim := fun a b => @thenMachine_right_step A B a b
  refine ⟨Trace.map _ hsim h.1, ?_⟩
  intro k e hk he
  rcases Trace.prefix_of_map _ hsim h.1 hk he with ⟨f, hf, rfl⟩
  exact h.2 k f hk hf

/-- Sequential calls add their exact step counts and retain the maximum of their
full-prefix visited-space bounds, with no reset of the visited-cell history. -/
theorem thenMachine_segments (A : PrimitiveMachine) (B : Program A.tapeCount)
    {a b : LocatedCfg A} {c : LocatedCfg (B.machine A.inputTape)}
    {m n : ℕ} {σ ρ : ℝ} (hw : LocatedWellFormed a)
    (ha : Segment A a b m σ) (hh : ∃ answer, b.config.state = Sum.inl answer)
    (hb : Segment (B.machine A.inputTape) (restartCfg A B b) c n ρ) :
    Segment (thenMachine A B) (leftCfg A B a) (rightCfg A B c) (m+n) (max σ ρ) := by
  have hleft := thenMachine_left_segment A B hw ha
  rw [leftCfg_halt A B hh] at hleft
  exact hleft.append (thenMachine_right_segment A B hb)

/-- Package an actual sequential run in the mission's `RunsWithin` predicate. -/
theorem thenMachine_runsWithin (A : PrimitiveMachine) (B : Program A.tapeCount)
    (out : Fin A.tapeCount) (input output : List Bool)
    {a : LocatedCfg A} {b : LocatedCfg (B.machine A.inputTape)}
    {m n : ℕ} {τ σ ρ : ℝ}
    (ha : Segment A (locatedInit A input) a m σ)
    (hha : ∃ answer, a.config.state = Sum.inl answer)
    (hb : Segment (B.machine A.inputTape) (restartCfg A B a) b n ρ)
    (hhb : ∃ answer, b.config.state = Sum.inl answer)
    (ho : b.config.tapes out = Turing.Tape.mk₁ (output.map some))
    (ht : ((m+n : ℕ) : ℝ) ≤ τ) :
    RunsWithin (thenMachine A B) out input output τ (max σ ρ) := by
  apply (runsWithin_iff_segment _ _ _ _ _ _).2
  refine ⟨m+n, rightCfg A B b, ?_, ?_, ho, ht⟩
  · simpa using thenMachine_segments A B (locatedWellFormed_init A input) ha hha hb
  · rcases hhb with ⟨answer, hh⟩
    exact ⟨answer, by simp [rightCfg, hh]⟩

/-- A convenience form with separate upper bounds for the two execution phases. -/
theorem thenMachine_runsWithin_add (A : PrimitiveMachine) (B : Program A.tapeCount)
    (out : Fin A.tapeCount) (input output : List Bool)
    {a : LocatedCfg A} {b : LocatedCfg (B.machine A.inputTape)}
    {m n : ℕ} {τ₁ τ₂ σ ρ : ℝ}
    (ha : Segment A (locatedInit A input) a m σ)
    (hha : ∃ answer, a.config.state = Sum.inl answer)
    (hb : Segment (B.machine A.inputTape) (restartCfg A B a) b n ρ)
    (hhb : ∃ answer, b.config.state = Sum.inl answer)
    (ho : b.config.tapes out = Turing.Tape.mk₁ (output.map some))
    (ht₁ : (m : ℝ) ≤ τ₁) (ht₂ : (n : ℝ) ≤ τ₂) :
    RunsWithin (thenMachine A B) out input output (τ₁+τ₂) (max σ ρ) := by
  apply thenMachine_runsWithin A B out input output ha hha hb hhb ho
  exact_mod_cast add_le_add ht₁ ht₂

/-- A uniform one-step halting machine, useful as a terminal continuation. -/
def haltMachine : PrimitiveMachine where
  tapeCount := 1
  stateCount := 1
  inputTape := 0
  start := 0
  scan _ := 0
  transition _ _ := .inl true

/-- This primitive machine returns its input in one step, retaining exactly
`max input.length 1` initially visited cells. -/
theorem haltMachine_runsWithin (input : List Bool) :
    RunsWithin haltMachine haltMachine.inputTape input input 1 ((max input.length 1 : ℕ) : ℝ) := by
  let initial := locatedInit haltMachine input
  let final : LocatedCfg haltMachine :=
    { initial with config := { initial.config with state := .inl true } }
  have hs : locatedStep haltMachine initial = some final := rfl
  have hv : visitedSpace initial = max input.length 1 := by
    simp [initial, visitedSpace, locatedInit, haltMachine]
    omega
  have hvf : visitedSpace final = max input.length 1 := hv
  refine ⟨1, final, .cons hs (.refl _), ⟨true, rfl⟩, ?_, by norm_num, ?_⟩
  · simp [final, initial, locatedInit, PrimitiveMachine.init, haltMachine]
  · intro k c hk hc
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · have : c = initial := (Trace.zero_iff.1 hc).symm
      subst c
      exact le_of_eq (congrArg (fun n : ℕ => (n : ℝ)) hv)
    · have : c = final := Trace.endpoint_unique hc (.cons hs (.refl _))
      subst c
      exact le_of_eq (congrArg (fun n : ℕ => (n : ℝ)) hvf)

/-- The monitor never forgets a visited cell. This does not need a well-formedness
hypothesis: `min`/`max` extend every interval monotonically. -/
theorem visitedSpace_le_monitor {A : PrimitiveMachine} (c : LocatedCfg A) (d : A.Cfg) :
    visitedSpace c ≤ visitedSpace (c.monitor d) := by
  unfold visitedSpace LocatedCfg.monitor
  cases hs : c.config.state with
  | inl b => exact le_refl _
  | inr q =>
    simp only [Sum.elim_inr]
    cases ht : A.transition q (c.config.tapes (A.scan q)).head with
    | inl b => exact le_refl _
    | inr qa =>
      rcases qa with ⟨q', action⟩
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = A.scan q
      · subst i
        simp only [Sum.elim_inr, Function.update_self]
        apply Int.toNat_le_toNat
        have hl := min_le_left (c.lower (A.scan q))
          (c.position (A.scan q) + headDisplacement action)
        have hu := le_max_left (c.upper (A.scan q))
          (c.position (A.scan q) + headDisplacement action)
        omega
      · simp [hi]

theorem visitedSpace_le_step {A : PrimitiveMachine} {c d : LocatedCfg A}
    (h : locatedStep A c = some d) : visitedSpace c ≤ visitedSpace d := by
  unfold locatedStep at h
  cases ht : A.step c.config with
  | none => simp [ht] at h
  | some d' =>
    have : c.monitor d' = d := by simpa [ht] using h
    subst d
    exact visitedSpace_le_monitor _ _

theorem visitedSpace_le_trace {A : PrimitiveMachine} {c d : LocatedCfg A} {n : ℕ}
    (h : Computation.Trace (locatedStep A) n c d) : visitedSpace c ≤ visitedSpace d := by
  induction h with
  | refl => exact le_refl _
  | cons hs ht ih => exact (visitedSpace_le_step hs).trans ih

/-- For this deterministic monitor, bounding the final interval union is equivalent
to bounding every execution prefix. -/
theorem segment_iff_final_space {A : PrimitiveMachine} {a b : LocatedCfg A}
    {n : ℕ} {σ : ℝ} :
    Segment A a b n σ ↔
      Computation.Trace (locatedStep A) n a b ∧ (visitedSpace b : ℝ) ≤ σ := by
  constructor
  · intro h
    exact ⟨h.1, h.2 n b le_rfl h.1⟩
  · rintro ⟨ht, hs⟩
    refine ⟨ht, ?_⟩
    intro k c hk hc
    rcases Trace.take_prefix ht hk with ⟨d, hd, hdb⟩
    have : c = d := Trace.endpoint_unique hc hd
    subst d
    exact le_trans (by exact_mod_cast visitedSpace_le_trace hdb) hs

/-- A convenient exact characterization of the mission predicate. The last
configuration's `visitedSpace` already contains the whole run's visit history. -/
theorem runsWithin_iff_final_space (A : PrimitiveMachine) (out : Fin A.tapeCount)
    (input output : List Bool) (τ σ : ℝ) :
    RunsWithin A out input output τ σ ↔
      ∃ n c, Computation.Trace (locatedStep A) n (locatedInit A input) c ∧
        (∃ b : Bool, c.config.state = Sum.inl b) ∧
        c.config.tapes out = Turing.Tape.mk₁ (output.map some) ∧
        (n : ℝ) ≤ τ ∧ (visitedSpace c : ℝ) ≤ σ := by
  rw [runsWithin_iff_segment]
  constructor
  · rintro ⟨n, c, hseg, hh, ho, hn⟩
    exact ⟨n, c, hseg.1, hh, ho, hn, (segment_iff_final_space.1 hseg).2⟩
  · rintro ⟨n, c, ht, hh, ho, hn, hs⟩
    exact ⟨n, c, segment_iff_final_space.2 ⟨ht, hs⟩, hh, ho, hn⟩

/-- Untouched extra tapes together with their existing visit history. This frame
can store the caller's stack while a padded submachine executes. -/
structure TapeFrame (r : ℕ) where
  tapes : Fin r → Turing.Tape (Option Bool)
  position : Fin r → ℤ
  lower : Fin r → ℤ
  upper : Fin r → ℤ

def TapeFrame.space {r : ℕ} (f : TapeFrame r) : ℕ :=
  ∑ i, (f.upper i - f.lower i + 1).toNat

def frameCfg (A : PrimitiveMachine) {r : ℕ} (f : TapeFrame r) (c : A.Cfg) :
    (addTapes A r).Cfg := ⟨c.state, Fin.append c.tapes f.tapes⟩

def frameLocated (A : PrimitiveMachine) {r : ℕ} (f : TapeFrame r) (c : LocatedCfg A) :
    LocatedCfg (addTapes A r) where
  config := frameCfg A f c.config
  position := Fin.append c.position f.position
  lower := Fin.append c.lower f.lower
  upper := Fin.append c.upper f.upper

@[simp] theorem frameCfg_step (A : PrimitiveMachine) {r : ℕ} (f : TapeFrame r) (c : A.Cfg) :
    (addTapes A r).step (frameCfg A f c) = (A.step c).map (frameCfg A f) := by
  rcases c with ⟨state, tapes⟩
  cases state with
  | inl b => rfl
  | inr q =>
    simp only [PrimitiveMachine.step, frameCfg, addTapes, Fin.append_left]
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨q', action⟩
      cases action <;> simp [Option.map, frameCfg, append_update]

@[simp] theorem frameLocated_monitor (A : PrimitiveMachine) {r : ℕ} (f : TapeFrame r)
    (c : LocatedCfg A) (c' : A.Cfg) :
    (frameLocated A f c).monitor (frameCfg A f c') = frameLocated A f (c.monitor c') := by
  rcases c with ⟨⟨state, tapes⟩, position, lower, upper⟩
  cases state with
  | inl b => rfl
  | inr q =>
    simp only [LocatedCfg.monitor, frameLocated, frameCfg, addTapes,
      Sum.elim_inr, Fin.append_left]
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨q', action⟩
      simp [append_update]

@[simp] theorem frameLocated_step (A : PrimitiveMachine) {r : ℕ} (f : TapeFrame r)
    (c : LocatedCfg A) :
    locatedStep (addTapes A r) (frameLocated A f c) =
      (locatedStep A c).map (frameLocated A f) := by
  unfold locatedStep
  rw [show (frameLocated A f c).config = frameCfg A f c.config from rfl, frameCfg_step]
  cases hs : A.step c.config <;> simp

@[simp] theorem frameLocated_space (A : PrimitiveMachine) {r : ℕ} (f : TapeFrame r)
    (c : LocatedCfg A) : visitedSpace (frameLocated A f c) = visitedSpace c + f.space := by
  change (∑ i : Fin (A.tapeCount + r),
    (Fin.append c.upper f.upper i - Fin.append c.lower f.lower i + 1).toNat) =
      visitedSpace c + f.space
  rw [Fin.sum_univ_add]
  simp [visitedSpace, TapeFrame.space]

/-- Calling a padded submachine preserves arbitrary caller tapes, with their exact
space footprint added to every execution prefix. -/
theorem frameLocated_segment (A : PrimitiveMachine) {r : ℕ} (f : TapeFrame r)
    {a b : LocatedCfg A} {n : ℕ} {σ : ℝ} (h : Segment A a b n σ) :
    Segment (addTapes A r) (frameLocated A f a) (frameLocated A f b) n (σ + f.space) := by
  have hsim : ∀ a b, locatedStep A a = some b →
      locatedStep (addTapes A r) (frameLocated A f a) = some (frameLocated A f b) := by
    intro a b hab
    simp [hab]
  refine ⟨Trace.map _ hsim h.1, ?_⟩
  intro k c hk hc
  rcases Trace.prefix_of_map _ hsim h.1 hk hc with ⟨d, hd, rfl⟩
  rw [frameLocated_space, Nat.cast_add]
  linarith [h.2 k d hk hd]

/-- Extract the operational segment of a subroutine call while retaining a stack
on the extra tapes. The returned configuration also retains that stack verbatim. -/
theorem runsWithin_framed_call {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ σ : ℝ} {r : ℕ} (f : TapeFrame r)
    (h : RunsWithin A out input output τ σ) :
    ∃ n c, Segment (addTapes A r) (frameLocated A f (locatedInit A input))
        (frameLocated A f c) n (σ + f.space) ∧
      (∃ b : Bool, c.config.state = Sum.inl b) ∧
      (frameLocated A f c).config.tapes (Fin.castAdd r out) =
        Turing.Tape.mk₁ (output.map some) ∧
      (n : ℝ) ≤ τ ∧
      (∀ i : Fin r, (frameLocated A f c).config.tapes (Fin.natAdd A.tapeCount i) = f.tapes i) := by
  rcases (runsWithin_iff_segment _ _ _ _ _ _).1 h with ⟨n, c, hseg, hh, ho, hn⟩
  refine ⟨n, c, frameLocated_segment A f hseg, hh, ?_, hn, ?_⟩
  · simpa [frameLocated, frameCfg] using ho
  · intro i; simp [frameLocated, frameCfg]

/-- Every source run from `locatedInit` retains the origin in each visited interval. -/
def OriginCovered {A : PrimitiveMachine} (c : LocatedCfg A) : Prop :=
  ∀ i, c.lower i ≤ 0 ∧ 0 ≤ c.upper i

theorem originCovered_init (A : PrimitiveMachine) (input : List Bool) :
    OriginCovered (locatedInit A input) := by
  intro i
  simp only [locatedInit, le_refl, true_and]
  split
  · exact Int.natCast_nonneg _
  · exact le_refl _

theorem originCovered_monitor {A : PrimitiveMachine} {c : LocatedCfg A}
    (h : OriginCovered c) (d : A.Cfg) : OriginCovered (c.monitor d) := by
  intro i
  unfold LocatedCfg.monitor
  cases hs : c.config.state with
  | inl b => exact h i
  | inr q =>
    simp only [Sum.elim_inr]
    cases ht : A.transition q (c.config.tapes (A.scan q)).head with
    | inl b => exact h i
    | inr qa =>
      by_cases hi : i = A.scan q
      · subst i
        simp only [Sum.elim_inr, Function.update_self]
        exact ⟨(min_le_left _ _).trans (h _).1, (h _).2.trans (le_max_left _ _)⟩
      · simpa [hi] using h i

theorem originCovered_step {A : PrimitiveMachine} {c d : LocatedCfg A}
    (h : OriginCovered c) (hs : locatedStep A c = some d) : OriginCovered d := by
  unfold locatedStep at hs
  cases ht : A.step c.config with
  | none => simp [ht] at hs
  | some d' =>
    have : c.monitor d' = d := by simpa [ht] using hs
    subst d
    exact originCovered_monitor h _

theorem originCovered_trace {A : PrimitiveMachine} {a b : LocatedCfg A} {n : ℕ}
    (h : OriginCovered a) (ht : Computation.Trace (locatedStep A) n a b) : OriginCovered b := by
  induction ht with
  | refl => exact h
  | cons hs ht ih => exact ih (originCovered_step h hs)

/-- Visit history belonging to previous calls on the subroutine's tapes. -/
structure TapeHistory (tapes : ℕ) where
  lower : Fin tapes → ℤ
  upper : Fin tapes → ℤ
  coversOrigin : ∀ i, lower i ≤ 0 ∧ 0 ≤ upper i

def TapeHistory.space {tapes : ℕ} (H : TapeHistory tapes) : ℕ :=
  ∑ i, (H.upper i - H.lower i + 1).toNat

/-- Widen the source monitor with the caller's pre-existing history, without
changing the actual machine configuration or head positions. -/
def withHistory (A : PrimitiveMachine) (H : TapeHistory A.tapeCount) (c : LocatedCfg A) :
    LocatedCfg A where
  config := c.config
  position := c.position
  lower i := min (c.lower i) (H.lower i)
  upper i := max (c.upper i) (H.upper i)

@[simp] theorem withHistory_monitor (A : PrimitiveMachine) (H : TapeHistory A.tapeCount)
    (c : LocatedCfg A) (d : A.Cfg) :
    (withHistory A H c).monitor d = withHistory A H (c.monitor d) := by
  rcases c with ⟨⟨state, tapes⟩, position, lower, upper⟩
  cases state with
  | inl b => rfl
  | inr q =>
    simp only [LocatedCfg.monitor, withHistory, Sum.elim_inr]
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b => rfl
    | inr qa =>
      apply locatedCfg_ext
      · rfl
      · rfl
      · funext i
        by_cases hi : i = A.scan q
        · subst i
          simp [min_assoc, min_comm, min_left_comm]
        · simp [hi]
      · funext i
        by_cases hi : i = A.scan q
        · subst i
          simp [max_assoc, max_comm, max_left_comm]
        · simp [hi]

@[simp] theorem withHistory_step (A : PrimitiveMachine) (H : TapeHistory A.tapeCount)
    (c : LocatedCfg A) :
    locatedStep A (withHistory A H c) = (locatedStep A c).map (withHistory A H) := by
  unfold locatedStep
  change (A.step c.config).map (withHistory A H c).monitor = _
  cases hs : A.step c.config <;> simp

theorem withHistory_space (A : PrimitiveMachine) (H : TapeHistory A.tapeCount)
    (c : LocatedCfg A) (hc : OriginCovered c) :
    visitedSpace (withHistory A H c) ≤ visitedSpace c + H.space := by
  unfold visitedSpace withHistory TapeHistory.space
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hci := hc i
  have hHi := H.coversOrigin i
  dsimp at hci hHi ⊢
  omega

/-- A subroutine can be called without resetting the visited-cell accounting of
previous calls. Only the old history's size is added to its isolated space bound. -/
theorem withHistory_segment (A : PrimitiveMachine) (H : TapeHistory A.tapeCount)
    {a b : LocatedCfg A} {n : ℕ} {σ : ℝ}
    (ha : OriginCovered a) (h : Segment A a b n σ) :
    Segment A (withHistory A H a) (withHistory A H b) n (σ + H.space) := by
  apply segment_iff_final_space.2
  constructor
  · apply Trace.map (withHistory A H) _ h.1
    intro c d hcd
    simp [hcd]
  · have hb := originCovered_trace ha h.1
    have hs := withHistory_space A H b hb
    have hsR : (visitedSpace (withHistory A H b) : ℝ) ≤ visitedSpace b + H.space := by
      exact_mod_cast hs
    linarith [(segment_iff_final_space.1 h).2]

/-- External-machine call interface: arbitrary caller stack tapes are preserved,
previous visits on the subroutine tapes are retained, and the original call's time
bound is unchanged. The caller need only establish the displayed physical entry
configuration before using this theorem. -/
theorem runsWithin_preserved_call {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ σ : ℝ} {r : ℕ}
    (H : TapeHistory A.tapeCount) (f : TapeFrame r)
    (h : RunsWithin A out input output τ σ) :
    ∃ n c, Segment (addTapes A r)
        (frameLocated A f (withHistory A H (locatedInit A input)))
        (frameLocated A f (withHistory A H c)) n (σ + H.space + f.space) ∧
      (∃ b : Bool, c.config.state = Sum.inl b) ∧
      (frameLocated A f (withHistory A H c)).config.tapes (Fin.castAdd r out) =
        Turing.Tape.mk₁ (output.map some) ∧ (n : ℝ) ≤ τ ∧
      (∀ i : Fin r, (frameLocated A f (withHistory A H c)).config.tapes
        (Fin.natAdd A.tapeCount i) = f.tapes i) := by
  rcases (runsWithin_iff_segment _ _ _ _ _ _).1 h with ⟨n, c, hseg, hh, ho, hn⟩
  have hhseg := withHistory_segment A H (originCovered_init A input) hseg
  refine ⟨n, c, frameLocated_segment A f hhseg, hh, ?_, hn, ?_⟩
  · simpa [frameLocated, frameCfg, withHistory] using ho
  · intro i; simp [frameLocated, frameCfg, withHistory]

def TapeFrame.WellFormed {r : ℕ} (f : TapeFrame r) : Prop :=
  ∀ i, f.lower i ≤ f.position i ∧ f.position i ≤ f.upper i

theorem withHistory_wellFormed (A : PrimitiveMachine) (H : TapeHistory A.tapeCount)
    {c : LocatedCfg A} (hc : LocatedWellFormed c) :
    LocatedWellFormed (withHistory A H c) := by
  intro i
  exact ⟨(min_le_left _ _).trans (hc i).1, (hc i).2.trans (le_max_left _ _)⟩

theorem frameLocated_wellFormed (A : PrimitiveMachine) {r : ℕ} {f : TapeFrame r}
    {c : LocatedCfg A} (hc : LocatedWellFormed c) (hf : f.WellFormed) :
    LocatedWellFormed (frameLocated A f c) := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa [frameLocated] using hc i
  | right i => simpa [frameLocated] using hf i

/-- A complete external-call/control-return interface. The constructed machine
executes the arbitrary supplied primitive submachine and then starts the supplied
continuation. The output word, caller's stack, and visit history survive the return;
there are no abstract oracle steps in this construction. -/
theorem thenMachine_preserved_call {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ σ : ℝ} {r : ℕ}
    (H : TapeHistory A.tapeCount) (f : TapeFrame r) (hf : f.WellFormed)
    (B : Program (addTapes A r).tapeCount)
    (h : RunsWithin A out input output τ σ) :
    ∃ n c, Segment (thenMachine (addTapes A r) B)
        (leftCfg (addTapes A r) B (frameLocated A f (withHistory A H (locatedInit A input))))
        (rightCfg (addTapes A r) B
          (restartCfg (addTapes A r) B (frameLocated A f (withHistory A H c))))
        n (σ + H.space + f.space) ∧
      (frameLocated A f (withHistory A H c)).config.tapes (Fin.castAdd r out) =
        Turing.Tape.mk₁ (output.map some) ∧ (n : ℝ) ≤ τ ∧
      (∀ i : Fin r, (frameLocated A f (withHistory A H c)).config.tapes
        (Fin.natAdd A.tapeCount i) = f.tapes i) := by
  rcases runsWithin_preserved_call H f h with ⟨n, c, hseg, hh, ho, hn, hframe⟩
  have hw : LocatedWellFormed (frameLocated A f (withHistory A H (locatedInit A input))) :=
    frameLocated_wellFormed A (withHistory_wellFormed A H (locatedWellFormed_init A input)) hf
  have hc := thenMachine_left_segment (addTapes A r) B hw hseg
  have hh' : ∃ answer,
      (frameLocated A f (withHistory A H c)).config.state = Sum.inl answer := hh
  rw [leftCfg_halt _ _ hh'] at hc
  exact ⟨n, c, hc, ho, hn, hframe⟩

/-- Direct adapter for the natural-number resource bounds produced by the existing
primitive compilers. The `Trace` and space certificate must concern the same run. -/
theorem runsWithin_of_nat_resources {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {T S : ℕ}
    (h : ∃ time ≤ T, ∃ final : LocatedCfg A,
      Computation.Trace (locatedStep A) time (locatedInit A input) final ∧
      (∃ answer, final.config.state = Sum.inl answer) ∧
      final.config.tapes out = Turing.Tape.mk₁ (output.map some) ∧
      ∀ k c, k ≤ time → Computation.Trace (locatedStep A) k (locatedInit A input) c →
        visitedSpace c ≤ S) :
    RunsWithin A out input output (T : ℝ) (S : ℝ) := by
  rcases h with ⟨n, hn, c, hc, hh, ho, hs⟩
  refine ⟨n, c, hc, hh, ho, ?_, ?_⟩
  · exact_mod_cast hn
  · intro k d hk hd
    exact_mod_cast hs k d hk hd

/-- Driver instructions: a local primitive action, a halt, or an actual call of the
linked submachine with a fixed finite-control return address. The submachine's
Boolean halt is ignored; its output word is left on its designated tape. -/
inductive CallInstr (states : ℕ) where
  | halt : Bool → CallInstr states
  | act : Fin states → Turing.TM0.Stmt (Option Bool) → CallInstr states
  | call : Fin states → CallInstr states

/-- A concrete finite-state driver with cyclic calls to one primitive submachine. -/
structure CallDriver (tapes : ℕ) where
  stateCount : ℕ
  start : Fin stateCount
  scan : Fin stateCount → Fin tapes
  transition : Fin stateCount → Option Bool → CallInstr stateCount

/-- Ordinary local finite-control code is usable as call-free driver code. A
concrete driver can reuse its state allocation and replace selected transitions
by `.call ret`. -/
def CallDriver.ofProgram {tapes : ℕ} (P : Program tapes) : CallDriver tapes where
  stateCount := P.stateCount
  start := P.start
  scan := P.scan
  transition q symbol := match P.transition q symbol with
    | .inl answer => .halt answer
    | .inr (q', action) => .act q' action

/-- Driver states occupy the initial block of the linked finite-state set. -/
def cyclicDriverState (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (q : Fin D.stateCount) : Fin (D.stateCount + D.stateCount * A.stateCount) :=
  Fin.castAdd (D.stateCount * A.stateCount) q

/-- A submachine copy stores its return address in finite control, not on a tape. -/
def cyclicSubState (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) (q : Fin A.stateCount) :
    Fin (D.stateCount + D.stateCount * A.stateCount) :=
  Fin.natAdd D.stateCount (finProdFinEquiv (ret, q))

/-- Actual cyclic link: driver `call ret` enters a copy of `A.start` tagged by ret;
A's halt jumps back to ret. Driver actions can make arbitrarily many later calls.
Both jumps are primitive no-op writes, and all tapes and visit history are shared. -/
def cyclicMachine (A : PrimitiveMachine) (D : CallDriver A.tapeCount) : PrimitiveMachine where
  tapeCount := A.tapeCount
  stateCount := D.stateCount + D.stateCount * A.stateCount
  inputTape := A.inputTape
  start := cyclicDriverState A D D.start
  scan := Fin.append D.scan (fun pq => A.scan (finProdFinEquiv.symm pq).2)
  transition := Fin.append
    (fun q symbol => match D.transition q symbol with
      | .halt answer => .inl answer
      | .act q' action => .inr (cyclicDriverState A D q', action)
      | .call ret => .inr (cyclicSubState A D ret A.start, .write symbol))
    (fun pq symbol =>
      let ret := (finProdFinEquiv.symm pq).1
      let q := (finProdFinEquiv.symm pq).2
      match A.transition q symbol with
      | .inl _ => .inr (cyclicDriverState A D ret, .write symbol)
      | .inr (q', action) => .inr (cyclicSubState A D ret q', action))

@[simp] theorem cyclicMachine_scan_driver (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (q : Fin D.stateCount) : (cyclicMachine A D).scan (cyclicDriverState A D q) = D.scan q := by
  simp [cyclicMachine, cyclicDriverState]

@[simp] theorem cyclicMachine_scan_sub (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) (q : Fin A.stateCount) :
    (cyclicMachine A D).scan (cyclicSubState A D ret q) = A.scan q := by
  simp only [cyclicMachine, cyclicSubState, Fin.append_right, Equiv.symm_apply_apply]

@[simp] theorem cyclicMachine_transition_driver (A : PrimitiveMachine)
    (D : CallDriver A.tapeCount) (q : Fin D.stateCount) (symbol : Option Bool) :
    (cyclicMachine A D).transition (cyclicDriverState A D q) symbol =
      match D.transition q symbol with
      | .halt answer => .inl answer
      | .act q' action => .inr (cyclicDriverState A D q', action)
      | .call ret => .inr (cyclicSubState A D ret A.start, .write symbol) := by
  simp [cyclicMachine, cyclicDriverState]

@[simp] theorem cyclicMachine_transition_sub (A : PrimitiveMachine)
    (D : CallDriver A.tapeCount) (ret : Fin D.stateCount) (q : Fin A.stateCount)
    (symbol : Option Bool) :
    (cyclicMachine A D).transition (cyclicSubState A D ret q) symbol =
      match A.transition q symbol with
      | .inl _ => .inr (cyclicDriverState A D ret, .write symbol)
      | .inr (q', action) => .inr (cyclicSubState A D ret q', action) := by
  simp only [cyclicMachine, cyclicSubState, Fin.append_right, Equiv.symm_apply_apply]

/-- Change only the finite control to a specified linked driver state. -/
def cyclicAtDriver (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (q : Fin D.stateCount) (c : LocatedCfg A) : LocatedCfg (cyclicMachine A D) where
  config := ⟨.inr (cyclicDriverState A D q), c.config.tapes⟩
  position := c.position
  lower := c.lower
  upper := c.upper

/-- Embed a running submachine; an original halting endpoint is its linked return. -/
def cyclicAtSub (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) (c : LocatedCfg A) : LocatedCfg (cyclicMachine A D) where
  config := ⟨c.config.state.elim (fun _ => .inr (cyclicDriverState A D ret))
    (fun q => .inr (cyclicSubState A D ret q)), c.config.tapes⟩
  position := c.position
  lower := c.lower
  upper := c.upper

/-- Reset only submachine control. Caller-provided tapes, heads, and visit history
are not changed; the driver must already have prepared its physical input layout. -/
def cyclicStartSub (A : PrimitiveMachine) (c : LocatedCfg A) : LocatedCfg A :=
  { c with config := { c.config with state := .inr A.start } }

@[simp] theorem cyclicAtDriver_space (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (q : Fin D.stateCount) (c : LocatedCfg A) :
    visitedSpace (cyclicAtDriver A D q c) = visitedSpace c := rfl

@[simp] theorem cyclicAtSub_space (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) (c : LocatedCfg A) :
    visitedSpace (cyclicAtSub A D ret c) = visitedSpace c := rfl

@[simp] theorem cyclicAtDriver_wellFormed (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (q : Fin D.stateCount) {c : LocatedCfg A} (hc : LocatedWellFormed c) :
    LocatedWellFormed (cyclicAtDriver A D q c) := hc

@[simp] theorem cyclicAtSub_wellFormed (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) {c : LocatedCfg A} (hc : LocatedWellFormed c) :
    LocatedWellFormed (cyclicAtSub A D ret c) := hc

@[simp] theorem cyclicAtSub_halt (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) {c : LocatedCfg A} (hh : ∃ b, c.config.state = Sum.inl b) :
    cyclicAtSub A D ret c = cyclicAtDriver A D ret c := by
  rcases hh with ⟨b, hb⟩
  simp [cyclicAtSub, cyclicAtDriver, hb]

/-- A driver call instruction is one real primitive no-op step into A.start. -/
theorem cyclicMachine_call_step (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    {q ret : Fin D.stateCount} {c : LocatedCfg A} (hw : LocatedWellFormed c)
    (ht : D.transition q (c.config.tapes (D.scan q)).head = .call ret) :
    locatedStep (cyclicMachine A D) (cyclicAtDriver A D q c) =
      some (cyclicAtSub A D ret (cyclicStartSub A c)) := by
  have hh : (cyclicMachine A D).transition (cyclicDriverState A D q)
      ((cyclicAtDriver A D q c).config.tapes
        ((cyclicMachine A D).scan (cyclicDriverState A D q))).head =
      Sum.inr (cyclicSubState A D ret A.start,
        .write ((cyclicAtDriver A D q c).config.tapes
          ((cyclicMachine A D).scan (cyclicDriverState A D q))).head) := by
    simp [cyclicAtDriver, ht]
  exact monitor_noop (cyclicAtDriver_wellFormed A D q hw) rfl hh

/-- Every source submachine step is one real linked step, including return on halt. -/
theorem cyclicMachine_sub_step (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) {c d : LocatedCfg A} (hw : LocatedWellFormed c)
    (h : locatedStep A c = some d) :
    locatedStep (cyclicMachine A D) (cyclicAtSub A D ret c) =
      some (cyclicAtSub A D ret d) := by
  rcases c with ⟨⟨state, tapes⟩, position, lower, upper⟩
  cases state with
  | inl b => simp [locatedStep, PrimitiveMachine.step] at h
  | inr q =>
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b =>
      have hd : d = ⟨⟨Sum.inl b, tapes⟩, position, lower, upper⟩ := by
        simpa [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, ht] using h.symm
      subst d
      have hl : min (lower (A.scan q)) (position (A.scan q)) = lower (A.scan q) :=
        min_eq_left (hw _).1
      have hu : max (upper (A.scan q)) (position (A.scan q)) = upper (A.scan q) :=
        max_eq_left (hw _).2
      simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cyclicAtSub,
        ht, headDisplacement, hl, hu]
    | inr qa =>
      rcases qa with ⟨q', action⟩
      cases action <;>
        simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, ht,
          headDisplacement] at h <;>
        subst d <;>
        simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cyclicAtSub,
          ht, headDisplacement]

theorem cyclicMachine_sub_trace (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) {c d : LocatedCfg A} {n : ℕ} (hw : LocatedWellFormed c)
    (h : Computation.Trace (locatedStep A) n c d) :
    Computation.Trace (locatedStep (cyclicMachine A D)) n
      (cyclicAtSub A D ret c) (cyclicAtSub A D ret d) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih =>
    exact .cons (cyclicMachine_sub_step A D ret hw hs) (ih (locatedWellFormed_step hw hs))

theorem cyclicMachine_sub_segment (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (ret : Fin D.stateCount) {c d : LocatedCfg A} {n : ℕ} {σ : ℝ}
    (hw : LocatedWellFormed c) (h : Segment A c d n σ) :
    Segment (cyclicMachine A D) (cyclicAtSub A D ret c) (cyclicAtSub A D ret d) n σ := by
  apply segment_iff_final_space.2
  exact ⟨cyclicMachine_sub_trace A D ret hw h.1, (segment_iff_final_space.1 h).2⟩

/-- One actual call/return segment: the driver call costs one step; all source
submachine steps, including its halt/return, are simulated one-for-one. -/
theorem cyclicMachine_call_segment (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    {q ret : Fin D.stateCount} {c d : LocatedCfg A} {n : ℕ} {σ : ℝ}
    (hw : LocatedWellFormed c)
    (ht : D.transition q (c.config.tapes (D.scan q)).head = .call ret)
    (h : Segment A (cyclicStartSub A c) d n σ)
    (hh : ∃ b, d.config.state = Sum.inl b) :
    Segment (cyclicMachine A D) (cyclicAtDriver A D q c)
      (cyclicAtDriver A D ret d) (n+1) σ := by
  apply segment_iff_final_space.2
  constructor
  · have hw' : LocatedWellFormed (cyclicStartSub A c) := hw
    have hsub := cyclicMachine_sub_trace A D ret hw' h.1
    rw [cyclicAtSub_halt A D ret hh] at hsub
    exact .cons (cyclicMachine_call_step A D hw ht) hsub
  · exact (segment_iff_final_space.1 h).2

/-- Physical effect of a driver-local primitive action. The source control field
is only a carrier: linked execution uses the separately supplied driver state. -/
def cyclicDoAction (A : PrimitiveMachine) (i : Fin A.tapeCount)
    (action : Turing.TM0.Stmt (Option Bool)) (c : LocatedCfg A) : LocatedCfg A where
  config := ⟨c.config.state, Function.update c.config.tapes i
    (match action with
      | .move direction => (c.config.tapes i).move direction
      | .write symbol => (c.config.tapes i).write symbol)⟩
  position := Function.update c.position i (c.position i + headDisplacement action)
  lower := Function.update c.lower i (min (c.lower i) (c.position i + headDisplacement action))
  upper := Function.update c.upper i (max (c.upper i) (c.position i + headDisplacement action))

/-- Every driver local move/write is an actual primitive step of the linked machine. -/
theorem cyclicMachine_driver_action (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    {q q' : Fin D.stateCount} {c : LocatedCfg A}
    {action : Turing.TM0.Stmt (Option Bool)}
    (ht : D.transition q (c.config.tapes (D.scan q)).head = .act q' action) :
    locatedStep (cyclicMachine A D) (cyclicAtDriver A D q c) =
      some (cyclicAtDriver A D q' (cyclicDoAction A (D.scan q) action c)) := by
  cases action <;>
    simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cyclicAtDriver,
      cyclicDoAction, ht, headDisplacement]

/-- Driver halt is also a real primitive step and keeps the complete space history. -/
def cyclicHalted (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (answer : Bool) (c : LocatedCfg A) : LocatedCfg (cyclicMachine A D) where
  config := ⟨.inl answer, c.config.tapes⟩
  position := c.position
  lower := c.lower
  upper := c.upper

@[simp] theorem cyclicHalted_space (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (answer : Bool) (c : LocatedCfg A) : visitedSpace (cyclicHalted A D answer c) = visitedSpace c := rfl

theorem cyclicMachine_driver_halt (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    {q : Fin D.stateCount} {answer : Bool} {c : LocatedCfg A}
    (ht : D.transition q (c.config.tapes (D.scan q)).head = .halt answer) :
    locatedStep (cyclicMachine A D) (cyclicAtDriver A D q c) =
      some (cyclicHalted A D answer c) := by
  simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cyclicAtDriver,
    cyclicHalted, ht]

/-- A driver action preserves the standard visited-interval invariant. -/
theorem cyclicDoAction_wellFormed (A : PrimitiveMachine) (i : Fin A.tapeCount)
    (action : Turing.TM0.Stmt (Option Bool)) {c : LocatedCfg A}
    (hw : LocatedWellFormed c) : LocatedWellFormed (cyclicDoAction A i action c) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [cyclicDoAction]
  · simpa [cyclicDoAction, Function.update_of_ne hji] using hw j

@[simp] theorem cyclicAtDriver_init (A : PrimitiveMachine) (D : CallDriver A.tapeCount)
    (input : List Bool) : cyclicAtDriver A D D.start (locatedInit A input) =
      locatedInit (cyclicMachine A D) input := rfl

/-- A linked execution certificate with arbitrarily many calls. The call constructor
requires the real source trace, not an oracle assumption; its cost is exactly n+1. Local
instructions and final halt each cost one primitive step. -/
inductive CyclicExec (A : PrimitiveMachine) (D : CallDriver A.tapeCount) :
    Fin D.stateCount → LocatedCfg A → ℕ → Bool → LocatedCfg A → Prop where
  | halt {q : Fin D.stateCount} {c : LocatedCfg A} {answer : Bool}
      (ht : D.transition q (c.config.tapes (D.scan q)).head = .halt answer) :
      CyclicExec A D q c 1 answer c
  | act {q q' : Fin D.stateCount} {c d : LocatedCfg A} {n : ℕ} {answer : Bool}
      {action : Turing.TM0.Stmt (Option Bool)}
      (ht : D.transition q (c.config.tapes (D.scan q)).head = .act q' action)
      (tail : CyclicExec A D q' (cyclicDoAction A (D.scan q) action c) n answer d) :
      CyclicExec A D q c (n+1) answer d
  | call {q ret : Fin D.stateCount} {c e d : LocatedCfg A} {m n : ℕ} {answer : Bool}
      (ht : D.transition q (c.config.tapes (D.scan q)).head = .call ret)
      (run : Computation.Trace (locatedStep A) m (cyclicStartSub A c) e)
      (hh : ∃ b, e.config.state = Sum.inl b)
      (tail : CyclicExec A D ret e n answer d) :
      CyclicExec A D q c (m+n+1) answer d

/-- Kernel-level soundness of the cyclic execution rules. Thus any number of
connected calls executes on one fixed `PrimitiveMachine`, with no tape resets. -/
theorem CyclicExec.trace {A : PrimitiveMachine} {D : CallDriver A.tapeCount}
    {q : Fin D.stateCount} {c d : LocatedCfg A} {n : ℕ} {answer : Bool}
    (h : CyclicExec A D q c n answer d) (hw : LocatedWellFormed c) :
    Computation.Trace (locatedStep (cyclicMachine A D)) n
      (cyclicAtDriver A D q c) (cyclicHalted A D answer d) := by
  induction h with
  | halt ht => exact .cons (cyclicMachine_driver_halt A D ht) (.refl _)
  | act ht tail ih =>
      exact .cons (cyclicMachine_driver_action A D ht)
        (ih (cyclicDoAction_wellFormed A _ _ hw))
  | @call q ret c e d m n answer ht run hh tail ih =>
      have hw' : LocatedWellFormed (cyclicStartSub A c) := hw
      have hrun := cyclicMachine_sub_trace A D ret hw' run
      rw [cyclicAtSub_halt A D ret hh] at hrun
      have htail := ih (locatedWellFormed_trace hw' run)
      have hboth := Trace.append hrun htail
      exact .cons (cyclicMachine_call_step A D hw ht) hboth

/-- The final monitor stores all local-action and all repeated-call visit history,
so its single bound certifies every actual primitive prefix of the cyclic run. -/
theorem CyclicExec.segment {A : PrimitiveMachine} {D : CallDriver A.tapeCount}
    {q : Fin D.stateCount} {c d : LocatedCfg A} {n : ℕ} {answer : Bool} {σ : ℝ}
    (h : CyclicExec A D q c n answer d) (hw : LocatedWellFormed c)
    (hs : (visitedSpace d : ℝ) ≤ σ) :
    Segment (cyclicMachine A D) (cyclicAtDriver A D q c)
      (cyclicHalted A D answer d) n σ :=
  segment_iff_final_space.2 ⟨h.trace hw, hs⟩

/-- Direct operational bridge for the actual driver code: a `CyclicExec` certificate
for this fixed control table gives the mission's exact `RunsWithin` predicate. -/
theorem CyclicExec.runsWithin {A : PrimitiveMachine} {D : CallDriver A.tapeCount}
    (out : Fin A.tapeCount) {input output : List Bool} {d : LocatedCfg A}
    {n : ℕ} {answer : Bool} {τ σ : ℝ}
    (h : CyclicExec A D D.start (locatedInit A input) n answer d)
    (hout : d.config.tapes out = Turing.Tape.mk₁ (output.map some))
    (ht : (n : ℝ) ≤ τ) (hs : (visitedSpace d : ℝ) ≤ σ) :
    RunsWithin (cyclicMachine A D) out input output τ σ := by
  apply (runsWithin_iff_final_space _ _ _ _ _ _).2
  refine ⟨n, cyclicHalted A D answer d, ?_, ⟨answer, rfl⟩, hout, ht, hs⟩
  simpa using h.trace (locatedWellFormed_init A input)

/-- Invoke the existing arbitrary-machine certificate inside the cyclic linker,
with preserved caller tapes and old visit history, then return to driver state ret. -/
theorem cyclicMachine_preserved_call {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ σ : ℝ} {r : ℕ}
    (H : TapeHistory A.tapeCount) (f : TapeFrame r) (hf : f.WellFormed)
    (D : CallDriver (addTapes A r).tapeCount) {q ret : Fin D.stateCount}
    (h : RunsWithin A out input output τ σ)
    (ht : D.transition q
      ((frameLocated A f (withHistory A H (locatedInit A input))).config.tapes
        (D.scan q)).head = .call ret) :
    ∃ n c, Segment (cyclicMachine (addTapes A r) D)
        (cyclicAtDriver (addTapes A r) D q
          (frameLocated A f (withHistory A H (locatedInit A input))))
        (cyclicAtDriver (addTapes A r) D ret
          (frameLocated A f (withHistory A H c)))
        (n+1) (σ + H.space + f.space) ∧
      (frameLocated A f (withHistory A H c)).config.tapes (Fin.castAdd r out) =
        Turing.Tape.mk₁ (output.map some) ∧ (n : ℝ) ≤ τ ∧
      (∀ i : Fin r, (frameLocated A f (withHistory A H c)).config.tapes
        (Fin.natAdd A.tapeCount i) = f.tapes i) := by
  rcases runsWithin_preserved_call H f h with ⟨n, c, hseg, hh, ho, hn, hframe⟩
  have hw : LocatedWellFormed (frameLocated A f (withHistory A H (locatedInit A input))) :=
    frameLocated_wellFormed A (withHistory_wellFormed A H (locatedWellFormed_init A input)) hf
  have he : cyclicStartSub (addTapes A r)
      (frameLocated A f (withHistory A H (locatedInit A input))) =
      frameLocated A f (withHistory A H (locatedInit A input)) := rfl
  have hh' : ∃ answer,
      (frameLocated A f (withHistory A H c)).config.state = Sum.inl answer := hh
  refine ⟨n, c, ?_, ho, hn, hframe⟩
  apply cyclicMachine_call_segment (addTapes A r) D hw ht _ hh'
  simpa only [he] using hseg

end DetDLP.MachineComposition


