-- Prove2me | Definitions.Def_DetDLP_W1_Pipeline
-- name    : DetDLP_W1_Pipeline
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:25:22.075317+00:00
-- url     : https://prove2.me/theorems/3282e813-87e7-4aac-803d-a4b3aa180e67
-- title:
--   Sequential execution with additive visited-space budgets
-- statement:
--   The output port of a producer is wired to the input port of a consumer with fresh work tapes. Both step counts add, while the space bound adds only the two visited-space budgets and a fixed allowance for the tape counts.

import Definitions.Def_DetDLP_W1_SavedCall


set_option autoImplicit false

namespace DetDLP_W1_Pipeline.CallWiring

open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP DetDLP.MachineComposition

def swapBlocks (a b : ℕ) : Fin (b+a) ≃ Fin (a+b) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin b) (Fin a)).trans finSumFinEquiv)

@[simp] theorem swapBlocks_left {a b : ℕ} (k : Fin b) :
    swapBlocks a b (Fin.castAdd a k) = Fin.natAdd a k := by simp [swapBlocks]

@[simp] theorem swapBlocks_right {a b : ℕ} (i : Fin a) :
    swapBlocks a b (Fin.natAdd b i) = Fin.castAdd b i := by simp [swapBlocks]

private theorem separate {a b : ℕ} (i : Fin a) (k : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a k := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hval
  omega

/-- Active port `inp` of B is the finished output port `out` of A. All other
    B ports are fresh. There is an unused fresh port at the old B-input location. -/
def wire {a b : ℕ} (out : Fin a) (inp : Fin b) : Fin (b+a) ≃ Fin (a+b) :=
  (swapBlocks a b).trans (Equiv.swap (Fin.natAdd a inp) (Fin.castAdd b out))

@[simp] theorem wire_input {a b : ℕ} (out : Fin a) (inp : Fin b) :
    wire out inp (Fin.castAdd a inp) = Fin.castAdd b out := by simp [wire]

@[simp] theorem wire_unused {a b : ℕ} (out : Fin a) (inp : Fin b) :
    wire out inp (Fin.natAdd b out) = Fin.natAdd a inp := by simp [wire]

theorem wire_work {a b : ℕ} (out : Fin a) {inp k : Fin b} (h : k ≠ inp) :
    wire out inp (Fin.castAdd a k) = Fin.natAdd a k := by
  simp only [wire, Equiv.trans_apply,swapBlocks_left]
  exact Equiv.swap_apply_of_ne_of_ne (fun e => h ((Fin.natAdd_inj a).mp e)) (Ne.symm (separate out k))

theorem wire_saved {a b : ℕ} {out i : Fin a} (inp : Fin b) (h : i ≠ out) :
    wire out inp (Fin.natAdd b i) = Fin.castAdd b i := by
  simp only [wire, Equiv.trans_apply,swapBlocks_right]
  exact Equiv.swap_apply_of_ne_of_ne (separate i inp) (fun e => h (Fin.castAdd_inj.mp e))

abbrev BitTape := Turing.Tape (Option Bool)

def saved {a : ℕ} (tapes : Fin a → BitTape) (out : Fin a) : TapeFrame a where
  tapes i := if i = out then Turing.Tape.mk₁ [] else tapes i
  lower _ := 0
  upper _ := 0
  position _ := 0

@[simp] theorem saved_space {a : ℕ} (tapes : Fin a → BitTape) (out : Fin a) :
    (saved tapes out).space = a := by simp [saved,TapeFrame.space]

/-- Exact physical tape contents at the change of finite control, for arbitrary old
    scratch-tape contents. In particular this does not assume the producer cleaned up. -/
theorem transfer {a : ℕ} (tapes : Fin a → BitTape) (out : Fin a) (B : PrimitiveMachine)
    (mid : List Bool) (hout : tapes out = Turing.Tape.mk₁ (mid.map some))
    (i : Fin (B.tapeCount+a)) :
    Fin.append tapes (fun _ : Fin B.tapeCount => Turing.Tape.mk₁ []) (wire out B.inputTape i) =
      Fin.append (B.init mid).tapes (saved tapes out).tapes i := by
  induction i using Fin.addCases with
  | left k =>
    by_cases he : k = B.inputTape
    · subst k; simpa [PrimitiveMachine.init] using hout
    · rw [wire_work out he]; simp [PrimitiveMachine.init,he]
  | right k =>
    by_cases he : k = out
    · subst k; simp [saved]
    · rw [wire_saved B.inputTape he]; simp [saved,he]

end DetDLP_W1_Pipeline.CallWiring





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP_W1_Pipeline.PermutedTapes

open DetDLP DetDLP.MachineComposition

variable {m n : ℕ} (P : Program m) (e : Fin m ≃ Fin n)

/-- Place source tape `i` at physical tape `e i`, without changing finite control. -/
def program : Program n where
  stateCount := P.stateCount
  start := P.start
  scan q := e (P.scan q)
  transition := P.transition

@[simp] theorem program_scan (q : Fin P.stateCount) :
    (program P e).scan q = e (P.scan q) := rfl

@[simp] theorem program_transition (q : Fin P.stateCount) (s : Option Bool) :
    (program P e).transition q s = P.transition q s := rfl

variable (src : Fin m) (dst : Fin n)

def positionedCfg (c : (P.machine src).Cfg) : ((program P e).machine dst).Cfg where
  state := c.state
  tapes := c.tapes ∘ e.symm

/-- Relocate an existing configuration, including its entire visit history. Neither
`src` nor `dst` is read: they designate the input tapes only at initialization. -/
def positioned (c : LocatedCfg (P.machine src)) : LocatedCfg ((program P e).machine dst) where
  config := positionedCfg P e src dst c.config
  position := c.position ∘ e.symm
  lower := c.lower ∘ e.symm
  upper := c.upper ∘ e.symm

section Readout

variable (c : LocatedCfg (P.machine src))

@[simp] theorem positioned_state : (positioned P e src dst c).config.state = c.config.state := rfl

theorem positioned_tapes_at (j : Fin n) :
    (positioned P e src dst c).config.tapes j = c.config.tapes (e.symm j) := rfl

theorem positioned_position_at (j : Fin n) :
    (positioned P e src dst c).position j = c.position (e.symm j) := rfl

theorem positioned_lower_at (j : Fin n) :
    (positioned P e src dst c).lower j = c.lower (e.symm j) := rfl

theorem positioned_upper_at (j : Fin n) :
    (positioned P e src dst c).upper j = c.upper (e.symm j) := rfl

@[simp] theorem positioned_tapes (i : Fin m) :
    (positioned P e src dst c).config.tapes (e i) = c.config.tapes i := by
  rw [positioned_tapes_at, e.symm_apply_apply]

@[simp] theorem positioned_position (i : Fin m) :
    (positioned P e src dst c).position (e i) = c.position i := by
  rw [positioned_position_at, e.symm_apply_apply]

@[simp] theorem positioned_lower (i : Fin m) :
    (positioned P e src dst c).lower (e i) = c.lower i := by
  rw [positioned_lower_at, e.symm_apply_apply]

@[simp] theorem positioned_upper (i : Fin m) :
    (positioned P e src dst c).upper (e i) = c.upper i := by
  rw [positioned_upper_at, e.symm_apply_apply]

@[simp] theorem positioned_space : visitedSpace (positioned P e src dst c) = visitedSpace c :=
  e.symm.sum_comp (fun i => (c.upper i - c.lower i + 1).toNat)

end Readout

/-- The primitive move or write updates `e (P.scan q)` and leaves every other tape alone. -/
@[simp] theorem positionedCfg_step (c : (P.machine src).Cfg) :
    ((program P e).machine dst).step (positionedCfg P e src dst c) =
      ((P.machine src).step c).map (positionedCfg P e src dst) := by
  rcases c with ⟨s, tapes⟩
  cases s with
  | inl b => rfl
  | inr q =>
    simp only [PrimitiveMachine.step, positionedCfg, Program.machine, program,
      Function.comp_apply, Equiv.symm_apply_apply]
    cases ht : P.transition q (tapes (P.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨next, action⟩
      cases action <;> simp [positionedCfg] <;>
        exact (Function.update_comp_equiv tapes e.symm (P.scan q) _).symm

/-- The monitor performs the same displacement and extends the same interval on the
permuted scanned tape. It never reinitializes an interval. -/
@[simp] theorem positioned_monitor (c : LocatedCfg (P.machine src)) (d : (P.machine src).Cfg) :
    (positioned P e src dst c).monitor (positionedCfg P e src dst d) =
      positioned P e src dst (c.monitor d) := by
  rcases c with ⟨⟨s, tapes⟩, pos, lo, hi⟩
  cases s with
  | inl b => rfl
  | inr q =>
    simp only [LocatedCfg.monitor, positioned, positionedCfg, Program.machine, program,
      Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    cases ht : P.transition q (tapes (P.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨next, action⟩
      simp [Function.update_comp_equiv]

@[simp] theorem positioned_step (c : LocatedCfg (P.machine src)) :
    locatedStep ((program P e).machine dst) (positioned P e src dst c) =
      (locatedStep (P.machine src) c).map (positioned P e src dst) := by
  unfold locatedStep
  rw [show (positioned P e src dst c).config = positionedCfg P e src dst c.config from rfl,
    positionedCfg_step]
  cases hs : (P.machine src).step c.config <;> simp

theorem positioned_step_some (a b : LocatedCfg (P.machine src))
    (h : locatedStep (P.machine src) a = some b) :
    locatedStep ((program P e).machine dst) (positioned P e src dst a) =
      some (positioned P e src dst b) := by
  simp only [positioned_step, h, Option.map_some]

theorem positioned_trace {a b : LocatedCfg (P.machine src)} {nstep : ℕ}
    (h : Computation.Trace (locatedStep (P.machine src)) nstep a b) :
    Computation.Trace (locatedStep ((program P e).machine dst)) nstep
      (positioned P e src dst a) (positioned P e src dst b) :=
  MachineComposition.Trace.map _ (positioned_step_some P e src dst) h

/-- Both endpoints and every prefix retain their physical tapes and recorded intervals
up to the same permutation, with the original step count and space bound. -/
theorem positioned_segment {a b : LocatedCfg (P.machine src)} {nstep : ℕ} {σ : ℝ}
    (h : Segment (P.machine src) a b nstep σ) :
    Segment ((program P e).machine dst) (positioned P e src dst a)
      (positioned P e src dst b) nstep σ := by
  refine ⟨positioned_trace P e src dst h.1, ?_⟩
  intro k c hk hc
  obtain ⟨d, hd, rfl⟩ := MachineComposition.Trace.prefix_of_map _
    (positioned_step_some P e src dst) h.1 hk hc
  simpa only [positioned_space] using h.2 k d hk hd

end DetDLP_W1_Pipeline.PermutedTapes





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP_W1_Pipeline.WordPipeline

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP DetDLP.MachineComposition

def tail (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine) :
    Program (A.tapeCount+B.tapeCount) :=
  PermutedTapes.program (.ofMachine (addTapes B A.tapeCount)) (CallWiring.wire out B.inputTape)

def machine (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine) : PrimitiveMachine :=
  thenMachine (addTapes A B.tapeCount) (tail A out B)

def resultPort (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine)
    (bout : Fin B.tapeCount) : Fin (machine A out B).tapeCount :=
  CallWiring.wire out B.inputTape (Fin.castAdd A.tapeCount bout)

/-- Sequential ordinary word computation with arbitrary work tape counts and arbitrary
    garbage on the producer's final tapes. Step counts add. Visited-cell budgets add up
    to a fixed number of tapes, independently of the (possibly very large) step counts. -/
theorem run (A : PrimitiveMachine) (out : Fin A.tapeCount) (B : PrimitiveMachine) (bout : Fin B.tapeCount)
    {input mid result : List Bool} {tA sA tB sB : ℝ}
    (ha : RunsWithin A out input mid tA sA) (hb : RunsWithin B bout mid result tB sB) :
    RunsWithin (machine A out B) (resultPort A out B bout) input result (tA+tB)
      (sA+B.tapeCount+(sB+A.tapeCount)) := by
  let A' := addTapes A B.tapeCount
  let B' := addTapes B A.tapeCount
  let P := Program.ofMachine B'
  let e := CallWiring.wire out B.inputTape
  let Q := PermutedTapes.program P e
  obtain ⟨n,a,ht,hh,ho,hn,hs⟩ := (runsWithin_iff_final_space _ _ _ _ _ _).1 ha
  obtain ⟨m,b,hbseg,hbh,hbo,hm⟩ := (runsWithin_iff_segment _ _ _ _ _ _).1 hb
  let a' := addTapesLocated A B.tapeCount a
  have hat : Computation.Trace (locatedStep A') n (locatedInit A' input) a' := by
    rw [addTapesLocated_init]
    apply MachineComposition.Trace.map (addTapesLocated A B.tapeCount) _ ht
    intro c d h
    rw [addTapesLocated_step,h]; rfl
  have hsa : (visitedSpace a' : ℝ) ≤ sA+B.tapeCount := by
    rw [show visitedSpace a' = visitedSpace a+B.tapeCount from addTapesLocated_space .., Nat.cast_add]
    linarith
  have ha' : Segment A' (locatedInit A' input) a' n (sA+B.tapeCount) := segment_iff_final_space.mpr ⟨hat,hsa⟩
  let fr := CallWiring.saved a.config.tapes out
  let start := frameLocated B fr (locatedInit B mid)
  let finish := frameLocated B fr b
  have hseg : Segment (P.machine B'.inputTape) start finish m (sB + fr.space) := frameLocated_segment B fr hbseg
  let move := PermutedTapes.positioned P e B'.inputTape A'.inputTape
  have hseg' : Segment (Q.machine A'.inputTape) (move start) (move finish) m (sB+A.tapeCount) := by
    change Segment ((PermutedTapes.program P e).machine A'.inputTape) _ _ _ _
    simpa only [move,fr,CallWiring.saved_space] using PermutedTapes.positioned_segment P e B'.inputTape A'.inputTape hseg
  let entry := restartCfg A' Q a'
  have hw : LocatedWellFormed entry := fun i => locatedWellFormed_reachable hat i
  have hc : entry.config = (move start).config := by
    change (⟨.inr _,_⟩ : (Q.machine A'.inputTape).Cfg) = ⟨.inr _,_⟩
    congr 1
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    change Fin.append a.config.tapes (fun _ : Fin B.tapeCount => Turing.Tape.mk₁ []) (e j) =
      Fin.append (B.init mid).tapes fr.tapes (e.symm (e j))
    rw [e.symm_apply_apply]
    exact CallWiring.transfer a.config.tapes out B mid ho j
  have hp : ∀ i, (move start).position i = 0 := by
    intro i
    change Fin.append (fun _ : Fin B.tapeCount => (0 : ℤ)) (fun _ : Fin A.tapeCount => (0 : ℤ)) (e.symm i) = 0
    generalize e.symm i = j; induction j using Fin.addCases <;> simp
  have hz : OriginCovered (move start) := by
    intro i
    change Fin.append (locatedInit B mid).lower (fun _ : Fin A.tapeCount => (0:ℤ)) (e.symm i) ≤ 0 ∧
      0 ≤ Fin.append (locatedInit B mid).upper (fun _ : Fin A.tapeCount => (0:ℤ)) (e.symm i)
    generalize e.symm i = j
    induction j using Fin.addCases with
    | left k => simpa only [Fin.append_left] using originCovered_init B mid k
    | right k => simp
  obtain ⟨actual,he,seg⟩ := DetDLP_W1_SavedCall.RelativeMonitor.call hw hc hp hz hseg'
  have hs' : Segment (Q.machine A'.inputTape) entry actual m (sA+B.tapeCount+(sB+A.tapeCount)) :=
    seg.mono (by change (visitedSpace a' : ℝ) + _ ≤ _; linarith)
  have halt : ∃ b, actual.config.state = Sum.inl b := by rw [he]; exact hbh
  have hout : actual.config.tapes (resultPort A out B bout) = Turing.Tape.mk₁ (result.map some) := by
    rw [he]
    change Fin.append b.config.tapes fr.tapes (e.symm (e (Fin.castAdd A.tapeCount bout))) = _
    rwa [e.symm_apply_apply,Fin.append_left]
  have hrun := thenMachine_runsWithin_add A' Q (resultPort A out B bout) input result ha' hh hs' halt hout hn hm
  have hsB : 0 ≤ sB := (Nat.cast_nonneg (visitedSpace b)).trans (segment_iff_final_space.mp hbseg).2
  exact runsWithin_mono hrun le_rfl (max_le (by linarith [Nat.cast_nonneg (α:=ℝ) A.tapeCount]) le_rfl)

end DetDLP_W1_Pipeline.WordPipeline


