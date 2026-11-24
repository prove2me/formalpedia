-- Prove2me | Definitions.Def_CSL_Shared_Memory_NormalizationController
-- name    : CSL_Shared_Memory_NormalizationController
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:30:03.868167+00:00
-- url     : https://prove2.me/theorems/65ee5d11-3a01-4a8c-8bd4-398400f810a1
-- title:
--   Coded sorting library: Shared / Memory / NormalizationController
-- statement:
--   Module `CodedSorting.Shared.Memory.NormalizationController` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A single three-region disk controller for compact input, an arbitrary logical
--   I/O policy, and compact output. Conversion loop sizes are stored in resident
--   word arrays. Each controller observation expands to a fixed number of the
--   previously proved physical microsteps; no disk copy is a RAM operation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.NormalizationController

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_PhysicalNormalizationCompact

/-!
A single three-region disk controller for compact input, an arbitrary logical
I/O policy, and compact output. Conversion loop sizes are stored in resident
word arrays. Each controller observation expands to a fixed number of the
previously proved physical microsteps; no disk copy is a RAM operation.
-/
set_option autoImplicit false
namespace CSL.CommonNormalizationController
open WordControl
variable {L R B b d w : ℕ}

local instance {α : Type*} (o : Option α) : Decidable (o=none) := Option.decidable_eq_none o

abbrev Address (R : ℕ) := Fin R ⊕ (Fin R ⊕ Fin R)
abbrev Disk (R B w : ℕ) := Address R → Words B w

structure Program (L R B b d w : ℕ) where
  positive_region : 0 < R
  positive_block : 0 < B
  block_ratio : b ≤ B
  counter_capacity : R  <  (2^w)^d
  phase_capacity : 8 ≤ 2^w
  padding : Word w
  policy : ControlledNormalization.Policy L b R (Word w)

structure State (L R B b d w : ℕ) where
  ram : Words L w
  buffer : Words B w
  scratch : Words b w
  counter : Words d w
  inputCount : Words d w
  outputCount : Words d w
  phase : Word w
  stage : Word w
  disk : Disk R B w

def code (p : Program L R B b d w) (k : Fin 8) : Word w :=
  ⟨k.val,lt_of_lt_of_le k.isLt p.phase_capacity⟩

def inputSize (s : State L R B b d w) : ℕ := min (decodeWords s.inputCount) R
def outputSize (s : State L R B b d w) : ℕ := min (decodeWords s.outputCount) (R-1)

def converter (p : Program L R B b d w) (n : ℕ) (hn : n ≤ R) :
    PhysicalNormalizationLayout.Program R B b d w :=
  ⟨n,hn,hn.trans_lt p.counter_capacity,p.positive_region,p.positive_block,
    p.block_ratio,p.phase_capacity,p.padding⟩

def inputProgram (p : Program L R B b d w) (s : State L R B b d w) :=
  converter p (inputSize s) (Nat.min_le_right _ _)
def outputProgram (p : Program L R B b d w) (s : State L R B b d w) :=
  converter p (outputSize s) ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))

def expandView (disk : Disk R B w) : PhysicalNormalizationLayout.Disk R B w
  | .inl a => disk (.inl a)
  | .inr a => disk (.inr (.inl a))
def compactView (disk : Disk R B w) : PhysicalNormalizationLayout.Disk R B w
  | .inl a => disk (.inr (.inl a))
  | .inr a => disk (.inr (.inr a))
def installExpand (old : Disk R B w) (new : PhysicalNormalizationLayout.Disk R B w) : Disk R B w
  | .inl a => new (.inl a)
  | .inr (.inl a) => new (.inr a)
  | .inr (.inr a) => old (.inr (.inr a))
def installCompact (old : Disk R B w) (new : PhysicalNormalizationLayout.Disk R B w) : Disk R B w
  | .inl a => old (.inl a)
  | .inr (.inl a) => new (.inl a)
  | .inr (.inr a) => new (.inr a)
def installCore (old : Disk R B w) (new : Normalization.Disk R B (Word w)) : Disk R B w
  | .inl a => old (.inl a)
  | .inr (.inl a) => new a
  | .inr (.inr a) => old (.inr (.inr a))

def expandState (s : State L R B b d w) : PhysicalNormalizationLayout.State R B b d w :=
  ⟨s.buffer,s.scratch,s.counter,s.phase,expandView s.disk⟩
def compactState (s : State L R B b d w) : PhysicalNormalizationLayout.State R B b d w :=
  ⟨s.buffer,s.scratch,s.counter,s.phase,compactView s.disk⟩
def coreState (s : State L R B b d w) : FixedPolicyNormalization.State L B R w :=
  ⟨⟨s.ram,s.buffer,fun a => s.disk (.inr (.inl a))⟩,s.phase⟩

def putExpand (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :=
  {s with buffer:=t.buffer,scratch:=t.scratch,counter:=t.counter,phase:=t.phase, disk:=installExpand s.disk t.disk}
def putCompact (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :=
  {s with buffer:=t.buffer,scratch:=t.scratch,counter:=t.counter,phase:=t.phase, disk:=installCompact s.disk t.disk}
def putCore (s : State L R B b d w) (t : FixedPolicyNormalization.State L B R w) :=
  {s with ram:=t.data.ram,buffer:=t.data.buffer,phase:=t.phase, disk:=installCore s.disk t.data.disk}

@[simp] theorem expand_put (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :
    expandState (putExpand s t)=t := by
  cases t
  simp only [expandState,putExpand,expandView,installExpand]
  congr
  funext a
  cases a  <;> rfl
@[simp] theorem compact_put (s : State L R B b d w) (t : PhysicalNormalizationLayout.State R B b d w) :
    compactState (putCompact s t)=t := by
  cases t
  simp only [compactState,putCompact,compactView,installCompact]
  congr
  funext a
  cases a  <;> rfl
@[simp] theorem core_put (s : State L R B b d w) (t : FixedPolicyNormalization.State L B R w) :
    coreState (putCore s t)=t := by cases t; rfl

@[simp] theorem putExpand_twice (s : State L R B b d w)
    (t u : PhysicalNormalizationLayout.State R B b d w) : putExpand (putExpand s t) u=putExpand s u := by
  simp only [putExpand]
  congr 1
  try (funext a; rcases a with a | a | a <;> rfl)
@[simp] theorem putCompact_twice (s : State L R B b d w)
    (t u : PhysicalNormalizationLayout.State R B b d w) : putCompact (putCompact s t) u=putCompact s u := by
  simp only [putCompact]
  congr 1
  try (funext a; rcases a with a | a | a <;> rfl)
@[simp] theorem putCore_twice (s : State L R B b d w)
    (t u : FixedPolicyNormalization.State L B R w) : putCore (putCore s t) u=putCore s u := by
  simp only [putCore]
  congr 1
  try (funext a; rcases a with a | a | a <;> rfl)


def microRun (next : State L R B b d w → State L R B b d w × ℕ) :
    ℕ → State L R B b d w → State L R B b d w × ℕ
  | 0,s => (s,0)
  | n+1,s =>
      let first := next s
      let rest := microRun next n first.1
      (rest.1,first.2+rest.2)
def expandMicro (p : Program L R B b d w) (s : State L R B b d w) :=
  let e := PhysicalNormalizationLayout.step (inputProgram p s) (expandState s)
  (putExpand s e.1,e.2)
def compactMicro (p : Program L R B b d w) (s : State L R B b d w) :=
  let e := PhysicalNormalizationCompact.step (outputProgram p s) (compactState s)
  (putCompact s e.1,e.2)
def coreMicro (p : Program L R B b d w) (s : State L R B b d w) :=
  let e := FixedPolicyNormalization.step p.block_ratio (by have := p.phase_capacity; omega)
    p.padding ⟨p.policy⟩ (coreState s)
  (putCore s e.1,e.2)

/-- A fixed observation consists of at most eight known physical microsteps.
The only transition between stages depends on stored counters or the fixed
policy's resident halt test, never on an external execution schedule. -/
def step (p : Program L R B b d w) (s : State L R B b d w) : State L R B b d w × ℕ :=
  match s.stage.val with
  | 0 =>
      if decodeWords s.counter  <  inputSize s then
        let e := PhysicalNormalizationLayout.run (inputProgram p s) 7 (expandState s)
        (putExpand s e.1,e.2)
      else ({s with stage:=code p 1,phase:=code p 0},0)
  | 1 =>
      if p.policy s.ram = none then
        ({s with stage:=code p 2,phase:=code p 0,counter:=PhysicalNormalizationLayout.counterCode d w 0, buffer:=fun _=>p.padding,scratch:=fun _=>p.padding},0)
      else
        let e := FixedPolicyNormalization.run p.block_ratio (by have := p.phase_capacity; omega) p.padding
          ⟨p.policy⟩ 2 (coreState s)
        (putCore s e.1,e.2)
  | 2 =>
      if decodeWords s.counter  <  outputSize s then
        let e := PhysicalNormalizationCompact.run (outputProgram p s) 8 (compactState s)
        (putCompact s e.1,e.2)
      else ({s with stage:=code p 3},0)
  | _ => (s,0)

def run (p : Program L R B b d w) : ℕ → State L R B b d w → State L R B b d w × ℕ
  | 0,s => (s,0)
  | fuel+1,s =>
      let first := step p s
      let rest := run p fuel first.1
      (rest.1,first.2+rest.2)

theorem run_add (p : Program L R B b d w) (n m : ℕ) (s : State L R B b d w) :
    run p (n+m) s =
      ((run p m (run p n s).1).1,(run p n s).2+(run p m (run p n s).1).2) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => rw [Nat.succ_add]; simp only [run,ih,Nat.add_assoc]

@[simp] theorem run_one (p : Program L R B b d w) (s : State L R B b d w) :
    run p 1 s=step p s := by simp [run]

def initial (p : Program L R B b d w) (ram : Words L w)
    (inputCount outputCount : Words d w) (disk : Disk R B w) : State L R B b d w :=
  ⟨ram,fun _=>p.padding,fun _=>p.padding,PhysicalNormalizationLayout.counterCode d w 0,
    inputCount,outputCount,code p 0,code p 0,disk⟩

@[simp] theorem putExpand_self (s : State L R B b d w) :
    putExpand s (expandState s)=s := by
  cases s
  simp only [putExpand,expandState,installExpand,expandView]
  congr
  funext a
  rcases a with a|a
  · rfl
  · cases a  <;> rfl
@[simp] theorem putCompact_self (s : State L R B b d w) :
    putCompact s (compactState s)=s := by
  cases s
  simp only [putCompact,compactState,installCompact,compactView]
  congr
  funext a
  rcases a with a|a
  · rfl
  · cases a  <;> rfl
@[simp] theorem putCore_self (s : State L R B b d w) :
    putCore s (coreState s)=s := by
  cases s
  simp only [putCore,coreState,installCore]
  congr
  funext a
  rcases a with a|a
  · rfl
  · cases a  <;> rfl

/-- Lifting each individual microstep preserves the single resident state;
there is no second buffer or source-state snapshot between microsteps. -/
theorem expand_microsteps (p : Program L R B b d w) (n : ℕ) (s : State L R B b d w) :
    microRun (expandMicro p) n s=
      (putExpand s (PhysicalNormalizationLayout.run (inputProgram p s) n (expandState s)).1,
       (PhysicalNormalizationLayout.run (inputProgram p s) n (expandState s)).2) := by
  induction n generalizing s with
  | zero => simp [microRun,PhysicalNormalizationLayout.run]
  | succ n ih =>
    simp only [microRun,expandMicro,ih,expand_put,putExpand_twice]
    rfl

theorem compact_microsteps (p : Program L R B b d w) (n : ℕ) (s : State L R B b d w) :
    microRun (compactMicro p) n s=
      (putCompact s (PhysicalNormalizationCompact.run (outputProgram p s) n (compactState s)).1,
       (PhysicalNormalizationCompact.run (outputProgram p s) n (compactState s)).2) := by
  induction n generalizing s with
  | zero => simp [microRun,PhysicalNormalizationCompact.run]
  | succ n ih =>
    simp only [microRun,compactMicro,ih,compact_put,putCompact_twice]
    rfl

theorem core_microsteps (p : Program L R B b d w) (n : ℕ) (s : State L R B b d w) :
    microRun (coreMicro p) n s=
      (putCore s (FixedPolicyNormalization.run p.block_ratio
        (by have := p.phase_capacity; omega) p.padding ⟨p.policy⟩ n (coreState s)).1,
       (FixedPolicyNormalization.run p.block_ratio
        (by have := p.phase_capacity; omega) p.padding ⟨p.policy⟩ n (coreState s)).2) := by
  induction n generalizing s with
  | zero => simp [microRun,FixedPolicyNormalization.run]
  | succ n ih =>
    simp only [microRun,coreMicro,ih,core_put,putCore_twice]
    rfl

/-- The expansion stage is controlled by its counted loop counter. Its n
observations are the actual 7n physical microsteps, on the very same disk. -/
theorem expansion_run (p : Program L R B b d w) (s : State L R B b d w)
    (hcounter : decodeWords s.counter=0) (hphase : s.phase=code p 0)
    (hstage : s.stage=code p 0) (n : ℕ) (hn : n ≤ inputSize s) :
    (run p n s).1=putExpand s
      (PhysicalNormalizationLayout.run (inputProgram p s) (7*n) (expandState s)).1 ∧
    decodeWords (run p n s).1.counter=n ∧
    (run p n s).1.phase=code p 0 ∧ (run p n s).1.stage=code p 0 ∧
    (run p n s).2=3*n := by
  induction n with
  | zero =>
    simp only [run,Nat.mul_zero,PhysicalNormalizationLayout.run,putExpand_self]
    exact ⟨trivial,hcounter,hphase,hstage,trivial⟩
  | succ n ih =>
    have prev := ih (by omega)
    let old := (run p n s).1
    have hparams : inputProgram p old=inputProgram p s := by
      try dsimp only [old]; rw [prev.1]; rfl
    have hsize : inputSize old=inputSize s := by dsimp only [old]; rw [prev.1]; rfl
    have cycle := PhysicalNormalizationLayout.seven_steps (inputProgram p old)
      (expandState old) n (by simpa [inputProgram,converter,hsize] using (show n < inputSize s by omega))
      prev.2.1 (by exact prev.2.2.1)
    have hs : step p old =
        (putExpand old (PhysicalNormalizationLayout.run (inputProgram p old) 7
          (expandState old)).1,3) := by
      have hst : old.stage=code p 0 := prev.2.2.2.1
      simp only [step,hst,code,Fin.isValue,Fin.val_zero,Fin.val_one,Fin.val_two]
      rw [show decodeWords old.counter=n from prev.2.1,hsize,if_pos (by omega),cycle.2.2.2]
      try rfl
    try dsimp only [old] at hs hparams cycle
    rw [run_add,run_one,hs]
    refine ⟨?_,cycle.2.1,cycle.2.2.1,prev.2.2.2.1,?_⟩
    · rw [hparams,prev.1,expand_put,putExpand_twice]
      rw [show 7*(n+1)=7*n+7 by omega,PhysicalNormalizationLayout.run_add]
    · rw [prev.2.2.2.2]; omega

/-- The compaction stage uses the updated dedicated backing bank. -/
theorem compaction_run (p : Program L R B b d w) (s : State L R B b d w)
    (hcounter : decodeWords s.counter=0) (hphase : s.phase=code p 0)
    (hstage : s.stage=code p 2) (n : ℕ) (hn : n ≤ outputSize s) :
    (run p n s).1=putCompact s
      (PhysicalNormalizationCompact.run (outputProgram p s) (8*n) (compactState s)).1 ∧
    decodeWords (run p n s).1.counter=n ∧
    (run p n s).1.phase=code p 0 ∧ (run p n s).1.stage=code p 2 ∧
    (run p n s).2=5*n := by
  induction n with
  | zero =>
    simp only [run,Nat.mul_zero,PhysicalNormalizationCompact.run,putCompact_self]
    exact ⟨trivial,hcounter,hphase,hstage,trivial⟩
  | succ n ih =>
    have prev := ih (by omega)
    let old := (run p n s).1
    have hparams : outputProgram p old=outputProgram p s := by dsimp only [old]; rw [prev.1]; rfl
    have hsize : outputSize old=outputSize s := by dsimp only [old]; rw [prev.1]; rfl
    have cycle := PhysicalNormalizationCompact.eight_steps (outputProgram p old)
      (compactState old) n (by simpa [outputProgram,converter,hsize] using (show n < outputSize s by omega))
      prev.2.1 (by exact prev.2.2.1)
    have hs : step p old =
        (putCompact old (PhysicalNormalizationCompact.run (outputProgram p old) 8
          (compactState old)).1,5) := by
      have hst : old.stage=code p 2 := prev.2.2.2.1
      simp only [step,hst,code,Fin.isValue,Fin.val_zero,Fin.val_one,Fin.val_two]
      rw [show decodeWords old.counter=n from prev.2.1,hsize,if_pos (by omega),cycle.2.2.2]
      try rfl
    try dsimp only [old] at hs hparams cycle
    rw [run_add,run_one,hs]
    refine ⟨?_,cycle.2.1,cycle.2.2.1,prev.2.2.2.1,?_⟩
    · rw [hparams,prev.1,compact_put,putCompact_twice]
      rw [show 8*(n+1)=8*n+8 by omega,PhysicalNormalizationCompact.run_add]
    · rw [prev.2.2.2.2]; omega

def coreRun (p : Program L R B b d w) (fuel : ℕ) (s : State L R B b d w) :=
  FixedPolicyNormalization.run p.block_ratio (by have := p.phase_capacity; omega)
    p.padding ⟨p.policy⟩ (2*fuel) (coreState s)

/-- Exactly fuel nonhalting source observations; the eventual halt condition
is checked separately when entering output conversion. -/
def CoreLive (p : Program L R B b d w) (fuel : ℕ) (s : State L R B b d w) : Prop :=
  ∀ k, k < fuel → p.policy (coreRun p k s).1.data.ram ≠ none

theorem core_run (p : Program L R B b d w) (s : State L R B b d w)
    (_hphase : s.phase=code p 0) (hstage : s.stage=code p 1)
    (fuel : ℕ) (hlive : CoreLive p fuel s) :
    run p fuel s = (putCore s (coreRun p fuel s).1,(coreRun p fuel s).2) := by
  induction fuel with
  | zero => simp [run,coreRun,FixedPolicyNormalization.run]
  | succ fuel ih =>
    have prev := ih (by intro k hk; exact hlive k (by omega))
    let old := (run p fuel s).1
    have ho : old=putCore s (coreRun p fuel s).1 := congrArg Prod.fst prev
    have hs : step p old =
        (putCore old (coreRun p 1 old).1,(coreRun p 1 old).2) := by
      have hst : old.stage=code p 1 := by rw [ho]; exact hstage
      have hn : p.policy old.ram≠none := by rw [ho]; exact hlive fuel (by omega)
      simp only [step,hst,code,Fin.isValue,Fin.val_zero,Fin.val_one,Fin.val_two,hn,if_false,coreRun]
    try dsimp only [old] at hs
    rw [run_add,run_one,hs]
    have hcombine : coreRun p (fuel+1) s =
        ((coreRun p 1 old).1,(coreRun p fuel s).2+(coreRun p 1 old).2) := by
      unfold coreRun
      rw [show 2*(fuel+1)=2*fuel+2*1 by omega,FixedPolicyNormalization.run_add]
      rw [ho,core_put]
      rfl
    rw [hcombine]
    simp only [Prod.fst,Prod.snd]
    change (putCore old (coreRun p 1 old).1,(run p fuel s).2+(coreRun p 1 old).2)=_
    simp only [ho,putCore_twice,congrArg Prod.snd prev]

def enterCore (p : Program L R B b d w) (s : State L R B b d w) :=
  {s with stage:=code p 1,phase:=code p 0}
def enterCompact (p : Program L R B b d w) (s : State L R B b d w) : State L R B b d w :=
  {s with stage:=code p 2,phase:=code p 0,counter:=PhysicalNormalizationLayout.counterCode d w 0, buffer:=fun _=>p.padding,scratch:=fun _=>p.padding}

theorem expansion_switch (p : Program L R B b d w) (s : State L R B b d w)
    (hc : decodeWords s.counter=inputSize s) (hs : s.stage=code p 0) :
    step p s=(enterCore p s,0) := by simp [step,hs,code,hc,enterCore]
theorem core_switch (p : Program L R B b d w) (s : State L R B b d w)
    (hh : p.policy s.ram=none) (hs : s.stage=code p 1) :
    step p s=(enterCompact p s,0) := by simp [step,hs,code,hh,enterCompact]

def expanded (p : Program L R B b d w) (s : State L R B b d w) :=
  putExpand s (PhysicalNormalizationLayout.run (inputProgram p s)
    (7*inputSize s) (expandState s)).1

def coreInput (p : Program L R B b d w) (s : State L R B b d w) :=
  enterCore p (expanded p s)
def computed (p : Program L R B b d w) (fuel : ℕ) (s : State L R B b d w) :=
  putCore (coreInput p s) (coreRun p fuel (coreInput p s)).1
def compactInput (p : Program L R B b d w) (fuel : ℕ) (s : State L R B b d w) :=
  enterCompact p (computed p fuel s)
def compacted (p : Program L R B b d w) (fuel : ℕ) (s : State L R B b d w) :=
  let t := compactInput p fuel s
  putCompact t (PhysicalNormalizationCompact.run (outputProgram p t)
    (8*outputSize t) (compactState t)).1

/-- The fixed controller performs all three stages. The horizon merely
observes the run; every actual stage change is decided by resident state. -/
theorem run_pipeline (p : Program L R B b d w) (s : State L R B b d w)
    (hcounter : decodeWords s.counter=0) (hphase : s.phase=code p 0)
    (hstage : s.stage=code p 0) (fuel : ℕ)
    (hlive : CoreLive p fuel (coreInput p s))
    (hhalt : p.policy (coreRun p fuel (coreInput p s)).1.data.ram=none) :
    run p (inputSize s+1+fuel+1+outputSize s) s =
      (compacted p fuel s,3*inputSize s+(coreRun p fuel (coreInput p s)).2+5*outputSize s) := by
  have he := expansion_run p s hcounter hphase hstage (inputSize s) (le_refl _)
  have heq : (run p (inputSize s) s).1=expanded p s := he.1
  have hsize : inputSize (expanded p s)=inputSize s := rfl
  have hes : step p (expanded p s)=(coreInput p s,0) := by
    apply expansion_switch
    · change decodeWords (expanded p s).counter=inputSize s
      rw [←heq]; exact he.2.1
    · rw [←heq]; exact he.2.2.2.1
  have hc := core_run p (coreInput p s) rfl rfl fuel hlive
  have hcs : step p (computed p fuel s)=(compactInput p fuel s,0) := by
    apply core_switch
    · exact hhalt
    · rfl
  have ho := compaction_run p (compactInput p fuel s)
    (by simp [compactInput,enterCompact,PhysicalNormalizationLayout.decode_counterCode])
    rfl rfl (outputSize s) (by exact le_refl _)
  have hoq : (run p (outputSize s) (compactInput p fuel s)).1=compacted p fuel s := ho.1
  have he1 : run p (inputSize s+1) s=(coreInput p s,3*inputSize s) := by
    rw [run_add,heq,run_one,hes,he.2.2.2.2]
    simp
  have hc1 : run p (inputSize s+1+fuel) s=
      (computed p fuel s,3*inputSize s+(coreRun p fuel (coreInput p s)).2) := by
    rw [run_add,he1,hc]
    rfl
  have hs1 : run p (inputSize s+1+fuel+1) s=
      (compactInput p fuel s,3*inputSize s+(coreRun p fuel (coreInput p s)).2) := by
    rw [run_add,hc1,run_one,hcs]
    simp
  rw [run_add,hs1,hoq,ho.2.2.2.2]


/-- One final local observation sets the halt stage. Thereafter the fixed
controller is stationary; the observation horizon is not its stopping rule. -/
theorem pipeline_halts (p : Program L R B b d w) (s : State L R B b d w)
    (hcounter : decodeWords s.counter=0) (hphase : s.phase=code p 0)
    (hstage : s.stage=code p 0) (fuel : ℕ)
    (hlive : CoreLive p fuel (coreInput p s))
    (hhalt : p.policy (coreRun p fuel (coreInput p s)).1.data.ram=none) :
    let result := run p (inputSize s+1+fuel+1+outputSize s+1) s
    result.1.disk=(compacted p fuel s).disk ∧
    step p result.1=(result.1,0) ∧
    result.2=3*inputSize s+(coreRun p fuel (coreInput p s)).2+5*outputSize s := by
  try dsimp only
  have ho := compaction_run p (compactInput p fuel s)
    (by simp [compactInput,enterCompact,PhysicalNormalizationLayout.decode_counterCode])
    rfl rfl (outputSize s) (by exact le_refl _)
  have hoq : (run p (outputSize s) (compactInput p fuel s)).1=compacted p fuel s := ho.1
  have hcount : decodeWords (compacted p fuel s).counter=outputSize s := by
    rw [←hoq]; exact ho.2.1
  have hdone : step p (compacted p fuel s)=
      ({compacted p fuel s with stage:=code p 3},0) := by
    have hst : (compacted p fuel s).stage=code p 2 := rfl
    have hsz : outputSize (compacted p fuel s)=outputSize s := rfl
    simp only [step,hst,code,Fin.isValue,Fin.val_zero,Fin.val_one,Fin.val_two,hcount,hsz,lt_self_iff_false,if_false]
    try rfl
  rw [run_add,run_pipeline p s hcounter hphase hstage fuel hlive hhalt,run_one,hdone]
  simp [step,code]

/-- The halted configuration of the pipeline is in the terminal stage `3`. -/
theorem pipeline_stage (p : Program L R B b d w) (s : State L R B b d w)
    (hcounter : decodeWords s.counter=0) (hphase : s.phase=code p 0)
    (hstage : s.stage=code p 0) (fuel : ℕ)
    (hlive : CoreLive p fuel (coreInput p s))
    (hhalt : p.policy (coreRun p fuel (coreInput p s)).1.data.ram=none) :
    (run p (inputSize s+1+fuel+1+outputSize s+1) s).1.stage = code p 3 := by
  have ho := compaction_run p (compactInput p fuel s)
    (by simp [compactInput,enterCompact,PhysicalNormalizationLayout.decode_counterCode])
    rfl rfl (outputSize s) (by exact le_refl _)
  have hoq : (run p (outputSize s) (compactInput p fuel s)).1=compacted p fuel s := ho.1
  have hcount : decodeWords (compacted p fuel s).counter=outputSize s := by
    rw [←hoq]; exact ho.2.1
  have hdone : step p (compacted p fuel s)=
      ({compacted p fuel s with stage:=code p 3},0) := by
    have hst : (compacted p fuel s).stage=code p 2 := rfl
    have hsz : outputSize (compacted p fuel s)=outputSize s := rfl
    simp only [step,hst,code,Fin.isValue,Fin.val_zero,Fin.val_one,Fin.val_two,hcount,hsz,lt_self_iff_false,if_false]
    try rfl
  rw [run_add,run_pipeline p s hcounter hphase hstage fuel hlive hhalt,run_one,hdone]

/-- Logical input seen by the arbitrary core. Live input blocks are
characterized below; the remaining backing blocks are arbitrary scratch. -/
def logicalInput (p : Program L R B b d w) (s : State L R B b d w) :
    Normalization.LogicalState L b R (Word w) :=
  ⟨s.ram,fun j => Normalization.blockPrefix p.block_ratio
    ((expanded p s).disk (.inr (.inl j)))⟩

def outputWord (p : Program L R B b d w) (s : State L R B b d w) :=
  PhysicalNormalizationCompact.targetWord (outputProgram p s) (compactView s.disk)

theorem core_logical_refinement (p : Program L R B b d w)
    (s : State L R B b d w) (fuel : ℕ) :
    Normalization.Represents p.block_ratio
      (ControlledNormalization.runLogical p.policy fuel (logicalInput p s)).1
      (coreRun p fuel (coreInput p s)).1.data ∧
    (ControlledNormalization.runLogical p.policy fuel (logicalInput p s)).2 =
      (coreRun p fuel (coreInput p s)).2 := by
  exact FixedPolicyNormalization.logical_refinement p.block_ratio
    (by have := p.phase_capacity; omega) p.padding ⟨p.policy⟩ fuel
    (logicalInput p s) (coreState (coreInput p s)).data ⟨rfl,fun _=>rfl⟩

/-- The compact output is the result of the arbitrary simulated algorithm,
not the input of a conversion roundtrip. All charges refer to the same run. -/
theorem simulation (p : Program L R B b d w) (s : State L R B b d w)
    (hcounter : decodeWords s.counter=0) (hphase : s.phase=code p 0)
    (hstage : s.stage=code p 0) (fuel : ℕ)
    (hlive : CoreLive p fuel (coreInput p s))
    (hhalt : p.policy (coreRun p fuel (coreInput p s)).1.data.ram=none) :
    let result := run p (inputSize s+1+fuel+1+outputSize s) s
    let logical := ControlledNormalization.runLogical p.policy fuel (logicalInput p s)
    (∀ j : Fin (outputSize s),∀ i : Fin b,
      outputWord p result.1 (j.val*b+i.val)=
        logical.1.disk (j.castLE ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))) i) ∧
    result.2=logical.2+3*inputSize s+5*outputSize s := by
  try dsimp only
  rw [run_pipeline p s hcounter hphase hstage fuel hlive hhalt]
  have hr := core_logical_refinement p s fuel
  constructor
  · intro j i
    let t := compactInput p fuel s
    have hspare : (outputProgram p t).blocks < R := by
      exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt p.positive_region (by omega))
    have hc := PhysicalNormalizationCompact.actual_compaction (outputProgram p t) hspare
      (compactView t.disk)
    have hinit : compactState t=PhysicalNormalizationLayout.initial (outputProgram p t) 0
        (compactView t.disk) := rfl
    have hout : outputWord p (compacted p fuel s) (j.val*b+i.val)=
        (coreRun p fuel (coreInput p s)).1.data.disk
          (PhysicalNormalizationLayout.index (outputProgram p t) j.val) (i.castLE p.block_ratio) := by
      change PhysicalNormalizationCompact.targetWord (outputProgram p t)
        (compactView (putCompact t
          (PhysicalNormalizationCompact.run (outputProgram p t) (8*outputSize t) (compactState t)).1).disk)
            (j.val*b+i.val)=_
      change PhysicalNormalizationCompact.targetWord (outputProgram p t)
        (PhysicalNormalizationCompact.run (outputProgram p t) (8*outputSize t) (compactState t)).1.disk
            (j.val*b+i.val)=_
      rw [hinit]
      exact hc.1 j i
    rw [hout]
    have hind : PhysicalNormalizationLayout.index (outputProgram p t) j.val=
        j.castLE ((Nat.min_le_right _ _).trans (Nat.sub_le _ _)) := by
      apply Fin.ext
      exact PhysicalNormalizationLayout.index_val _ _ (j.isLt.trans hspare)
    rw [hind]
    exact (congrFun (hr.1.2 _) i).symm
  · rw [←hr.2]
    omega

/-- Ordinary termination of the source is sufficient. Choosing its first
halt supplies the exact nonhalting prefix used in the staged refinement. -/
theorem terminating_simulation (p : Program L R B b d w) (s : State L R B b d w)
    (hcounter : decodeWords s.counter=0) (hphase : s.phase=code p 0)
    (hstage : s.stage=code p 0)
    (hterm : ∃ fuel, p.policy (coreRun p fuel (coreInput p s)).1.data.ram=none) :
    ∃ fuel,
      let result := run p (inputSize s+1+fuel+1+outputSize s) s
      let logical := ControlledNormalization.runLogical p.policy fuel (logicalInput p s)
      (∀ j : Fin (outputSize s),∀ i : Fin b,
        outputWord p result.1 (j.val*b+i.val)=
          logical.1.disk (j.castLE ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))) i) ∧
      result.2=logical.2+3*inputSize s+5*outputSize s ∧
      let halted := run p (inputSize s+1+fuel+1+outputSize s+1) s
      step p halted.1=(halted.1,0) := by
  classical
  let fuel := Nat.find hterm
  have hhalt : p.policy (coreRun p fuel (coreInput p s)).1.data.ram=none := Nat.find_spec hterm
  have hlive : CoreLive p fuel (coreInput p s) := by
    intro k hk
    exact Nat.find_min hterm hk
  refine ⟨fuel,?_⟩
  have hs := simulation p s hcounter hphase hstage fuel hlive hhalt
  have hh := pipeline_halts p s hcounter hphase hstage fuel hlive hhalt
  exact ⟨hs.1,hs.2,hh.2.1⟩

theorem expansion_untouched (p : PhysicalNormalizationLayout.Program R B b d w)
    (disk : PhysicalNormalizationLayout.Disk R B w) (n : ℕ) (hn : n ≤ p.blocks)
    (j : Fin R) (hj : n ≤ j.val) :
    PhysicalNormalizationLayout.writtenLoop p n disk (.inr j)=disk (.inr j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [PhysicalNormalizationLayout.writtenLoop,PhysicalNormalizationLayout.written]
    have hne : (Sum.inr j : PhysicalNormalizationLayout.Address R) ≠ Sum.inr (PhysicalNormalizationLayout.index p n) := by
      intro h
      have he := congrArg Fin.val (Sum.inr.inj h)
      rw [PhysicalNormalizationLayout.index_val p n
        (by have := p.block_bound; omega)] at he
      omega
    rw [Function.update_of_ne hne]
    exact ih (by omega) (by omega)

/-- Conversion changes only live logical input blocks; pre-existing scratch
blocks are the same arbitrary backing contents presented to the source. -/
theorem logicalInput_scratch (p : Program L R B b d w) (ram : Words L w)
    (nIn nOut : Words d w) (disk : Disk R B w) (j : Fin R)
    (hj : min (decodeWords nIn) R ≤ j.val) (i : Fin b) :
    let s := initial p ram nIn nOut disk
    (logicalInput p s).disk j i=disk (.inr (.inl j)) (i.castLE p.block_ratio) := by
  try dsimp only
  let s := initial p ram nIn nOut disk
  have he := PhysicalNormalizationLayout.loop_refines (inputProgram p s)
    (expandView disk) (inputSize s) (le_refl _)
  change (PhysicalNormalizationLayout.run (inputProgram p s) (7*inputSize s)
      (PhysicalNormalizationLayout.initial (inputProgram p s) 0 (expandView disk))).1.disk
        (.inr j) (i.castLE p.block_ratio)=_
  rw [he.1,expansion_untouched (inputProgram p s) (expandView disk)
    (inputSize s) (le_refl _) j hj]
  rfl

/-- Expanded logical input positions equal the caller's compact source words. -/
theorem logicalInput_payload (p : Program L R B b d w) (ram : Words L w)
    (nIn nOut : Words d w) (disk : Disk R B w)
    (j : Fin (min (decodeWords nIn) R)) (i : Fin b) :
    let s := initial p ram nIn nOut disk
    (logicalInput p s).disk (j.castLE (Nat.min_le_right _ _)) i=
      PhysicalNormalizationLayout.sourceWord (inputProgram p s) (expandView disk)
        (j.val*b+i.val) := by
  try dsimp only
  let s := initial p ram nIn nOut disk
  have he := PhysicalNormalizationLayout.actual_expansion (inputProgram p s) (expandView disk)
  have hind : PhysicalNormalizationLayout.index (inputProgram p s) j.val=
      j.castLE (Nat.min_le_right _ _) := by
    apply Fin.ext
    exact PhysicalNormalizationLayout.index_val _ _ (j.isLt.trans_le (Nat.min_le_right _ _))
  have hx := he.1 j (i.castLE p.block_ratio)
  simp only [Fin.coe_castLE,if_pos i.isLt,hind] at hx
  exact hx

/-- Every changing payload/control cell is explicit. Address ports can be
reserved separately without changing this count. -/
theorem resident_word_count :
    Fintype.card (Fin L ⊕ (Fin B ⊕ (Fin b ⊕ (Fin d ⊕ (Fin d ⊕ (Fin d ⊕ Fin 2)))))) =
      L+B+b+3*d+2 := by simp; omega

/-- A counted address port uses one more word than a region-local counter.
The fixed eight-phase capacity is already enough to select all three banks. -/
def physicalAddress (a : Address R) : Fin (R+(R+R)) :=
  finSumFinEquiv (Sum.map id finSumFinEquiv a)

theorem physicalAddress_injective : Function.Injective (@physicalAddress R) := by
  intro a z h
  apply (Sum.map_injective.mpr ⟨Function.injective_id,finSumFinEquiv.injective⟩)
  exact finSumFinEquiv.injective h

theorem address_capacity (p : Program L R B b d w) :
    R+(R+R)  ≤  (2^w)^(d+1) := by
  rw [pow_succ]
  have h1 : R ≤ (2^w)^d := Nat.le_of_lt p.counter_capacity
  have h2 : 3 ≤ 2^w := by have := p.phase_capacity; omega
  calc
    R+(R+R)=R*3 := by omega
    _  ≤  (2^w)^d*3 := Nat.mul_le_mul_right _ h1
    _  ≤  (2^w)^d*(2^w) := Nat.mul_le_mul_left _ h2

def addressWords (a : Address R) : Words (d+1) w :=
  PhysicalNormalizationLayout.counterCode (d+1) w (physicalAddress a).val

theorem addressWords_decode (p : Program L R B b d w) (a : Address R) :
    decodeWords (addressWords (d:=d) (w:=w) a)=(physicalAddress a).val := by
  rw [addressWords,PhysicalNormalizationLayout.decode_counterCode,
    Nat.mod_eq_of_lt ((physicalAddress a).isLt.trans_le (address_capacity p))]

/-- The state plus a separate physical-address port fits the ordinary
normalized branch once its fixed control threshold is respected. -/
theorem normalized_memory_fit (M B b d : ℕ) (hB : 2*B ≤ M)
    (hb : 8*b ≤ M) (hcontrol : 32*d+24 ≤ M) :
    M/4+B+b+3*d+2+(d+1) ≤ M := by omega

theorem normalized_controller_memory (ratio C M B d : ℕ) (hratio : 2 ≤ ratio)
    (hB : 0 < B) (hMB : 2*B ≤ M)
    (hM : NormalizationComplete.threshold ratio C (8*d+6) ≤ M) :
    M/4+B+Normalization.logicalBlockSize B (NormalizationComplete.scale ratio)+4*d+3 ≤ M := by
  have hp := NormalizationComplete.normalized_parameters ratio C (8*d+6) M B
    hratio hB hMB hM
  have ht := NormalizationComplete.threshold_bounds ratio C (8*d+6) M hM
  have hratioBlock := hp.2.1
  have hb : 8*Normalization.logicalBlockSize B (NormalizationComplete.scale ratio) ≤ M := by
    have hdiv : 4*(M/4) ≤ M := Nat.mul_div_le M 4
    nlinarith
  have h := normalized_memory_fit M B
    (Normalization.logicalBlockSize B (NormalizationComplete.scale ratio)) d hMB hb (by omega)
  omega

/-- The exact charge established by simulation has the required scan order
for possibly different live input and output lengths. -/
theorem normalized_conversion_charge (inputWords outputWords B K : ℕ)
    (hB : 0 < B) (hK : 0 < K) :
    3*LayoutConversion.blockCount inputWords (Normalization.logicalBlockSize B K)+
      5*LayoutConversion.blockCount outputWords (Normalization.logicalBlockSize B K)  ≤ 
    10*K*(LayoutConversion.blockCount inputWords B+LayoutConversion.blockCount outputWords B) := by
  have hi := LayoutConversion.normalized_blockCount inputWords B K hB hK
  have ho := LayoutConversion.normalized_blockCount outputWords B K hB hK
  nlinarith

/-- Input/output lengths are ordinary runtime words; they do not select code. -/
theorem encoded_sizes (p : Program L R B b d w) (ram : Words L w) (disk : Disk R B w)
    (nIn nOut : ℕ) (hin : nIn ≤ R) (hout : nOut < R) :
    let s := initial p ram (PhysicalNormalizationLayout.counterCode d w nIn) (PhysicalNormalizationLayout.counterCode d w nOut) disk
    inputSize s=nIn ∧ outputSize s=nOut := by
  try dsimp [initial,inputSize,outputSize]
  rw [PhysicalNormalizationLayout.decode_counterCode,PhysicalNormalizationLayout.decode_counterCode,
    Nat.mod_eq_of_lt (hin.trans_lt p.counter_capacity),
    Nat.mod_eq_of_lt (hout.trans p.counter_capacity)]
  exact ⟨Nat.min_eq_left hin,Nat.min_eq_left (by omega)⟩

end CSL.CommonNormalizationController


