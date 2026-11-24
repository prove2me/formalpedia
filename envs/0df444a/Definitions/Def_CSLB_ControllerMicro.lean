-- Prove2me | Definitions.Def_CSLB_ControllerMicro
-- name    : CSLB_ControllerMicro
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T16:00:43.949326+00:00
-- url     : https://prove2.me/theorems/401a5f56-432e-42a8-9d42-ca853687f40f
-- title:
--   Coded sorting bridge: ControllerMicro
-- statement:
--   # The normalization controller as a sequence of single-transfer micro-steps
--
--   One observation (`CommonNormalizationController.step`) of the controller runs 7, 2 or 8
--   micro-steps of an inner machine, or makes a free stage transition. Here a counter `r` of
--   remaining micro-steps of the current observation is added, giving a one-transfer-per-step
--   machine `micro`. Every micro-step is described by a block action that depends only on the
--   resident state (`microAct`), and `micro` iterated reproduces `run`.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSLB_MicroSpecs

/-! # The normalization controller as a sequence of single-transfer micro-steps

One observation (`CommonNormalizationController.step`) of the controller runs 7, 2 or 8
micro-steps of an inner machine, or makes a free stage transition. Here a counter `r` of
remaining micro-steps of the current observation is added, giving a one-transfer-per-step
machine `micro`. Every micro-step is described by a block action that depends only on the
resident state (`microAct`), and `micro` iterated reproduces `run`. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CSLB.ControllerMicro
open CSL CSL.CommonNormalizationController CSLB.MicroSpecs WordControl

variable {L R B b d w : ℕ}

local instance {α : Type*} (o : Option α) : Decidable (o=none) := Option.decidable_eq_none o

def expAddr : PhysicalNormalizationLayout.Address R → Address R
  | .inl a => .inl a
  | .inr a => .inr (.inl a)

def cmpAddr : PhysicalNormalizationLayout.Address R → Address R
  | .inl a => .inr (.inl a)
  | .inr a => .inr (.inr a)

def coreAddr (a : Fin R) : Address R := .inr (.inl a)

def _root_.CSLB.MicroSpecs.BAct.map {α β : Type} (f : α → β) : BAct α → BAct β
  | .none => .none
  | .read a => .read (f a)
  | .write a => .write (f a)

/-- One micro-step. Returns the new state, the new remaining-step counter, and the cost. -/
def micro (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ) :
    State L R B b d w × ℕ × ℕ :=
  if r = 0 then
    match s.stage.val with
    | 0 => if decodeWords s.counter < inputSize s then
          ((expandMicro p s).1, 6, (expandMicro p s).2)
        else (enterCore p s, 0, 0)
    | 1 => if p.policy s.ram = none then (enterCompact p s, 0, 0)
        else ((coreMicro p s).1, 1, (coreMicro p s).2)
    | 2 => if decodeWords s.counter < outputSize s then
          ((compactMicro p s).1, 7, (compactMicro p s).2)
        else ({s with stage := code p 3}, 0, 0)
    | _ => (s, 0, 0)
  else
    match s.stage.val with
    | 0 => ((expandMicro p s).1, r - 1, (expandMicro p s).2)
    | 1 => ((coreMicro p s).1, r - 1, (coreMicro p s).2)
    | 2 => ((compactMicro p s).1, r - 1, (compactMicro p s).2)
    | _ => (s, 0, 0)

def expandAct (p : Program L R B b d w) (s : State L R B b d w) : BAct (Address R) :=
  (layoutAct (inputProgram p s) (expandState s)).map expAddr

def compactAct' (p : Program L R B b d w) (s : State L R B b d w) : BAct (Address R) :=
  (compactAct (outputProgram p s) (compactState s)).map cmpAddr

def coreAct' (p : Program L R B b d w) (s : State L R B b d w) : BAct (Address R) :=
  (coreAct (⟨p.policy⟩ : FixedPolicyNormalization.Program L b R w) (coreState s)).map coreAddr

/-- The block action of `micro`; it depends only on the resident part of `s`. -/
def microAct (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ) : BAct (Address R) :=
  if r = 0 then
    match s.stage.val with
    | 0 => if decodeWords s.counter < inputSize s then expandAct p s else .none
    | 1 => if p.policy s.ram = none then .none else coreAct' p s
    | 2 => if decodeWords s.counter < outputSize s then compactAct' p s else .none
    | _ => .none
  else
    match s.stage.val with
    | 0 => expandAct p s
    | 1 => coreAct' p s
    | 2 => compactAct' p s
    | _ => .none

/-! Disk bookkeeping for the three views. -/

theorem installExpand_view (old : Disk R B w) : installExpand old (expandView old) = old := by
  funext a; rcases a with a | a | a <;> rfl

theorem installExpand_update (old : Disk R B w) (x : PhysicalNormalizationLayout.Address R)
    (v : Words B w) :
    installExpand old (Function.update (expandView old) x v) =
      Function.update old (expAddr x) v := by
  funext a
  rcases x with x | x <;> rcases a with a | a | a <;>
    simp [installExpand, expandView, expAddr, Function.update_apply]

theorem installCompact_view (old : Disk R B w) : installCompact old (compactView old) = old := by
  funext a; rcases a with a | a | a <;> rfl

theorem installCompact_update (old : Disk R B w) (x : PhysicalNormalizationLayout.Address R)
    (v : Words B w) :
    installCompact old (Function.update (compactView old) x v) =
      Function.update old (cmpAddr x) v := by
  funext a
  rcases x with x | x <;> rcases a with a | a | a <;>
    simp [installCompact, compactView, cmpAddr, Function.update_apply]

theorem installCore_view (old : Disk R B w) :
    installCore old (fun a => old (.inr (.inl a))) = old := by
  funext a; rcases a with a | a | a <;> rfl

theorem installCore_update (old : Disk R B w) (x : Fin R) (v : Words B w) :
    installCore old (Function.update (fun a => old (.inr (.inl a))) x v) =
      Function.update old (coreAddr x) v := by
  funext a
  rcases a with a | a | a <;> simp [installCore, coreAddr, Function.update_apply]

/-! Specification of each lifted micro-step against an arbitrary dummy disk `z`. -/

/-- The result of a block action applied to the step computed with a dummy disk. -/
def resolve (s : State L R B b d w) (t : State L R B b d w) :
    BAct (Address R) → State L R B b d w × ℕ
  | .none => ({t with disk := s.disk}, 0)
  | .read a => ({t with buffer := s.disk a, disk := s.disk}, 1)
  | .write a => ({t with disk := Function.update s.disk a s.buffer}, 1)

theorem expandMicro_spec (p : Program L R B b d w) (s : State L R B b d w)
    (z : Disk R B w) :
    expandMicro p s = resolve s (expandMicro p {s with disk := z}).1 (expandAct p s) := by
  unfold expandMicro expandAct
  have hspec := layout_spec (inputProgram p s) (expandState s) (expandView z)
  have he : expandState {s with disk := z} = {expandState s with disk := expandView z} := rfl
  have hi : inputProgram p {s with disk := z} = inputProgram p s := rfl
  rw [he, hi, hspec]
  generalize layoutAct (inputProgram p s) (expandState s) = act
  rcases act with _ | a | a
  · simp only [resolve, BAct.map, putExpand]
    rw [show (expandState s).disk = expandView s.disk from rfl, installExpand_view]
    try rfl
  · simp only [resolve, BAct.map, putExpand]
    rw [show (expandState s).disk = expandView s.disk from rfl, installExpand_view]
    rcases a with a | a <;> rfl
  · simp only [resolve, BAct.map, putExpand]
    rw [show (expandState s).disk = expandView s.disk from rfl, installExpand_update]
    rfl

theorem compactMicro_spec (p : Program L R B b d w) (s : State L R B b d w)
    (z : Disk R B w) :
    compactMicro p s = resolve s (compactMicro p {s with disk := z}).1 (compactAct' p s) := by
  unfold compactMicro compactAct'
  have hspec := compact_spec (outputProgram p s) (compactState s) (compactView z)
  have he : compactState {s with disk := z} = {compactState s with disk := compactView z} := rfl
  have hi : outputProgram p {s with disk := z} = outputProgram p s := rfl
  rw [he, hi, hspec]
  generalize compactAct (outputProgram p s) (compactState s) = act
  rcases act with _ | a | a
  · simp only [resolve, BAct.map, putCompact]
    rw [show (compactState s).disk = compactView s.disk from rfl, installCompact_view]
    try rfl
  · simp only [resolve, BAct.map, putCompact]
    rw [show (compactState s).disk = compactView s.disk from rfl, installCompact_view]
    rcases a with a | a <;> rfl
  · simp only [resolve, BAct.map, putCompact]
    rw [show (compactState s).disk = compactView s.disk from rfl, installCompact_update]
    try rfl

theorem coreMicro_spec (p : Program L R B b d w) (s : State L R B b d w)
    (z : Disk R B w) :
    coreMicro p s = resolve s (coreMicro p {s with disk := z}).1 (coreAct' p s) := by
  unfold coreMicro coreAct'
  have hspec := core_spec p.block_ratio (by have := p.phase_capacity; omega) p.padding
    (⟨p.policy⟩ : FixedPolicyNormalization.Program L b R w) (coreState s)
    (fun a => z (.inr (.inl a)))
  have he : coreState {s with disk := z} =
      ⟨{(coreState s).data with disk := fun a => z (.inr (.inl a))}, (coreState s).phase⟩ := rfl
  rw [he, hspec]
  generalize coreAct (⟨p.policy⟩ : FixedPolicyNormalization.Program L b R w) (coreState s) = act
  rcases act with _ | a | a
  · simp only [resolve, BAct.map, putCore]
    rw [show (coreState s).data.disk = (fun a => s.disk (.inr (.inl a))) from rfl,
      installCore_view]
    try rfl
  · simp only [resolve, BAct.map, putCore]
    rw [show (coreState s).data.disk = (fun a => s.disk (.inr (.inl a))) from rfl,
      installCore_view]
    try rfl
  · simp only [resolve, BAct.map, putCore]
    rw [show (coreState s).data.disk = (fun a => s.disk (.inr (.inl a))) from rfl,
      installCore_update]
    try rfl

theorem resolve_none (s t : State L R B b d w) (h : t = {s with disk := t.disk}) :
    resolve s t .none = (s, 0) := by
  rw [h]; rfl

theorem micro_spec (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ) (z : Disk R B w) :
    micro p s r =
      ((resolve s (micro p {s with disk := z} r).1 (microAct p s r)).1,
       (micro p {s with disk := z} r).2.1,
       (resolve s (micro p {s with disk := z} r).1 (microAct p s r)).2) := by
  have hE := expandMicro_spec p s z
  have hC := compactMicro_spec p s z
  have hK := coreMicro_spec p s z
  have hin : inputSize {s with disk := z} = inputSize s := rfl
  have hout : outputSize {s with disk := z} = outputSize s := rfl
  unfold micro microAct
  simp only [hin, hout]
  by_cases hr : r = 0
  · simp only [hr, if_true]
    generalize hk : s.stage.val = k
    rcases k with _ | _ | _ | k
    · by_cases hc : decodeWords s.counter < inputSize s
      · simp only [hc, if_true]; rw [hE]
      · simp only [hc, if_false]; rfl
    · by_cases hc : p.policy s.ram = none
      · simp only [hc, if_true]; rfl
      · simp only [hc, if_false]; rw [hK]
    · by_cases hc : decodeWords s.counter < outputSize s
      · simp only [hc, if_true]; rw [hC]
      · simp only [hc, if_false]; rfl
    · rfl
  · simp only [hr, if_false]
    generalize hk : s.stage.val = k
    rcases k with _ | _ | _ | k
    · rw [hE]; try rfl
    · rw [hK]; try rfl
    · rw [hC]; try rfl
    · rfl

theorem map_write {α β : Type} (f : α → β) (act : BAct α) (a : β)
    (h : act.map f = .write a) : ∃ x, act = .write x := by
  cases act <;> simp_all [BAct.map]

theorem micro_write_buffer (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ)
    (a : Address R) (h : microAct p s r = .write a) : (micro p s r).1.buffer = s.buffer := by
  have hE : ∀ a, expandAct p s = .write a → (expandMicro p s).1.buffer = s.buffer := by
    intro a ha
    obtain ⟨x, hx⟩ := map_write _ _ _ ha
    exact layout_write_buffer _ _ x hx
  have hC : ∀ a, compactAct' p s = .write a → (compactMicro p s).1.buffer = s.buffer := by
    intro a ha
    obtain ⟨x, hx⟩ := map_write _ _ _ ha
    exact compact_write_buffer _ _ x hx
  have hK : ∀ a, coreAct' p s = .write a → (coreMicro p s).1.buffer = s.buffer := by
    intro a ha
    obtain ⟨x, hx⟩ := map_write _ _ _ ha
    exact core_write_buffer _ _ _ _ _ x hx
  unfold micro
  unfold microAct at h
  by_cases hr : r = 0
  · simp only [hr, if_true] at h ⊢
    generalize hk : s.stage.val = k at h ⊢
    rcases k with _ | _ | _ | k
    · by_cases hc : decodeWords s.counter < inputSize s
      · simp only [hc, if_true] at h ⊢; exact hE a h
      · simp [hc] at h
    · by_cases hc : p.policy s.ram = none
      · simp [hc] at h
      · simp only [hc, if_false] at h ⊢; exact hK a h
    · by_cases hc : decodeWords s.counter < outputSize s
      · simp only [hc, if_true] at h ⊢; exact hC a h
      · simp [hc] at h
    · simp at h
  · simp only [hr, if_false] at h ⊢
    generalize hk : s.stage.val = k at h ⊢
    rcases k with _ | _ | _ | k
    · exact hE a h
    · exact hK a h
    · exact hC a h
    · simp at h

/-! Iterating micro-steps. -/

/-- `n` micro-steps from `(s, r)`: final state, final counter, total cost. -/
def iter (p : Program L R B b d w) : ℕ → State L R B b d w → ℕ → State L R B b d w × ℕ × ℕ
  | 0, s, r => (s, r, 0)
  | n + 1, s, r =>
      let m := micro p s r
      let rest := iter p n m.1 m.2.1
      (rest.1, rest.2.1, m.2.2 + rest.2.2)

theorem iter_succ (p : Program L R B b d w) (n : ℕ) (s : State L R B b d w) (r : ℕ) :
    iter p (n + 1) s r =
      ((iter p n (micro p s r).1 (micro p s r).2.1).1,
       (iter p n (micro p s r).1 (micro p s r).2.1).2.1,
       (micro p s r).2.2 + (iter p n (micro p s r).1 (micro p s r).2.1).2.2) := rfl

theorem iter_add (p : Program L R B b d w) (n m : ℕ) (s : State L R B b d w) (r : ℕ) :
    iter p (n + m) s r =
      let x := iter p n s r
      let y := iter p m x.1 x.2.1
      (y.1, y.2.1, x.2.2 + y.2.2) := by
  induction n generalizing s r with
  | zero => simp [iter]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [iter, ih, Nat.add_assoc]

theorem expand_stage (p : Program L R B b d w) (t : State L R B b d w) :
    (expandMicro p t).1.stage = t.stage := rfl
theorem compact_stage (p : Program L R B b d w) (t : State L R B b d w) :
    (compactMicro p t).1.stage = t.stage := rfl
theorem core_stage (p : Program L R B b d w) (t : State L R B b d w) :
    (coreMicro p t).1.stage = t.stage := rfl

theorem expand_iter (p : Program L R B b d w) (k : ℕ) (t : State L R B b d w)
    (h : t.stage.val = 0) :
    iter p k t k = ((microRun (expandMicro p) k t).1, 0, (microRun (expandMicro p) k t).2) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    have hm : micro p t (k + 1) = ((expandMicro p t).1, k, (expandMicro p t).2) := by
      simp only [micro, Nat.succ_ne_zero, if_false, h]
      rfl
    simp only [iter, hm]
    rw [ih _ (by rw [expand_stage]; exact h)]
    rfl

theorem compact_iter (p : Program L R B b d w) (k : ℕ) (t : State L R B b d w)
    (h : t.stage.val = 2) :
    iter p k t k = ((microRun (compactMicro p) k t).1, 0, (microRun (compactMicro p) k t).2) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    have hm : micro p t (k + 1) = ((compactMicro p t).1, k, (compactMicro p t).2) := by
      simp only [micro, Nat.succ_ne_zero, if_false, h]
      rfl
    simp only [iter, hm]
    rw [ih _ (by rw [compact_stage]; exact h)]
    rfl

theorem core_iter (p : Program L R B b d w) (k : ℕ) (t : State L R B b d w)
    (h : t.stage.val = 1) :
    iter p k t k = ((microRun (coreMicro p) k t).1, 0, (microRun (coreMicro p) k t).2) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    have hm : micro p t (k + 1) = ((coreMicro p t).1, k, (coreMicro p t).2) := by
      simp only [micro, Nat.succ_ne_zero, if_false, h]
      rfl
    simp only [iter, hm]
    rw [ih _ (by rw [core_stage]; exact h)]
    rfl

/-- One observation of the controller is a finite run of micro-steps from counter `0` back
to counter `0`. -/
theorem step_iter (p : Program L R B b d w) (s : State L R B b d w) :
    ∃ k, iter p k s 0 = ((step p s).1, 0, (step p s).2) := by
  generalize hk : s.stage.val = k
  rcases k with _ | _ | _ | k
  · by_cases hc : decodeWords s.counter < inputSize s
    · refine ⟨7, ?_⟩
      have hm : micro p s 0 = ((expandMicro p s).1, 6, (expandMicro p s).2) := by
        simp only [micro, if_true, hk, hc]
      have hstep : step p s = microRun (expandMicro p) 7 s := by
        rw [expand_microsteps]
        simp only [step, hk, hc, if_true]
      rw [iter_succ, hm]
      simp only
      rw [expand_iter p 6 _ (by rw [expand_stage]; exact hk), hstep]
      rfl
    · refine ⟨1, ?_⟩
      simp only [iter, micro, if_true, hk, hc, if_false, step]
      rfl
  · by_cases hc : p.policy s.ram = none
    · refine ⟨1, ?_⟩
      simp only [iter, micro, if_true, hk, hc, step]
      rfl
    · refine ⟨2, ?_⟩
      have hm : micro p s 0 = ((coreMicro p s).1, 1, (coreMicro p s).2) := by
        simp only [micro, if_true, hk, hc, if_false]
      have hstep : step p s = microRun (coreMicro p) 2 s := by
        rw [core_microsteps]
        simp only [step, hk, hc, if_false]
      rw [iter_succ, hm]
      simp only
      rw [core_iter p 1 _ (by rw [core_stage]; exact hk), hstep]
      rfl
  · by_cases hc : decodeWords s.counter < outputSize s
    · refine ⟨8, ?_⟩
      have hm : micro p s 0 = ((compactMicro p s).1, 7, (compactMicro p s).2) := by
        simp only [micro, if_true, hk, hc]
      have hstep : step p s = microRun (compactMicro p) 8 s := by
        rw [compact_microsteps]
        simp only [step, hk, hc, if_true]
      rw [iter_succ, hm]
      simp only
      rw [compact_iter p 7 _ (by rw [compact_stage]; exact hk), hstep]
      rfl
    · refine ⟨1, ?_⟩
      simp only [iter, micro, if_true, hk, hc, if_false, step]
      try rfl
  · refine ⟨1, ?_⟩
    simp only [iter, micro, if_true, hk, step]
    try rfl

theorem run_iter (p : Program L R B b d w) (n : ℕ) (s : State L R B b d w) :
    ∃ k, iter p k s 0 = ((run p n s).1, 0, (run p n s).2) := by
  induction n generalizing s with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨k1, h1⟩ := step_iter p s
    obtain ⟨k2, h2⟩ := ih (step p s).1
    refine ⟨k1 + k2, ?_⟩
    rw [iter_add]
    simp only [h1, h2, run]

/-! Shape of the block actions. -/

theorem layoutAct_write (lp : PhysicalNormalizationLayout.Program R B b d w)
    (t : PhysicalNormalizationLayout.State R B b d w) (a : PhysicalNormalizationLayout.Address R)
    (h : layoutAct lp t = .write a) : ∃ x, a = .inr x := by
  unfold layoutAct at h
  split_ifs at h
  generalize t.phase.val = k at h
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    first | (simp at h; done) | (simp only [BAct.write.injEq] at h; exact ⟨_, h.symm⟩)

theorem compactAct_write (lp : PhysicalNormalizationLayout.Program R B b d w)
    (t : PhysicalNormalizationLayout.State R B b d w) (a : PhysicalNormalizationLayout.Address R)
    (h : compactAct lp t = .write a) : ∃ x, a = .inr x := by
  unfold compactAct at h
  split_ifs at h
  generalize t.phase.val = k at h
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
    first | (simp at h; done) | (simp only [BAct.write.injEq] at h; exact ⟨_, h.symm⟩)

theorem microAct_cases (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ) :
    microAct p s r = .none ∨
    (s.stage.val = 0 ∧ microAct p s r = expandAct p s) ∨
    (s.stage.val = 1 ∧ microAct p s r = coreAct' p s) ∨
    (s.stage.val = 2 ∧ microAct p s r = compactAct' p s) := by
  unfold microAct
  by_cases hr : r = 0
  · simp only [hr, if_true]
    generalize hk : s.stage.val = k
    rcases k with _ | _ | _ | k
    · by_cases hc : decodeWords s.counter < inputSize s <;> simp [hc]
    · by_cases hc : p.policy s.ram = none <;> simp [hc]
    · by_cases hc : decodeWords s.counter < outputSize s <;> simp [hc]
    · simp
  · simp only [hr, if_false]
    generalize hk : s.stage.val = k
    rcases k with _ | _ | _ | k <;> simp

theorem microAct_read_inl (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ)
    (x : Fin R) (h : microAct p s r = .read (.inl x)) : s.stage.val = 0 := by
  rcases microAct_cases p s r with h0 | ⟨hs, he⟩ | ⟨hs, he⟩ | ⟨hs, he⟩
  · rw [h0] at h; cases h
  · exact hs
  · rw [he] at h; unfold coreAct' at h
    cases hc : coreAct (⟨p.policy⟩ : FixedPolicyNormalization.Program L b R w) (coreState s) <;>
      simp [hc, BAct.map, coreAddr] at h
  · rw [he] at h; unfold compactAct' at h
    cases hc : compactAct (outputProgram p s) (compactState s) with
    | none => simp [hc, BAct.map] at h
    | read y => rcases y with y | y <;> simp [hc, BAct.map, cmpAddr] at h
    | write y => simp [hc, BAct.map] at h

theorem microAct_write_shape (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ)
    (a : Address R) (h : microAct p s r = .write a) :
    (∃ x, a = .inr (.inl x)) ∨ (s.stage.val = 2 ∧ ∃ x, a = .inr (.inr x)) := by
  rcases microAct_cases p s r with h0 | ⟨hs, he⟩ | ⟨hs, he⟩ | ⟨hs, he⟩
  · rw [h0] at h; cases h
  · rw [he] at h; unfold expandAct at h
    cases hc : layoutAct (inputProgram p s) (expandState s) with
    | none => simp [hc, BAct.map] at h
    | read y => simp [hc, BAct.map] at h
    | write y =>
      obtain ⟨x, rfl⟩ := layoutAct_write _ _ _ hc
      simp [hc, BAct.map, expAddr] at h
      exact Or.inl ⟨x, h.symm⟩
  · rw [he] at h; unfold coreAct' at h
    cases hc : coreAct (⟨p.policy⟩ : FixedPolicyNormalization.Program L b R w) (coreState s) with
    | none => simp [hc, BAct.map] at h
    | read y => simp [hc, BAct.map] at h
    | write y => simp [hc, BAct.map, coreAddr] at h; exact Or.inl ⟨y, h.symm⟩
  · rw [he] at h; unfold compactAct' at h
    cases hc : compactAct (outputProgram p s) (compactState s) with
    | none => simp [hc, BAct.map] at h
    | read y => simp [hc, BAct.map] at h
    | write y =>
      obtain ⟨x, rfl⟩ := compactAct_write _ _ _ hc
      simp [hc, BAct.map, cmpAddr] at h
      exact Or.inr ⟨hs, x, h.symm⟩

theorem microAct_disk (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ)
    (z : Disk R B w) : microAct p {s with disk := z} r = microAct p s r := rfl

theorem micro_rem (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ) (hr : r ≤ 7) :
    (micro p s r).2.1 ≤ 7 := by
  unfold micro
  by_cases h0 : r = 0
  · simp only [h0, if_true]
    generalize s.stage.val = k
    rcases k with _ | _ | _ | k
    · split_ifs <;> simp
    · split_ifs <;> simp
    · split_ifs <;> simp
    · simp
  · simp only [h0, if_false]
    generalize s.stage.val = k
    rcases k with _ | _ | _ | k <;> simp <;> omega

theorem micro_stage_mono (p : Program L R B b d w) (s : State L R B b d w) (r : ℕ) :
    s.stage.val ≤ (micro p s r).1.stage.val := by
  unfold micro
  by_cases h0 : r = 0
  · simp only [h0, if_true]
    rcases hk : s.stage.val with _ | _ | _ | k
    · exact Nat.zero_le _
    · simp only
      split_ifs
      · simp [enterCompact, code]
      · rw [core_stage, hk]
    · simp only
      split_ifs
      · rw [compact_stage, hk]
      · simp [code]
    · simp only; rw [hk]
  · simp only [h0, if_false]
    rcases hk : s.stage.val with _ | _ | _ | k
    · exact Nat.zero_le _
    · simp only; rw [core_stage, hk]
    · simp only; rw [compact_stage, hk]
    · simp only; rw [hk]

end CSLB.ControllerMicro


