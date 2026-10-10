-- Prove2me | Definitions.Def_IntMul_TrackedReturnReplacement
-- name    : IntMul_TrackedReturnReplacement
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T01:21:07.321289+00:00
-- url     : https://prove2.me/theorems/0e134b47-0424-462d-a450-c2e0687d4292
-- title:
--   Physical result-buffer replacement retaining its marker and erasing old tails
-- statement:
--   A fixed finite shared-tape service physically copies the current output-bank bit word into a caller buffer that may already contain a longer earlier result. It erases every excess old visited buffer cell, physically restores both local boundaries, restores the buffer return marker, and physically seeks the first fresh cell after the new result. The full source bank, all visited flags, all other banks and their heads remain exact. Empty and shorter returned words are allowed. The alphabet and k+2 tapes are fixed, and no word length or address enters delta. This discharges the empty-buffer assumption that would otherwise fail after nested calls.
-- source:
--   Original recursive result-buffer replacement for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedWordInputBridge

namespace IntMul.TrackedReturnReplacement

open IntMul.TrackedBankedSimulation (Sym)

abbrev State := TrackedWordInputBridge.State ⊕ Bool
abbrev bufferTape (M : MultitapeTM) := TrackedWordInputBridge.bufferTape M

def bitWord (M : MultitapeTM) (w : List Bool) : TrackedWordInputBridge.ValidWord M :=
  ⟨w.map M.bitSym,by
    intro a ha
    rcases List.mem_map.mp ha with ⟨b,_,rfl⟩
    cases b <;> simp [MultitapeTM.bitSym]⟩

noncomputable def sealActions (M : MultitapeTM) (a : Fin (M.k+2) → Sym M) : Fin (M.k+2) → Sym M × Move := by
  classical
  exact fun i => TrackedBankCleanup.protect M (a i)
    (if i=bufferTape M then some (M.startSym,true) else a i)
    (if i=bufferTape M then .right else .stay)

noncomputable def seekActions (M : MultitapeTM) (a : Fin (M.k+2) → Sym M) : Fin (M.k+2) → Sym M × Move := by
  classical
  exact fun i => (a i,if i=bufferTape M then .right else .stay)

noncomputable def transition (M : MultitapeTM) (q : State) (a : Fin (M.k+2) → Sym M) :
    State × (Fin (M.k+2) → Sym M × Move) := by
  classical
  exact match q with
  | .inl s =>
    if s=(TrackedWordInputBridge.machine M).qHalt then (.inr false,sealActions M a)
    else let r := TrackedWordInputBridge.transition M s a; (.inl r.1,r.2)
  | .inr false =>
    if TrackedBankCleanup.visited M (a (bufferTape M))=true then (.inr false,seekActions M a)
    else (.inr true,fun i => (a i,.stay))
  | .inr true => (.inr true,fun i => (a i,.stay))

private theorem transition_actions (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (P : (Fin (M.k+2) → Sym M × Move) → Prop)
    (stay : P (fun i => (a i,.stay))) (hseal : P (sealActions M a)) (seek : P (seekActions M a))
    (input : ∀ s, P (TrackedWordInputBridge.transition M s a).2) (q : State) :
    P (transition M q a).2 := by
  classical
  cases q with
  | inl s =>
    by_cases h : s=(TrackedWordInputBridge.machine M).qHalt
    · simpa only [transition,if_pos h] using hseal
    · simpa only [transition,if_neg h] using input s
  | inr b =>
    cases b
    · by_cases h : TrackedBankCleanup.visited M (a (bufferTape M))=true
      · simpa only [transition,if_pos h] using seek
      · simpa only [transition,if_neg h] using stay
    · simpa only [transition] using stay

/-- Replace any older returned buffer word with the actual physical output
bank word, erase its excess visited tail, retain a return marker, and seek
the first fresh cell after the replacement. No lengths occur in delta. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State
  qStart := .inl .before
  qHalt := .inr true
  start_ne_halt := by simp
  k := M.k+2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    apply transition_actions M a (fun r => (r i).1=none ∧ (r i).2≠.left)
    · simp [hi]
    · simp only [sealActions,hi,TrackedBankCleanup.protect]
      split_ifs <;> simp
    · simp only [seekActions,hi]
      split_ifs <;> simp
    · intro s; exact (TrackedWordInputBridge.machine M).start_preserved s a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    apply transition_actions M a (fun r => (r i).1≠none)
    · exact hi
    · cases h : a i with
      | none => exact False.elim (hi h)
      | some s => simp only [sealActions,h]; split_ifs <;> simp [TrackedBankCleanup.protect]
    · simpa only [seekActions] using hi
    · intro s; exact (TrackedWordInputBridge.machine M).start_only_at_start s a i hi
  halt_fixed := by intro a; rfl
  input_readonly := by
    classical
    intro q a
    apply transition_actions M a (fun r => (r ⟨0,by omega⟩).1=a ⟨0,by omega⟩)
    · rfl
    · have h : (⟨0,by omega⟩ : Fin (M.k+2))≠bufferTape M := by
        intro h
        have h := congrArg Fin.val h
        simp [bufferTape,TrackedWordInputBridge.bufferTape] at h
      simp only [sealActions,if_neg h]
      cases a ⟨0,by omega⟩ <;> rfl
    · rfl
    · intro s; exact (TrackedWordInputBridge.machine M).input_readonly s a

noncomputable def inputBase (M : MultitapeTM) (base : (machine M).Cfg) : (TrackedWordInputBridge.machine M).Cfg where
  state := .before
  cells := base.cells
  head := base.head

noncomputable def liftInput (M : MultitapeTM) (c : (TrackedWordInputBridge.machine M).Cfg) : (machine M).Cfg where
  state := .inl c.state
  cells := c.cells
  head := c.head

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (machine M).Cfg :=
  liftInput M (TrackedWordInputBridge.initialFrame M (inputBase M base) sigma offset extent c v)

noncomputable def seekFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .inr false
  cells := fun i => if i=bufferTape M then TrackedOutputReturn.bufferTape M (base.cells i) sigma w
    else (TrackedWordInputBridge.finalFrame M (inputBase M base) sigma offset extent c v (bitWord M w)).cells i
  head := fun i => if i=bufferTape M then sigma+j+1
    else (TrackedWordInputBridge.finalFrame M (inputBase M base) sigma offset extent c v (bitWord M w)).head i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (machine M).Cfg where
  state := .inr true
  cells := (seekFrame M base sigma offset extent c v w w.length).cells
  head := (seekFrame M base sigma offset extent c v w w.length).head

end IntMul.TrackedReturnReplacement


