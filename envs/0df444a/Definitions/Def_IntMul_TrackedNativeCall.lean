-- Prove2me | Definitions.Def_IntMul_TrackedNativeCall
-- name    : IntMul_TrackedNativeCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:11:48.153883+00:00
-- url     : https://prove2.me/theorems/9d61ae8c-7549-444b-b9ed-47d2638296a5
-- title:
--   Complete native fixed-tape child caller with physical input production and fresh-bank output return
-- statement:
--   For any finite child M, one fixed machine over Option(M.Sym×Bool) with exactly M.k+2 tapes combines five-state real native input copying, complete tracked bank preparation/execution/output/cleanup, and seven-state physical native output placement. All phases share the same alphabet and tape set; the finite sum contains M.K plus twenty-three extra states. Both outer stage switches are actual transitions, with the inner switches already charged. It starts from ordinary native initCfg x y, preserves root input, physically produces and erases the mutable child input, runs the child, returns its output and clears every child suffix and marker, then shifts the returned bits to native output position and erases the final duplicate. The final native output is canonical and every work bank is fresh and parked at one. No prepared input, infinite control, address, workspace bound or oracle enters delta. This is a one-level child compiler; an unbounded fixed-tape recursive scheduler remains separate.
-- source:
--   Original complete physical native caller and fresh-bank return compiler for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedRootInputCopy
import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift

namespace IntMul.TrackedNativeCall

open IntMul.TrackedBankedSimulation (Sym)

/-- Native input copying, complete tracked child calling and native output
placement share one fixed finite alphabet and the same M.k+2 tapes. -/
abbrev State (M : MultitapeTM) := TrackedRootInputCopy.State ⊕ (TrackedBankedCall.State M ⊕ TrackedOutputShift.State)

noncomputable def transition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Sym M) : State M × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .inl q =>
      if q = .halt then (.inr (.inl (.inl .mark)),fun i => (a i,.stay)) else
        let r := TrackedRootInputCopy.transition M q a
        (.inl r.1,r.2)
  | .inr (.inl q) =>
      if q = (TrackedBankedCall.machine M).qHalt then (.inr (.inr .rewind),fun i => (a i,.stay)) else
        let r := TrackedBankedCall.transition M q a
        (.inr (.inl r.1),r.2)
  | .inr (.inr q) =>
      let r := TrackedOutputShift.transition M q a
      (.inr (.inr r.1),r.2)

/-- One fixed native caller, starting from its actual initCfg and finishing
with native output and completely fresh child work banks. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State M
  qStart := .inl .start
  qHalt := .inr (.inr .halt)
  start_ne_halt := by simp
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simp [transition,h,hi]
        · simpa [transition,h] using (TrackedRootInputCopy.machine M).start_preserved q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (TrackedBankedCall.machine M).qHalt
            · simp [transition,h,hi]
            · simpa [transition,h] using (TrackedBankedCall.machine M).start_preserved q a i hi
        | inr q =>
            simpa only [transition] using (TrackedOutputShift.machine M).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simpa [transition,h] using hi
        · simpa [transition,h] using (TrackedRootInputCopy.machine M).start_only_at_start q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (TrackedBankedCall.machine M).qHalt
            · simpa [transition,h] using hi
            · simpa [transition,h] using (TrackedBankedCall.machine M).start_only_at_start q a i hi
        | inr q =>
            simpa only [transition] using (TrackedOutputShift.machine M).start_only_at_start q a i hi
  halt_fixed := by
    intro a
    have h := (TrackedOutputShift.machine M).halt_fixed a
    change TrackedOutputShift.transition M .halt a = (.halt,fun i => (a i,.stay)) at h
    simp only [transition,h]
  input_readonly := by
    classical
    intro q a
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simp [transition,h]
        · simpa [transition,h] using (TrackedRootInputCopy.machine M).input_readonly q a
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (TrackedBankedCall.machine M).qHalt
            · simp [transition,h]
            · simpa [transition,h] using (TrackedBankedCall.machine M).input_readonly q a
        | inr q =>
            simpa only [transition] using (TrackedOutputShift.machine M).input_readonly q a

noncomputable def liftRoot (M : MultitapeTM) (c : (TrackedRootInputCopy.machine M).Cfg) : (machine M).Cfg where
  state := .inl c.state
  cells := c.cells
  head := c.head

noncomputable def liftCall (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) : (machine M).Cfg where
  state := .inr (.inl c.state)
  cells := c.cells
  head := c.head

noncomputable def liftShift (M : MultitapeTM) (c : (TrackedOutputShift.machine M).Cfg) : (machine M).Cfg where
  state := .inr (.inr c.state)
  cells := c.cells
  head := c.head

noncomputable def callBase (M : MultitapeTM) (x y : List Bool) : (TrackedBankedCall.machine M).Cfg where
  state := .inl .mark
  cells := (TrackedRootInputCopy.finalFrame M x y).cells
  head := (TrackedRootInputCopy.finalFrame M x y).head

noncomputable def shiftBase (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) : (TrackedOutputShift.machine M).Cfg where
  state := .rewind
  cells := c.cells
  head := c.head

noncomputable def finalFrame (M : MultitapeTM) (x y : List Bool) (T : ℕ) (w : List Bool) : (machine M).Cfg :=
  liftShift M (TrackedOutputShift.finalFrame M
    (shiftBase M (TrackedBankedCall.finalFrame M (callBase M x y) 1 (fun _ => 1)
      (TrackedBankedSimulation.extents M (M.initCfg x y) (TrackedBankPreparation.initialExtent M x y) T)
      (M.step^[T] (M.initCfg x y)) w)) w)

end IntMul.TrackedNativeCall


