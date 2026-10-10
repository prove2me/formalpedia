-- Prove2me | Definitions.Def_IntMul_TrackedReentrantCall
-- name    : IntMul_TrackedReentrantCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:38:17.523042+00:00
-- url     : https://prove2.me/theorems/4da1149a-0df0-487f-8768-6ba1984a60e1
-- title:
--   Shared-tape physical child caller with fresh-suffix reservation and exact parent restoration
-- statement:
--   For a finite child machine with k work tapes, one finite caller uses k+2 tapes and the common tagged alphabet throughout fresh-suffix reservation, child preparation, tracked execution, output return, complete child cleanup and restoration of parent heads. Its state set combines the three finite phase controls, with two explicit outer dispatch transitions. The parent's visited flags physically locate each first fresh suffix; child cleanup erases every child marker; retained parent markers then physically stop independent rewinds. No offset, extent or clock enters the transition table. Initial and final proof frames describe exact bank cells, flags, caller buffers and heads. Caller input must already have been physically produced; arbitrary input generation and an unbounded recursive scheduler are separate requirements.
-- source:
--   Original complete physical reusable child call for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankReservation
import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedParentRestore

namespace IntMul.TrackedReentrantCall

open IntMul.TrackedBankedSimulation (Sym)

/-- Physical fresh-bank reservation, complete tracked child calling and parent
head restoration share one fixed finite alphabet and the same M.k+2 tapes. -/
abbrev State (M : MultitapeTM) := TrackedBankReservation.State ⊕ (TrackedBankedCall.State M ⊕ TrackedParentRestore.State)

noncomputable def transition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Sym M) : State M × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .inl q =>
      if q = .halt then (.inr (.inl (.inl .mark)),fun i => (a i,.stay)) else
        let r := TrackedBankReservation.transition M q a
        (.inl r.1,r.2)
  | .inr (.inl q) =>
      if q = (TrackedBankedCall.machine M).qHalt then (.inr (.inr .rewind),fun i => (a i,.stay)) else
        let r := TrackedBankedCall.transition M q a
        (.inr (.inl r.1),r.2)
  | .inr (.inr q) =>
      let r := TrackedParentRestore.transition M q a
      (.inr (.inr r.1),r.2)

/-- One fixed interior caller reserves fresh suffixes, prepares and runs the
child, returns its output, clears child banks and restores parent heads. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State M
  qStart := .inl .seek
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
        · simpa [transition,h] using (TrackedBankReservation.machine M).start_preserved q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (TrackedBankedCall.machine M).qHalt
            · simp [transition,h,hi]
            · simpa [transition,h] using (TrackedBankedCall.machine M).start_preserved q a i hi
        | inr q =>
            simpa only [transition] using (TrackedParentRestore.machine M).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simpa [transition,h] using hi
        · simpa [transition,h] using (TrackedBankReservation.machine M).start_only_at_start q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (TrackedBankedCall.machine M).qHalt
            · simpa [transition,h] using hi
            · simpa [transition,h] using (TrackedBankedCall.machine M).start_only_at_start q a i hi
        | inr q =>
            simpa only [transition] using (TrackedParentRestore.machine M).start_only_at_start q a i hi
  halt_fixed := by
    intro a
    have h := (TrackedParentRestore.machine M).halt_fixed a
    change TrackedParentRestore.transition M .halt a = (.halt,fun i => (a i,.stay)) at h
    simp only [transition,h]
  input_readonly := by
    classical
    intro q a
    cases q with
    | inl q =>
        by_cases h : q = .halt
        · simp [transition,h]
        · simpa [transition,h] using (TrackedBankReservation.machine M).input_readonly q a
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = (TrackedBankedCall.machine M).qHalt
            · simp [transition,h]
            · simpa [transition,h] using (TrackedBankedCall.machine M).input_readonly q a
        | inr q =>
            simpa only [transition] using (TrackedParentRestore.machine M).input_readonly q a

noncomputable def liftReservation (M : MultitapeTM) (c : (TrackedBankReservation.machine M).Cfg) : (machine M).Cfg where
  state := .inl c.state
  cells := c.cells
  head := c.head

noncomputable def liftCall (M : MultitapeTM) (c : (TrackedBankedCall.machine M).Cfg) : (machine M).Cfg where
  state := .inr (.inl c.state)
  cells := c.cells
  head := c.head

noncomputable def liftRestore (M : MultitapeTM) (c : (TrackedParentRestore.machine M).Cfg) : (machine M).Cfg where
  state := .inr (.inr c.state)
  cells := c.cells
  head := c.head

noncomputable def reservationBase (M : MultitapeTM) (base : (machine M).Cfg) :
    (TrackedBankReservation.machine M).Cfg where
  state := .seek
  cells := base.cells
  head := base.head

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) : (machine M).Cfg :=
  liftReservation M (TrackedBankReservation.initialFrame M (reservationBase M base) offset extent c)

noncomputable def callBase (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) : (TrackedBankedCall.machine M).Cfg where
  state := .inl .mark
  cells := (TrackedBankReservation.finalFrame M (reservationBase M base) offset extent c).cells
  head := (TrackedBankReservation.finalFrame M (reservationBase M base) offset extent c).head

noncomputable def childFinal (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (x y : List Bool) (T : ℕ) (w : List Bool) : (TrackedBankedCall.machine M).Cfg :=
  TrackedBankedCall.finalFrame M (callBase M base offset extent c) sigma
    (TrackedBankReservation.newOffsets M offset extent)
    (TrackedBankedSimulation.extents M (M.initCfg x y) (TrackedBankPreparation.initialExtent M x y) T)
    (M.step^[T] (M.initCfg x y)) w

noncomputable def restoreBase (M : MultitapeTM) (d : (TrackedBankedCall.machine M).Cfg) :
    (TrackedParentRestore.machine M).Cfg where
  state := .rewind
  cells := d.cells
  head := d.head

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (x y : List Bool) (T : ℕ) (w : List Bool) : (machine M).Cfg :=
  liftRestore M (TrackedParentRestore.finalFrame M
    (restoreBase M (childFinal M base sigma offset extent c x y T w)) offset extent c)

end IntMul.TrackedReentrantCall


