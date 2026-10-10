-- Prove2me | Definitions.Def_IntMul_TrackedReturnCall
-- name    : IntMul_TrackedReturnCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T22:28:38.301983+00:00
-- url     : https://prove2.me/theorems/4d5b0b33-8986-4134-8e94-df66ba2aa813
-- title:
--   One fixed child caller with tracked execution, output return and complete workspace cleanup
-- statement:
--   For each finite child machine M, one fixed machine with M.k+2 tapes, finite alphabet Option(M.Sym×Bool), and the finite sum of the child states, three output-return states and four workspace-cleanup states. A tracked child run dispatches at its first halt to the physical output-return program; that program dispatches at its first halt to physical workspace cleanup. Both stage switches take actual transitions and preserve complete cells/heads. The child output is copied into the caller buffer before cleanup clears every child bank suffix and local marker and parks its head at the same offset. Earlier caller prefixes and root input are retained. The table contains no bounds, offsets, head addresses or unbounded stack as primitive data. Prepared banks, buffer preparation and a complete recursive scheduler remain separate obligations.
-- source:
--   Original fixed-state-sum child/output/cleanup compiler for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedOutputReturn

namespace IntMul.TrackedReturnCall

open IntMul.TrackedBankedSimulation (Sym)

/-- The three programs share one finite alphabet and exactly the same tapes.
Their different control states are combined in one fixed finite sum. -/
abbrev State (M : MultitapeTM) := M.K ⊕ (TrackedOutputReturn.State ⊕ TrackedBankCleanup.State)

noncomputable def transition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Sym M) : State M × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .inl q =>
      if q = M.qHalt then (.inr (.inl .rewind),fun i => (a i,.stay)) else
        let r := TrackedBankedSimulation.transition M q a
        (.inl r.1,r.2)
  | .inr (.inl q) =>
      if q = .halt then (.inr (.inr .rewind),fun i => (a i,.stay)) else
        let r := TrackedOutputReturn.transition M q a
        (.inr (.inl r.1),r.2)
  | .inr (.inr q) =>
      let r := TrackedBankCleanup.transition M q a
      (.inr (.inr r.1),r.2)

/-- One fixed prepared-bank child caller: track the child, physically return
its output, then erase and restore all child banks for reuse. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State M
  qStart := .inl M.qStart
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
        by_cases h : q = M.qHalt
        · simp [transition,h,hi]
        · simpa [transition,h] using (TrackedBankedSimulation.machine M).start_preserved q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = .halt
            · simp [transition,h,hi]
            · simpa [transition,h] using (TrackedOutputReturn.machine M).start_preserved q a i hi
        | inr q =>
            simpa only [transition] using (TrackedBankCleanup.machine M).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        by_cases h : q = M.qHalt
        · simpa [transition,h] using hi
        · simpa [transition,h] using (TrackedBankedSimulation.machine M).start_only_at_start q a i hi
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = .halt
            · simpa [transition,h] using hi
            · simpa [transition,h] using (TrackedOutputReturn.machine M).start_only_at_start q a i hi
        | inr q =>
            simpa only [transition] using (TrackedBankCleanup.machine M).start_only_at_start q a i hi
  halt_fixed := by
    intro a
    have h := (TrackedBankCleanup.machine M).halt_fixed a
    change TrackedBankCleanup.transition M .halt a = (.halt,fun i => (a i,.stay)) at h
    simp only [transition,h]
  input_readonly := by
    classical
    intro q a
    cases q with
    | inl q =>
        by_cases h : q = M.qHalt
        · simp [transition,h]
        · simpa [transition,h] using (TrackedBankedSimulation.machine M).input_readonly q a
    | inr q =>
        cases q with
        | inl q =>
            by_cases h : q = .halt
            · simp [transition,h]
            · simpa [transition,h] using (TrackedOutputReturn.machine M).input_readonly q a
        | inr q =>
            simpa only [transition] using (TrackedBankCleanup.machine M).input_readonly q a

noncomputable def liftChild (M : MultitapeTM) (c : (TrackedBankedSimulation.machine M).Cfg) : (machine M).Cfg where
  state := .inl c.state
  cells := c.cells
  head := c.head

noncomputable def liftReturn (M : MultitapeTM) (c : (TrackedOutputReturn.machine M).Cfg) : (machine M).Cfg where
  state := .inr (.inl c.state)
  cells := c.cells
  head := c.head

noncomputable def liftCleanup (M : MultitapeTM) (c : (TrackedBankCleanup.machine M).Cfg) : (machine M).Cfg where
  state := .inr (.inr c.state)
  cells := c.cells
  head := c.head

noncomputable def returnBase (M : MultitapeTM) (base : (machine M).Cfg) : (TrackedOutputReturn.machine M).Cfg where
  state := .rewind
  cells := base.cells
  head := base.head

noncomputable def childBase (M : MultitapeTM) (base : (machine M).Cfg) (sigma a : ℕ) :
    (TrackedBankedSimulation.machine M).Cfg :=
  TrackedOutputReturn.callerBase M (returnBase M base) sigma a

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) : (machine M).Cfg :=
  liftChild M (TrackedBankedSimulation.embed M (childBase M base sigma a) offset extent c)

/-- Copying moves only the output work head; every other child head remains. -/
noncomputable def postCopyHeads (M : MultitapeTM) (c : M.Cfg) (w : List Bool) : Fin M.k → ℕ := by
  classical
  exact fun j => if j = M.outTape then w.length + 1 else c.head j

noncomputable def cleanupBase (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (TrackedBankCleanup.machine M).Cfg where
  state := .rewind
  cells := (TrackedOutputReturn.finalFrame M (returnBase M base) sigma offset extent c w).cells
  head := (TrackedOutputReturn.finalFrame M (returnBase M base) sigma offset extent c w).head

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) : (machine M).Cfg :=
  liftCleanup M (TrackedBankCleanup.finalFrame M (cleanupBase M base sigma offset extent c w) offset)

end IntMul.TrackedReturnCall


