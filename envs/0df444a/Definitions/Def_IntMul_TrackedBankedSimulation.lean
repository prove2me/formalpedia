-- Prove2me | Definitions.Def_IntMul_TrackedBankedSimulation
-- name    : IntMul_TrackedBankedSimulation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T21:54:21.137063+00:00
-- url     : https://prove2.me/theorems/b92db41b-540a-45b5-88ce-1336cf73a401
-- title:
--   Literal work-bank simulator with zero-step-overhead visited-prefix tracking
-- statement:
--   For each finite child machine M, defines a fixed M.k+2-tape simulator over the finite alphabet Option(M.Sym×Bool). The outer global marker is none; child symbols carry one finite visited flag. Every nonhalting child transition performs its ordinary write while marking the currently scanned bank cell true, at no additional transition cost. The halted state freezes all cells and flags. Root input and caller buffer are frozen. Prepared bank offsets and extents appear only in proof-side embeddings/history, absent from the transition table. A head is at most one cell beyond its visited extent, and unit moves maintain a contiguous flagged prefix. This supplies a physical stopping boundary for separately charged workspace clearing; setup, output copy before clearing and cleanup are separate proof obligations.
-- source:
--   Original finite visited-workspace instrumentation for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_BankedSimulation

namespace IntMul.TrackedBankedSimulation

open IntMul.BankedSimulation (workTape innerTape)

/-- The finite visited bit marks the contiguous bank prefix actually touched
by the child. False-tagged blank cells form the unused suffix. -/
abbrev Sym (M : MultitapeTM) := Option (M.Sym × Bool)

def decode (M : MultitapeTM) : Sym M → M.Sym
  | none => M.startSym
  | some s => s.1

/-- Mark the currently scanned work cell while executing its ordinary child
write. This adds no transition. The global outer marker remains protected. -/
def protect (M : MultitapeTM) (old : Sym M) (write : M.Sym) (move : Move) : Sym M × Move :=
  match old with
  | none => (none,match move with | .left => .stay | other => other)
  | some _ => (some (write,true),move)

noncomputable def transition (M : MultitapeTM) (q : M.K) (a : Fin (M.k + 2) → Sym M) :
    M.K × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact if q = M.qHalt then (q,fun i => (a i,.stay)) else
    let r := M.δ q (fun j => decode M (a (workTape M j)))
    (r.1,fun i => if h : 2 ≤ i.val then
      protect M (a i) (r.2 (innerTape M i h)).1 (r.2 (innerTape M i h)).2
      else (a i,.stay))

/-- One fixed finite child simulator with a visited bit in its alphabet.
Root input and caller buffer are frozen. No bounds or addresses enter delta. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := by
    classical
    have hd := M.syms_distinct
    simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at hd
    simp_all
  K := M.K
  qStart := M.qStart
  qHalt := M.qHalt
  start_ne_halt := M.start_ne_halt
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    by_cases hq : q = M.qHalt
    · simp [transition,hq,hi]
    · simp only [transition,if_neg hq]
      split
      · rw [hi]
        simp only [protect]
        split <;> simp_all
      · simp [hi]
  start_only_at_start := by
    classical
    intro q a i hi
    by_cases hq : q = M.qHalt
    · simpa [transition,hq] using hi
    · simp only [transition,if_neg hq]
      split
      · cases hs : a i with
        | none => exact False.elim (hi hs)
        | some s => simp [protect]
      · exact hi
  halt_fixed := by intro a; simp [transition]
  input_readonly := by
    classical
    intro q a
    by_cases hq : q = M.qHalt
    · simp [transition,hq]
    · simp [transition,hq,MultitapeTM.inTape]

/-- Prepared tracked banks. Cells through the extent (including marker zero)
are visited; the next cell may be reached by a head but not yet scanned. -/
def embed (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) : (machine M).Cfg where
  state := c.state
  cells := fun i p => if h : 2 ≤ i.val then
    let j := innerTape M i h
    if p < offset j then base.cells i p
    else some (c.cells j (p - offset j),decide (p - offset j ≤ extent j))
    else base.cells i p
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) + c.head (innerTape M i h)
    else base.head i

/-- Proof-only high-water extent update, never an input to the finite table. -/
noncomputable def nextExtent (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) : Fin M.k → ℕ := by
  classical
  exact if c.state = M.qHalt then extent else fun j => max (extent j) (c.head j)

noncomputable def extents (M : MultitapeTM) (c : M.Cfg) (initial : Fin M.k → ℕ) : ℕ → Fin M.k → ℕ
  | 0 => initial
  | T + 1 => nextExtent M (M.step^[T] c) (extents M c initial T)

end IntMul.TrackedBankedSimulation


