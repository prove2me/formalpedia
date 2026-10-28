-- Prove2me | Definitions.Def_BitDFT_BitAdvance
-- name    : BitDFT_BitAdvance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T04:59:00.075827+00:00
-- url     : https://prove2.me/theorems/ec677e69-5b19-4a46-8ed9-6e50c4a4b221
-- title:
--   Advance across a run of binary symbols
-- statement:
--   A two-tape controller reads a designated counter tape and moves both its own head and a designated source head one cell right for each consecutive binary symbol (zero or one). At the first non-binary symbol it halts without moving either head. Both tapes are read-only.
-- source:
--   A finite-state head-positioning controller used to move across a stored binary word by its exact length, including a suffix of an operand after a separately positioned prefix.

import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.BitAdvance
open IntMul BitDFT.MachineSequence

/-- Move one cell for each binary data symbol on the counter tape; stop at its
    first non-bit symbol. Both tapes are read-only. -/
def transition (N : MultitapeTM) (source counter : Fin N.k)
    (q : Bool) (a : Fin N.k → N.Sym) : Bool × (Fin N.k → N.Sym × Move) := by
  classical
  exact if q then (true, fun i => (a i, .stay)) else
    if a counter = N.zero ∨ a counter = N.one then
      (false, fun i => (a i, if i = source ∨ i = counter then .right else .stay))
    else (true, fun i => (a i, .stay))

def control (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) : Controller N := by
  classical
  exact {
    K := Bool
    entry := false
    exit := true
    distinct := by decide
    transition := transition N source counter
    marker := by
      intro q a i hi
      cases q
      · simp only [transition, Bool.false_eq_true, if_false]
        by_cases hbit : a counter = N.zero ∨ a counter = N.one
        · simp only [if_pos hbit, Prod.fst, Prod.snd]
          constructor
          · exact hi
          · by_cases hm : i = source ∨ i = counter <;> simp [hm]
        · simp only [if_neg hbit, Prod.fst, Prod.snd]
          exact ⟨hi, by simp⟩
      · simp [transition, hi]
    noMarker := by
      intro q a i hi
      cases q
      · by_cases hbit : a counter = N.zero ∨ a counter = N.one <;> simp [transition, hbit, hi]
      · simp [transition, hi]
    frozen := by intro a; rfl
    readonly := by
      intro q a
      cases q
      · by_cases hbit : a counter = N.zero ∨ a counter = N.one <;> simp [transition, hbit]
      · simp [transition] }

abbrev machine (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) := (control N source counter hsc).machine

def frame (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (q : Bool) (sourceHead counterHead : ℕ) :
    (machine N source counter hsc).Cfg :=
  ⟨q, base.cells,
    Function.update (Function.update base.head source sourceHead) counter counterHead⟩

end BitDFT.BitAdvance


