-- Prove2me | Definitions.Def_BitDFT_UnaryAdvance
-- name    : BitDFT_UnaryAdvance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T23:30:33.535994+00:00
-- url     : https://prove2.me/theorems/47ee96c6-b2fe-43c9-bab3-03d1c7aaed62
-- title:
--   Unary-controlled head positioning machine
-- statement:
--   A finite-state controller positions a source head by scanning a separate tape containing a unary count. It moves the source head and the count head right together for each one, then halts on the first non-one symbol. All tape symbols are preserved, and every other head stays fixed.
-- source:
--   A tape-level positioning stage for the output-scaling wrapper in the finite-precision Fourier transfer construction.

import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.UnaryAdvance
open IntMul BitDFT.MachineSequence

/-- Walk a source head to the right once per unary one on a separate counter tape.
    The count tape and source tape are read-only during this positioning phase. -/
def transition (N : MultitapeTM) (source counter : Fin N.k)
    (q : Bool) (a : Fin N.k → N.Sym) : Bool × (Fin N.k → N.Sym × Move) := by
  classical
  exact if q then (true, fun i => (a i, .stay)) else
    if a counter = N.one then
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
        by_cases hone : a counter = N.one
        · simp only [if_pos hone, Prod.fst, Prod.snd]
          constructor
          · exact hi
          · by_cases hm : i = source ∨ i = counter <;> simp [hm]
        · simp only [if_neg hone, Prod.fst, Prod.snd]
          exact ⟨hi, by simp⟩
      · simp [transition, hi]
    noMarker := by
      intro q a i hi
      cases q
      · by_cases hone : a counter = N.one <;> simp [transition, hone, hi]
      · simp [transition, hi]
    frozen := by
      intro a
      rfl
    readonly := by
      intro q a
      cases q
      · by_cases hone : a counter = N.one <;> simp [transition, hone]
      · simp [transition] }

abbrev machine (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) := (control N source counter hsc).machine

def frame (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (q : Bool) (sourceHead counterHead : ℕ) :
    (machine N source counter hsc).Cfg :=
  ⟨q, base.cells,
    Function.update (Function.update base.head source sourceHead) counter counterHead⟩

end BitDFT.UnaryAdvance


