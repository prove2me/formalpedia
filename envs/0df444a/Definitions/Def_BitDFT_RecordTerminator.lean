-- Prove2me | Definitions.Def_BitDFT_RecordTerminator
-- name    : BitDFT_RecordTerminator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T19:33:13.258669+00:00
-- url     : https://prove2.me/theorems/c03ae37f-608d-40d7-938a-7309a6b9943d
-- title:
--   Append a separator to an extracted signed record
-- statement:
--   Define a marker-preserving controller that writes a separator at the scratch head after signed-coordinate extraction. It preserves the start marker, leaves the input read-only, and freezes after its transition.
-- source:
--   Machine-level preparation for copying the low-precision multiplier operand from a signed coordinate record.

import Definitions.Def_BitDFT_FirstCoordinate
import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.RecordTerminator
open IntMul MachineSequence
abbrev storage (M : MultitapeTM) := FirstCoordinate.machine M
abbrev target (M : MultitapeTM) : Fin (storage M).k := SignedBlockPlacement.scratchTape M.k

def protect (M : MultitapeTM) (a : (storage M).Sym)
    (w : (storage M).Sym × Move) : (storage M).Sym × Move :=
  if a = (storage M).startSym then
    ((storage M).startSym, if w.2 = .left then .stay else w.2)
  else (if w.1 = (storage M).startSym then a else w.1, w.2)

private theorem start_ne_sep (M : MultitapeTM) :
    (storage M).startSym ≠ (storage M).sep := by
  have h := (storage M).syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at h
  rcases h with ⟨⟨_,_,_,_⟩,⟨_,_,h,_⟩,_,_⟩
  exact h

private theorem blank_ne_start (M : MultitapeTM) :
    (storage M).blank ≠ (storage M).startSym := by
  have h := (storage M).syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  rcases h with ⟨⟨h,_,_,_⟩,_,_,_⟩
  exact h

private theorem protect_start (M : MultitapeTM) (a : (storage M).Sym)
    (w : (storage M).Sym × Move) (h : a = (storage M).startSym) :
    (protect M a w).1 = (storage M).startSym ∧ (protect M a w).2 ≠ .left := by
  subst a
  constructor
  · simp [protect]
  · by_cases hm : w.2 = .left <;> simp [protect,hm]

private theorem protect_nonstart (M : MultitapeTM) (a : (storage M).Sym)
    (w : (storage M).Sym × Move) (h : a ≠ (storage M).startSym)
    (hw : w.1 ≠ (storage M).startSym) :
    (protect M a w).1 ≠ (storage M).startSym := by
  simp [protect,h,hw]

private theorem protect_self (M : MultitapeTM) (a : (storage M).Sym) :
    protect M a (a,.stay) = (a,.stay) := by
  by_cases h : a = (storage M).startSym <;> simp [protect,h]

def transition (M : MultitapeTM) (q : Bool) (a : Fin (storage M).k → (storage M).Sym) :=
  (true, fun i => protect M (a i)
    ((if !q && i = target M then (storage M).sep else a i),Move.stay))

def control (M : MultitapeTM) : Controller (storage M) where
  K := Bool
  entry := false
  exit := true
  distinct := by decide
  transition := transition M
  marker := by
    intro q a i hi
    exact protect_start M (a i) _ hi
  noMarker := by
    intro q a i hi
    have hw : (if !q && i = target M then (storage M).sep else a i) ≠ (storage M).startSym := by
      cases q with
      | false =>
        by_cases ht : i = target M
        · subst i
          simpa using Ne.symm (start_ne_sep M)
        · simpa [ht] using hi
      | true => simpa using hi
    exact protect_nonstart M (a i)
      ((if !q && i = target M then (storage M).sep else a i),Move.stay) hi hw
  frozen := by
    intro a
    apply Prod.ext
    · rfl
    · funext i
      exact protect_self M (a i)
  readonly := by
    intro q a
    have hi : (storage M).inTape ≠ target M := by
      intro h
      have hv := congrArg Fin.val h
      simp [MultitapeTM.inTape,target,SignedBlockPlacement.scratchTape] at hv
    change (protect M (a (storage M).inTape)
      ((if !q && (storage M).inTape = target M then (storage M).sep
        else a (storage M).inTape),Move.stay)).1 = a (storage M).inTape
    by_cases hq : q
    · simpa [hq] using congrArg Prod.fst (protect_self M (a (storage M).inTape))
    · simp [hq,hi]
      rw [protect_self]

abbrev controlMachine (M : MultitapeTM) := Controller.machine (control M)

private theorem target_transition (M : MultitapeTM)
    (cells : Fin (storage M).k → ℕ → (storage M).Sym)
    (head : Fin (storage M).k → ℕ)
    (hblank : cells (target M) (head (target M)) = (storage M).blank) :
    (transition M false (fun i => cells i (head i))).2 (target M) =
      ((storage M).sep,Move.stay) := by
  change protect M (cells (target M) (head (target M)))
    ((if !false && target M = target M then (storage M).sep
      else cells (target M) (head (target M))),Move.stay) = _
  rw [if_pos (by simp)]
  have hb := blank_ne_start M
  have hs := start_ne_sep M
  simp [protect,hblank,hb,hs]

private theorem other_transition (M : MultitapeTM)
    (cells : Fin (storage M).k → ℕ → (storage M).Sym)
    (head : Fin (storage M).k → ℕ) (i : Fin (storage M).k)
    (hi : i ≠ target M) :
    (transition M false (fun j => cells j (head j))).2 i =
      (cells i (head i),Move.stay) := by
  change protect M (cells i (head i))
    ((if !false && i = target M then (storage M).sep else cells i (head i)),Move.stay) = _
  rw [if_neg (by simp [hi])]
  exact protect_self M _

private theorem cfg_ext {N : MultitapeTM} (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

abbrev machine (M : MultitapeTM) :=
  (MachineSequence.sequence (MachineSequence.native (storage M))
    (BitDFT.RecordTerminator.control M)).machine

def final (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y : List Bool) : (machine M).Cfg :=
  rightCfg (MachineSequence.native (storage M)) (BitDFT.RecordTerminator.control M)
    (let b := FirstCoordinate.final M c rootCells rootHead sign x y
     { state := true,
       cells := Function.update b.cells (target M)
         (Function.update (b.cells (target M)) (b.head (target M)) (storage M).sep)
       head := b.head })

/-- One controller step writes the separator at the scratch head when it is blank. -/
theorem control_step (M : MultitapeTM) (cells : Fin (storage M).k → ℕ → (storage M).Sym)
    (head : Fin (storage M).k → ℕ)
    (hblank : cells (target M) (head (target M)) = (storage M).blank) :
    (controlMachine M).step ⟨false,cells,head⟩ =
      ⟨true, Function.update cells (target M)
        (Function.update (cells (target M)) (head (target M)) (storage M).sep), head⟩ := by
  apply cfg_ext
  · rfl
  · funext i
    change Function.update (cells i) (head i)
      ((transition M false (fun j => cells j (head j))).2 i).1 = _
    by_cases hi : i = target M
    · subst i
      rw [target_transition M cells head hblank]
      funext p
      by_cases hp : p = head (target M)
      · subst p
        simp
      · simp [Function.update, hp]
    · rw [other_transition M cells head i hi]
      simp [hi]
  · funext i
    have hmove : ((transition M false (fun j => cells j (head j))).2 i).2 = Move.stay := by
      simp only [transition, protect]
      split <;> rfl
    change (match ((transition M false (fun j => cells j (head j))).2 i).2 with
      | Move.left => head i - 1
      | Move.stay => head i
      | Move.right => head i + 1) = head i
    rw [hmove]

end BitDFT.RecordTerminator


