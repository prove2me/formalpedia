-- Prove2me | Definitions.Def_BitDFT_ControllerPadding
-- name    : BitDFT_ControllerPadding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T07:10:41.685+00:00
-- url     : https://prove2.me/theorems/257932bb-9655-407e-9548-392852a51fb0
-- title:
--   Pad a controller with stationary work tapes
-- statement:
--   Let a finite-tape controller run on a machine and append any finite number of tapes to that machine's tape layout. There is a controller on the enlarged layout that performs the original transition on the original tapes and leaves every appended tape and head unchanged. A tape permutation fixing the read-only input tape can then be incorporated into the controller transition.
-- source:
--   The construction extends the transition pointwise on the original tape prefix, assigns stationary moves to appended tapes, and conjugates transitions by a finite tape permutation.

import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapePermutation

set_option autoImplicit false
namespace BitDFT.MachineSequence
open IntMul

/-- Run a controller on the original tapes of an extended machine, leaving
    every appended tape untouched. -/
def padController {M : MultitapeTM} (C : Controller M) (r : ℕ) :
    Controller (TapeExtension.machine C.machine r) where
  K := C.K
  entry := C.entry
  exit := C.exit
  distinct := C.distinct
  transition := fun q a =>
    let z := C.transition q (fun i => a (TapeExtension.oldTape C.machine r i))
    (z.1, fun j => if h : j.val < C.machine.k then z.2 ⟨j.val, h⟩ else (a j, .stay))
  marker := by
    intro q a j hj
    by_cases h : j.val < C.machine.k
    · have hm := C.marker q (fun i => a (TapeExtension.oldTape C.machine r i)) ⟨j.val,h⟩ hj
      simpa [TapeExtension.machine, TapeExtension.transition, TapeExtension.oldTape,
        h] using hm
    · simp [TapeExtension.machine, TapeExtension.transition, TapeExtension.oldTape,
        h, hj]
  noMarker := by
    intro q a j hj
    by_cases h : j.val < C.machine.k
    · have hm := C.noMarker q (fun i => a (TapeExtension.oldTape C.machine r i)) ⟨j.val,h⟩ hj
      simpa [TapeExtension.machine, TapeExtension.transition, TapeExtension.oldTape,
        h] using hm
    · simp [TapeExtension.machine, TapeExtension.transition, TapeExtension.oldTape,
        h, hj]
  frozen := by
    intro a
    have hf := C.frozen (fun i => a (TapeExtension.oldTape C.machine r i))
    apply Prod.ext
    · simpa [TapeExtension.machine, TapeExtension.transition] using congrArg Prod.fst hf
    · funext j
      by_cases h : j.val < C.machine.k
      · simpa [TapeExtension.machine, TapeExtension.transition, TapeExtension.oldTape,h]
          using congrFun (congrArg Prod.snd hf) ⟨j.val,h⟩
      · simp [TapeExtension.machine, TapeExtension.transition, TapeExtension.oldTape,h]
  readonly := by
    intro q a
    have hidx : (TapeExtension.machine C.machine r).inTape =
        TapeExtension.oldTape C.machine r C.machine.inTape := by
      apply Fin.ext
      rfl
    rw [hidx]
    have hi : C.machine.inTape.val < C.machine.k := by
      change 0 < M.k
      have hk := M.two_le_k
      omega
    have hmi : M.inTape = C.machine.inTape := by
      apply Fin.ext
      rfl
    simpa [TapeExtension.machine, TapeExtension.transition,
      TapeExtension.oldTape, hi, hmi] using
      C.readonly q (fun i => a (TapeExtension.oldTape C.machine r i))

/-- Execute a controller after relocating its logical tapes through a
    permutation that fixes the read-only input tape. -/
def permuteController {M : MultitapeTM} (C : Controller M)
    (e : Fin M.k ≃ Fin M.k) (he : e M.inTape = M.inTape) : Controller M where
  K := C.K
  entry := C.entry
  exit := C.exit
  distinct := C.distinct
  transition := fun q a =>
    let z := C.transition q (fun j => a (e j))
    (z.1, fun i => z.2 (e.symm i))
  marker := by
    intro q a i hi
    have hm := C.marker q (fun j => a (e j)) (e.symm i) (by simpa using hi)
    simpa using hm
  noMarker := by
    intro q a i hi
    have hm := C.noMarker q (fun j => a (e j)) (e.symm i) (by simpa using hi)
    simpa using hm
  frozen := by
    intro a
    have hf := C.frozen (fun j => a (e j))
    apply Prod.ext
    · simpa using congrArg Prod.fst hf
    · funext i
      simpa using congrFun (congrArg Prod.snd hf) (e.symm i)
  readonly := by
    intro q a
    have hi : e.symm M.inTape = M.inTape := by
      apply e.injective
      simpa using he.symm
    have hr := C.readonly q (fun j => a (e j))
    change ((C.transition q (fun j => a (e j))).2 (e.symm M.inTape)).1 =
      a M.inTape
    rw [hi]
    simpa [he] using hr

theorem padController_machine {M : MultitapeTM} (C : Controller M) (r : ℕ) :
    (padController C r).machine = TapeExtension.machine C.machine r := by
  rfl

theorem permuteController_machine {M : MultitapeTM} (C : Controller M)
    (e : Fin M.k ≃ Fin M.k) (he : e M.inTape = M.inTape) :
    (permuteController C e he).machine =
      TapePermutation.machine C.machine e (by
        have hi : C.machine.inTape = M.inTape := by
          apply Fin.ext
          rfl
        rw [hi]
        exact he) := by
  rfl

end BitDFT.MachineSequence


