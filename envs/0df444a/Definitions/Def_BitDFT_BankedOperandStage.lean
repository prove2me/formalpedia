-- Prove2me | Definitions.Def_BitDFT_BankedOperandStage
-- name    : BitDFT_BankedOperandStage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:04:48.065036+00:00
-- url     : https://prove2.me/theorems/61870ba5-dc02-4095-93c9-12744711d445
-- title:
--   A shared-host controller for staging the Fourier coordinate and dimension operands
-- statement:
--   In the disjoint-bank host for a Fourier coordinate reader, a tracked integer multiplier, and a header reader, route the coordinate bank, retained dimension tape, and multiplier caller buffer to their designated host tapes. Define a finite controller that skips the signed coordinate prefix, prepares a zero-padded dimension operand, inserts the separator, and copies the low coordinate bits as the second operand. The controller uses the same finite transition table for every input size.
-- source:
--   Staging interface for BitDFT.rescale_output_machine. It reuses the published dedicated-tape-bank host and the explicit operand-stage controller; the accompanying exact-run theorem supplies configuration-level correctness and transition count.

import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_CoordinateReadable
import Definitions.Def_BitDFT_HeaderReader

set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedOperandStage
open IntMul

abbrev fourierSide (F : MultitapeTM) := BitDFT.CoordinateReadable.machine F
abbrev multiplierSide (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev headerSide := BitDFT.HeaderReader.machine

def coordinateTape (A M H : MultitapeTM) (j : Fin A.k) :
    Fin (BitDFT.DedicatedTapeBanks.width A (TrackedBankedCall.machine M) H) :=
  ⟨j.val, by
    rw [BitDFT.DedicatedTapeBanks.width_eq_sum]
    change j.val < A.k + (M.k + 2) + H.k + 1
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega⟩

def dimensionTape (A M H : MultitapeTM) :
    Fin (BitDFT.DedicatedTapeBanks.width A (TrackedBankedCall.machine M) H) :=
  ⟨A.k + M.k + 3, by
    rw [BitDFT.DedicatedTapeBanks.width_eq_sum]
    change A.k + M.k + 3 < A.k + (M.k + 2) + H.k + 1
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega⟩

def multiplierOutputTape (A M H : MultitapeTM) :
    Fin (BitDFT.DedicatedTapeBanks.width A (TrackedBankedCall.machine M) H) :=
  ⟨A.k, by rw [BitDFT.DedicatedTapeBanks.width_eq_sum]; change A.k < A.k + (M.k + 2) + H.k + 1; have hM := M.two_le_k; have hH := H.two_le_k; omega⟩

theorem coordinateTape_positive (A M H : MultitapeTM) (j : Fin A.k)
    (hj : 1 ≤ j.val) : 1 ≤ (coordinateTape A M H j).val := hj

theorem dimensionTape_positive (A M H : MultitapeTM) :
    1 ≤ (dimensionTape A M H).val := by
  change 1 ≤ A.k + M.k + 3
  omega

theorem outputTape_positive (A M H : MultitapeTM) :
    1 ≤ (multiplierOutputTape A M H).val := by
  change 1 ≤ A.k
  have hA := A.two_le_k
  omega

theorem coordinate_ne_dimension (A M H : MultitapeTM) (j : Fin A.k) :
    coordinateTape A M H j ≠ dimensionTape A M H := by
  intro he
  have hv := congrArg Fin.val he
  simp [coordinateTape, dimensionTape] at hv
  have hA := A.two_le_k; have hM := M.two_le_k
  omega

theorem coordinate_ne_output (A M H : MultitapeTM) (j : Fin A.k)
    (hj : 1 ≤ j.val) : coordinateTape A M H j ≠ multiplierOutputTape A M H := by
  intro he
  have hv := congrArg Fin.val he
  simp [coordinateTape, multiplierOutputTape] at hv
  omega

theorem dimension_ne_output (A M H : MultitapeTM) :
    dimensionTape A M H ≠ multiplierOutputTape A M H := by
  intro he
  have hv := congrArg Fin.val he
  simp [dimensionTape, multiplierOutputTape] at hv
  have hM := M.two_le_k
  omega

def controller (A M H : MultitapeTM) (j : Fin A.k) (hj : 1 ≤ j.val) :=
  BitDFT.OperandStage.control
    (BitDFT.BankedTripleAlphabetHost.multiplierMachine A (TrackedBankedCall.machine M) H)
    (coordinateTape A M H j) (dimensionTape A M H) (multiplierOutputTape A M H)
    (by
      intro h
      have hv := congrArg Fin.val h
      change j.val = 0 at hv
      omega)
    (by
      intro h
      have hv := congrArg Fin.val h
      change A.k + M.k + 3 = 0 at hv
      omega)
    (by
      intro h
      have hv := congrArg Fin.val h
      change A.k = 0 at hv
      omega)
    (coordinate_ne_dimension A M H j)
    (coordinate_ne_output A M H j hj)
    (dimension_ne_output A M H)

abbrev machine (A M H : MultitapeTM) (j : Fin A.k) (hj : 1 ≤ j.val) :=
  (controller A M H j hj).machine

end BitDFT.BankedOperandStage
end


