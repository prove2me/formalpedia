-- Prove2me | Definitions.Def_DetDLP_D4Slice
-- name    : DetDLP_D4Slice
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:22:30.52041+00:00
-- url     : https://prove2.me/theorems/c66b1c7d-9c81-463a-8ba9-4d9a766d6bcb
-- title:
--   Polynomial-time digit extraction at prescribed Kronecker addresses
-- statement:
--   The bit-string transformation groups coefficient words by their supplied packed indices, extracts a specified block of bits, and writes the complete dense row at the requested working precision. It is polynomial-time on arbitrary inputs, with the output arity supplied in unary.

import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_PolyT_sum

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace DetDLP.D4Slice
open Groundwork DetDLP_W1_Queries Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT

abbrev W := List Bool

def field : ℕ → W → W
  | 0 => first
  | n+1 => fun w => field n (more w)

@[local fun_prop] theorem field_poly {α : Type} [Enc α] (n : ℕ) {w : α → W} (hw : PolyT w) :
    PolyT (fun x => field n (w x)) := by
  induction n generalizing w with
  | zero => exact first_poly hw
  | succ n ih => exact ih (more_poly hw)

/-- The six fields carry the unary output length, addresses in source-word order,
    working modulus, digit divisor, digit modulus, and the returned source words. -/
def raw (w : W) : W :=
  let ps := w5_M6Sort.decode (field 1 w)
  let xs := w5_M6Sort.decode (field 5 w)
  encodeNatListBin ((List.range (field 0 w).length).map fun i =>
    ((ps.zip xs).map (fun a => if a.1 = i then a.2 / bval (field 3 w) % bval (field 4 w) else 0)).sum % bval (field 2 w))

attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk
  PolyT.map PolyT.length PolyT.div PolyT.mod PolyT.sum PolyT.zip
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219

private theorem rangeLen {α : Type} [Enc α] {w : α → W} (hw : PolyT w) :
    PolyT (fun x => List.range (w x).length) := by
  apply PolyT.range
  have hm : PolyT (fun x => (w x).map fun _ => ()) := by fun_prop
  apply hm.congr
  simp

@[local fun_prop] private theorem decodeP {α : Type} [Enc α] {w : α → W} (hw : PolyT w) :
    PolyT (fun x => w5_M6Sort.decode (w x)) := w5_M6Sort.decode_poly.comp hw

theorem raw_poly : PolyT raw := by
  unfold raw
  apply w5_M6Sort.encode_poly
  apply PolyT.map (f := fun w (i : ℕ) => (((w5_M6Sort.decode (field 1 w)).zip (w5_M6Sort.decode (field 5 w))).map
    (fun a => if a.1 = i then a.2 / bval (field 3 w) % bval (field 4 w) else 0)).sum % bval (field 2 w))
  · apply PolyT.mod
    · apply PolyT.sum
      apply PolyT.map (f := fun (p : W × ℕ) (a : ℕ × ℕ) => if a.1 = p.2 then a.2 / bval (field 3 p.1) % bval (field 4 p.1) else 0)
      · fun_prop
      · fun_prop
    · fun_prop
  · apply rangeLen
    fun_prop
end DetDLP.D4Slice


