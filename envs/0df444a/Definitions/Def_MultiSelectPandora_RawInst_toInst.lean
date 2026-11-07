-- Prove2me | Definitions.Def_MultiSelectPandora_RawInst_toInst
-- name    : MultiSelectPandora_RawInst_toInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:12.776415+00:00
-- url     : https://prove2.me/theorems/1e7368a0-14ed-4c1b-8d54-7b0f6873960c
-- title:
--   The real instance of a rational instance
-- statement:
--   Reads a rational instance as an instance: the boxes are the entries of the list, and costs, values and probabilities are cast to the reals.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_RawInst

namespace MultiSelectPandora

/-- **The real instance of a rational one.** Auxiliary to §2.1, p.5 (PDF p.6) of the Beyhaghi–Han–Luqman manuscript. -/
noncomputable def RawInst.toInst (I : RawInst) : Inst where
  n := I.length
  c i := ((I.get i).1 : ℝ)
  s i := (I.get i).2.length
  val i j := (((I.get i).2.get j).1 : ℝ)
  prob i j := (((I.get i).2.get j).2 : ℝ)

end MultiSelectPandora


