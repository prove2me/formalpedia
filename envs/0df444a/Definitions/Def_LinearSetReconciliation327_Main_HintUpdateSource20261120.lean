-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdateSource20261120
-- name    : LinearSetReconciliation327_Main_HintUpdateSource20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:07:22.50905+00:00
-- url     : https://prove2.me/theorems/9c1d9323-563b-4b53-a77f-aa6b06dda1ee
-- title:
--   LinearSetReconciliation327 — HintUpdateSource (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdateSource20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateExport20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintSourceFamily20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePrepared20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePayload20261120

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateLayout20261120

set_option autoImplicit false

namespace LinearSetReconciliation327.Main

theorem upvZ1_shift_zero (E : RAMEnv) (it : UpIt) (ab : UpAbs) :
    upvZ1 (upShiftDetEnv E 0) it ab = upvZ1 E it ab := by
  unfold upvZ1
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvZ2_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) :
    upvZ2 (upShiftDetEnv E 0) i it = upvZ2 E i it := by
  unfold upvZ2
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvZ3_shift_zero (E : RAMEnv) (it : UpIt) :
    upvZ3 (upShiftDetEnv E 0) it = upvZ3 E it := by
  unfold upvZ3
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvZ4_shift_zero (E : RAMEnv) (it : UpIt) (ab : UpAbs) :
    upvZ4 (upShiftDetEnv E 0) it ab = upvZ4 E it ab := by
  unfold upvZ4
  simp only [upvZ1_shift_zero, upvZ3_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvZ5_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvZ5 (upShiftDetEnv E 0) i it ab = upvZ5 E i it ab := by
  unfold upvZ5
  simp only [upvZ2_shift_zero, upvZ4_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvZ6_shift_zero (E : RAMEnv) (it : UpIt) (ab : UpAbs) :
    upvZ6 (upShiftDetEnv E 0) it ab = upvZ6 E it ab := by
  unfold upvZ6
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvZ7_shift_zero (E : RAMEnv) (it : UpIt) :
    upvZ7 (upShiftDetEnv E 0) it = upvZ7 E it := by
  unfold upvZ7
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvZ8_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvZ8 (upShiftDetEnv E 0) i it ab = upvZ8 E i it ab := by
  unfold upvZ8
  simp only [upvZ5_shift_zero, upvZ7_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvImg_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvImg (upShiftDetEnv E 0) i it ab = upvImg E i it ab := by
  unfold upvImg
  simp only [upvZ6_shift_zero, upvZ8_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvJ0_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvJ0 (upShiftDetEnv E 0) i it ab = upvJ0 E i it ab := by
  unfold upvJ0
  simp only [upvImg_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvPos_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvPos (upShiftDetEnv E 0) i it ab = upvPos E i it ab := by
  unfold upvPos
  simp only [upvImg_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY1_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY1 (upShiftDetEnv E 0) i it ab = upvY1 E i it ab := by
  unfold upvY1
  simp only [upvJ0_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY2_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY2 (upShiftDetEnv E 0) i it ab = upvY2 E i it ab := by
  unfold upvY2
  simp only [upvY1_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvCn_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvCn (upShiftDetEnv E 0) i it ab = upvCn E i it ab := by
  unfold upvCn
  simp only [upvY2_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY3_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY3 (upShiftDetEnv E 0) i it ab = upvY3 E i it ab := by
  unfold upvY3
  simp only [upvJ0_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvQ_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvQ (upShiftDetEnv E 0) i it ab = upvQ E i it ab := by
  unfold upvQ
  simp only [upvY3_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY4_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY4 (upShiftDetEnv E 0) i it ab = upvY4 E i it ab := by
  unfold upvY4
  simp only [upvQ_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY5_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY5 (upShiftDetEnv E 0) i it ab = upvY5 E i it ab := by
  unfold upvY5
  simp only [upvPos_shift_zero, upvY4_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvCoin_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvCoin (upShiftDetEnv E 0) i it ab = upvCoin E i it ab := by
  unfold upvCoin
  simp only [upvY5_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY6_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY6 (upShiftDetEnv E 0) i it ab = upvY6 E i it ab := by
  unfold upvY6
  simp only [upvCoin_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY7_shift_zero (E : RAMEnv) (it : UpIt) :
    upvY7 (upShiftDetEnv E 0) it = upvY7 E it := by
  unfold upvY7
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY8_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY8 (upShiftDetEnv E 0) i it ab = upvY8 E i it ab := by
  unfold upvY8
  simp only [upvY6_shift_zero, upvY7_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY9_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY9 (upShiftDetEnv E 0) i it ab = upvY9 E i it ab := by
  unfold upvY9
  simp only [upvY8_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY10_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY10 (upShiftDetEnv E 0) i it ab = upvY10 E i it ab := by
  unfold upvY10
  simp only [upvY9_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvY11_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvY11 (upShiftDetEnv E 0) i it ab = upvY11 E i it ab := by
  unfold upvY11
  simp only [upvY10_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvFn_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvFn (upShiftDetEnv E 0) i it ab = upvFn E i it ab := by
  unfold upvFn
  simp only [upvY11_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX1_shift_zero (E : RAMEnv) (it : UpIt) :
    upvX1 (upShiftDetEnv E 0) it = upvX1 E it := by
  unfold upvX1
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX2_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX2 (upShiftDetEnv E 0) i it ab = upvX2 E i it ab := by
  unfold upvX2
  simp only [upvCoin_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvW0_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvW0 (upShiftDetEnv E 0) i it ab = upvW0 E i it ab := by
  unfold upvW0
  simp only [upvX1_shift_zero, upvX2_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX3_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX3 (upShiftDetEnv E 0) i it ab = upvX3 E i it ab := by
  unfold upvX3
  simp only [upvCn_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvTb_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvTb (upShiftDetEnv E 0) i it ab = upvTb E i it ab := by
  unfold upvTb
  simp only [upvX3_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvCard_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvCard (upShiftDetEnv E 0) i it ab = upvCard E i it ab := by
  unfold upvCard
  rw [upvTb_shift_zero]
  simp only [upShiftDetEnv, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (show upvTb E i it ab < 2 ^ E.W from Nat.mod_lt _ (Nat.two_pow_pos E.W))]


theorem upvValid_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvValid (upShiftDetEnv E 0) i it ab = upvValid E i it ab := by
  unfold upvValid
  simp only [upvCard_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX4_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX4 (upShiftDetEnv E 0) i it ab = upvX4 E i it ab := by
  unfold upvX4
  simp only [upvTb_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX5_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX5 (upShiftDetEnv E 0) i it ab = upvX5 E i it ab := by
  unfold upvX5
  simp only [upvX4_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvElem_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvElem (upShiftDetEnv E 0) i it ab = upvElem E i it ab := by
  unfold upvElem
  rw [upvX5_shift_zero]
  simp only [upShiftDetEnv, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (show upvX5 E i it ab < 2 ^ E.W from Nat.mod_lt _ (Nat.two_pow_pos E.W))]


theorem upvX6_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX6 (upShiftDetEnv E 0) i it ab = upvX6 E i it ab := by
  unfold upvX6
  simp only [upvQ_shift_zero, upvElem_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX7_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX7 (upShiftDetEnv E 0) i it ab = upvX7 E i it ab := by
  unfold upvX7
  simp only [upvX6_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX8_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX8 (upShiftDetEnv E 0) i it ab = upvX8 E i it ab := by
  unfold upvX8
  simp only [upvX7_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvBit_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvBit (upShiftDetEnv E 0) i it ab = upvBit E i it ab := by
  unfold upvBit
  simp only [upvQ_shift_zero, upvX8_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX9_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX9 (upShiftDetEnv E 0) i it ab = upvX9 E i it ab := by
  unfold upvX9
  simp only [upvW0_shift_zero, upvValid_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX10_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX10 (upShiftDetEnv E 0) i it ab = upvX10 E i it ab := by
  unfold upvX10
  simp only [upvX9_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvWt_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvWt (upShiftDetEnv E 0) i it ab = upvWt E i it ab := by
  unfold upvWt
  simp only [upvW0_shift_zero, upvX10_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvX11_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvX11 (upShiftDetEnv E 0) i it ab = upvX11 E i it ab := by
  unfold upvX11
  simp only [upvFn_shift_zero, upvWt_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvMask0_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvMask0 (upShiftDetEnv E 0) i it ab = upvMask0 E i it ab := by
  unfold upvMask0
  simp only [upvX11_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvWw_shift_zero (E : RAMEnv) :
    upvWw (upShiftDetEnv E 0)  = upvWw E  := by
  unfold upvWw
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvB1_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvB1 (upShiftDetEnv E 0) i it ab = upvB1 E i it ab := by
  unfold upvB1
  simp only [upvBit_shift_zero, upvWw_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvSh_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvSh (upShiftDetEnv E 0) i it ab = upvSh E i it ab := by
  unfold upvSh
  simp only [upvB1_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvMask_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvMask (upShiftDetEnv E 0) i it ab = upvMask E i it ab := by
  unfold upvMask
  simp only [upvMask0_shift_zero, upvSh_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvWi_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvWi (upShiftDetEnv E 0) i it ab = upvWi E i it ab := by
  unfold upvWi
  simp only [upvBit_shift_zero, upvWw_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvOld_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvOld (upShiftDetEnv E 0) i it ab = upvOld E i it ab := by
  unfold upvOld
  simp only [upvWi_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvNew_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) :
    upvNew (upShiftDetEnv E 0) i it ab = upvNew E i it ab := by
  unfold upvNew
  simp only [upvMask_shift_zero, upvOld_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upApplyBody_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upApplyBody (upShiftDetEnv E 0) i it a = upApplyBody E i it a := by
  unfold upApplyBody
  simp only [upvCn_shift_zero, upvFn_shift_zero, upvWi_shift_zero, upvNew_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvG2_shift_zero (E : RAMEnv) (it : UpIt) :
    upvG2 (upShiftDetEnv E 0) it = upvG2 E it := by
  unfold upvG2
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvG3_shift_zero (E : RAMEnv) (it : UpIt) :
    upvG3 (upShiftDetEnv E 0) it = upvG3 E it := by
  unfold upvG3
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvA2_shift_zero (E : RAMEnv) (it : UpIt) :
    upvA2 (upShiftDetEnv E 0) it = upvA2 E it := by
  unfold upvA2
  simp only [upvG2_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvA3_shift_zero (E : RAMEnv) (it : UpIt) :
    upvA3 (upShiftDetEnv E 0) it = upvA3 E it := by
  unfold upvA3
  simp only [upvG3_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvRt_shift_zero (E : RAMEnv) (it : UpIt) :
    upvRt (upShiftDetEnv E 0) it = upvRt E it := by
  unfold upvRt
  simp only [upvA3_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvSv_shift_zero (E : RAMEnv) (it : UpIt) :
    upvSv (upShiftDetEnv E 0) it = upvSv E it := by
  unfold upvSv
  simp only [upvA2_shift_zero, upvRt_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvM0_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upvM0 (upShiftDetEnv E 0) i it a = upvM0 E i it a := by
  unfold upvM0
  simp only [upApplyBody_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvM1_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upvM1 (upShiftDetEnv E 0) i it a = upvM1 E i it a := by
  unfold upvM1
  simp only [upApplyBody_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvCnf_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upvCnf (upShiftDetEnv E 0) i it a = upvCnf E i it a := by
  unfold upvCnf
  simp only [upvCn_shift_zero, upvRt_shift_zero, upvM0_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvFnf_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upvFnf (upShiftDetEnv E 0) i it a = upvFnf E i it a := by
  unfold upvFnf
  simp only [upvFn_shift_zero, upvRt_shift_zero, upvM1_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvV0_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upvV0 (upShiftDetEnv E 0) i it a = upvV0 E i it a := by
  unfold upvV0
  simp only [upvSv_shift_zero, upvM0_shift_zero, upvCnf_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upvV1_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upvV1 (upShiftDetEnv E 0) i it a = upvV1 E i it a := by
  unfold upvV1
  simp only [upvSv_shift_zero, upvM1_shift_zero, upvFnf_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upApply_shift_zero (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) :
    upApply (upShiftDetEnv E 0) i it a = upApply E i it a := by
  unfold upApply
  simp only [upApplyBody_shift_zero, upvCnf_shift_zero, upvFnf_shift_zero, upvV0_shift_zero, upvV1_shift_zero]
  all_goals simp only [upShiftDetEnv, Nat.zero_add, Nat.mod_mod]


theorem upFold_shift_zero (E : RAMEnv) (i : ℕ) (items : List UpIt) (ab : UpAbs) :
    upFold (upShiftDetEnv E 0) i ab items = upFold E i ab items := by
  induction items generalizing ab with
  | nil => rfl
  | cons it rest ih =>
      change upFold (upShiftDetEnv E 0) i (upApply (upShiftDetEnv E 0) i it ab) rest =
        upFold E i (upApply E i it ab) rest
      rw [upApply_shift_zero]
      exact ih _
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
theorem packMem_zero_ge_words (W M : ℕ) (hW : 0 < W) (y : Fin M → ZMod 2) (a : ℕ)
    (ha : wordsOf W M ≤ a) : packMem W y a = 0 := by
  unfold packMem
  apply Finset.sum_eq_zero
  intro p _
  apply if_neg
  rintro ⟨he, _⟩
  have hp : p.val / W < wordsOf W M :=
    (Nat.div_lt_iff_lt_mul hW).mpr (p.isLt.trans_le (up_words_cover W M hW))
  omega

theorem upVirtualMem_zero_pack (W M : ℕ) (hW : 0 < W) (hWords : wordsOf W M ≤ 2 ^ W)
    (y : Fin M → ZMod 2) : upVirtualMem W 0 (packMem W y) = packMem W y := by
  funext a
  by_cases ha : a < 2 ^ W
  · simp only [upVirtualMem, if_pos ha, upCyclicAddr, Nat.zero_add,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (packMem_lt W hW y a)]
  · rw [upVirtualMem, if_neg ha, packMem_zero_ge_words W M hW y a (by omega)]

theorem upSavedAt_program : At progUpSaved 0 (upSavedSup.compile 0) := by
  intro a ha
  simp only [progUpSaved, Nat.zero_add]
  exact List.getElem?_append_left ha

theorem upSavedSup_halted (out : RAMState) (hpc : out.pc = 156) : Halted progUpSaved out := by
  have hLen : (upSavedSup.compile 0).length = 156 := by rw [Stmt.length_compile, upSavedSup_len]
  unfold Halted
  simp only [progUpSaved, hpc]
  rw [← hLen]
  simp

theorem upSaved_toggles_of_fold (E : RAMEnv) (items : List UpIt) {N M : ℕ}
    (H : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) (B : ℝ)
    (h16 : 16 < 2 ^ E.W) (hWpos : 0 < E.W) (hWords : wordsOf E.W M ≤ 2 ^ E.W)
    (hLayout : UpSavedLayout E 0 items) (hCount : E.det 0 % 2 ^ E.W = items.length)
    (hBudget : ((147 * items.length + 10 : ℕ) : ℝ) ≤ B)
    (hEffect : ∀ (y : Fin M → ZMod 2) (i : Fin N) (a : ℕ), a < wordsOf E.W M →
      (upFold E i.val (⟨packMem E.W y, 0, 1⟩ : UpAbs) items).mem a =
        packMem E.W (y + H (Pi.single i 1)) a) :
    TogglesWithin progUpSaved E H B := by
  intro y i
  let s := initState (packMem E.W y) i.val 0 0
  let ab : UpAbs := ⟨packMem E.W y, 0, 1⟩
  have hMem : upVirtualMem E.W 0 s.mem = ab.mem := upVirtualMem_zero_pack E.W M hWpos hWords y
  have hRaw : UpBasedRawPayload 0 (wordsOf E.W M) ab s := by
    intro q hq
    simp only [s, ab, initState, Nat.zero_add]
  have hExec := upSavedSup_payload_sem progUpSaved E 0 0 0 i.val (wordsOf E.W M) items s ab
    upSavedAt_program rfl hLayout hMem rfl rfl hRaw (Nat.two_pow_pos E.W)
    (by simpa only [Nat.zero_add] using hWords) h16
    (by simp [s, initState]) (by simp [s, initState]) (by simp [s, initState])
    (by simpa only [Nat.zero_mod] using hCount)
  obtain ⟨_, k, out, hRun, hPc, hCost, hView, hRawOut, hR0, hR14, hR15⟩ := hExec
  refine ⟨out, ⟨k, ?_, hRun, upSavedSup_halted out (by simpa only [Nat.zero_add] using hPc)⟩, ?_⟩
  · have hk : (k : ℝ) ≤ ((147 * items.length + 10 : ℕ) : ℝ) := by exact_mod_cast hCost
    exact hk.trans hBudget
  · intro a ha
    rw [upFold_shift_zero] at hRawOut
    simpa only [Nat.zero_add] using (hRawOut a ha).trans (hEffect y i a ha)

theorem upSaved_cost_of_old (L nc d bell bc : ℕ) (B : ℝ)
    (hL : L ≤ nc * (d + 2 * bell + bc))
    (hOld : ((125 * (nc * (d + bell + bc)) + 12 : ℕ) : ℝ) ≤ B) :
    ((147 * L + 10 : ℕ) : ℝ) ≤ 3 * B := by
  have hNat : 147 * (nc * (d + 2 * bell + bc)) + 10 ≤
      3 * (125 * (nc * (d + bell + bc)) + 12) := by
    ring_nf
    omega
  have hLe : 147 * L + 10 ≤ 3 * (125 * (nc * (d + bell + bc)) + 12) :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 147 hL) 10).trans hNat
  have hReal : ((147 * L + 10 : ℕ) : ℝ) ≤ 3 * ((125 * (nc * (d + bell + bc)) + 12 : ℕ) : ℝ) := by
    exact_mod_cast hLe
  exact hReal.trans (mul_le_mul_of_nonneg_left hOld (by norm_num))

end LinearSetReconciliation327.Main

noncomputable section
namespace LinearSetReconciliation327.Main
theorem upSavedFold_packMem_of_local (CR : CRFamily) (P : HintParams) (T : Node)
    (hT : IsSchemeTree P T) (r : (hintSpec T).Seed) (E : RAMEnv) (Bc colBase sav : ℕ)
    (hW : 1 < 2 ^ E.W) (hWpos : 0 < E.W) (hN : 0 < T.N) (hNM : T.N ≤ 2 ^ E.W)
    (hLocal : ∀ i : Fin T.N, UpLocalTree CR E i.val Bc colBase T (hintKappa P T hT r) 0 0 0)
    (hRoom : UpSaveRoom (wordsOf E.W (synLen CR T)) sav T) :
    ∀ (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N) (a : ℕ),
      a < wordsOf E.W (synLen CR T) →
      (upFold E i.val (⟨packMem E.W y, 0, 1⟩ : UpAbs)
        (upSched CR Bc colBase T 0 0 0 sav [])).mem a =
      packMem E.W (y + hintH_trees CR P T hT r (Pi.single i 1)) a := by
  intro y i a ha
  rw [packMem_add_H_single CR P T hT r E.W hWpos y i a]
  exact upFold_root_of_local CR E Bc colBase (wordsOf E.W (synLen CR T)) sav T
    (hintKappa P T hT r) i.val hW hN hNM (hLocal i)
    (up_words_cover E.W (synLen CR T) hWpos) hRoom i.isLt (packMem E.W y)
    (fun a => packMem_lt E.W hWpos y a) a ha

theorem upSavedRoot_toggles_after (CR : CRFamily) (P : HintParams) (W Bc U Bell : ℕ)
    (T : Node) (hT : IsSchemeTree P T) (B : ℝ) (hdr : ℕ → ℕ) (decItems : List DecIt)
    (hW : 8 ≤ W) (hFits : (hintSpec T).Fits W)
    (hWords : wordsOf W (synLen CR T) ≤ 2 ^ W)
    (hStatic : UpTreeStatic CR Bc U T) (hU : U ≤ 2 ^ W) (hN : 0 < T.N)
    (hBc : Bc ≤ 4 * (2 ^ W) ^ 3) (hBell : 1 ≤ Bell) (hEll : UpEllOK Bell T)
    (hOld : ((125 * (T.nodeCount * (T.depth + Bell + Bc)) + 12 : ℕ) : ℝ) ≤ B)
    (r : (hintSpec T).Seed) :
    TogglesWithin progUpSaved
      ((hintSpec T).env (upWideWord W)
        (decTabAfter (upRootDet CR W Bc T) hdr (upRootBase Bc T) (upTabLen Bc T) decItems) r)
      (hintH_trees CR P T hT r) (3 * B) := by
  have hLayout := upRoot_layout_fits CR P W Bc U T hT hW hFits hWords hStatic hU hN hBc
  let V := upWideWord W
  let items := upRootItems CR W Bc T
  let colBase := upRootBase Bc T
  let merged := decTabAfter (upRootDet CR W Bc T) hdr colBase (upTabLen Bc T) decItems
  let E := (hintSpec T).env V merged r
  have hVpos : 0 < V := by unfold V upWideWord; omega
  have hCol : colBase = 8 + 16 * items.length := by
    change 8 + 16 * upRootCount Bc T = 8 + 16 * items.length
    rw [hLayout.length_eq]
  have hLocal : ∀ i : Fin T.N, UpLocalTree CR E i.val Bc colBase T
      (hintKappa P T hT r) 0 0 0 := by
    intro i
    exact UpLocalTree.of_decTabAfter CR (hintSpec T) V (upRootDet CR W Bc T) hdr colBase
      (upTabLen Bc T) decItems r i.val Bc hLayout.word (by have h := hLayout.colBase; omega)
      hLayout.table_end T (hintKappa P T hT r) 0 0 0 (by simp only [Nat.zero_add]; exact le_rfl)
      (upRoot_localTree CR P W Bc U T hT r i.val hW hFits hU hStatic hLayout)
  have hEffect := upSavedFold_packMem_of_local CR P T hT r E Bc colBase (upRootSlot CR W T)
    hLayout.word hVpos hN hLayout.universe_fits hLocal hLayout.room
  have hL : items.length ≤ T.nodeCount * (T.depth + 2 * Bell + Bc) :=
    upSched_count_le CR Bc Bell colBase hBell T hEll 0 0 0 (upRootSlot CR W T)
  have hBudget := upSaved_cost_of_old items.length T.nodeCount T.depth Bell Bc B hL hOld
  have hFields : ∀ j (hj : j < items.length), ∀ t, t < 16 →
      E.det (8 + 16 * j + t) % 2 ^ E.W = (items[j]).fld t := by
    intro j hj t ht
    change merged (8 + 16 * j + t) % 2 ^ V = (items[j]).fld t
    dsimp only [merged]
    rw [decTabAfter_agrees (upRootDet CR W Bc T) hdr colBase (upTabLen Bc T) decItems (8 + 16 * j + t)
      (by unfold decAfterBase; omega) (by omega)]
    exact hLayout.fields j hj t ht
  have hCount : E.det 0 % 2 ^ E.W = items.length := by
    change merged 0 % 2 ^ V = items.length
    dsimp only [merged]
    rw [decTabAfter_agrees (upRootDet CR W Bc T) hdr colBase (upTabLen Bc T) decItems 0
      (by unfold decAfterBase; omega) (by decide)]
    exact hLayout.count_read
  have hHeaderWidth : upvWw E = E.W := by
    change merged (1 % 2 ^ V) % 2 ^ V = V
    rw [Nat.mod_eq_of_lt hLayout.word]
    dsimp only [merged]
    rw [decTabAfter_agrees (upRootDet CR W Bc T) hdr colBase (upTabLen Bc T) decItems 1
      (by unfold decAfterBase; omega) (by omega)]
    simp only [upRootDet, upDet_one]
    change V % 2 ^ V = V
    exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := V))
  have hSavedLayout : UpSavedLayout E 0 items := by
    refine ⟨hLayout.address, ?_, ?_, ?_, ?_⟩
    · intro j hj t ht
      change E.det ((0 + (8 + 16 * j + t)) % 2 ^ E.W) % 2 ^ E.W = (items[j]).fld t
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by have hh : 8 + 16 * items.length < 2 ^ E.W := hLayout.address; omega : 8 + 16 * j + t < 2 ^ E.W)]
      exact hFields j hj t ht
    · rw [upvWw_shift_zero]
      exact hHeaderWidth
    · exact upSched_kind CR Bc colBase T 0 0 0 (upRootSlot CR W T) [] (by simp)
    · intro it hi _
      exact hLayout.saves it hi
  have h16 : 16 < 2 ^ E.W := by
    have hFive : 5 ≤ V := by unfold V upWideWord; omega
    have hPow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hFive
    norm_num only [Nat.reducePow] at hPow
    exact lt_of_lt_of_le (by decide : 16 < 2 ^ 5) hPow
  have hWordsV : wordsOf V (synLen CR T) ≤ 2 ^ V :=
    (wordsOf_antitone_word (by omega : 0 < W) (upWideWord_ge W)).trans
      (hWords.trans (Nat.pow_le_pow_right (by decide) (upWideWord_ge W)))
  apply upSaved_toggles_of_fold E items (hintH_trees CR P T hT r) (3 * B)
    h16 hVpos hWordsV hSavedLayout hCount hBudget
  exact hEffect

end LinearSetReconciliation327.Main
end

noncomputable section
namespace LinearSetReconciliation327.Main
theorem hintSavedToggles_actual_after {CR : CRFamily} {KCR : ℝ} {n lam N X Y : ℕ}
    (hRows : ∀ Nv t, t ≤ Nv → (CR.rows Nv t : ℝ) ≤ KCR * ((t : ℝ) * lg ((Nv : ℝ) + 2) ^ 2))
    (hCol : ∀ Nv t, t ≤ Nv → ∀ c, ((CR.col Nv t c).card : ℝ) ≤ KCR * lg ((Nv : ℝ) + 2) ^ 2)
    (hRange : ∀ Nv t, t ≤ Nv → ∀ c, c < Nv → CR.col Nv t c ⊆ Finset.range (CR.rows Nv t))
    (hArgs : (hintP KCR n lam).NodeArgs N X Y)
    (fuel : ℕ) (T : Node) (hTree : (hintP KCR n lam).tree fuel N X Y = some T)
    (hT : IsSchemeTree (hintP KCR n lam) T) (hdr : ℕ → ℕ) (decItems : List DecIt)
    (r : (hintSpec T).Seed) :
    TogglesWithin progUpSaved
      ((hintSpec T).env (upWideWord (hintW (hintColK KCR) n))
        (decTabAfter (upRootDet CR (hintW (hintColK KCR) n) (colBc KCR n) T) hdr
          (upRootBase (colBc KCR n) T) (upTabLen (colBc KCR n) T) decItems) r)
      (hintH_trees CR (hintP KCR n lam) T hT r)
      ((3 * hintCu (hintColK KCR)) * lg (n : ℝ) ^ hintpu) := by
  have h := upHint_prepared hRows hCol hRange hArgs fuel T hTree
  have hh := upSavedRoot_toggles_after CR (hintP KCR n lam) (hintW (hintColK KCR) n)
    (colBc KCR n) n (colBℓ KCR n) T hT (hintCu (hintColK KCR) * lg (n : ℝ) ^ hintpu)
    hdr decItems h.word_min h.fits h.words h.static h.universe_fits h.positive
    h.padding h.ell_pos h.ell h.cost r
  simpa only [mul_assoc] using hh
end LinearSetReconciliation327.Main
end

noncomputable section
namespace LinearSetReconciliation327.Main
theorem hintSavedToggles_source (S : CRSourceBundle) {n lam N X Y : ℕ}
    (hArgs : (hintP S.K n lam).NodeArgs N X Y)
    (fuel : ℕ) (T : Node) (hTree : (hintP S.K n lam).tree fuel N X Y = some T)
    (hT : IsSchemeTree (hintP S.K n lam) T) (hdr : ℕ → ℕ) (decItems : List DecIt)
    (r : (hintSpec T).Seed) :
    TogglesWithin progUpSaved
      ((hintSpec T).env (upWideWord (hintW (hintColK S.K) n))
        (decTabAfter (upRootDet (crFamily S) (hintW (hintColK S.K) n) (colBc S.K n) T) hdr
          (upRootBase (colBc S.K n) T) (upTabLen (colBc S.K n) T) decItems) r)
      (hintH_trees (crFamily S) (hintP S.K n lam) T hT r)
      ((3 * hintCu (hintColK S.K)) * lg (n : ℝ) ^ hintpu) := by
  exact hintSavedToggles_actual_after (crFamily_rows S) (crFamily_columns S)
    (fun Nv t ht c hc => crFamily_range S Nv t c) hArgs fuel T hTree hT hdr decItems r

end LinearSetReconciliation327.Main
end

#print axioms LinearSetReconciliation327.Main.hintSavedToggles_source


