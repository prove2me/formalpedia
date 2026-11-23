-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_DecOutBase20261123
-- name    : LinearSetReconciliation327_Main_DecOutBase20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T12:28:01.619444+00:00
-- url     : https://prove2.me/theorems/1198760a-4849-4719-83f6-e9fd3fc6c498
-- title:
--   The cr pre at 2.3's decoder: bb = decOutBase, frame bound decOutBase + N
-- statement:
--   Pins the abstract `cr`-slot interface to Proposition 2.3's own decoder: the output base is `bb = decOutBase N t` (the published exit register) and the frame bound is `decFrameBound N t = decOutBase N t + N` (the decoder's output window is `[decOutBase, decOutBase + |S|)` with `|S| <= N`). It names the one missing statement, `decMemFrameAtOut`: the decoder writes nothing at or above `decOutBase N t + N`, and proves that this is exactly what the `cr` field needs - `crDecOut_of_hdecW_exit`, `hdecIn_of_hdecW_frame_out` (from the shape of the published `hdecW` plus the frame) and `stageRun_crSlot_out`, the `cr` field at Proposition 2.3's decoder whose merge step is `crMergeInD_of_upk`.
-- source:
--   arXiv:2611.11409 (Linear Set Reconciliation with O(d) Additive Redundancy), Theorem 6.5 / Proposition 2.3

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrSlot20261123
import Definitions.Def_LinearSetReconciliation327_Main_CR23DecExitWz20261123

/-!
# The `cr` pre at 2.3's decoder: `bb = decOutBase N t`, frame bound `decOutBase N t + N`

`Def_…_CrSlot20261123` closes the `cr` slot from an abstract decoder exit contract
(`CRS.DecExitF`) with an abstract output base `bb` and frame bound `B`.  This bundle pins those two
numbers to Proposition 2.3's own decoder:

* `bb = decOutBase N t` — the decoder's published exit register `s'.regs r0 = decOutBase N t`;
* `B = decOutBase N t + N` — the decoder's output window is `[decOutBase, decOutBase + |S|)` with
  `|S| ≤ N`, so `B` is the first address the decoder provably does not write.

`decMemFrameAtOut` names the one missing statement (**the decoder memory-frame lemma**), and
`hdecIn_of_hdecW_frame_out` / `stageRun_crSlot_out` show that it is *exactly* what the `cr` field
needs: with it, `CRS.hdecW` (published, `Proved`) closes the slot and `crMergeInD_of_upk` applies.

Axiom-clean: no `Theorems.Thm_*` import; only `Mathlib` and published `Definitions.Def_*` bundles.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! ## 1. The two numbers -/

/-- **The decoder frame bound**: the first address above the decoder's output window. -/
def decFrameBound (N t : ℕ) : ℕ := decOutBase N t + N

/-- **The decoder memory-frame lemma, at Proposition 2.3's decoder** — *the decoder writes nothing at
or above `decOutBase N t + N`*.  This is the one statement no published bundle has; it is the
round's only new obligation. -/
def decMemFrameAtOut (N t : ℕ) (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (T : ℝ) : Prop :=
  DecMemFrame (detEnv (cr23Word N) (cr23DecDet N t C)) (decFrameBound N t) decStmt T

/-! ## 2. `CrDecOut` from the exit + the frame -/

/-- **`CrDecOut` from the published exit facts, at `bb = decOutBase N t`, `B = decOutBase N t + N`.** -/
theorem crDecOut_of_hdecW_exit {E : RAMEnv} {N t : ℕ} {x : Fin N → ZMod 2} {xbase m bl : ℕ}
    {y : Fin (E.W * m) → ZMod 2} {S : Finset ℕ} {s s' : RAMState}
    (hout : OutputsSupport s' x)
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (h0 : s'.regs 0 = decOutBase N t) (h1 : s'.regs 1 = bl)
    (hframe : ∀ a : ℕ, decFrameBound N t ≤ a → s'.mem a = s.mem a)
    (hpad : C8R.HoldsVecPad E.W m xbase s y) (hxb : decFrameBound N t ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : decOutBase N t + bl ≤ 2 ^ E.W) :
    CrDecOut E xbase m (decOutBase N t) bl y S s' := by
  have h := crDecOut_of_exitF (B := decFrameBound N t)
    (decExitF_of_outputs hout hS h0 hframe h1) hS hpad hxb hWN hbl hbbbl
  simpa [decFrameBound] using h

/-! ## 3. The `hdec` slot and the `cr` field with the sharp bound -/

/-- **The `hdec` slot of `stageRun_crPipeline` from `CRS.hdecW`'s shape plus the frame lemma.** -/
theorem hdecIn_of_hdecW_frame_out {Sinit Srow Sdec Sassem Sres : Stmt} {E : RAMEnv} {N t : ℕ}
    {x : Fin N → ZMod 2} {xbase m bl : ℕ} {y : Fin (E.W * m) → ZMod 2} {S : Finset ℕ} {Tdec : ℝ}
    {Pre : RAMState → Prop}
    (hdecW : ∀ s : RAMState, s.pc = 0 → Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        OutputsSupport s' x ∧ s'.regs 0 = decOutBase N t)
    (hframe : DecMemFrame E (decFrameBound N t) decStmt Tdec)
    (hpre : ∀ s : RAMState, Pre s → C8R.HoldsVecPad E.W m xbase s y)
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (hblcard : bl = S.card)
    (hxb : decFrameBound N t ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : decOutBase N t + bl ≤ 2 ^ E.W) :
    ∀ s : RAMState, s.pc = 0 → Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        CrDecOut E xbase m (decOutBase N t) bl y S
          (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s') :=
  hdecIn_of_hdecW_frame (bb := decOutBase N t) (B := decFrameBound N t)
    hdecW hframe hpre hS hblcard hxb hWN hbl hbbbl

/-- **The `cr` field of Theorem 6.5 at Proposition 2.3's decoder**, with the estimate-payload frame
in its pre and the sharp frame bound.  Its merge step is `crMergeInD_of_upk`. -/
theorem stageRun_crSlot_out {Sinit Srow Sdec Sassem Sres : Stmt} {E : RAMEnv}
    {M Z xbase m ab bl ob al : ℕ} {y : Fin M → ZMod 2} {yest : Fin (E.W * m) → ZMod 2}
    {Lx : List ℕ} {S xhat : Finset ℕ} {Tdec : ℝ} {N t : ℕ} {x : Fin N → ZMod 2}
    (hdecW : ∀ s : RAMState, s.pc = 0 →
      CrStageInWzE E M Z y xbase m yest ab al (decOutBase N t) bl ob Lx
        (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        OutputsSupport s' x ∧ s'.regs 0 = decOutBase N t)
    (hframe : DecMemFrame E (decFrameBound N t) decStmt Tdec)
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (hblcard : bl = S.card)
    (hxhat : (packedSupp E.W m yest).toFinset = xhat)
    (hxdisj : xbase + m ≤ ab) (hEhab : ab + E.W * m + 1 < 2 ^ E.W)
    (hob : ob < 2 ^ E.W)
    (hdisj : decOutBase N t + bl ≤ ab ∨ ab + (m * E.W + 1) ≤ decOutBase N t)
    (hobig : ob + ((packedSupp E.W m yest).length + bl) + 1 < 2 ^ E.W)
    (hAob : ab + (packedSupp E.W m yest).length ≤ ob) (hBob : decOutBase N t + bl ≤ ob)
    (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W)
    (hxb : decFrameBound N t ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : decOutBase N t + bl ≤ 2 ^ E.W) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob)) E
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob))
      (Tdec + 5 + ((16 * (E.W * m) + 17 : ℕ) : ℝ) +
        RMR.mrgCost (packedSupp E.W m yest).length bl)
      (CrStageInWzE E M Z y xbase m yest ab al (decOutBase N t) bl ob Lx)
      (fun s' => OutListIs s' (symmDiff xhat S)) :=
  stageRun_crSlot (bb := decOutBase N t) (B := decFrameBound N t) (N := N) (x := x)
    (by
      intro s hpc hPre
      obtain ⟨s', hrun, hout, h0⟩ := hdecW s hpc hPre
      have hset : (outList s').toFinset = S := outList_toFinset_eq hout hS
      refine ⟨s', hrun, decExitF_of_outputs hout hS h0 (hframe s s' hrun) ?_⟩
      rw [regs_one_eq_card hout hset, ← hblcard])
    hS hxhat hxdisj hEhab hob hdisj hobig hAob hBob hW hWm hxb hWN hbl hbbbl

end CRS
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.CRS.crDecOut_of_hdecW_exit
#print axioms LinearSetReconciliation327.Main.CRS.hdecIn_of_hdecW_frame_out
#print axioms LinearSetReconciliation327.Main.CRS.stageRun_crSlot_out


