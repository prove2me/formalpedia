-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrSlotZ20261123
-- name    : LinearSetReconciliation327_Main_CrSlotZ20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T12:24:18.46721+00:00
-- url     : https://prove2.me/theorems/a3d12169-aebd-4870-8ca2-7db87b96e2c7
-- title:
--   The CrMergeIn half of hdec at the z addresses: stageRun_crPipelineZ
-- statement:
--   `stageRun_crPipeline` proves decoder ; setup ; unpack ; merge for the published program at `dCrBase`; Theorem 6.5 needs it for `zProgDecOfTop` at `zDCrBase = dCrBase + 2`. Since `StageRun` cannot be transported and the addresses are not definitionally equal as programs, this bundle re-proves the composition at the shifted addresses (`stageRun_crPipelineZ`), using the `At` facts of the `CrAtZ` bundle. Its merge step is `crMergeInD_of_upk`, so this is the `CrMergeIn` half of `hdec`: the setup and the unpack are composed, the unpack's repacked estimate becomes the merge's A-side list, and the stage ends in `OutListIs s' (x hat triangle e hat)`.
-- source:
--   arXiv:2611.11409 (Linear Set Reconciliation with O(d) Additive Redundancy), Theorem 6.5 / Proposition 2.3

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrAtZ20261123

/-!
# The `cr` merge half of `hdec` at the `z` addresses

`CRS.stageRun_crPipeline` proves decoder · `upkSetup` · the 31-instruction unpack · the merge for the
*published* program `progDecOfTop`, at `dCrBase`.  Theorem 6.5 needs it for the *dispatched* program
`RSD.zProgDecOfTop … Scr ell`, whose `cr` block sits at `zDCrBase = dCrBase + 2`.

`StageRun` records only the endpoint, so the published statement cannot be relocated
(`CrStage20261122`'s `step_window`/`iterate_window` do the per-step work, but no invariant bounds the
intermediate program counters).  This bundle therefore **re-proves** the composition at the shifted
addresses, using the `At` facts of `Def_…_CrAtZ20261123`.

Its merge step is `CRS.crMergeInD_of_upk`, so this is the `CrMergeIn` half of `hdec`: the setup and
unpack are composed, and the unpack's repacked estimate becomes the merge's `A`-side list.

Axiom-clean: only `Mathlib` and published `Definitions.Def_*` bundles are imported.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65F

open RSD
open CRS

/-- **Decoder · setup · unpack · merge at the `z` addresses.**

The decoder's half is the published exit contract `CrDecOut` (its `OutputsSupport` conclusion, the
output window, the payload frame and the window's word bound); the setup, the unpack and the merge
are the three published blocks, at `zDCrBase`, `zDCrBase + decStmt.len` and `+ 5`/`+ 5 + 31`. -/
theorem stageRun_crPipelineZ (Sinit Srow Sdec Sassem Sres : Stmt) (E : RAMEnv) (ell : ℕ)
    {xbase m ab bb bl ob : ℕ} {y : Fin (E.W * m) → ZMod 2} {S xhat : Finset ℕ} {Tdec : ℝ}
    {Pre : RAMState → Prop}
    (hdec : ∀ s : RAMState, s.pc = 0 →
      Pre (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        CrDecOut E xbase m bb bl y S
          (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len) s'))
    (hxhat : (packedSupp E.W m y).toFinset = xhat)
    (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W) (hxdisj : xbase + m ≤ ab)
    (hab : ab + E.W * m + 1 < 2 ^ E.W) (hbb : bb < 2 ^ E.W) (hbl : bl < 2 ^ E.W)
    (hob : ob < 2 ^ E.W) (hdisj : bb + bl ≤ ab ∨ ab + (m * E.W + 1) ≤ bb)
    (hobig : ob + ((packedSupp E.W m y).length + bl) + 1 < 2 ^ E.W)
    (hAob : ab + (packedSupp E.W m y).length ≤ ob) (hBob : bb + bl ≤ ob) :
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CrStage4 decStmt E.W xbase m ab ob) ell) E
      (zDCrBase Sinit Srow Sdec Sassem Sres ell)
      (zDEnd Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob) ell)
      (Tdec + 5 + ((16 * (E.W * m) + 17 : ℕ) : ℝ) +
        RMR.mrgCost (packedSupp E.W m y).length bl)
      Pre (fun s' => OutListIs s' (symmDiff xhat S)) := by
  intro t htpc hPre
  -- word bounds read off the block arithmetic
  have hxw : xbase < 2 ^ E.W := by omega
  have hmw : m < 2 ^ E.W := by omega
  have habw : ab < 2 ^ E.W := by omega
  have halw : (packedSupp E.W m y).length < 2 ^ E.W := by
    have := packedSupp_length_le E.W m y; omega
  have habal : ab + (packedSupp E.W m y).length ≤ 2 ^ E.W := by
    have := packedSupp_length_le E.W m y; omega
  -- 1. 2.3's decoder, relocated to `zDCrBase`
  obtain ⟨s1, ⟨k1, hk1, hrun1, hhalt1⟩, hD1⟩ :=
    hdec (withPc 0 t) rfl
      (by
        rw [show (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell) (withPc 0 t) : RAMState) = t
          from withPc_self htpc]
        exact hPre)
  have hhalt1' : s1.pc = decStmt.len := haltPc_of_haltFree decStmt_haltFree hhalt1
  obtain ⟨k1', hk1', hstep1⟩ := run_transport
    (G := RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob) ell)
    (S := decStmt) (base := zDCrBase Sinit Srow Sdec Sassem Sres ell) (T := Tdec)
    (s := withPc 0 t) (s' := s1)
    (zAt_crStage4_dec Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob ell)
    decStmt_noJump ⟨k1, hk1, hrun1, hhalt1⟩ rfl hhalt1'
  have hs1 : (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell) (withPc 0 t) : RAMState) = t :=
    withPc_self htpc
  rw [hs1] at hstep1
  -- 2. the setup, with its (empty) memory footprint
  obtain ⟨h0, h1, hpad, hnd, hset, hval, hblw, hbbbl⟩ := hD1
  obtain ⟨-, k2, s2, hstep2, hpc2, hk2, hs2⟩ := by
    have := Sem.block
      (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob) ell) E
      (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len) (upkSetup E.W xbase m ab ob)
      (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len) s1)
      (zAt_crStage4_setup Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob ell)
      (upkSetup_noBranch _ _ _ _ _) rfl
    rwa [upkSetup_length] at this
  have hs2' : s2 = upkSetupSt E xbase m ab ob
      (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len + 5) s1) := by
    rw [hs2]
    have h := upkSetup_run E (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len)
      (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len) s1) xbase m ab ob
      hxw habw hob hmw
    simpa only [withPc] using h
  have hs2mem : s2.mem = s1.mem := by
    rw [hs2']
    rfl
  have hIn2 : UpkIn E xbase m ab bb bl ob y s2 := by
    rw [hs2']
    refine ⟨?_, ?_, upkSetupSt_r2 E xbase m ab ob _, upkSetupSt_r3 E xbase m ab ob _,
      upkSetupSt_r4 E xbase m ab ob _, upkSetupSt_r5 E xbase m ab ob _,
      upkSetupSt_r6 E xbase m ab ob _,
      holdsVecPad_congr_mem (by rfl :
        (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len) s1).mem
          = (upkSetupSt E xbase m ab ob
              (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len + 5) s1)).mem) hpad⟩
    · rw [upkSetupSt_r0]; exact h0
    · rw [upkSetupSt_r1]; exact h1
  -- 3. the unpack, with its memory footprint
  obtain ⟨s3, ⟨k3, hk3, hrun3, hhalt3⟩, hOut3, hmem3⟩ :=
    upk_halts_frame E xbase m ab bb bl ob y (withPc 0 s2) hIn2 rfl hW hWm hxdisj hab hbb hbl hob
  have hhalt3' : s3.pc = upkStmt.len := haltPc_of_haltFree upkStmt_haltFreeB hhalt3
  obtain ⟨k3', hk3', hstep3⟩ := run_transport
    (G := RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob) ell)
    (S := upkStmt) (base := zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len + 5)
    (T := ((16 * (E.W * m) + 17 : ℕ) : ℝ)) (s := withPc 0 s2) (s' := s3)
    (zAt_crStage4_upk Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob ell)
    upkStmt_noJumpB ⟨k3, hk3, hrun3, hhalt3⟩ rfl hhalt3'
  have hs3 : (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len + 5)
      (withPc 0 s2) : RAMState) = s2 := withPc_self hpc2
  rw [hs3] at hstep3
  -- 4. the merge
  have hmem31 : s3.mem = upkMem E.W xbase s1.mem ab (E.W * m) := by
    have h3 := hmem3
    have h2 : (withPc 0 s2).mem = s1.mem := by
      show s2.mem = s1.mem
      exact hs2mem
    rw [h3, h2]
  obtain ⟨him, -⟩ : CrMergeInD E ab (packedSupp E.W m y).length bb bl ob m
      (packedSupp E.W m y) S
      (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len + 5 + 31) s3)
      ∧ True :=
    ⟨crMergeInD_of_upk (s := s1) (E := E) (xbase := xbase) (m := m) (ab := ab) (bb := bb)
      (bl := bl) (ob := ob) (y := y) (S := S) hOut3 hmem31 h0 h1 hnd hset hval hWm hdisj
      halw habal hblw hbbbl hobig hAob hBob, trivial⟩
  obtain ⟨k4, s4, hk4, hstep4, hpc4, hpost⟩ :=
    stageRun_mergeAtD (G := RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CrStage4 decStmt E.W xbase m ab ob) ell)
      (E := E) (base := zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len + 5 + 31)
      (ab := ab) (al := (packedSupp E.W m y).length) (bb := bb) (bl := bl) (ob := ob) (m := m)
      (Lx := packedSupp E.W m y) (S := S) (xhat := xhat)
      (zAt_crStage4_mrg Sinit Srow Sdec Sassem Sres decStmt E.W xbase m ab ob ell) hW hxhat
      (withPc (zDCrBase Sinit Srow Sdec Sassem Sres ell + decStmt.len + 5 + 31) s3) rfl him
  -- 5. glue the four runs
  refine ⟨k1' + k2 + k3' + k4, s4, ?_, ?_, ?_, hpost⟩
  · have e1 : (k1' : ℝ) ≤ Tdec := hk1'
    have e2 : (k2 : ℝ) ≤ 5 := by rw [hk2]; norm_num
    have e3 : (k3' : ℝ) ≤ ((16 * (E.W * m) + 17 : ℕ) : ℝ) := hk3'
    have e4 : (k4 : ℝ) ≤ RMR.mrgCost (packedSupp E.W m y).length bl := hk4
    have hcast : ((k1' + k2 + k3' + k4 : ℕ) : ℝ)
        = (k1' : ℝ) + (k2 : ℝ) + (k3' : ℝ) + (k4 : ℝ) := by push_cast; ring
    rw [hcast]; linarith
  · rw [upkStmt_len] at hstep3
    rw [show k1' + k2 + k3' + k4 = k4 + (k3' + (k2 + k1')) from by omega,
      Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      hstep1, hstep2, hstep3, hstep4]
  · rw [hpc4, zDEnd_crStage4, RMR.mrgStmtFull_len]
    try omega

end W65F
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.W65F.stageRun_crPipelineZ


