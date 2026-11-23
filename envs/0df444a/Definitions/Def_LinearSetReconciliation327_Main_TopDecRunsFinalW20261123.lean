-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsFinalW20261123
-- name    : LinearSetReconciliation327_Main_TopDecRunsFinalW20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T11:02:12.334734+00:00
-- url     : https://prove2.me/theorems/03f7b1a1-7077-46a6-b82a-a1b5ed9e7e9c
-- title:
--   Theorem 6.5: the six decoder fields with no memory frame
-- statement:
--   Theorem 6.5's six decoder-stage fields, restated about the dispatched program with **no memory-frame parameter**.  The previous version of the structure had to thread a frame predicate `MemInv` through the prologue, row, column and assembly stages, because the residual stage's postcondition pinned the whole infinite memory.  Replacing that postcondition by the finite window pin of `CrStageInW20261123` removes the parameter entirely: the prologue lands on the row entry state, the row stage exits with the two counters at `d` and the column payload layout, the column stage exits with both counters at `ell`, the assembly and residual stages start and end in the window pin, and the `CR` stage runs Proposition 2.3's decoder, setup, unpack and merge from the window pin to the symmetric difference of the estimate and the decoded residual.  The bundle proves the assembly rule in this frame-free signature, re-derives the halting conjunct from the six fields, records that the residual field is satisfiable (its identity run, with a non-degenerate model in which the payload is non-zero and memory past the window is arbitrary), and proves the exact two-instruction address relocation of the assembly, residual, `CR` and final-halt addresses.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1; the project's published `TopDecRunsFinal20261123`, `CrStage20261122`, `CrPipeline20261122` and the new `CrStageInW20261123` bundle.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsFinal20261123
import Definitions.Def_LinearSetReconciliation327_Main_CrStageInW20261123

/-!
# `TopDecRunsFinalW`: the corrected six fields with **no memory frame**

The published `W65F.TopDecRunsFinal` carries a parameter `MemInv : (ℕ → ℕ) → Prop` and threads it
through `init → row → col → as`, because its `res` field posted the whole-memory `CrStageIn` and no
finite run can restore an infinite tail of zeros.

With the **window pin** `CRS.CrStageInW` (bundle `CrStageInW20261123`) the frame parameter is gone:

* `init` posts `RSD.zRowIn` (no frame);
* `row` posts `ZRowPostW` = `r1 = d ∧ r2 = d ∧ CwPay` (no frame; `CwPay` is the payload layout the
  column loop really consumes, a memory *predicate*, not a frame);
* `col` posts `r1 = ℓ ∧ r2 = ℓ` — exactly the published `W65C.zColStageRun_wrap`'s post;
* `as` posts, and `res`/`cr` pre- and post-, the window pin `CrStageInW`.

Contents:

* `ZRowPostW` and `dispatch_bridgeW` — the row post and the two-instruction dispatch, frame-free;
* `TopDecRunsFinalW` — the six fields, no `MemInv`;
* `topDecRunsFinalW_of_stages` — the assembly rule (**this is the re-proved
  `topDecRunsFinal_of_stages` in the weakened signature: six MemInv-free stage statements in, the
  structure out**; no `MemInv` argument at all);
* `topDecRunsFinalW_haltsWithin` — conjunct 7 from it;
* the `res`-field satisfiability facts: the identity stage at the window pin, its non-degenerate
  model, and the `as → res` chain that closes with no frame.

No holes and no new axiom, nothing from `Solutions.*`.
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

/-! ## 1. The frame-free row post and the dispatch -/

/-- **The row loop's exit, without a memory frame**: `r1 = d`, `r2 = d`, and the payload layout the
column loop consumes. -/
def ZRowPostW (E : RAMEnv) (d ell M : ℕ) (y : Fin M → ZMod 2) (β0 ms : ℕ)
    (s : RAMState) : Prop :=
  s.regs 1 = d ∧ s.regs 2 = d ∧ CwPay E ell M y β0 ms s

/-- **The dispatch, frame-free.**  `r1 := 0; r2 := ℓ` establishes the column loop's entry from the
row loop's exit, and touches no memory, so the payload layout survives.  (The published
`dispatch_bridge` is this statement with an extra `MemInv s.mem` conjunct in both pre and post.) -/
theorem dispatch_bridgeW {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {d ℓ M β0 ms : ℕ} {y : Fin M → ZMod 2}
    (hW : 1 < 2 ^ E.W) (hell : ℓ < 2 ^ E.W) :
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDColBase Sinit Srow) (RSD.zDColHead Sinit Srow ℓ) 2
      (ZRowPostW E d ℓ M y β0 ms)
      (fun s => W65C.cwInv E ℓ M y β0 ms 0 s) := by
  intro s hpc hpre
  obtain ⟨-, k, z, hstep, hpcZ, hQ⟩ :=
    RSD.zDispatch_ColIn (P := RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ)
      (pc := RSD.zDColBase Sinit Srow) (ell := ℓ) (s := s)
      (RSD.zAt_dispatch_codeD Sinit Srow Sdec Sassem Sres Scr ℓ) hpc hW hell
  obtain ⟨hk, hcol, hm⟩ := hQ
  obtain ⟨h1, h2, hpay⟩ := hpre
  refine ⟨k, z, ?_, hstep, by rw [hpcZ]; rfl, ?_⟩
  · rw [hk]; norm_num
  · refine ⟨hcol.1, hcol.2, ?_⟩
    intro r hr q hq
    rw [hm]
    exact hpay r hr q hq

/-! ## 2. The structure -/

/-- **Theorem 6.5's six decoder fields about `zProgDecOfTop`, with no memory frame parameter.**

Every field's pre and post is a predicate on finitely many registers and on the finite windows the
blocks read; in particular the `as`/`res`/`cr` fields use the window pin `CRS.CrStageInW`, so the
`res` pre is satisfiable and nothing has to be threaded through `init → row → col → as`. -/
structure TopDecRunsFinalW (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv)
    (W M n d ℓ β0 ms : ℕ) (Tini Trow Tdec Tas Tres Tcr : ℝ) (ab al bb bl ob : ℕ)
    (Lx : List ℕ) (S xhat : Finset ℕ) (Mrow : ℕ → ℕ → ℕ) : Prop where
  /-- The prologue: read `d`, `ℓ`, `wordsOf` from the header, clear the header registers. -/
  init : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0 (RSD.zDRowBase Sinit) Tini
      (fun s => s = decoderStart W y [])
      (fun s => RSD.zRowIn Sinit E d Mrow s)
  /-- Row decoding: `d` iterations of `proposition_2_1`, post `r1 = d ∧ r2 = d ∧ CwPay`. -/
  row : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDRowBase Sinit) (RSD.zDColBase Sinit Srow) Trow
      (fun s => RSD.zRowIn Sinit E d Mrow s)
      (ZRowPostW E d ℓ M y β0 ms)
  /-- The `ℓ` child decoders of `theorem_5_1`, from `cwInv` to `r1 = r2 = ℓ`. -/
  col : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDColHead Sinit Srow ℓ) (RSD.zDAsBase Sinit Srow Sdec ℓ) Tdec
      (fun s => W65C.cwInv E ℓ M y β0 ms 0 s)
      (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ)
  /-- Prefix assembly: from the column exit to the **window-pinned** `cr` entry. -/
  as : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDAsBase Sinit Srow Sdec ℓ) (zDResBase Sinit Srow Sdec Sassem ℓ) Tas
      (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ)
      (CRS.CrStageInW E M y ab al bb bl ob Lx)
  /-- **The residual stage, satisfiable**: its pre and post are the *same* finite window pin, so the
  stage exists (the identity run does it; the real `Sres` also writes only that window). -/
  res : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (zDResBase Sinit Srow Sdec Sassem ℓ) (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) Tres
      (CRS.CrStageInW E M y ab al bb bl ob Lx) (CRS.CrStageInW E M y ab al bb bl ob Lx)
  /-- The `cr` stage: 2.3's decoder · setup · unpack · merge from the window pin to `x̂ △ ê`. -/
  cr : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) (zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ) Tcr
      (CRS.CrStageInW E M y ab al bb bl ob Lx)
      (fun s' => CRS.OutListIs s' (symmDiff xhat S))

/-! ## 3. The assembly rule (the re-proved `topDecRunsFinal_of_stages`) -/

/-- **`TopDecRunsFinalW` from its six stage statements — with no `MemInv` parameter.**

This is the repaired `topDecRunsFinal_of_stages`: the six MemInv-free stage contracts in, the
structure out.  Nothing about a memory frame appears in the statement or the proof. -/
theorem topDecRunsFinalW_of_stages {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ β0 ms : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {S xhat : Finset ℕ} {Mrow : ℕ → ℕ → ℕ}
    (hinit : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0 (RSD.zDRowBase Sinit) Tini
        (fun s => s = decoderStart W y [])
        (fun s => RSD.zRowIn Sinit E d Mrow s))
    (hrow : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (RSD.zDRowBase Sinit) (RSD.zDColBase Sinit Srow) Trow
        (fun s => RSD.zRowIn Sinit E d Mrow s)
        (ZRowPostW E d ℓ M y β0 ms))
    (hcol : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (RSD.zDColHead Sinit Srow ℓ) (RSD.zDAsBase Sinit Srow Sdec ℓ) Tdec
        (fun s => W65C.cwInv E ℓ M y β0 ms 0 s)
        (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ))
    (has : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (RSD.zDAsBase Sinit Srow Sdec ℓ) (zDResBase Sinit Srow Sdec Sassem ℓ) Tas
        (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ)
        (CRS.CrStageInW E M y ab al bb bl ob Lx))
    (hres : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (zDResBase Sinit Srow Sdec Sassem ℓ) (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) Tres
        (CRS.CrStageInW E M y ab al bb bl ob Lx) (CRS.CrStageInW E M y ab al bb bl ob Lx))
    (hcr : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) (zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ) Tcr
        (CRS.CrStageInW E M y ab al bb bl ob Lx)
        (fun s' => CRS.OutListIs s' (symmDiff xhat S))) :
    TopDecRunsFinalW Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ β0 ms
      Tini Trow Tdec Tas Tres Tcr ab al bb bl ob Lx S xhat Mrow :=
  ⟨hinit, hrow, hcol, has, hres, hcr⟩

/-! ## 4. Conjunct 7 from the six fields -/

/-- **Conjunct 7 (`haltsWithin_topDec`) from the six frame-free fields.** -/
theorem topDecRunsFinalW_haltsWithin {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ β0 ms : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {S xhat : Finset ℕ} {Mrow : ℕ → ℕ → ℕ}
    (h : TopDecRunsFinalW Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ β0 ms
      Tini Trow Tdec Tas Tres Tcr ab al bb bl ob Lx S xhat Mrow)
    (hW : 1 < 2 ^ E.W) (hell : ℓ < 2 ^ E.W) (y : Fin M → ZMod 2) :
    ∃ s' : RAMState,
      HaltsWithin (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (Tini + Trow + 2 + Tdec + Tas + Tres + Tcr) (decoderStart W y []) s' := by
  have hIR : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (RSD.zDColBase Sinit Srow) (Tini + Trow)
      (fun s => s = decoderStart W y []) (ZRowPostW E d ℓ M y β0 ms) :=
    (h.init y).trans (h.row y)
  have hIRD : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (RSD.zDColHead Sinit Srow ℓ) (Tini + Trow + 2)
      (fun s => s = decoderStart W y [])
      (fun s => W65C.cwInv E ℓ M y β0 ms 0 s) :=
    hIR.trans (dispatch_bridgeW (Sinit := Sinit) (Srow := Srow) (Sdec := Sdec)
      (Sassem := Sassem) (Sres := Sres) (Scr := Scr) (E := E) (d := d) (ℓ := ℓ) (M := M)
      (β0 := β0) (ms := ms) (y := y) hW hell)
  have hIRDC : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (RSD.zDAsBase Sinit Srow Sdec ℓ) (Tini + Trow + 2 + Tdec)
      (fun s => s = decoderStart W y []) (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ) :=
    hIRD.trans (h.col y)
  have hIRDCA : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (zDResBase Sinit Srow Sdec Sassem ℓ) (Tini + Trow + 2 + Tdec + Tas)
      (fun s => s = decoderStart W y []) (CRS.CrStageInW E M y ab al bb bl ob Lx) :=
    hIRDC.trans (h.as y)
  have hIRDCAR : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) (Tini + Trow + 2 + Tdec + Tas + Tres)
      (fun s => s = decoderStart W y []) (CRS.CrStageInW E M y ab al bb bl ob Lx) :=
    hIRDCA.trans (h.res y)
  have hstep : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ)
      (Tini + Trow + 2 + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart W y []) (fun _ => True) :=
    hIRDCAR.trans (C8R.stageRun_post (h.cr y) (fun _ _ => trivial))
  obtain ⟨k, s', hk, hrun, hpc, -⟩ :=
    hstep (decoderStart W y []) rfl rfl
  have hlen := zDEnd_eq_compile Sinit Srow Sdec Sassem Sres Scr ℓ
  have hhalt :
      (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ)[zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ]? =
        some Instr.halt := by
    rw [hlen]
    rw [show RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ =
      (RSD.zTopDecStmt Sinit Srow Sdec Sassem Sres Scr ℓ).compile 0 ++ [Instr.halt] from rfl,
      List.getElem?_append_right (le_refl _)]
    simp
  exact ⟨s', k, by simpa using hk, hrun, by simp only [Halted, hpc, hhalt]⟩

/-! ## 5. The `res` field: the identity stage at the window pin, non-degenerately -/

/-- Any predicate is a `0`-step stage from itself to itself. -/
theorem stageRun_refl_zero {P : Program} {E : RAMEnv} {a : ℕ} {I : RAMState → Prop} :
    StageRun P E a a 0 I I := by
  intro s hpc hI
  exact ⟨0, s, by norm_num, rfl, hpc, hI⟩

/-- **The `res` field statement is satisfiable and its pre is not a singleton.**  With the window pin
the identity run is a `res` field, and its precondition has a model whose word
`wordsOf 8 8 + 1` is `1` — impossible for the old whole-memory `CrStageIn`. -/
theorem resField_nonvacuous :
    (∃ s : RAMState, CRS.CrStageInW CRS.E8 8 CRS.y8 10 1 20 1 40 [5] s ∧
        s.mem (wordsOf 8 8 + 1) = 1) ∧
      (∀ (P : Program) (E : RAMEnv) (a : ℕ),
        StageRun P E a a 0 (CRS.CrStageInW CRS.E8 8 CRS.y8 10 1 20 1 40 [5])
          (CRS.CrStageInW CRS.E8 8 CRS.y8 10 1 20 1 40 [5])) :=
  ⟨CRS.crStageInW_nondegen_concrete, fun P E a => stageRun_refl_zero⟩

/-- **The `as → res` chain closes with no memory frame.**  Given the assembly stage ending in the
window pin, the residual field is the identity stage on that pin, so the two fields compose and no
`MemInv` appears anywhere. -/
theorem as_res_chain_noMemInv {P : Program} {E : RAMEnv} {a b : ℕ} {Tas : ℝ}
    {I : RAMState → Prop} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ}
    (has : StageRun P E a b Tas I (CRS.CrStageInW E M y ab al bb bl ob Lx)) :
    StageRun P E a b (Tas + 0) I (CRS.CrStageInW E M y ab al bb bl ob Lx) := by
  simpa using has.trans (stageRun_refl_zero (P := P) (E := E) (a := b)
    (I := CRS.CrStageInW E M y ab al bb bl ob Lx))

/-! ## 6. The `+2` address relocation, arithmetically -/

/-- The dispatch block is two instructions. -/
theorem zDispatch_len (ell : ℕ) : (RSD.zDispatch ell).len = 2 := rfl

/-- `zDColBase` is exactly the published `dColBase`: the dispatch is inserted *at* it. -/
theorem zDColBase_eq_dColBase (Sinit Srow : Stmt) :
    RSD.zDColBase Sinit Srow = dColBase Sinit Srow := by
  simp [RSD.zDColBase, RSD.zDRowBase, dColBase, dRowBase]

/-- The column loop head is `dColBase + 2`. -/
theorem zDColHead_eq (Sinit Srow : Stmt) (ell : ℕ) :
    RSD.zDColHead Sinit Srow ell = dColBase Sinit Srow + 2 := by
  simp [RSD.zDColHead, zDColBase_eq_dColBase, zDispatch_len]

/-- **The assembly sits two instructions after its published address.** -/
theorem zDAsBase_eq (Sinit Srow Sdec : Stmt) (ell : ℕ) :
    RSD.zDAsBase Sinit Srow Sdec ell = dAsBase Sinit Srow Sdec + 2 := by
  simp only [RSD.zDAsBase, zDColHead_eq, dAsBase, Stmt.len]
  omega

/-- **The residual stage sits two instructions after its published address.** -/
theorem zDResBase_eq (Sinit Srow Sdec Sassem : Stmt) (ell : ℕ) :
    zDResBase Sinit Srow Sdec Sassem ell = dResBase Sinit Srow Sdec Sassem + 2 := by
  simp only [zDResBase, zDAsBase_eq, dResBase]
  omega

/-- **The `CR` call sits two instructions after its published address.** -/
theorem zDCrBase_eq (Sinit Srow Sdec Sassem Sres : Stmt) (ell : ℕ) :
    zDCrBase Sinit Srow Sdec Sassem Sres ell = dCrBase Sinit Srow Sdec Sassem Sres + 2 := by
  simp only [zDCrBase, zDResBase_eq, dCrBase]
  omega

/-- **The trailing `halt` sits two instructions after its published address.** -/
theorem zDEnd_eq (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    zDEnd Sinit Srow Sdec Sassem Sres Scr ell = dEnd Sinit Srow Sdec Sassem Sres Scr + 2 := by
  simp only [zDEnd, zDCrBase_eq, dEnd]
  omega

end W65F
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.W65F.dispatch_bridgeW
#print axioms LinearSetReconciliation327.Main.W65F.topDecRunsFinalW_of_stages
#print axioms LinearSetReconciliation327.Main.W65F.topDecRunsFinalW_haltsWithin
#print axioms LinearSetReconciliation327.Main.W65F.resField_nonvacuous
#print axioms LinearSetReconciliation327.Main.W65F.as_res_chain_noMemInv
#print axioms LinearSetReconciliation327.Main.W65F.zDAsBase_eq
#print axioms LinearSetReconciliation327.Main.W65F.zDResBase_eq
#print axioms LinearSetReconciliation327.Main.W65F.zDCrBase_eq
#print axioms LinearSetReconciliation327.Main.W65F.zDEnd_eq


