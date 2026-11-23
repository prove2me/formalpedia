-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_ResReset20261123
-- name    : LinearSetReconciliation327_Main_ResReset20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T12:09:04.770377+00:00
-- url     : https://prove2.me/theorems/48007f87-68a5-4511-b1d4-359e5dbbe077
-- title:
--   The sixteen-register reset block: resReset and its StageRun
-- statement:
--   `CrStageInW`/`CrStageInWz` pin all sixteen registers to `decoderStart E.W y []`'s register file (`r0 = 0`, `r1 = wordsOf E.W M`, `r2 = ... = r15 = 0`), but the published residual stage `stageRun_resP` only sets `r0, r1, r2`. This bundle supplies the missing piece as an interface: the sixteen-instruction reset `resReset Wo` (`r0 := 0; r1 := Wo; r2 := ... := r15 := 0`), the exact `runBlock` equation (`resReset_run`: the register file becomes `resRegs Wo`, memory untouched), and the `StageRun` (`stageRun_resReset`, 16 steps, precondition `True`), together with `stageRun_resReset_crStageIn_regs`, which establishes the full sixteen-register conjunct of the `cr` pre from an arbitrary incoming register file. This is the parametric form of the model's `Model.resetStmt`.
-- source:
--   arXiv:2611.11409 (Linear Set Reconciliation with O(d) Additive Redundancy), Theorem 6.5 / Proposition 2.3

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStageInWz20261123

/-!
# The sixteen-register reset block (Theorem 6.5, residual item 4)

`CrStageInW`/`CrStageInWz` pin **all sixteen** registers to `decoderStart E.W y []`'s register file

```
r0 = 0,  r1 = wordsOf E.W M,  r2 = 0,  r3 = … = r15 = 0,
```

but the published residual stage `C8R.stageRun_resP` only sets `r0, r1, r2` (through
`DecInputOn E.W M 0 …`: `r0 = 0`, `r1 = wordsOf E.W M`, `r2 = 0`).  The remaining thirteen
registers are whatever the residual block's `xorStmt`/`epilogue` left there.

This bundle supplies the missing piece as an interface: a **sixteen-instruction reset**
`resReset Wo` (`r0 := 0; r1 := Wo; r2 := 0; r3 := 0; …; r15 := 0`) and its `StageRun`, which
establishes the *whole* register file of `decoderStart` from an arbitrary one — no memory is touched,
so every memory conjunct of the `cr` pre survives it.

This is the parametric form of the model's `Model.resetStmt` (`TopDecRunsFinalModel20261123`), which
is the same block at the concrete `Wo = 1`.

Axiom-clean: the only imports are `Mathlib` and a published `Definitions.Def_*` bundle.
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

/-! ## 1. The block and its shape -/

/-- **The sixteen-instruction register reset.**  `r0 := 0`, `r1 := Wo`, `r2 := 0`, and `r3 … r15 := 0`
— exactly `decoderStart`'s register file when `Wo = wordsOf E.W M`. -/
def resReset (Wo : ℕ) : List Instr :=
  [iImm r0 0, iImm r1 Wo, iImm r2 0, iImm r3 0, iImm r4 0, iImm r5 0, iImm r6 0, iImm r7 0,
   iImm r8 0, iImm r9 0, iImm r10 0, iImm r11 0, iImm r12 0, iImm r13 0, iImm r14 0, iImm r15 0]

/-- The reset as a `Stmt`. -/
abbrev resResetStmt (Wo : ℕ) : Stmt := .code (resReset Wo)

theorem resReset_len (Wo : ℕ) : (resReset Wo).length = 16 := rfl

theorem resResetStmt_len (Wo : ℕ) : (resResetStmt Wo).len = 16 := rfl

theorem resResetStmt_compile (Wo : ℕ) (base : ℕ) :
    (resResetStmt Wo).compile base = resReset Wo := rfl

theorem resReset_noBranch (Wo : ℕ) : NoBranch (resReset Wo) := by
  simp [resReset, NoBranch, Instr.NoBranchI]

theorem resResetStmt_noJump (Wo : ℕ) : sNoJumpB (resResetStmt Wo) = true := rfl

theorem resResetStmt_haltFree (Wo : ℕ) : sHaltFreeB (resResetStmt Wo) = true := rfl

/-- The register file `resReset Wo` produces. -/
def resRegs (Wo : ℕ) : Fin 16 → ℕ := fun i => if i = r1 then Wo else 0

/-! ## 2. `decoderStart`'s register file is `resRegs (wordsOf E.W M)` -/

theorem decoderStart_regs_eq (E : RAMEnv) {M : ℕ} (y : Fin M → ZMod 2) :
    (decoderStart E.W y []).regs = resRegs (wordsOf E.W M) := by
  funext i
  fin_cases i <;> simp [decoderStart, initState, resRegs]

/-- The same, in the shape the reset's `StageRun` states it. -/
theorem decoderStart_regs_eq_of {E : RAMEnv} {M : ℕ} (y : Fin M → ZMod 2) {Wo : ℕ}
    (h : Wo = wordsOf E.W M) :
    (decoderStart E.W y []).regs = resRegs Wo := by
  rw [decoderStart_regs_eq, h]

/-! ## 3. The run

`runBlock (resReset Wo) E {s with pc := k}` is `s` with the register file replaced by `resRegs Wo`
(and the program counter advanced by sixteen).  Memory and the incoming register values are
irrelevant: every instruction is an immediate load. -/

theorem resReset_run (E : RAMEnv) (Wo k : ℕ) (s : RAMState) (hWo : Wo < 2 ^ E.W) :
    runBlock (resReset Wo) E { s with pc := k }
      = { s with pc := k + 16, regs := resRegs Wo } := by
  apply ramState_eq_of
  · rw [runBlock_pc _ E _ (resReset_noBranch Wo)]
    simp [resReset_len]
  · rfl
  · intro d
    fin_cases d <;>
      simp [resReset, resRegs, runBlock_cons, runBlock_nil, execInstr, Function.update_self,
        Function.update_of_ne, Nat.mod_eq_of_lt hWo, Nat.mod_eq_of_lt (show 0 < 2 ^ E.W from
          Nat.two_pow_pos E.W), Fin.ext_iff, Fin.zero_eta, Fin.mk_one]

/-! ## 4. The stage -/

/-- **The reset as a `StageRun`**: sixteen steps from any state to one whose register file is
`resRegs Wo`.  The precondition is `True`: the block is unconditional, and it touches no memory. -/
theorem stageRun_resReset {G : Program} {E : RAMEnv} {base Wo : ℕ}
    (hAt : At G base (resReset Wo)) (hWo : Wo < 2 ^ E.W) :
    StageRun G E base (base + 16) (16 : ℝ) (fun _ => True) (fun s => s.regs = resRegs Wo) := by
  intro s hpc _
  have hb := Sem.block G E base (resReset Wo) s hAt (resReset_noBranch Wo) hpc
  rw [resReset_len] at hb
  obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ := hb
  refine ⟨k, s', by rw [hk]; norm_num, hstep, hpc', ?_⟩
  have hrun : runBlock (resReset Wo) E s = { s with pc := base + 16, regs := resRegs Wo } := by
    have h2 := resReset_run E Wo base s hWo
    rw [withPc_self hpc] at h2
    exact h2
  rw [hs', hrun]

/-- **The reset establishes the full sixteen-register conjunct of `CrStageInW`** (and hence of
`CrStageInWz` / `CrStageInWzE`), from an arbitrary incoming register file. -/
theorem stageRun_resReset_crStageIn_regs {G : Program} {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2}
    {base : ℕ} (hAt : At G base (resReset (wordsOf E.W M)))
    (hWo : wordsOf E.W M < 2 ^ E.W) :
    StageRun G E base (base + 16) (16 : ℝ) (fun _ => True)
      (fun s => s.regs = (decoderStart E.W y []).regs) := by
  refine stageRun_post (stageRun_resReset (E := E) (base := base)
    (Wo := wordsOf E.W M) hAt hWo) (fun s h => ?_)
  rw [h, decoderStart_regs_eq]

end CRS
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.CRS.decoderStart_regs_eq
#print axioms LinearSetReconciliation327.Main.CRS.resReset_run
#print axioms LinearSetReconciliation327.Main.CRS.stageRun_resReset
#print axioms LinearSetReconciliation327.Main.CRS.stageRun_resReset_crStageIn_regs


