-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_20
-- name    : LinearSetReconciliation327_Main_B65_20
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T03:14:28.055566+00:00
-- url     : https://prove2.me/theorems/ca8ced4c-cf0a-4a2a-8069-6a487c7a5f3a
-- title:
--   Theorem 6.5 dependency bundle 20
-- statement:
--   Theorem 6.5 dependency bundle 20
-- source:
--   arXiv:2611.11409, Theorem 6.5 dependency closure (bundled for publication).

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_B65_18
set_option autoImplicit false

section S_P21ReadFor6520261123
/-!
# Proposition 2.1's read stage: bounded zero **and** the weakened `det` contract

The published `Definitions.Def_..._P21BndRead20261122` re-derives the read stage
(`inputSavedProcedure`, 110 instructions) at a memory that is only zero *inside* the decoder's
scratch, but it keeps `hdet : E.det = detStd t N b iota`.  The row body of Theorem 6.5 needs the
same environment to carry its own header (`det 15 = payTab`, `det 16 = stageBase`, ...), so the
`det` half must be the weakened `DetAgrees` contract of `Definitions.Def_..._P21DetFront20261121`.

This bundle is the published stage text with the four `hdet` binders re-pointed:

* `hdet : E.det = detStd t N b iota`  ->  `hdet : DetAgrees E t N b iota`;
* `rw [hdet, detStd_hdr t N w b iota (by norm_num : k < 13), ...]`
    ->  `rw [hdet.1 k (by decide), detStd_hdr t N w b iota (by norm_num : k < 13), ...]`;
* `rw [hdet, detStd_sq t N w b iota (enc_lt b _), hW]`
    ->  `rw [hdet.2 _ (by have h := detMulBase_le_detSqBase w; omega), detStd_sq ...]`.

Everything else — the mask `maskMem`, the masked loops, the frame above `decoderAllocEnd t` — is
byte-identical to the published masked re-derivation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Finset Polynomial

namespace LinearSetReconciliation327.Main

namespace P21DetBnd

/-! ## The read stage at a memory that is zero only inside the workspace

The decoder stages keep their whole workspace in `[0, decoderAllocEnd t)`.  The published read
contract (`pinsketch_decoder_read`) is however stated at the *globally* zero memory
`hintMem (8w) y []`, because the copy-in of `pinsketchRunStmt` builds that memory exactly.  The row
loop of Theorem 6.5 only ever clears its own scratch, so here we re-run the same read stage from an
ambient memory `m` that merely agrees with `hintMem` on `[0, decoderAllocEnd t)`.

The device that makes the port mechanical is the mask

  `maskMem N c m a = if a < N then c a else m a`

with `N = decoderAllocEnd t`: every memory the stage builds is `maskMem` applied to the canonical
`readMem`/`expandMem`, and every `if` is discharged by the static layout bound
`S0 + 2t ≤ decoderAllocEnd t`.  The stage therefore *cannot* disturb anything at or above
`decoderAllocEnd t`, which is exactly the frame the row loop needs. -/

section BoundedRead

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- `maskMem N c m` is `c` below `N` and the ambient memory `m` at and above `N`. -/
def maskMem (N : ℕ) (c m : ℕ → ℕ) : ℕ → ℕ := fun a => if a < N then c a else m a

theorem maskMem_lt {N : ℕ} {c m : ℕ → ℕ} {a : ℕ} (h : a < N) : maskMem N c m a = c a :=
  if_pos h

theorem maskMem_ge {N : ℕ} {c m : ℕ → ℕ} {a : ℕ} (h : N ≤ a) : maskMem N c m a = m a :=
  if_neg (by omega)

theorem maskMem_update {N : ℕ} {c m : ℕ → ℕ} {a v : ℕ} (h : a < N) :
    maskMem N (Function.update c a v) m = Function.update (maskMem N c m) a v := by
  funext x
  by_cases hx : x = a
  · subst hx
    rw [maskMem_lt h, Function.update_self, Function.update_self]
  · by_cases hN : x < N
    · rw [maskMem_lt hN, Function.update_of_ne hx, Function.update_of_ne hx, maskMem_lt hN]
    · rw [maskMem_ge (show N ≤ x by omega), Function.update_of_ne hx,
        maskMem_ge (show N ≤ x by omega)]

/-- The payload never needs more words than there are syndrome coordinates. -/
theorem frontBound {S0 t : ℕ} (hS0 : S0 ≤ t) : S0 + 2 * t ≤ decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  omega

/-- The saved-syndrome block ends inside the decoder's scratch. -/
theorem savedBase_le_allocEnd (t : ℕ) : decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  unfold decoderSavedBase
  omega

/-- The syndrome-polynomial block `[decoderSavedBase t, decoderSavedBase t + decoderCapacity t)`
ends inside the decoder's scratch. -/
theorem savedCapBound (t j : ℕ) (hj : j < decoderCapacity t) :
    decoderSavedBase t + j < decoderAllocEnd t := by
  rw [decoderAllocEnd_eq]
  unfold decoderSavedBase
  unfold decoderCapacity decoderLength at hj
  omega

/-- **The bounded-tail form of `saved_syndrome_polynomial`**: zeros are needed only inside the
decoder's scratch. -/
theorem saved_syndrome_polynomialB {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (t : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hstored : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    PolynomialStored b m (decoderSavedBase t) (decoderCapacity t) (syndromePoly e t) := by
  intro j hj
  rw [syndromePoly_coeff]
  by_cases h : j < 2 * t
  · rw [if_pos h]
    exact hstored j h
  · rw [if_neg h, enc_zero]
    exact htail _ (by omega) (savedCapBound t j hj)

/-! ### The read loop at a masked memory -/

/-- The read-loop memory, masked at `N`. -/
noncomputable def readMemB {M : ℕ} (N : ℕ) (m : ℕ → ℕ) (S0 w : ℕ) (y : Fin M → ZMod 2) (k : ℕ) :
    ℕ → ℕ :=
  maskMem N (readMem S0 w y k) m

theorem readMemB_succ {M : ℕ} {N : ℕ} {m : ℕ → ℕ} {S0 w : ℕ} {y : Fin M → ZMod 2} {k : ℕ}
    (hk : S0 + 2 * k < N) :
    readMemB N m S0 w y (k + 1)
      = Function.update (readMemB N m S0 w y k) (S0 + 2 * k) (syndromeInt w y k) := by
  unfold readMemB
  rw [readMem_succ]
  exact maskMem_update hk

theorem readMemB_below {M : ℕ} {N : ℕ} {m : ℕ → ℕ} {S0 w : ℕ} {y : Fin M → ZMod 2} {k : ℕ}
    {addr : ℕ} (hN : S0 ≤ N) (h : addr < S0) :
    readMemB N m S0 w y k addr = packMem (8 * w) y addr := by
  unfold readMemB
  rw [maskMem_lt (by omega), readMem_below S0 w y k h]

/-- The read-loop state, at a memory masked at `decoderAllocEnd t`. -/
noncomputable def readStateB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    RAMState where
  pc := base
  regs := ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w]
  mem := readMemB (decoderAllocEnd t) m S0 w y k

attribute [local simp] readStateB

theorem readStateB_regs_eq (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readStateB m base S0 w t y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem readStateB_r14 (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (readStateB m base S0 w t y k).regs r14 = 0 := by
  rw [readStateB_regs_eq]
  simp

/-- The state at the entry of the loop body, at a masked memory. -/
noncomputable def readBodyInB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    RAMState where
  pc := base + 2
  regs := Function.update (readStateB m base S0 w t y k).regs r14 1
  mem := readMemB (decoderAllocEnd t) m S0 w y k

/-- **The read-loop body, as a state map, at a masked memory.** -/
theorem readBody_specB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t k : ℕ)
    (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2)
    (hregs : s.regs = Function.update (readStateB m base S0 w t y k).regs r14 1)
    (hmem : s.mem = readMemB (decoderAllocEnd t) m S0 w y k)
    (hW : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0) (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hkN : S0 + 2 * k < decoderAllocEnd t) :
    runBlock readBody E s = { readStateB m base S0 w t y (k + 1) with pc := base + 18 } := by
  have haddr2 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k := haddr2_of haddr
  have hval : ((packMem (8 * w) y (k / 8) / 2 ^ (k % 8 * w)) % 2 ^ E.W % 2 ^ w) % 2 ^ E.W
      = syndromeInt w y k := by
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w))
      (Nat.pow_le_pow_right (by norm_num) hwe))]
    exact read_value hwe hw (t * w) y k
  have hbelow : readMemB (decoderAllocEnd t) m S0 w y k (k / 8) = packMem (8 * w) y (k / 8) :=
    readMemB_below hSN hword
  have hpc' : (runBlock readBody E s).pc = base + 18 := by
    rw [runBlock_pc readBody E s (by simp [readBody]), hpc, readBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock readBody E s).mem addr = readMemB (decoderAllocEnd t) m S0 w y (k + 1) addr
    by_cases h : addr = S0 + 2 * k
    · rw [h, readMemB_succ hkN, Function.update_self]
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul_detFor65,
        hregs, readStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, hmem, execInstr_div_detFor65, Function.update_self, hdiv,
        execInstr_mod_detFor65, hmod, execInstr_load_detFor65, hbelow, hpk, execInstr_shr,
        Function.update_idem, execInstr_band, Nat.and_two_pow_sub_one_eq_mod, hval, execInstr_add_detFor65,
        Nat.mod_add_mod, haddr2, execInstr_store_detFor65, hk1, execInstr_imm_detFor65, Nat.zero_mod, runBlock_nil]
    · rw [readMemB_succ hkN, Function.update_of_ne h]
      simp [readBody, runBlock_cons, runBlock_nil, hregs, hmem, readStateB, hmul, hdiv, hmod,
        haddr, haddr2, hk1, hmask, hbelow, hpk, hval, Function.update_of_ne h]
  · intro d
    simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul_detFor65,
      hregs, readStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div_detFor65, Function.update_self, hdiv,
      execInstr_mod_detFor65, hmod, execInstr_load_detFor65, execInstr_shr, Function.update_idem, execInstr_band,
      Nat.and_two_pow_sub_one_eq_mod, execInstr_add_detFor65, Nat.mod_add_mod, execInstr_store_detFor65, hk1, execInstr_imm_detFor65,
      Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [readBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_mul_detFor65,
        hregs, readStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.cons_val_zero, hmul, execInstr_div_detFor65, Function.update_self, hdiv,
        execInstr_mod_detFor65, hmod, execInstr_load_detFor65, execInstr_shr, Function.update_idem, execInstr_band,
        Nat.and_two_pow_sub_one_eq_mod, execInstr_add_detFor65, Nat.mod_add_mod, execInstr_store_detFor65, hk1, execInstr_imm_detFor65,
        Nat.zero_mod, runBlock_nil, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Nat.add_left_cancel_iff]

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem readStateB_eta (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ readStateB m base S0 w t y k with pc := base } : RAMState) = readStateB m base S0 w t y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test holds exactly when the counter is below `t`. -/
theorem readCond_evalB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (readStateB m base S0 w t y k) ↔ k < t := by
  simp [Cond.eval, readStateB_regs_eq]

/-- At the exit the test fails. -/
theorem readCond_falseB (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ¬ readCond.eval (readStateB m base S0 w t y t) := by
  rw [readCond_evalB]
  exact lt_irrefl t

/-- Running the test at a masked memory. -/
theorem runBlock_readCondB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (readStateB m base S0 w t y k)
      = { pc := base + 1,
          regs := Function.update (readStateB m base S0 w t y k).regs r14
            ((if k < t then 1 else 0) % 2 ^ E.W),
          mem := readMemB (decoderAllocEnd t) m S0 w y k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [readStateB]
  try rfl

theorem runBlock_readCondB_of_lt (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (readStateB m base S0 w t y k)
      = ⟨base + 1, Function.update (readStateB m base S0 w t y k).regs r14 1,
          readMemB (decoderAllocEnd t) m S0 w y k⟩ := by
  rw [runBlock_readCondB, if_pos hk, Nat.mod_eq_of_lt hW]

theorem runBlock_readCondB_of_ge (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hk : ¬ k < t) :
    runBlock readCond.code E (readStateB m base S0 w t y k)
      = ⟨base + 1, Function.update (readStateB m base S0 w t y k).regs r14 0,
          readMemB (decoderAllocEnd t) m S0 w y k⟩ := by
  rw [runBlock_readCondB, if_neg hk, Nat.zero_mod]

theorem runBlock_readCondB_exit (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (readStateB m base S0 w t y t)
      = ⟨base + 1, (readStateB m base S0 w t y t).regs,
          readMemB (decoderAllocEnd t) m S0 w y t⟩ := by
  have h0 : (readStateB m base S0 w t y t).regs r14 = 0 := readStateB_r14 m base S0 w t y t
  have h := runBlock_readCondB_of_ge E m base S0 w t y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  exact h

/-- The body entry state, in the shape the loop rule produces. -/
theorem readBodyInB_eq (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (readStateB m base S0 w t y k) with
        pc := base + readCond.code.length + 1 } : RAMState) = readBodyInB m base S0 w t y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_readCondB_of_lt E m base S0 w t y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [readBodyInB]
    rw [hcl]
  · simp only [readBodyInB]
    rw [hrun]
  · intro d
    simp only [readBodyInB]
    rw [hrun]

/-- The body of the read loop, as a `Sem` run, at a masked memory. -/
theorem readBody_semB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hAt : At P (base + 2) readBody)
    (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hkN : S0 + 2 * k < decoderAllocEnd t) :
    Sem P E (base + 2) (base + 18) (readBodyInB m base S0 w t y k)
      (fun c s' => c = 16 ∧ s' = { readStateB m base S0 w t y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) readBody (readBodyInB m base S0 w t y k) hAt
    (by simp [readBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, readBody_length]
  · rw [hs]
    exact readBody_specB E m base S0 w t k y (readBodyInB m base S0 w t y k) rfl rfl rfl hW8 hwe hw
      hmul hdiv hmod haddr hk1 hmask hword hpk hSN hkN

/-- The iteration *after* the test: body entry back to the loop head, at a masked memory. -/
theorem readBodyIterB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) (hAt : At P base (Stmt.compile readLoopStmt base))
    (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w) (hwe : w ≤ E.W) (hw : 0 < w) (hk : k < t)
    (hmul : k * w % 2 ^ E.W = k * w) (hdiv : k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : k * w % (8 * w) % 2 ^ E.W = k % 8 * w) (haddr : (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1) (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : k / 8 < S0)
    (hpk : packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hkN : S0 + 2 * k < decoderAllocEnd t) :
    Sem P E (base + readCond.code.length + 1) base
      ({ runBlock readCond.code E (readStateB m base S0 w t y k) with
        pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = readStateB m base S0 w t y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_read hAt
  have hbody := readBody_semB P E m base S0 w t y k hbodyAt hW hW8 hwe hw hmul hdiv hmod haddr hk1
    hmask hword hpk hSN hkN
  rw [readBodyInB_eq E m base S0 w t y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact readStateB_eta m base S0 w t y (k + 1)

/-- The exit state of the read loop at a masked memory. -/
theorem readLoop_exit_stateB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (readStateB m base S0 w t y t) with
        pc := base + readCond.code.length + (Stmt.code readBody).len + 2 } : RAMState)
      = { readStateB m base S0 w t y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code readBody).len = 16 := readBody_length
  have hrun := runBlock_readCondB_exit E m base S0 w t y
  rw [hrun]
  rfl

/-- **The read loop at a masked memory.** -/
theorem readLoop_specB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile readLoopStmt base)) (hW : 1 < 2 ^ E.W) (hW8 : E.W = 8 * w)
    (hwe : w ≤ E.W) (hw : 0 < w)
    (hmul : ∀ k < t, k * w % 2 ^ E.W = k * w)
    (hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8)
    (hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w)
    (haddr : ∀ k < t, (S0 + 2 * k) % 2 ^ E.W = S0 + 2 * k)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1)
    (hword : ∀ k < t, k / 8 < S0)
    (hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8))
    (hSN : S0 ≤ decoderAllocEnd t) (hSt : S0 + 2 * t ≤ decoderAllocEnd t) :
    Sem P E base (base + 19) (readStateB m base S0 w t y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { readStateB m base S0 w t y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code readBody) hAt hW t
    (fun j => readStateB m base S0 w t y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (readCond_evalB m base S0 w t y j).mpr hj)
    (readCond_falseB m base S0 w t y)
    (fun j hj => readBodyIterB P E m base S0 w t y j hAt hW hW8 hwe hw hj (hmul j hj) (hdiv j hj)
      (hmod j hj) (haddr j hj) (hk1 j hj) hmask (hword j hj) (hpk j hj) hSN (by omega))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact readLoop_exit_stateB E m base S0 w t y

/-! ### The expansion loop at a masked memory -/

/-- The expansion-loop memory, masked at `N`. -/
noncomputable def expandMemB {w : ℕ} (N t : ℕ) (m : ℕ → ℕ) (S0 : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) : ℕ → ℕ :=
  maskMem N (expandMem S0 b y t k) m

theorem expandMemB_zero {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} (S0 : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) :
    expandMemB N t m S0 b y 0 = readMemB N m S0 w y t := by
  unfold expandMemB readMemB
  rw [expandMem_zero]

theorem expandMemB_succ {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {k : ℕ}
    (hk : S0 + 2 * k + 1 < N) :
    expandMemB N t m S0 b y (k + 1)
      = Function.update (expandMemB N t m S0 b y k) (S0 + 2 * k + 1)
          (enc b (eSeq b y (2 * k + 1))) := by
  unfold expandMemB
  rw [expandMem_succ]
  exact maskMem_update hk

theorem expandMemB_get {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {k a : ℕ}
    (hN : S0 + a < N) (ht : a / 2 < t) (hk : a % 2 = 1 → a / 2 < k) :
    expandMemB N t m S0 b y k (S0 + a) = enc b (eSeq b y a) := by
  unfold expandMemB
  rw [maskMem_lt hN]
  exact expandMem_get S0 b y t k a ht hk

theorem expandMemB_src {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {k : ℕ}
    (hN : S0 + k < N) (hk : k < t) :
    expandMemB N t m S0 b y k (S0 + k) = enc b (eSeq b y k) :=
  expandMemB_get (a := k) (k := k) hN (by omega) (fun _ => by omega)

theorem expandMemB_complete {w M : ℕ} {N t : ℕ} {m : ℕ → ℕ} {S0 : ℕ}
    {b : Module.Basis (Fin w) (ZMod 2) F} {y : Fin M → ZMod 2} {a : ℕ}
    (hN : S0 + a < N) (ha : a < 2 * t) :
    expandMemB N t m S0 b y t (S0 + a) = enc b (eSeq b y a) :=
  expandMemB_get (a := a) (k := t) hN (by omega) (fun _ => by omega)

theorem expandMemB_after {w M : ℕ} {N t : ℕ} (m : ℕ → ℕ) (S0 : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin M → ZMod 2) (addr : ℕ) (haddr : N ≤ addr) :
    expandMemB N t m S0 b y t addr = m addr := by
  unfold expandMemB
  exact maskMem_ge haddr

/-- The expansion-loop state, at a memory masked at `decoderAllocEnd t`. -/
noncomputable def expandStateB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) : RAMState where
  pc := base
  regs := ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w]
  mem := expandMemB (decoderAllocEnd t) t m S0 b y k

attribute [local simp] expandStateB

theorem expandStateB_regs_eq (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (expandStateB m base S0 w t b y k).regs
      = ![t, w, S0, 2 ^ w - 1, detSqBase w, k, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8 * w] := rfl

@[simp] theorem expandStateB_r14 (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    (expandStateB m base S0 w t b y k).regs r14 = 0 := by
  rw [expandStateB_regs_eq]
  simp

/-- The state at the entry of the expansion body, at a masked memory. -/
noncomputable def expandBodyInB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) : RAMState where
  pc := base + 2
  regs := Function.update (expandStateB m base S0 w t b y k).regs r14 1
  mem := expandMemB (decoderAllocEnd t) t m S0 b y k

/-- A loop-head state with its own program counter written back is unchanged. -/
theorem expandStateB_eta (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    ({ expandStateB m base S0 w t b y k with pc := base } : RAMState)
      = expandStateB m base S0 w t b y k := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp
  · simp
  · intro d; simp

/-- The loop test for the expansion loop, at a masked memory. -/
theorem expandCond_evalB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    readCond.eval (expandStateB m base S0 w t b y k) ↔ k < t := by
  simp [Cond.eval, expandStateB_regs_eq]

theorem expandCond_falseB (m : ℕ → ℕ) (base S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) : ¬ readCond.eval (expandStateB m base S0 w t b y t) := by
  rw [expandCond_evalB]
  exact lt_irrefl t

/-- Running the expansion test at a masked memory. -/
theorem runBlock_expandCondB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ) :
    runBlock readCond.code E (expandStateB m base S0 w t b y k)
      = { pc := base + 1,
          regs := Function.update (expandStateB m base S0 w t b y k).regs r14
            ((if k < t then 1 else 0) % 2 ^ E.W),
          mem := expandMemB (decoderAllocEnd t) t m S0 b y k } := by
  have hcode : readCond.code = [iLt r14 r5 r0] := rfl
  rw [hcode, runBlock_cons, runBlock_nil, execInstr_lt]
  dsimp only [expandStateB]
  try rfl

theorem runBlock_expandCondB_of_lt (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    runBlock readCond.code E (expandStateB m base S0 w t b y k)
      = ⟨base + 1, Function.update (expandStateB m base S0 w t b y k).regs r14 1,
          expandMemB (decoderAllocEnd t) t m S0 b y k⟩ := by
  rw [runBlock_expandCondB, if_pos hk, Nat.mod_eq_of_lt hW]

theorem runBlock_expandCondB_of_ge (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hk : ¬ k < t) :
    runBlock readCond.code E (expandStateB m base S0 w t b y k)
      = ⟨base + 1, Function.update (expandStateB m base S0 w t b y k).regs r14 0,
          expandMemB (decoderAllocEnd t) t m S0 b y k⟩ := by
  rw [runBlock_expandCondB, if_neg hk, Nat.zero_mod]

theorem runBlock_expandCondB_exit (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    runBlock readCond.code E (expandStateB m base S0 w t b y t)
      = ⟨base + 1, (expandStateB m base S0 w t b y t).regs,
          expandMemB (decoderAllocEnd t) t m S0 b y t⟩ := by
  have h0 : (expandStateB m base S0 w t b y t).regs r14 = 0 := expandStateB_r14 m base S0 w t b y t
  have h := runBlock_expandCondB_of_ge E m base S0 w t b y t (lt_irrefl t)
  rw [update_zero_eq _ h0] at h
  exact h

theorem expandBodyInB_eq (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hW : 1 < 2 ^ E.W) (hk : k < t) :
    ({ runBlock readCond.code E (expandStateB m base S0 w t b y k) with
        pc := base + readCond.code.length + 1 } : RAMState) = expandBodyInB m base S0 w t b y k := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hrun := runBlock_expandCondB_of_lt E m base S0 w t b y k hW hk
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp only [expandBodyInB]
    rw [hcl]
  · simp only [expandBodyInB]
    rw [hrun]
  · intro d
    simp only [expandBodyInB]
    rw [hrun]

/-- **The expansion body, as a state map, at a masked memory.** -/
theorem expandBody_specB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t k : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (s : RAMState)
    (hpc : s.pc = base + 2)
    (hregs : s.regs = Function.update (expandStateB m base S0 w t b y k).regs r14 1)
    (hmem : s.mem = expandMemB (decoderAllocEnd t) t m S0 b y k)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1)
    (hkN : S0 + 2 * k + 1 < decoderAllocEnd t) :
    runBlock expandBody E s = { expandStateB m base S0 w t b y (k + 1) with pc := base + 18 } := by
  have hpc' : (runBlock expandBody E s).pc = base + 18 := by
    rw [runBlock_pc expandBody E s (by simp [expandBody]), hpc, expandBody_length]
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock expandBody E s).mem addr
      = expandMemB (decoderAllocEnd t) t m S0 b y (k + 1) addr
    by_cases h : addr = S0 + 2 * k + 1
    · rw [h, expandMemB_succ hkN, Function.update_self]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add_detFor65,
        hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load_detFor65, Function.update_self, hsrcval, hld, hsq, execInstr_qDet_detFor65, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store_detFor65, hk1, execInstr_imm_detFor65, Nat.zero_mod, runBlock_nil]
    · rw [expandMemB_succ hkN, Function.update_of_ne h]
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add_detFor65,
        hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, hmem, execInstr_load_detFor65, Function.update_self, hsrcval, hld, hsq, execInstr_qDet_detFor65, htab, hval, hkk,
        hkkS0, Function.update_idem, haddr, execInstr_store_detFor65, hk1, execInstr_imm_detFor65, Nat.zero_mod, runBlock_nil,
        Function.update_of_ne h]
  · intro d
    simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add_detFor65,
      hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
      hsrc, execInstr_load_detFor65, Function.update_self, Nat.add_mod_mod, execInstr_qDet_detFor65, hkk, hkkS0,
      Function.update_idem, haddr, execInstr_store_detFor65, hk1, execInstr_imm_detFor65, Nat.zero_mod, runBlock_nil]
    fin_cases d <;>
      simp only [expandBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_add_detFor65,
        hregs, expandStateB, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Matrix.cons_val,
        hsrc, execInstr_load_detFor65, Function.update_self, Nat.add_mod_mod, execInstr_qDet_detFor65, hkk, hkkS0,
        Function.update_idem, haddr, execInstr_store_detFor65, hk1, execInstr_imm_detFor65, Nat.zero_mod, runBlock_nil,
        Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
        Nat.add_left_cancel_iff]

/-- The expansion body as a `Sem` run, at a masked memory. -/
theorem expandBody_semB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P (base + 2) expandBody)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1)
    (hkN : S0 + 2 * k + 1 < decoderAllocEnd t) :
    Sem P E (base + 2) (base + 18) (expandBodyInB m base S0 w t b y k)
      (fun c s' => c = 16 ∧ s' = { expandStateB m base S0 w t b y (k + 1) with pc := base + 18 }) := by
  refine Sem.mono (Sem.block P E (base + 2) expandBody (expandBodyInB m base S0 w t b y k) hAt
    (by simp [expandBody]) rfl) ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hc, expandBody_length]
  · rw [hs]
    exact expandBody_specB E m base S0 w t k b y (expandBodyInB m base S0 w t b y k) rfl rfl rfl hsrc
      hsrcval hld hsq htab hval hkk hkkS0 haddr hk1 hkN

/-- The expansion iteration after the test, at a masked memory. -/
theorem expandBodyIterB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (k : ℕ)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W) (hk : k < t)
    (hsrc : (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : (k + 1) % 2 ^ E.W = k + 1)
    (hkN : S0 + 2 * k + 1 < decoderAllocEnd t) :
    Sem P E (base + readCond.code.length + 1) base
      ({ runBlock readCond.code E (expandStateB m base S0 w t b y k) with
        pc := base + readCond.code.length + 1 } : RAMState)
      (fun c s' => c = 17 ∧ s' = expandStateB m base S0 w t b y (k + 1)) := by
  obtain ⟨hjz, hbodyAt, hjmp⟩ := at_loop_expand hAt
  have hbody := expandBody_semB P E m base S0 w t b y k hbodyAt hsrc hsrcval hld hsq htab hval hkk hkkS0
    haddr hk1 hkN
  rw [expandBodyInB_eq E m base S0 w t b y k hW hk]
  refine Sem.jmp_append (hAt := hjmp) ?_
  refine Sem.mono hbody ?_
  intro c s' hQ
  obtain ⟨hc, hs⟩ := hQ
  refine ⟨by omega, ?_⟩
  rw [hs]
  exact expandStateB_eta m base S0 w t b y (k + 1)

/-- The exit state of the expansion loop, at a masked memory. -/
theorem expandLoop_exit_stateB (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) :
    ({ runBlock readCond.code E (expandStateB m base S0 w t b y t) with
        pc := base + readCond.code.length + (Stmt.code expandBody).len + 2 } : RAMState)
      = { expandStateB m base S0 w t b y t with pc := base + 19 } := by
  have hcl : readCond.code.length = 1 := readCond_code_length
  have hbl : (Stmt.code expandBody).len = 16 := expandBody_length
  have hrun := runBlock_expandCondB_exit E m base S0 w t b y
  rw [hrun]
  rfl

/-- **The expansion loop at a masked memory.** -/
theorem expandLoop_specB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hSt : S0 + 2 * t ≤ decoderAllocEnd t) :
    Sem P E base (base + 19) (expandStateB m base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandStateB m base S0 w t b y t with pc := base + 19 }) := by
  have hloop := Sem.loop P E base readCond (Stmt.code expandBody) hAt hW t
    (fun j => expandStateB m base S0 w t b y j) (fun _ => 17)
    (fun j => rfl)
    (fun j hj => (expandCond_evalB m base S0 w t b y j).mpr hj)
    (expandCond_falseB m base S0 w t b y)
    (fun j hj => expandBodyIterB P E m base S0 w t b y j hAt hW hj (hsrc j hj) (hsrcval j hj)
      (hld j hj) (hsq j hj) (htab j hj) (hval j hj) (hkk j hj) (hkkS0 j hj) (haddr j hj) (hk1 j hj)
      (by omega))
  have h19 : ((readCond.code.length + 1) + 17) = 19 := by
    rw [readCond_code_length]
  have hsum19 : (∑ j ∈ Finset.range t, (19 : ℕ)) = 19 * t := sum_range_const_mul t 19
  have hsum : (∑ j ∈ Finset.range t, ((readCond.code.length + 1) + 17)) = 19 * t := by
    rw [← hsum19]
    exact Finset.sum_congr rfl (fun j _ => h19)
  refine Sem.mono hloop ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [hsum] at hle
    rw [readCond_code_length] at hle
    omega
  · rw [hs]
    exact expandLoop_exit_stateB E m base S0 w t b y

/-- **The array is complete when the expansion loop exits**, at a masked memory. -/
theorem expandLoop_resultB (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (base S0 w t : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2)
    (hAt : At P base (Stmt.compile expandLoopStmt base)) (hW : 1 < 2 ^ E.W)
    (hsrc : ∀ k < t, (S0 + k) % 2 ^ E.W = S0 + k)
    (hsrcval : ∀ k < t, expandMemB (decoderAllocEnd t) t m S0 b y k (S0 + k) = enc b (eSeq b y k))
    (hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k))
    (hsq : ∀ k < t, (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k))
    (htab : ∀ k < t, E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)))
    (hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)))
    (hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k)
    (hkkS0 : ∀ k < t, (k + k + S0) % 2 ^ E.W = S0 + 2 * k)
    (haddr : ∀ k < t, (S0 + 2 * k + 1) % 2 ^ E.W = S0 + 2 * k + 1)
    (hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1)
    (hSt : S0 + 2 * t ≤ decoderAllocEnd t) :
    Sem P E base (base + 19) (expandStateB m base S0 w t b y 0)
      (fun c s' => c ≤ 19 * t + 2 ∧ s' = { expandStateB m base S0 w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → s'.mem (S0 + a) = enc b (eSeq b y a)) := by
  refine Sem.mono (expandLoop_specB P E m base S0 w t b y hAt hW hsrc hsrcval hld hsq htab hval hkk
    hkkS0 haddr hk1 hSt) ?_
  intro c s' hQ
  obtain ⟨hle, hs⟩ := hQ
  refine ⟨hle, hs, ?_⟩
  intro a ha
  rw [hs]
  exact expandMemB_complete (by omega) ha

/-! ### The read prologue and the front of the stage, at a masked memory -/

/-- `readMem` at counter `0` is `hintMem`, so the mask at `0` is the ambient memory itself. -/
theorem readMemB_zero {M : ℕ} {N : ℕ} {m : ℕ → ℕ} {S0 w : ℕ} {y : Fin M → ZMod 2}
    (hS0 : S0 = wordsOf (8 * w) M)
    (hmem : ∀ a, a < N → m a = hintMem (8 * w) y [] a) :
    readMemB N m S0 w y 0 = m := by
  funext a
  by_cases ha : a < N
  · rw [readMemB, maskMem_lt ha]
    have hz : readMem S0 w y 0 a = hintMem (8 * w) y [] a := by
      rw [readMem_zero]
      simp only [hS0, hintMem, List.getD_nil]
    rw [hz, hmem a ha]
  · rw [readMemB, maskMem_ge (by omega)]

/-- **The prologue, at a masked memory.**  `paramBody` reads only registers, so it leaves `m` alone. -/
theorem paramBodyAt_specB (E : RAMEnv) (m : ℕ → ℕ) (base N t w S0 : ℕ)
    (y : Fin (t * w) → ZMod 2)
    (hS0 : S0 = wordsOf (8 * w) (t * w)) (hW : E.W = 8 * w) (hw1 : 1 ≤ w)
    (h0 : E.det 0 % 2 ^ E.W = t) (h1 : E.det 1 % 2 ^ E.W = w) (h4 : E.det 4 % 2 ^ E.W = S0)
    (h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1) (h6 : E.det 6 % 2 ^ E.W = detSqBase w)
    (h12 : E.det 12 % 2 ^ E.W = 8 * w) (h1W : (1 : ℕ) % 2 ^ E.W = 1)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    runBlock paramBody E ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      = readStateB m (base + 14) S0 w t y 0 := by
  have hmem0 : readMemB (decoderAllocEnd t) m S0 w y 0 = m := readMemB_zero hS0 hmem
  have hpc' : (runBlock paramBody E ⟨base, (decoderStart (8 * w) y []).regs, m⟩).pc
      = base + 14 := by
    rw [runBlock_pc paramBody E _ (by simp [paramBody]), paramBody_length]
  have h4m : (4 : ℕ) % 2 ^ E.W = 4 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have h5m : (5 : ℕ) % 2 ^ E.W = 5 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have h6m : (6 : ℕ) % 2 ^ E.W = 6 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have h12m : (12 : ℕ) % 2 ^ E.W = 12 := Nat.mod_eq_of_lt (by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by rw [hW]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  refine ramState_eq_of _ _ hpc' ?_ ?_
  · funext addr
    show (runBlock paramBody E ⟨base, (decoderStart (8 * w) y []).regs, m⟩).mem addr
      = readMemB (decoderAllocEnd t) m S0 w y 0 addr
    rw [hmem0]
    simp only [paramBody, Fin.isValue, List.cons_append, List.nil_append, runBlock_cons, execInstr_imm_detFor65,
      Nat.zero_mod, execInstr_qDet_detFor65, Function.update_self, runBlock_nil]
  · intro d
    simp only [paramBody, readStateB, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
      decoderStart, initState, runBlock_cons, runBlock_nil, execInstr_imm_detFor65, execInstr_qDet_detFor65,
      Function.update_idem]
    fin_cases d <;>
      simp [paramBody, readStateB, h0, h1, h4, h5, h6, h12, h1W, h4m, h5m, h6m, h12m,
        decoderStart, initState, runBlock_cons, runBlock_nil]

/-- **The read loop's input stage, at a masked memory.** -/
theorem inputRead_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (m : ℕ → ℕ) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputReadStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E base (base + 33) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 19 * t + 16 ∧
        z = { readStateB m (base + 14) (wordsOf (8 * w) (t * w)) w t y t with pc := base + 33 }) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hwW : w < 2 ^ (8 * w) := lt_of_lt_of_le (Nat.lt_two_pow_self (n := w)) h2w
  have hS0W : wordsOf (8 * w) (t * w) < 2 ^ (8 * w) :=
    lt_of_le_of_lt (wordsOf_le w t hw1) htW
  have hmaskW : 2 ^ w - 1 < 2 ^ (8 * w) := by
    have := Nat.two_pow_pos w
    omega
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  have h0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet.1 0 (by decide), detStd_hdr t N w b ι (by norm_num : (0 : ℕ) < 13), hdrTab_zero, hW]
    exact Nat.mod_eq_of_lt htW
  have h1 : E.det 1 % 2 ^ E.W = w := by
    rw [hdet.1 1 (by decide), detStd_hdr t N w b ι (by norm_num : (1 : ℕ) < 13), hdrTab_one, hW]
    exact Nat.mod_eq_of_lt hwW
  have h4 : E.det 4 % 2 ^ E.W = wordsOf (8 * w) (t * w) := by
    rw [hdet.1 4 (by decide), detStd_hdr t N w b ι (by norm_num : (4 : ℕ) < 13), hdrTab_four, hW]
    exact Nat.mod_eq_of_lt hS0W
  have h5 : E.det 5 % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hdet.1 5 (by decide), detStd_hdr t N w b ι (by norm_num : (5 : ℕ) < 13), hdrTab_five, hW]
    exact Nat.mod_eq_of_lt hmaskW
  have h6 : E.det 6 % 2 ^ E.W = detSqBase w := by
    rw [hdet.1 6 (by decide), detStd_hdr t N w b ι (by norm_num : (6 : ℕ) < 13), hdrTab_six, hW]
    exact Nat.mod_eq_of_lt (detSqBase_lt hw1)
  have h12 : E.det 12 % 2 ^ E.W = 8 * w := by
    rw [hdet.1 12 (by decide), detStd_hdr t N w b ι (by norm_num : (12 : ℕ) < 13), hdrTab_twelve, hW]
    exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have h1W : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt h1E
  have hmul : ∀ k < t, k * w % 2 ^ E.W = k * w := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (mul_lt_two_pow_eight hw1 hNw (lt_of_lt_of_le hk htN))
  have hdiv : ∀ k < t, k * w / (8 * w) % 2 ^ E.W = k / 8 := by
    intro k hk
    rw [mul_div_eight w hpos k, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k / 8 ≤ k := Nat.div_le_self _ _
      _ < 2 ^ w := by omega
      _ ≤ 2 ^ (8 * w) := h2w
  have hmod : ∀ k < t, k * w % (8 * w) % 2 ^ E.W = k % 8 * w := by
    intro k hk
    rw [mul_mod_eight, hW]
    refine Nat.mod_eq_of_lt ?_
    calc k % 8 * w ≤ 7 * w := Nat.mul_le_mul_right w (by
          have := Nat.mod_lt k (by norm_num : (0 : ℕ) < 8)
          omega)
      _ < 8 * w := by omega
      _ ≤ 2 ^ (8 * w) := le_of_lt (Nat.lt_two_pow_self (n := 8 * w))
  have haddr : ∀ k < t, (wordsOf (8 * w) (t * w) + 2 * k) % 2 ^ E.W
      = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_lt_two_pow_eight hw1
      (lt_of_le_of_lt htN hNw) (wordsOf_le w t hw1) hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1' : k + 1 ≤ t := by omega
    omega
  have hmask : (2 ^ w - 1) % 2 ^ E.W = 2 ^ w - 1 := by
    rw [hW]
    exact Nat.mod_eq_of_lt hmaskW
  have hword : ∀ k < t, k / 8 < wordsOf (8 * w) (t * w) := by
    intro k hk
    rw [wordsOf_eight w t hpos]
    omega
  have hpk : ∀ k < t, packMem (8 * w) y (k / 8) % 2 ^ E.W = packMem (8 * w) y (k / 8) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (packMem_lt_detFor65 hpos y (k / 8))
  have hS0le : wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t := by
    have h1' : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw1
    rw [decoderAllocEnd_eq]
    omega
  have hSt : wordsOf (8 * w) (t * w) + 2 * t ≤ decoderAllocEnd t :=
    frontBound (wordsOf_le w t hw1)
  obtain ⟨hParamAt, hLoopAt⟩ := At.seqStmt hAt
  have hPro : Sem P E base (base + 14) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 14 ∧ z = readStateB m (base + 14) (wordsOf (8 * w) (t * w)) w t y 0) := by
    refine Sem.mono (Sem.block P E base paramBody _ hParamAt (by simp [paramBody]) rfl) ?_
    intro k z hQ
    have hk : k = 14 := hQ.1
    exact ⟨by omega, hQ.2.trans (paramBodyAt_specB E m base N t w (wordsOf (8 * w) (t * w)) y rfl
      hW hw1 h0 h1 h4 h5 h6 h12 h1W hmem)⟩
  have hLoop := readLoop_specB P E m (base + 14) (wordsOf (8 * w) (t * w)) w t y hLoopAt
    h1E hW (by rw [hW]; omega) hpos hmul hdiv hmod haddr hk1 hmask hword hpk hS0le hSt
  have hFull := Sem.seq_bound hPro (fun z _ hz => by subst z; exact hLoop)
  exact Sem.mono hFull (fun k z hQ => ⟨by omega, hQ.2⟩)

/-- **The read loop's output is the expansion's input, at a masked memory.** -/
theorem readToExpansion_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (m : ℕ → ℕ) (readBase pc S0 w t : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F)
    (y : Fin (t * w) → ZMod 2) :
    runBlock [iImm r5 0] E { readStateB m readBase S0 w t y t with pc := pc }
      = expandStateB m (pc + 1) S0 w t b y 0 := by
  apply ramState_eq_of
  · rfl
  · show readMemB (decoderAllocEnd t) m S0 w y t
      = (expandStateB m (pc + 1) S0 w t b y 0).mem
    exact (expandMemB_zero S0 b y).symm
  · intro r
    fin_cases r <;> simp [runBlock_cons, runBlock_nil, execInstr, readStateB, expandStateB]

/-- **The expansion stage at a masked memory.** -/
theorem expandAt_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (P : Program) (E : RAMEnv) (m : ℕ → ℕ) (N t w base : ℕ)
    (b : Module.Basis (Fin w) (ZMod 2) F) (y : Fin (t * w) → ZMod 2) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile expandLoopStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι) :
    Sem P E base (base + 19) (expandStateB m base (wordsOf (8 * w) (t * w)) w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧
        z = { expandStateB m base (wordsOf (8 * w) (t * w)) w t b y t with pc := base + 19 } ∧
        ∀ a, a < 2 * t → z.mem (wordsOf (8 * w) (t * w) + a) = enc b (eSeq b y a)) := by
  have hpos : 0 < w := by omega
  have h2w : (2 : ℕ) ^ w ≤ 2 ^ (8 * w) :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : w ≤ 8 * w)
  have htW : t < 2 ^ (8 * w) := lt_of_le_of_lt htN (lt_of_lt_of_le hNw h2w)
  have hS0t : wordsOf (8 * w) (t * w) ≤ t := wordsOf_le w t hw1
  have hSt : wordsOf (8 * w) (t * w) + 2 * t ≤ decoderAllocEnd t := frontBound hS0t
  have h1E : (1 : ℕ) < 2 ^ E.W := by
    rw [hW]
    have h0 : 0 < 8 * w := by omega
    have h := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h0
    simpa using h
  have hsrc : ∀ k < t, (wordsOf (8 * w) (t * w) + k) % 2 ^ E.W
      = wordsOf (8 * w) (t * w) + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := by omega
    calc wordsOf (8 * w) (t * w) + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have henc : ∀ k < t, enc b (eSeq b y k) < 2 ^ E.W := by
    intro k hk
    rw [hW]
    exact lt_of_lt_of_le (enc_lt b _) h2w
  have hsrcval : ∀ k < t, expandMemB (decoderAllocEnd t) t m (wordsOf (8 * w) (t * w)) b y k
      (wordsOf (8 * w) (t * w) + k) = enc b (eSeq b y k) := by
    intro k hk
    exact expandMemB_src (by omega) hk
  have hld : ∀ k < t, enc b (eSeq b y k) % 2 ^ E.W = enc b (eSeq b y k) := by
    intro k hk
    exact Nat.mod_eq_of_lt (henc k hk)
  have hsq : ∀ k < t,
      (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = detSqBase w + enc b (eSeq b y k) := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (detSqBase_add_lt hw1 (enc_lt b _))
  have htab : ∀ k < t,
      E.det (detSqBase w + enc b (eSeq b y k)) % 2 ^ E.W = sqTab b (enc b (eSeq b y k)) := by
    intro k hk
    rw [hdet.2 _ (by have h := detMulBase_le_detSqBase w; omega), detStd_sq t N w b ι (enc_lt b _), hW]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (enc_lt b _) h2w)
  have hval : ∀ k < t, sqTab b (enc b (eSeq b y k)) = enc b (eSeq b y (2 * k + 1)) := by
    intro k hk
    exact sqTab_enc b y k
  have hkk : ∀ k < t, (k + k) % 2 ^ E.W = k + k := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h1 : k + k < 2 ^ w + 2 ^ w := by omega
    calc k + k < 2 ^ w + 2 ^ w := h1
      _ = 2 ^ (w + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkkS0 : ∀ k < t,
      (k + k + wordsOf (8 * w) (t * w)) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k := by
    intro k hk
    have h := addr_lt_two_pow_eight (w := w) (t := t) (k := k)
      (S0 := wordsOf (8 * w) (t * w)) hw1 (lt_of_le_of_lt htN hNw) hS0t hk
    have h2 : k + k + wordsOf (8 * w) (t * w) = wordsOf (8 * w) (t * w) + 2 * k := by omega
    rw [h2, hW]
    exact Nat.mod_eq_of_lt h
  have haddr : ∀ k < t,
      (wordsOf (8 * w) (t * w) + 2 * k + 1) % 2 ^ E.W = wordsOf (8 * w) (t * w) + 2 * k + 1 := by
    intro k hk
    rw [hW]
    exact Nat.mod_eq_of_lt (addr_succ_lt_two_pow_eight hw1 (lt_of_le_of_lt htN hNw) hS0t hk)
  have hk1 : ∀ k < t, (k + 1) % 2 ^ E.W = k + 1 := by
    intro k hk
    rw [hW]
    refine Nat.mod_eq_of_lt ?_
    have h2 : k + 1 ≤ t := by omega
    omega
  exact expandLoop_resultB P E m base (wordsOf (8 * w) (t * w)) w t b y hAt
    h1E hsrc hsrcval hld hsq htab hval hkk hkkS0 haddr hk1 hSt

/-- **The input front of the read stage, at a masked memory.** -/
theorem inputFront_specB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (m : ℕ → ℕ) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputFrontStmt base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E base (base + 69) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 38 * t + 35 ∧
        z = boundaryState (base + 69)
          (expandMemB (decoderAllocEnd t) t m (wordsOf (8 * w) (t * w)) b y t) ∧
        FieldArrayStored b z.mem (wordsOf (8 * w) (t * w)) (2 * t) (eSeq b y) ∧
        (∀ addr, decoderAllocEnd t ≤ addr → z.mem addr = m addr)) := by
  let S0 := wordsOf (8 * w) (t * w)
  have hSt : S0 + 2 * t ≤ decoderAllocEnd t := frontBound (wordsOf_le w t hw1)
  obtain ⟨hReadAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hResetAt, hRest2At⟩ := At.seqStmt hRestAt
  obtain ⟨hExpandAt, hZeroAt⟩ := At.seqStmt hRest2At
  have hRead := inputRead_specB E P m base N t w y b ι hReadAt hW hw1 hNw htN hdet hmem
  have hReset : Sem P E (base + 33) (base + 34)
      { readStateB m (base + 14) S0 w t y t with pc := base + 33 }
      (fun k z => k ≤ 1 ∧ z = expandStateB m (base + 34) S0 w t b y 0) := by
    refine Sem.mono (Sem.block P E (base + 33) [iImm r5 0] _ hResetAt (by simp) rfl) ?_
    intro k z hQ
    have hk : k = 1 := hQ.1
    exact ⟨by omega, hQ.2.trans (readToExpansion_specB E m (base + 14) (base + 33) S0 w t b y)⟩
  have hExpand := expandAt_specB P E m N t w (base + 34) b y ι hExpandAt hW hw1 hNw htN hdet
  have hExpandExact : Sem P E (base + 34) (base + 53) (expandStateB m (base + 34) S0 w t b y 0)
      (fun k z => k ≤ 19 * t + 2 ∧
        z = { expandStateB m (base + 34) S0 w t b y t with pc := base + 53 }) :=
    Sem.mono hExpand (fun _ _ hQ => ⟨hQ.1, hQ.2.1⟩)
  have hZero := Sem.zero_block P E (base + 53)
    { expandStateB m (base + 34) S0 w t b y t with pc := base + 53 } hZeroAt rfl
  have hFull := Sem.seq_bound hRead (fun z _ hz => by
    subst z
    exact Sem.seq_bound hReset (fun z _ hz => by
      subst z
      exact Sem.seq_bound hExpandExact (fun z _ hz => by subst z; exact hZero)))
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, hz⟩ := hQ
  refine ⟨by omega, ⟨hz, ⟨?_, ?_⟩⟩⟩
  · rw [hz]
    intro j hj
    exact expandMemB_complete (by omega) hj
  · rw [hz]
    intro addr ha
    exact expandMemB_after m S0 b y addr ha

/-- **The syndrome-saving stage at a masked memory.** -/
theorem saveSyndromeProcedure_specB {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (P : Program) (E : RAMEnv) (pc S0 t : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile saveSyndromeProcedure pc))
    (hmeta : (128 : ℕ) < 2 ^ E.W) (hwe : w ≤ E.W)
    (hS0 : S0 ≤ t) (hword : decoderSavedBase t + 2 * t ≤ 2 ^ E.W)
    (hBfit : decoderSavedBase t < 2 ^ E.W)
    (h0 : E.det 0 % 2 ^ E.W = t) (h4 : E.det 4 % 2 ^ E.W = S0)
    (hsums : FieldArrayStored b m S0 (2 * t) e)
    (htail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    Sem P E pc (pc + 41) (boundaryState pc m)
      (fun k z => k ≤ 12 * (2 * t) + 31 ∧
        z = boundaryState (pc + 41)
          (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t)) ∧
        FieldArrayStored b z.mem (decoderSavedBase t) (2 * t) e ∧
        (∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → z.mem addr = 0) ∧
        (∀ addr, decoderAllocEnd t ≤ addr → z.mem addr = m addr)) := by
  have hlen : 2 * t < 2 ^ E.W := by
    have hb : 128 ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
    omega
  have hsrc : S0 + 2 * t ≤ 2 ^ E.W := by dsimp [decoderSavedBase] at hword; omega
  have hdisj : S0 + 2 * t ≤ decoderSavedBase t := by unfold decoderSavedBase; omega
  have hsaved : decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := savedBase_le_allocEnd t
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hCopyAt, hZeroAt⟩ := At.seqStmt hRestAt
  have hArgs : Sem P E pc (pc + 13) (boundaryState pc m)
      (fun k z => k ≤ 13 ∧
        z = copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) 0) := by
    refine Sem.mono (Sem.block P E pc saveArgsCode _ hArgsAt
      (by simp [saveArgsCode, saveHeaderCode, saveDestinationCode]) rfl) ?_
    intro k z hQ
    have hk : k = 13 := hQ.1
    exact ⟨by omega, hQ.2.trans (saveArgs_spec E pc S0 t m hmeta hlen hBfit h0 h4)⟩
  have hCopy := copyArray_spec P E (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) hCopyAt
    (by omega) hlen hword hsrc (Or.inl hdisj) (by
      intro j hj
      rw [hsums j hj]
      exact lt_of_lt_of_le (enc_lt b _) (Nat.pow_le_pow_right (by norm_num) hwe))
  have hZero := Sem.zero_block P E (pc + 25)
    { copyState (pc + 13) (decoderSavedBase t) S0 (2 * t) m (fun _ => 0) (2 * t) with pc := pc + 25 }
    hZeroAt rfl
  have hFull := Sem.seq_bound hArgs (fun z _ hz => by
    subst z
    exact Sem.seq_bound hCopy (fun z _ hz => by subst z; exact hZero))
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, hz⟩ := hQ
  refine ⟨by omega, ⟨hz, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩
  · rw [hz]
    change FieldArrayStored b (writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t))
      (decoderSavedBase t) (2 * t) e
    intro j hj
    rw [writeArray_get _ _ _ (2 * t) j hj]
    exact hsums j hj
  · rw [hz]
    change ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t →
      writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t) addr = 0
    intro addr ha hlt
    rw [writeArray_frame _ _ _ _ addr (Or.inr ha)]
    exact htail addr ha hlt
  · rw [hz]
    change ∀ addr, decoderAllocEnd t ≤ addr →
      writeArray (decoderSavedBase t) m (fun i => m (S0 + i)) (2 * t) addr = m addr
    intro addr ha
    rw [writeArray_frame _ _ _ _ addr (Or.inr (by omega))]

/-- **The read stage of Proposition 2.1 at a memory that is zero only inside the decoder's own
workspace.**  If `m` agrees with the canonical entry memory `hintMem (8w) y []` on
`[0, decoderAllocEnd t)`, the read stage runs in the same `62t + 66` steps, produces the same
workspace on `[0, decoderAllocEnd t)`, and **leaves every word at or above `decoderAllocEnd t`
untouched**. -/
theorem pinsketch_decoder_readB {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P base (Stmt.compile inputSavedProcedure base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : DetAgrees E t N b ι)
    (hmem : ∀ a, a < decoderAllocEnd t → m a = hintMem (8 * w) y [] a) :
    Sem P E base (base + 110) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 62 * t + 66 ∧
        ∃ m', z = boundaryState (base + 110) m' ∧
          FieldArrayStored b m' (decoderSavedBase t) (2 * t) (eSeq b y) ∧
          PolynomialStored b m' (decoderSavedBase t) (decoderCapacity t)
            (syndromePoly (eSeq b y) t) ∧
          (∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m' addr = 0) ∧
          (∀ addr, decoderAllocEnd t ≤ addr → m' addr = m addr)) := by
  let S0 := wordsOf (8 * w) (t * w)
  have hAlloc : decoderAllocEnd t < 2 ^ E.W := by
    rw [hW]
    exact decoderAllocEnd_fits t w hw1 (lt_of_le_of_lt htN hNw)
  have hEBword : decoderSavedBase t + 2 * t ≤ 2 ^ E.W := by
    have hE : decoderSavedBase t + 2 * t ≤ decoderAllocEnd t := savedBase_le_allocEnd t
    omega
  have hEBfit : decoderSavedBase t < 2 ^ E.W := by
    have he : decoderSavedBase t ≤ decoderAllocEnd t := by
      have h := savedBase_le_allocEnd t
      unfold decoderSavedBase at *
      omega
    omega
  have hmeta : (128 : ℕ) < 2 ^ E.W := by
    have hp : (2 : ℕ) ^ 8 ≤ 2 ^ E.W := by
      rw [hW]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (by norm_num : 128 < 2 ^ 8) hp
  have hS0 : S0 ≤ t := wordsOf_le w t hw1
  have h0 : E.det 0 % 2 ^ E.W = t := by
    rw [hdet.1 0 (by decide), detStd_hdr t N w b ι (by norm_num : 0 < 13), hdrTab_zero,
      Nat.mod_eq_of_lt (by omega)]
  have h4 : E.det 4 % 2 ^ E.W = S0 := by
    rw [hdet.1 4 (by decide), detStd_hdr t N w b ι (by norm_num : 4 < 13), hdrTab_four,
      Nat.mod_eq_of_lt (by omega)]
  have hSt : S0 + 2 * t ≤ decoderAllocEnd t := frontBound hS0
  obtain ⟨hFrontAt, hSaveAt⟩ := At.seqStmt hAt
  have hFront := inputFront_specB E P m base N t w y b ι hFrontAt hW hw1 hNw htN hdet hmem
  have hFrontExact : Sem P E base (base + 69) ⟨base, (decoderStart (8 * w) y []).regs, m⟩
      (fun k z => k ≤ 38 * t + 35 ∧
        z = boundaryState (base + 69) (expandMemB (decoderAllocEnd t) t m S0 b y t)) := by
    refine Sem.mono hFront ?_
    intro k z hQ
    exact ⟨hQ.1, hQ.2.1⟩
  have hValues : FieldArrayStored b (expandMemB (decoderAllocEnd t) t m S0 b y t) S0 (2 * t)
      (eSeq b y) := by
    intro j hj
    exact expandMemB_complete (by omega) hj
  have hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t →
      expandMemB (decoderAllocEnd t) t m S0 b y t addr = 0 := by
    intro addr ha hlt
    rw [expandMemB, maskMem_lt hlt]
    exact expandMem_after_zero S0 b y t addr (by dsimp [S0, decoderSavedBase] at ha; omega)
  have hSave := saveSyndromeProcedure_specB b P E (base + 69) S0 t (eSeq b y)
    (expandMemB (decoderAllocEnd t) t m S0 b y t) hSaveAt hmeta (by omega) hS0 hEBword hEBfit h0 h4
    hValues hTail
  have hFull := Sem.seq_bound hFrontExact (fun z _ hz => by subst z; exact hSave)
  refine Sem.mono hFull ?_
  intro k z hQ
  obtain ⟨hk, hz, hsums, htail, hframe⟩ := hQ
  have hzmem : z.mem = writeArray (decoderSavedBase t)
      (expandMemB (decoderAllocEnd t) t m S0 b y t)
      (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t) := by
    rw [hz]
    rfl
  rw [hzmem] at hsums htail hframe
  have hframe2 : ∀ addr, decoderAllocEnd t ≤ addr →
      writeArray (decoderSavedBase t) (expandMemB (decoderAllocEnd t) t m S0 b y t)
        (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t) addr = m addr := by
    intro addr ha
    rw [hframe addr ha]
    exact expandMemB_after m S0 b y addr ha
  have hpoly : PolynomialStored b
      (writeArray (decoderSavedBase t) (expandMemB (decoderAllocEnd t) t m S0 b y t)
        (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t))
      (decoderSavedBase t) (decoderCapacity t) (syndromePoly (eSeq b y) t) :=
    saved_syndrome_polynomialB b t (eSeq b y) _ hsums htail
  exact ⟨by omega,
    writeArray (decoderSavedBase t) (expandMemB (decoderAllocEnd t) t m S0 b y t)
      (fun i => expandMemB (decoderAllocEnd t) t m S0 b y t (S0 + i)) (2 * t),
    hz, hsums, hpoly, htail, hframe2⟩

end BoundedRead

end P21DetBnd

end LinearSetReconciliation327.Main
end S_P21ReadFor6520261123


