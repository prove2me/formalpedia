-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdateArithmetic20261120
-- name    : LinearSetReconciliation327_Main_HintUpdateArithmetic20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:30:52.59604+00:00
-- url     : https://prove2.me/theorems/1af77cf1-caa7-4bc0-83ad-fbdeb4cbfe2d
-- title:
--   LinearSetReconciliation327 — HintUpdateArithmetic (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdateArithmetic20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
abbrev jz (c : Fin 16) (t : ℕ) : List Instr := [iJz c t]
abbrev jmp (t : ℕ) : List Instr := [iJmp t]
abbrev halt : List Instr := [iHalt]
@[simp] theorem execInstr_halt (E : RAMEnv) (s : RAMState) : execInstr .halt E s = s := rfl
@[simp] theorem execInstr_imm (E : RAMEnv) (s : RAMState) (d : Fin 16) (v : ℕ) :
    execInstr (.imm d v) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (v % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_add (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.add d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_sub (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.sub d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) + 2 ^ E.W - (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_mul (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.mul d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) * (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_div (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.div d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) / (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_mod (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.mod d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) % (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_bxor (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.bxor d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) ^^^ (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_shl (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.shl d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) * 2 ^ (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_load (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.load d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((s.mem (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_store (E : RAMEnv) (s : RAMState) (a v : Fin 16) :
    execInstr (.store a v) E s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.regs a) (s.regs v) } := rfl
@[simp] theorem execInstr_qDet (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.qDet d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.det (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_qPerm (E : RAMEnv) (s : RAMState) (d k a : Fin 16) :
    execInstr (.qPerm d k a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.perm (s.regs k) (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_qCoeff (E : RAMEnv) (s : RAMState) (d k a : Fin 16) :
    execInstr (.qCoeff d k a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.coeff (s.regs k) (s.regs a)) % 2 ^ E.W) } := rfl
def Instr.dest? : Instr → Option (Fin 16)
  | .imm d _ => some d
  | .add d _ _ => some d
  | .sub d _ _ => some d
  | .mul d _ _ => some d
  | .div d _ _ => some d
  | .mod d _ _ => some d
  | .band d _ _ => some d
  | .bor d _ _ => some d
  | .bxor d _ _ => some d
  | .shl d _ _ => some d
  | .shr d _ _ => some d
  | .lt d _ _ => some d
  | .load d _ => some d
  | .store _ _ => none
  | .jz _ _ => none
  | .jmp _ => none
  | .qDet d _ => some d
  | .qPerm d _ _ => some d
  | .qPermInv d _ _ => some d
  | .qCoeff d _ _ => some d
  | .halt => none
theorem execInstr_regs (i : Instr) (E : RAMEnv) (s : RAMState) (d : Fin 16)
    (h : i.dest? ≠ some d) : (execInstr i E s).regs d = s.regs d := by
  cases i <;>
    simp only [execInstr, Instr.dest?] at h ⊢ <;>
    first
      | rfl
      | (rw [Function.update_of_ne (fun he => h (by rw [he]))])
@[simp] theorem noBranch_append (a b : List Instr) : NoBranch (a ++ b) ↔ NoBranch a ∧ NoBranch b := by
  induction a with
  | nil => simp
  | cons i t ih => simp [ih, and_assoc]
@[simp] theorem noBranchI_band (d a b : Fin 16) : (iBand d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_shr (d a b : Fin 16) : (iShr d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qPerm (d k a : Fin 16) : (Instr.qPerm d k a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qPermInv (d k a : Fin 16) : (Instr.qPermInv d k a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qCoeff (d k a : Fin 16) : (Instr.qCoeff d k a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
theorem runBlock_regs_frame (code : List Instr) (E : RAMEnv) (s : RAMState) (d : Fin 16)
    (h : ∀ i ∈ code, i.dest? ≠ some d) : (runBlock code E s).regs d = s.regs d := by
  induction code generalizing s with
  | nil => rfl
  | cons i tl ih =>
      rw [runBlock_cons, ih (s := execInstr i E s) (fun j hj => h j (by
        simp only [List.mem_cons]; exact Or.inr hj))]
      exact execInstr_regs i E s d (h i (by simp))
structure UpIt where
  setSt : ℕ := 0
  fromI : ℕ := 0
  srcC : ℕ := 0
  kp : ℕ := 0
  m : ℕ := 0
  ell : ℕ := 0
  nmax : ℕ := 0
  kc : ℕ := 0
  s : ℕ := 0
  base : ℕ := 0
  mode : ℕ := 0
  useC : ℕ := 0
  mOn : ℕ := 0
  stride : ℕ := 0
  cidx : ℕ := 0
  sav : ℕ := 0
def UpIt.fld (it : UpIt) : ℕ → ℕ
  | 0 => it.setSt
  | 1 => it.fromI
  | 2 => it.srcC
  | 3 => it.kp
  | 4 => it.m
  | 5 => it.ell
  | 6 => it.nmax
  | 7 => it.kc
  | 8 => it.s
  | 9 => it.base
  | 10 => it.mode
  | 11 => it.useC
  | 12 => it.mOn
  | 13 => it.stride
  | 14 => it.cidx
  | _ => it.sav
structure UpAbs where
  mem : ℕ → ℕ
  c : ℕ
  f : ℕ
def upvZ1 (E : RAMEnv) (it : UpIt) (ab : UpAbs) : ℕ := E.perm it.kp ab.c % 2 ^ E.W
def upvZ2 (E : RAMEnv) (i : ℕ) (it : UpIt) : ℕ := it.fromI * i % 2 ^ E.W
def upvZ3 (E : RAMEnv) (it : UpIt) : ℕ := (1 % 2 ^ E.W + 2 ^ E.W - it.fromI) % 2 ^ E.W
def upvZ4 (E : RAMEnv) (it : UpIt) (ab : UpAbs) : ℕ := upvZ1 E it ab * upvZ3 E it % 2 ^ E.W
def upvZ5 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvZ4 E it ab + upvZ2 E i it) % 2 ^ E.W
def upvZ6 (E : RAMEnv) (it : UpIt) (ab : UpAbs) : ℕ := it.srcC * ab.c % 2 ^ E.W
def upvZ7 (E : RAMEnv) (it : UpIt) : ℕ := (1 % 2 ^ E.W + 2 ^ E.W - it.srcC) % 2 ^ E.W
def upvZ8 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvZ5 E i it ab * upvZ7 E it % 2 ^ E.W
def upvImg (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvZ8 E i it ab + upvZ6 E it ab) % 2 ^ E.W
def upvJ0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvImg E i it ab % it.m % 2 ^ E.W
def upvPos (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvImg E i it ab / it.m % 2 ^ E.W
def upvY1 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvJ0 E i it ab + 2 ^ E.W - ab.c) % 2 ^ E.W
def upvY2 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvY1 E i it ab * it.setSt % 2 ^ E.W
def upvCn (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (ab.c + upvY2 E i it ab) % 2 ^ E.W
def upvY3 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvJ0 E i it ab * it.ell % 2 ^ E.W
def upvQ (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvY3 E i it ab + it.s) % 2 ^ E.W
def upvY4 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvQ E i it ab * it.nmax % 2 ^ E.W
def upvY5 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvY4 E i it ab + upvPos E i it ab) % 2 ^ E.W
def upvCoin (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  E.coeff it.kc (upvY5 E i it ab) % 2 ^ E.W
def upvY6 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  ab.f * upvCoin E i it ab % 2 ^ E.W
def upvY7 (E : RAMEnv) (it : UpIt) : ℕ := (1 % 2 ^ E.W + 2 ^ E.W - it.fromI) % 2 ^ E.W
def upvY8 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvY6 E i it ab * upvY7 E it % 2 ^ E.W
def upvY9 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvY8 E i it ab + it.fromI) % 2 ^ E.W
def upvY10 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvY9 E i it ab + 2 ^ E.W - ab.f) % 2 ^ E.W
def upvY11 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvY10 E i it ab * it.setSt % 2 ^ E.W
def upvFn (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (ab.f + upvY11 E i it ab) % 2 ^ E.W
def upvX1 (E : RAMEnv) (it : UpIt) : ℕ := (1 % 2 ^ E.W + 2 ^ E.W - it.useC) % 2 ^ E.W
def upvX2 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  it.useC * upvCoin E i it ab % 2 ^ E.W
def upvW0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvX2 E i it ab + upvX1 E it) % 2 ^ E.W
def upvX3 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  it.stride * upvCn E i it ab % 2 ^ E.W
def upvTb (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvX3 E i it ab + it.cidx) % 2 ^ E.W
def upvCard (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  E.det (upvTb E i it ab) % 2 ^ E.W
def upvValid (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (if it.sav < upvCard E i it ab then 1 else 0) % 2 ^ E.W
def upvX4 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvTb E i it ab + it.sav) % 2 ^ E.W
def upvX5 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvX4 E i it ab + 1 % 2 ^ E.W) % 2 ^ E.W
def upvElem (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  E.det (upvX5 E i it ab) % 2 ^ E.W
def upvX6 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvElem E i it ab + 2 ^ E.W - upvQ E i it ab) % 2 ^ E.W
def upvX7 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvX6 E i it ab * it.mode % 2 ^ E.W
def upvX8 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvX7 E i it ab + it.base) % 2 ^ E.W
def upvBit (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvX8 E i it ab + upvQ E i it ab) % 2 ^ E.W
def upvX9 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvValid E i it ab + 2 ^ E.W - upvW0 E i it ab) % 2 ^ E.W
def upvX10 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvX9 E i it ab * it.mode % 2 ^ E.W
def upvWt (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvX10 E i it ab + upvW0 E i it ab) % 2 ^ E.W
def upvX11 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvWt E i it ab * upvFn E i it ab % 2 ^ E.W
def upvMask0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvX11 E i it ab * it.mOn % 2 ^ E.W
def upC1 : List Instr :=
  [ iTbl r10 r7, iAdd r7 r7 r15,
    iTbl r11 r7, iAdd r7 r7 r15,
    iTbl r12 r7, iAdd r7 r7 r15,
    iTbl r13 r7, iAdd r7 r7 r15 ]
def upC2 : List Instr :=
  [ Instr.qPerm r1 r13 r8,
    iMul r2 r11 r0,
    iSub r3 r15 r11,
    iMul r1 r1 r3,
    iAdd r1 r1 r2,
    iMul r2 r12 r8,
    iSub r3 r15 r12,
    iMul r1 r1 r3,
    iAdd r1 r1 r2 ]
def upC3 : List Instr :=
  [ iTbl r3 r7, iAdd r7 r7 r15,
    iMod r2 r1 r3,
    iDiv r1 r1 r3,
    iSub r12 r2 r8,
    iMul r12 r12 r10,
    iAdd r8 r8 r12 ]
def upC4 : List Instr :=
  [ iTbl r3 r7, iAdd r7 r7 r15,
    iMul r3 r2 r3,
    iTbl r4 r7, iAdd r7 r7 r15,
    iTbl r12 r7, iAdd r7 r7 r15,
    iTbl r13 r7, iAdd r7 r7 r15,
    iAdd r3 r3 r13,
    iMul r4 r3 r4,
    iAdd r4 r4 r1,
    Instr.qCoeff r4 r12 r4 ]
def upC5 : List Instr :=
  [ iMul r1 r9 r4,
    iSub r2 r15 r11,
    iMul r1 r1 r2,
    iAdd r1 r1 r11,
    iSub r1 r1 r9,
    iMul r1 r1 r10,
    iAdd r9 r9 r1 ]
def upC6 : List Instr :=
  [ iTbl r10 r7, iAdd r7 r7 r15,
    iTbl r12 r7, iAdd r7 r7 r15,
    iTbl r2 r7, iAdd r7 r7 r15,
    iSub r11 r15 r2,
    iMul r4 r2 r4,
    iAdd r4 r4 r11 ]
def upC7 : List Instr :=
  [ iTbl r13 r7, iAdd r7 r7 r15,
    iTbl r2 r7, iAdd r7 r7 r15,
    iMul r2 r2 r8,
    iTbl r11 r7, iAdd r7 r7 r15,
    iAdd r2 r2 r11,
    iTbl r1 r7, iAdd r7 r7 r15 ]
def upC8 : List Instr :=
  [ iTbl r11 r2,
    iLt r11 r1 r11,
    iAdd r2 r2 r1,
    iAdd r2 r2 r15,
    iTbl r1 r2,
    iSub r2 r1 r3,
    iMul r2 r2 r12,
    iAdd r2 r2 r10,
    iAdd r2 r2 r3,
    iSub r3 r11 r4,
    iMul r3 r3 r12,
    iAdd r3 r3 r4,
    iMul r3 r3 r9,
    iMul r3 r3 r13 ]
theorem upC1_run (E : RAMEnv) (st : RAMState) :
    runBlock upC1 E st =
      { pc := st.pc + 8,
        regs :=
          let M := 2 ^ E.W
          let a1 := (st.regs r7 + st.regs r15) % M
          let a2 := (a1 + st.regs r15) % M
          let a3 := (a2 + st.regs r15) % M
          let a4 := (a3 + st.regs r15) % M
          Function.update (Function.update (Function.update (Function.update (Function.update
            st.regs r10 (E.det (st.regs r7) % M)) r11 (E.det a1 % M)) r12 (E.det a2 % M))
            r13 (E.det a3 % M)) r7 a4,
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC1, runBlock_cons, runBlock_nil, execInstr_add, execInstr_qDet] <;> omega
  · simp [upC1, runBlock_cons, runBlock_nil, execInstr_add, execInstr_qDet]
  · intro d
    fin_cases d <;>
      simp [upC1, runBlock_cons, runBlock_nil, execInstr_add, execInstr_qDet]
theorem upC2_run (E : RAMEnv) (st : RAMState) :
    runBlock upC2 E st =
      { pc := st.pc + 9,
        regs :=
          let M := 2 ^ E.W
          let z1 := E.perm (st.regs r13) (st.regs r8) % M
          let z2 := st.regs r11 * st.regs r0 % M
          let z3 := (st.regs r15 + M - st.regs r11) % M
          let z4 := z1 * z3 % M
          let z5 := (z4 + z2) % M
          let z6 := st.regs r12 * st.regs r8 % M
          let z7 := (st.regs r15 + M - st.regs r12) % M
          let z8 := z5 * z7 % M
          Function.update (Function.update (Function.update st.regs r1 ((z8 + z6) % M)) r2 z6) r3 z7,
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC2, runBlock_cons, runBlock_nil, execInstr_qPerm, execInstr_mul, execInstr_sub,
      execInstr_add] <;> omega
  · simp [upC2, runBlock_cons, runBlock_nil, execInstr_qPerm, execInstr_mul, execInstr_sub,
      execInstr_add]
  · intro d
    fin_cases d <;>
      simp [upC2, runBlock_cons, runBlock_nil, execInstr_qPerm, execInstr_mul, execInstr_sub,
        execInstr_add]
theorem upC3_run (E : RAMEnv) (st : RAMState) :
    runBlock upC3 E st =
      { pc := st.pc + 7,
        regs :=
          let M := 2 ^ E.W
          let F4 := E.det (st.regs r7) % M
          let a1 := (st.regs r7 + st.regs r15) % M
          let j0 := (st.regs r1 % F4) % M
          let pos := (st.regs r1 / F4) % M
          let y1 := (j0 + M - st.regs r8) % M
          let y2 := (y1 * st.regs r10) % M
          let c' := (st.regs r8 + y2) % M
          Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update st.regs r3 F4) r7 a1) r2 j0) r1 pos) r12 y2) r8 c',
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC3, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mod,
      execInstr_div, execInstr_sub, execInstr_mul] <;> omega
  · simp [upC3, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mod,
      execInstr_div, execInstr_sub, execInstr_mul]
  · intro d
    fin_cases d <;>
      simp [upC3, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mod,
        execInstr_div, execInstr_sub, execInstr_mul]
theorem upC4_run (E : RAMEnv) (st : RAMState) :
    runBlock upC4 E st =
      { pc := st.pc + 13,
        regs :=
          let M := 2 ^ E.W
          let F5 := E.det (st.regs r7) % M
          let a1 := (st.regs r7 + st.regs r15) % M
          let y3 := (st.regs r2 * F5) % M
          let F6 := E.det a1 % M
          let a2 := (a1 + st.regs r15) % M
          let F7 := E.det a2 % M
          let a3 := (a2 + st.regs r15) % M
          let F8 := E.det a3 % M
          let a4 := (a3 + st.regs r15) % M
          let q := (y3 + F8) % M
          let y4 := (q * F6) % M
          let y5 := (y4 + st.regs r1) % M
          let co := E.coeff F7 y5 % M
          Function.update (Function.update (Function.update (Function.update (Function.update
            st.regs r3 q) r4 co) r12 F7) r13 F8) r7 a4,
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC4, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mul,
      execInstr_qCoeff] <;> omega
  · simp [upC4, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mul,
      execInstr_qCoeff]
  · intro d
    fin_cases d <;>
      simp [upC4, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mul,
        execInstr_qCoeff]
theorem upC5_run (E : RAMEnv) (st : RAMState) :
    runBlock upC5 E st =
      { pc := st.pc + 7,
        regs :=
          let M := 2 ^ E.W
          let y6 := (st.regs r9 * st.regs r4) % M
          let y7 := (st.regs r15 + M - st.regs r11) % M
          let y8 := (y6 * y7) % M
          let y9 := (y8 + st.regs r11) % M
          let y10 := (y9 + M - st.regs r9) % M
          let y11 := (y10 * st.regs r10) % M
          let f' := (st.regs r9 + y11) % M
          Function.update (Function.update (Function.update st.regs r1 y11) r2 y7) r9 f',
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC5, runBlock_cons, runBlock_nil, execInstr_mul, execInstr_sub, execInstr_add] <;> omega
  · simp [upC5, runBlock_cons, runBlock_nil, execInstr_mul, execInstr_sub, execInstr_add]
  · intro d
    fin_cases d <;>
      simp [upC5, runBlock_cons, runBlock_nil, execInstr_mul, execInstr_sub, execInstr_add]
theorem upC6_run (E : RAMEnv) (st : RAMState) :
    runBlock upC6 E st =
      { pc := st.pc + 9,
        regs :=
          let M := 2 ^ E.W
          let F9 := E.det (st.regs r7) % M
          let a1 := (st.regs r7 + st.regs r15) % M
          let F10 := E.det a1 % M
          let a2 := (a1 + st.regs r15) % M
          let F11 := E.det a2 % M
          let a3 := (a2 + st.regs r15) % M
          let x1 := (st.regs r15 + M - F11) % M
          let x2 := (F11 * st.regs r4) % M
          let w0 := (x2 + x1) % M
          Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update st.regs r10 F9) r7 a3) r12 F10) r2 F11) r11 x1) r4 w0,
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC6, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_sub,
      execInstr_mul] <;> omega
  · simp [upC6, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_sub,
      execInstr_mul]
  · intro d
    fin_cases d <;>
      simp [upC6, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_sub,
        execInstr_mul]
theorem upC7_run (E : RAMEnv) (st : RAMState) :
    runBlock upC7 E st =
      { pc := st.pc + 10,
        regs :=
          let M := 2 ^ E.W
          let F12 := E.det (st.regs r7) % M
          let a1 := (st.regs r7 + st.regs r15) % M
          let F13 := E.det a1 % M
          let a2 := (a1 + st.regs r15) % M
          let x3 := (F13 * st.regs r8) % M
          let F14 := E.det a2 % M
          let a3 := (a2 + st.regs r15) % M
          let tb := (x3 + F14) % M
          let F15 := E.det a3 % M
          let a4 := (a3 + st.regs r15) % M
          Function.update (Function.update (Function.update (Function.update (Function.update
            st.regs r13 F12) r2 tb) r11 F14) r1 F15) r7 a4,
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC7, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mul] <;> omega
  · simp [upC7, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mul]
  · intro d
    fin_cases d <;>
      simp [upC7, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_add, execInstr_mul]
theorem upC8_run (E : RAMEnv) (st : RAMState) :
    runBlock upC8 E st =
      { pc := st.pc + 14,
        regs :=
          let M := 2 ^ E.W
          let card := E.det (st.regs r2) % M
          let valid := (if st.regs r1 < card then 1 else 0) % M
          let x4 := (st.regs r2 + st.regs r1) % M
          let x5 := (x4 + st.regs r15) % M
          let elem := E.det x5 % M
          let x6 := (elem + M - st.regs r3) % M
          let x7 := (x6 * st.regs r12) % M
          let x8 := (x7 + st.regs r10) % M
          let bit := (x8 + st.regs r3) % M
          let x9 := (valid + M - st.regs r4) % M
          let x10 := (x9 * st.regs r12) % M
          let w := (x10 + st.regs r4) % M
          let x11 := (w * st.regs r9) % M
          let mask0 := (x11 * st.regs r13) % M
          Function.update (Function.update (Function.update (Function.update st.regs r11 valid)
            r2 bit) r3 mask0) r1 elem,
        mem := st.mem } := by
  refine ramState_eq_of _ _ ?_ ?_ ?_
  · simp [upC8, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_lt, execInstr_add,
      execInstr_sub, execInstr_mul] <;> omega
  · simp [upC8, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_lt, execInstr_add,
      execInstr_sub, execInstr_mul]
  · intro d
    fin_cases d <;>
      simp [upC8, runBlock_cons, runBlock_nil, execInstr_qDet, execInstr_lt, execInstr_add,
        execInstr_sub, execInstr_mul]
set_option maxHeartbeats 1600000
theorem add_mod_pow_eq (W a k : ℕ) (hk : k ≤ 16) (ha : a + 16 < 2 ^ W) :
    (a + k) % 2 ^ W = a + k :=
  Nat.mod_eq_of_lt (by omega)
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
structure DecIt where
  bit : ℕ := 0
  cr : ℕ := 0
  crN : ℕ := 0
  crT : ℕ := 0
  crOff : ℕ := 0
  rule : ℕ := 0
  vN : ℕ := 0
  vT : ℕ := 0
  vM : ℕ := 0
  vEll : ℕ := 0
  colBase : ℕ := 0
  childBase : ℕ := 0
  vBc : ℕ := 0
  vK : ℕ := 0
  aux : ℕ := 0
def DecIt.fld (it : DecIt) : ℕ → ℕ
  | 0 => it.bit
  | 1 => it.cr
  | 2 => it.crN
  | 3 => it.crT
  | 4 => it.crOff
  | 5 => it.rule
  | 6 => it.vN
  | 7 => it.vT
  | 8 => it.vM
  | 9 => it.vEll
  | 10 => it.colBase
  | 11 => it.childBase
  | 12 => it.vBc
  | 13 => it.vK
  | 14 => it.aux
  | _ => it.aux
structure DecHdr where
  dcnt : ℕ := 0
  colB : ℕ := 0
  recB : ℕ := 0
  hBc : ℕ := 0
  sM : ℕ := 0
  sWords : ℕ := 0
  outB : ℕ := 0
  h7 : ℕ := 0
  h8 : ℕ := 0
  h9 : ℕ := 0
  h10 : ℕ := 0
  h11 : ℕ := 0
  h12 : ℕ := 0
  h13 : ℕ := 0
  h14 : ℕ := 0
  h15 : ℕ := 0
def DecHdr.fld (hd : DecHdr) : ℕ → ℕ
  | 0 => hd.dcnt
  | 1 => hd.colB
  | 2 => hd.recB
  | 3 => hd.hBc
  | 4 => hd.sM
  | 5 => hd.sWords
  | 6 => hd.outB
  | 7 => hd.h7
  | 8 => hd.h8
  | 9 => hd.h9
  | 10 => hd.h10
  | 11 => hd.h11
  | 12 => hd.h12
  | 13 => hd.h13
  | 14 => hd.h14
  | _ => hd.h15
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def upCore : List Instr := upC1 ++ (upC2 ++ (upC3 ++ (upC4 ++ (upC5 ++ (upC6 ++ (upC7 ++ upC8))))))
theorem upCore_length : upCore.length = 77 := rfl
theorem upCore_noBranch : NoBranch upCore := by
  simp [upCore, upC1, upC2, upC3, upC4, upC5, upC6, upC7, upC8]
theorem upCore_dest_ne_r0 : ∀ i ∈ upCore, i.dest? ≠ some r0 := by
  simp [upCore, upC1, upC2, upC3, upC4, upC5, upC6, upC7, upC8, Instr.dest?]
theorem upCore_dest_ne_r5 : ∀ i ∈ upCore, i.dest? ≠ some r5 := by
  simp [upCore, upC1, upC2, upC3, upC4, upC5, upC6, upC7, upC8, Instr.dest?]
def upCoreRun (E : RAMEnv) (st : RAMState) : RAMState := runBlock upCore E st
theorem upCoreRun_eq (E : RAMEnv) (st : RAMState) : upCoreRun E st = runBlock upCore E st := by unfold upCoreRun <;> rfl
attribute [irreducible] upCoreRun
theorem upCore_facts (E : RAMEnv) (st : RAMState) (i : ℕ) (it : UpIt) (ab : UpAbs) (a : ℕ)
    (hW : 1 < 2 ^ E.W) (h0 : st.regs r0 = i) (h7 : st.regs r7 = a) (h8 : st.regs r8 = ab.c)
    (h9 : st.regs r9 = ab.f) (hmem : st.mem = ab.mem) (h15 : st.regs r15 = 1 % 2 ^ E.W)
    (h16 : a + 16 < 2 ^ E.W)
    (hF : ∀ j, j < 16 → E.det (a + j) % 2 ^ E.W = it.fld j) :
    (upCoreRun E st).pc = st.pc + 77 ∧
      (upCoreRun E st).regs r0 = i ∧
      (upCoreRun E st).regs r5 = st.regs r5 ∧
      (upCoreRun E st).regs r7 = a + 16 ∧
      (upCoreRun E st).regs r8 = upvCn E i it ab ∧
      (upCoreRun E st).regs r9 = upvFn E i it ab ∧
      (upCoreRun E st).regs r2 = upvBit E i it ab ∧
      (upCoreRun E st).regs r3 = upvMask0 E i it ab ∧
      (upCoreRun E st).mem = ab.mem := by
  have h1M : 1 % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hF0 : E.det a % 2 ^ E.W = it.fld 0 := by simpa using hF 0 (by norm_num)
  have hb : runBlock upCore E st =
      runBlock upC8 E (runBlock upC7 E (runBlock upC6 E (runBlock upC5 E
        (runBlock upC4 E (runBlock upC3 E (runBlock upC2 E (runBlock upC1 E st))))))) := by
    simp only [upCore, runBlock_append]
  rw [upCoreRun_eq, hb]
  set s1 : RAMState := runBlock upC1 E st with hs1
  set s2 : RAMState := runBlock upC2 E s1 with hs2
  set s3 : RAMState := runBlock upC3 E s2 with hs3
  set s4 : RAMState := runBlock upC4 E s3 with hs4
  set s5 : RAMState := runBlock upC5 E s4 with hs5
  set s6 : RAMState := runBlock upC6 E s5 with hs6
  set s7 : RAMState := runBlock upC7 E s6 with hs7
  set s8 : RAMState := runBlock upC8 E s7 with hs8
  have hL1 : s1 = _ := hs1
  have hL2 : s2 = _ := hs2
  have hL3 : s3 = _ := hs3
  have hL4 : s4 = _ := hs4
  have hL5 : s5 = _ := hs5
  have hL6 : s6 = _ := hs6
  have hL7 : s7 = _ := hs7
  have hL8 : s8 = _ := hs8
  rw [upC1_run] at hL1
  rw [upC2_run] at hL2
  rw [upC3_run] at hL3
  rw [upC4_run] at hL4
  rw [upC5_run] at hL5
  rw [upC6_run] at hL6
  rw [upC7_run] at hL7
  rw [upC8_run] at hL8
  have e1 : (a + 1) % 2 ^ E.W = a + 1 := add_mod_pow_eq E.W a 1 (by norm_num) h16
  have e2 : (a + 1 + 1) % 2 ^ E.W = a + 2 := add_mod_pow_eq E.W a 2 (by norm_num) h16
  have e3 : (a + 2 + 1) % 2 ^ E.W = a + 3 := add_mod_pow_eq E.W a 3 (by norm_num) h16
  have e4 : (a + 3 + 1) % 2 ^ E.W = a + 4 := add_mod_pow_eq E.W a 4 (by norm_num) h16
  have e5 : (a + 4 + 1) % 2 ^ E.W = a + 5 := add_mod_pow_eq E.W a 5 (by norm_num) h16
  have e6 : (a + 5 + 1) % 2 ^ E.W = a + 6 := add_mod_pow_eq E.W a 6 (by norm_num) h16
  have e7 : (a + 6 + 1) % 2 ^ E.W = a + 7 := add_mod_pow_eq E.W a 7 (by norm_num) h16
  have e8 : (a + 7 + 1) % 2 ^ E.W = a + 8 := add_mod_pow_eq E.W a 8 (by norm_num) h16
  have e9 : (a + 8 + 1) % 2 ^ E.W = a + 9 := add_mod_pow_eq E.W a 9 (by norm_num) h16
  have e10 : (a + 9 + 1) % 2 ^ E.W = a + 10 := add_mod_pow_eq E.W a 10 (by norm_num) h16
  have e11 : (a + 10 + 1) % 2 ^ E.W = a + 11 := add_mod_pow_eq E.W a 11 (by norm_num) h16
  have e12 : (a + 11 + 1) % 2 ^ E.W = a + 12 := add_mod_pow_eq E.W a 12 (by norm_num) h16
  have e13 : (a + 12 + 1) % 2 ^ E.W = a + 13 := add_mod_pow_eq E.W a 13 (by norm_num) h16
  have e14 : (a + 13 + 1) % 2 ^ E.W = a + 14 := add_mod_pow_eq E.W a 14 (by norm_num) h16
  have e15 : (a + 14 + 1) % 2 ^ E.W = a + 15 := add_mod_pow_eq E.W a 15 (by norm_num) h16
  have e16 : (a + 15 + 1) % 2 ^ E.W = a + 16 := add_mod_pow_eq E.W a 16 (by norm_num) h16
  have v1_0 : s1.regs r0 = i := by rw [hL1]; simp [h0]
  have v1_8 : s1.regs r8 = ab.c := by rw [hL1]; simp [h8]
  have v1_9 : s1.regs r9 = ab.f := by rw [hL1]; simp [h9]
  have v1_15 : s1.regs r15 = 1 % 2 ^ E.W := by rw [hL1]; simp [h15]
  have v1_10 : s1.regs r10 = it.fld 0 := by rw [hL1]; simp [h7, hF0, UpIt.fld]
  have v1_11 : s1.regs r11 = it.fld 1 := by
    rw [hL1]; simp [h7, h15, h1M, e1, hF 1 (by norm_num), UpIt.fld]
  have v1_12 : s1.regs r12 = it.fld 2 := by
    rw [hL1]; simp [h7, h15, h1M, e1, e2, hF 2 (by norm_num), UpIt.fld]
  have v1_13 : s1.regs r13 = it.fld 3 := by
    rw [hL1]; simp [h7, h15, h1M, e1, e2, e3, hF 3 (by norm_num), UpIt.fld]
  have v1_7 : s1.regs r7 = a + 4 := by
    rw [hL1]; simp [h7, h15, h1M, e1, e2, e3, e4]
  have v2_1 : s2.regs r1 = upvImg E i it ab := by
    rw [hL2]
    simp [upvImg, upvZ1, upvZ2, upvZ3, upvZ4, upvZ5, upvZ6, upvZ7, upvZ8, v1_0, v1_8, v1_11,
      v1_12, v1_13, v1_15, h1M, UpIt.fld]
  have v2_2 : s2.regs r2 = upvZ6 E it ab := by
    rw [hL2]; simp [upvZ6, v1_8, v1_12, UpIt.fld]
  have v2_3 : s2.regs r3 = upvZ7 E it := by
    rw [hL2]; simp [upvZ7, v1_12, v1_15, h1M, UpIt.fld]
  have v2_7 : s2.regs r7 = a + 4 := by rw [hL2]; simp [v1_7]
  have v2_8 : s2.regs r8 = ab.c := by rw [hL2]; simp [v1_8]
  have v2_9 : s2.regs r9 = ab.f := by rw [hL2]; simp [v1_9]
  have v2_10 : s2.regs r10 = it.fld 0 := by rw [hL2]; simp [v1_10]
  have v2_11 : s2.regs r11 = it.fld 1 := by rw [hL2]; simp [v1_11]
  have v2_15 : s2.regs r15 = 1 % 2 ^ E.W := by rw [hL2]; simp [v1_15]
  have v3_3 : s3.regs r3 = it.fld 4 := by
    rw [hL3]; simp [v2_7, hF 4 (by norm_num), UpIt.fld]
  have v3_2 : s3.regs r2 = upvJ0 E i it ab := by
    rw [hL3]; simp [upvJ0, v2_1, v2_7, hF 4 (by norm_num), UpIt.fld]
  have v3_1 : s3.regs r1 = upvPos E i it ab := by
    rw [hL3]; simp [upvPos, v2_1, v2_7, hF 4 (by norm_num), UpIt.fld]
  have v3_8 : s3.regs r8 = upvCn E i it ab := by
    rw [hL3]
    simp [upvCn, upvY1, upvY2, upvJ0, v2_1, v2_8, v2_10, v2_7, hF 4 (by norm_num), UpIt.fld]
  have v3_7 : s3.regs r7 = a + 5 := by
    rw [hL3]; simp [v2_7, v2_15, h1M, e5]
  have v3_10 : s3.regs r10 = it.fld 0 := by rw [hL3]; simp [v2_10]
  have v3_11 : s3.regs r11 = it.fld 1 := by rw [hL3, hL2]; simp [v1_11]
  have v3_9 : s3.regs r9 = ab.f := by rw [hL3, hL2, hL1]; simp [h9]
  have v3_15 : s3.regs r15 = 1 % 2 ^ E.W := by rw [hL3, hL2, hL1]; simp [h15]
  have v4_3 : s4.regs r3 = upvQ E i it ab := by
    rw [hL4]
    simp [upvQ, upvY3, v3_2, v3_7, v3_15, h1M, e6, e7, e8, hF 5 (by norm_num),
      hF 8 (by norm_num), UpIt.fld]
  have v4_4 : s4.regs r4 = upvCoin E i it ab := by
    rw [hL4]
    simp [upvCoin, upvY3, upvY4, upvY5, upvQ, upvJ0, v3_2, v3_1, v3_7, v3_15, h1M, e6, e7, e8,
      hF 5 (by norm_num), hF 6 (by norm_num), hF 7 (by norm_num), hF 8 (by norm_num), UpIt.fld]
  have v4_12 : s4.regs r12 = it.fld 7 := by
    rw [hL4]
    simp [v3_7, v3_15, h1M, e6, e7, hF 7 (by norm_num), UpIt.fld]
  have v4_13 : s4.regs r13 = it.fld 8 := by
    rw [hL4]
    simp [v3_7, v3_15, h1M, e6, e7, e8, hF 8 (by norm_num), UpIt.fld]
  have v4_7 : s4.regs r7 = a + 9 := by
    rw [hL4]; simp [v3_7, v3_15, h1M, e6, e7, e8, e9]
  have v4_9 : s4.regs r9 = ab.f := by rw [hL4, hL3, hL2, hL1]; simp [h9]
  have v4_10 : s4.regs r10 = it.fld 0 := by rw [hL4, hL3]; simp [v2_10]
  have v4_11 : s4.regs r11 = it.fld 1 := by rw [hL4, hL3, hL2]; simp [v1_11]
  have v4_15 : s4.regs r15 = 1 % 2 ^ E.W := by rw [hL4, hL3, hL2, hL1]; simp [h15]
  have v5_9 : s5.regs r9 = upvFn E i it ab := by
    rw [hL5]
    simp [upvFn, upvY6, upvY7, upvY8, upvY9, upvY10, upvY11, v4_4, v4_9, v4_10, v4_11, v4_15,
      h1M, UpIt.fld]
  have v5_7 : s5.regs r7 = a + 9 := by rw [hL5]; simp [v4_7]
  have v5_4 : s5.regs r4 = upvCoin E i it ab := by rw [hL5]; simp [v4_4]
  have v5_3 : s5.regs r3 = upvQ E i it ab := by rw [hL5]; simp [v4_3]
  have v5_10 : s5.regs r10 = it.fld 0 := by rw [hL5, hL4, hL3]; simp [v2_10]
  have v5_11 : s5.regs r11 = it.fld 1 := by rw [hL5, hL4, hL3, hL2]; simp [v1_11]
  have v5_15 : s5.regs r15 = 1 % 2 ^ E.W := by rw [hL5, hL4, hL3, hL2, hL1]; simp [h15]
  have v6_10 : s6.regs r10 = it.fld 9 := by
    rw [hL6]; simp [v5_7, hF 9 (by norm_num), UpIt.fld]
  have v6_12 : s6.regs r12 = it.fld 10 := by
    rw [hL6]; simp [v5_7, v5_15, h1M, e10, hF 10 (by norm_num), UpIt.fld]
  have v6_2 : s6.regs r2 = it.fld 11 := by
    rw [hL6]; simp [v5_7, v5_15, h1M, e10, e11, hF 11 (by norm_num), UpIt.fld]
  have v6_11 : s6.regs r11 = upvX1 E it := by
    rw [hL6]
    simp [upvX1, v5_7, v5_15, h1M, e10, e11, hF 11 (by norm_num), UpIt.fld]
  have v6_4 : s6.regs r4 = upvW0 E i it ab := by
    rw [hL6]
    simp [upvW0, upvX1, upvX2, v5_4, v5_7, v5_15, h1M, e10, e11, hF 11 (by norm_num),
      UpIt.fld]
  have v6_7 : s6.regs r7 = a + 12 := by
    rw [hL6]; simp [v5_7, v5_15, h1M, e10, e11, e12]
  have v6_3 : s6.regs r3 = upvQ E i it ab := by rw [hL6]; simp [v5_3]
  have v6_9 : s6.regs r9 = upvFn E i it ab := by rw [hL6]; simp [v5_9]
  have v6_8 : s6.regs r8 = upvCn E i it ab := by rw [hL6, hL5, hL4]; simpa using v3_8
  have v6_15 : s6.regs r15 = 1 % 2 ^ E.W :=
    by rw [hL6, hL5, hL4, hL3, hL2, hL1]; simp [h15]
  have v6_mem : s6.mem = ab.mem := by rw [hL6, hL5, hL4, hL3, hL2, hL1]; simp [hmem]
  have v7_13 : s7.regs r13 = it.fld 12 := by
    rw [hL7]; simp [v6_7, hF 12 (by norm_num), UpIt.fld]
  have v7_2 : s7.regs r2 = upvTb E i it ab := by
    rw [hL7]
    simp [upvTb, upvX3, v6_8, v6_7, v6_15, h1M, e13, e14, hF 13 (by norm_num),
      hF 14 (by norm_num), UpIt.fld]
  have v7_11 : s7.regs r11 = it.fld 14 := by
    rw [hL7]; simp [v6_7, v6_15, h1M, e13, e14, hF 14 (by norm_num), UpIt.fld]
  have v7_1 : s7.regs r1 = it.fld 15 := by
    rw [hL7]; simp [v6_7, v6_15, h1M, e13, e14, e15, hF 15 (by norm_num), UpIt.fld]
  have v7_7 : s7.regs r7 = a + 16 := by
    rw [hL7]; simp [v6_7, v6_15, h1M, e13, e14, e15, e16]
  have v7_3 : s7.regs r3 = upvQ E i it ab := by rw [hL7]; simp [v6_3]
  have v7_12 : s7.regs r12 = it.fld 10 := by rw [hL7]; simp [v6_12]
  have v7_10 : s7.regs r10 = it.fld 9 := by rw [hL7]; simp [v6_10]
  have v7_4 : s7.regs r4 = upvW0 E i it ab := by rw [hL7]; simp [v6_4]
  have v7_9 : s7.regs r9 = upvFn E i it ab := by rw [hL7]; simp [v6_9]
  have v7_15 : s7.regs r15 = 1 % 2 ^ E.W := by rw [hL7, hL6, hL5, hL4, hL3, hL2, hL1]; simp [h15]
  have v8_11 : s8.regs r11 = upvValid E i it ab := by
    rw [hL8]
    simp only [upvValid, upvCard, v7_2, v7_1, UpIt.fld]
    by_cases h : it.sav < E.det (upvTb E i it ab) % 2 ^ E.W <;> simp [h]
  have v8_2 : s8.regs r2 = upvBit E i it ab := by
    rw [hL8]
    simp [upvBit, upvX4, upvX5, upvX6, upvX7, upvX8, upvElem, upvQ, v7_2, v7_1, v7_3,
      v7_12, v7_10, v7_15, h1M, UpIt.fld]
  have v8_3 : s8.regs r3 = upvMask0 E i it ab := by
    rw [hL8]
    simp [upvMask0, upvX11, upvWt, upvX10, upvX9, upvW0, upvX2, upvX1, upvValid, upvCard, upvFn,
      upvY11, upvY10, upvY9, upvY8, upvY7, upvY6, upvCoin, upvY5, upvY4, upvY3, upvQ, upvTb,
      upvX3, upvCn, upvY2, upvY1, upvPos, upvJ0, upvImg, upvZ1, upvZ2, upvZ3, upvZ4, upvZ5, upvZ6,
      upvZ7, upvZ8, v7_2, v7_1, v7_3, v7_4, v7_9, v7_10, v7_12, v7_13, v7_15, h1M,
      UpIt.fld] <;>
    (by_cases h : it.sav < E.det (upvTb E i it ab) % 2 ^ E.W <;> simp [h])
  have v8_1 : s8.regs r1 = upvElem E i it ab := by
    rw [hL8]; simp [upvElem, upvX5, upvX4, v7_2, v7_1, v7_15, h1M, UpIt.fld]
  have v8_mem : s8.mem = ab.mem := by rw [hL8, hL7, hL6, hL5, hL4, hL3, hL2, hL1]; simp [hmem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, v8_2, v8_3, v8_mem⟩
  · rw [← hb, runBlock_pc upCore E st upCore_noBranch, upCore_length]
  · rw [← hb]
    exact (runBlock_regs_frame upCore E st r0 upCore_dest_ne_r0).trans h0
  · rw [← hb]
    exact runBlock_regs_frame upCore E st r5 upCore_dest_ne_r5
  · rw [hL8]; simpa using v7_7
  · rw [hL8, hL7, hL6, hL5, hL4]; simpa using v3_8
  · rw [hL8]; simpa using v7_9
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upShiftDetEnv (E : RAMEnv) (beta : ℕ) : RAMEnv :=
  { E with det := fun a => E.det ((beta + a) % 2 ^ E.W) }
def upPureInstruction : Instr → Prop
  | .load _ _ | .store _ _ | .jmp _ | .jz _ _ | .halt => False
  | _ => True
def upRegTarget : Instr → Option (Fin 16)
  | .imm d _ | .add d _ _ | .sub d _ _ | .mul d _ _ | .div d _ _ | .mod d _ _
  | .band d _ _ | .bor d _ _ | .bxor d _ _ | .shl d _ _ | .shr d _ _ | .lt d _ _
  | .load d _ | .qDet d _ | .qPerm d _ _ | .qPermInv d _ _ | .qCoeff d _ _ => some d
  | _ => none
def upTranslateInstr (rho : Equiv.Perm (Fin 16)) : Instr → List Instr
  | .imm d v => [.imm (rho d) v]
  | .add d a b => [.add (rho d) (rho a) (rho b)]
  | .sub d a b => [.sub (rho d) (rho a) (rho b)]
  | .mul d a b => [.mul (rho d) (rho a) (rho b)]
  | .div d a b => [.div (rho d) (rho a) (rho b)]
  | .mod d a b => [.mod (rho d) (rho a) (rho b)]
  | .band d a b => [.band (rho d) (rho a) (rho b)]
  | .bor d a b => [.bor (rho d) (rho a) (rho b)]
  | .bxor d a b => [.bxor (rho d) (rho a) (rho b)]
  | .shl d a b => [.shl (rho d) (rho a) (rho b)]
  | .shr d a b => [.shr (rho d) (rho a) (rho b)]
  | .lt d a b => [.lt (rho d) (rho a) (rho b)]
  | .qDet d a => [.add (rho d) 14 (rho a), .qDet (rho d) (rho d)]
  | .qPerm d k a => [.qPerm (rho d) (rho k) (rho a)]
  | .qPermInv d k a => [.qPermInv (rho d) (rho k) (rho a)]
  | .qCoeff d k a => [.qCoeff (rho d) (rho k) (rho a)]
  | _ => []
def upTranslateCode (rho : Equiv.Perm (Fin 16)) (code : List Instr) : List Instr :=
  code.flatMap (upTranslateInstr rho)
def upRegsRelated (rho : Equiv.Perm (Fin 16)) (s t : RAMState) : Prop :=
  ∀ r, t.regs (rho r) = s.regs r
theorem upTranslateInstr_related (rho : Equiv.Perm (Fin 16)) (E : RAMEnv)
    (beta : ℕ) (s t : RAMState) (ins : Instr)
    (hp : upPureInstruction ins) (hr : upRegsRelated rho s t) (hb : t.regs 14 = beta) :
    upRegsRelated rho (execInstr ins (upShiftDetEnv E beta) s)
      (runBlock (upTranslateInstr rho ins) E t) := by
  intro r
  have hEq : ∀ a b : Fin 16, (rho a = rho b) ↔ a = b := fun a b => rho.injective.eq_iff
  cases ins <;> simp_all [upPureInstruction, upTranslateInstr, upRegsRelated,
    runBlock, execInstr, upShiftDetEnv, Function.update_apply, hEq]
theorem upTranslateInstr_mem (rho : Equiv.Perm (Fin 16)) (E : RAMEnv)
    (t : RAMState) (ins : Instr) (hp : upPureInstruction ins) :
    (runBlock (upTranslateInstr rho ins) E t).mem = t.mem := by
  cases ins <;> simp_all [upPureInstruction, upTranslateInstr, runBlock, execInstr]
theorem upTranslateInstr_noBranch (rho : Equiv.Perm (Fin 16)) (ins : Instr)
    (hp : upPureInstruction ins) : NoBranch (upTranslateInstr rho ins) := by
  cases ins <;> simp_all [upPureInstruction, upTranslateInstr, NoBranch, Instr.NoBranchI]
theorem upTranslateInstr_frame (rho : Equiv.Perm (Fin 16)) (E : RAMEnv)
    (t : RAMState) (ins : Instr) (r : Fin 16) (hp : upPureInstruction ins)
    (hd : (upRegTarget ins).map rho ≠ some r) :
    (runBlock (upTranslateInstr rho ins) E t).regs r = t.regs r := by
  cases ins <;> simp_all [upPureInstruction, upRegTarget, upTranslateInstr,
    runBlock, execInstr, Function.update_apply, eq_comm]
theorem upTranslateCode_related (rho : Equiv.Perm (Fin 16)) (E : RAMEnv)
    (beta : ℕ) (code : List Instr) (s t : RAMState)
    (hp : ∀ ins ∈ code, upPureInstruction ins)
    (hd : ∀ ins ∈ code, (upRegTarget ins).map rho ≠ some 14)
    (hr : upRegsRelated rho s t) (hb : t.regs 14 = beta) :
    upRegsRelated rho (runBlock code (upShiftDetEnv E beta) s)
      (runBlock (upTranslateCode rho code) E t) := by
  induction code generalizing s t with
  | nil => exact hr
  | cons ins rest ih =>
      have hpI := hp ins (by simp)
      have hdI := hd ins (by simp)
      have hRel := upTranslateInstr_related rho E beta s t ins hpI hr hb
      have hBase := (upTranslateInstr_frame rho E t ins 14 hpI hdI).trans hb
      have hRest := ih (execInstr ins (upShiftDetEnv E beta) s)
        (runBlock (upTranslateInstr rho ins) E t)
        (fun op ho => hp op (by simp [ho])) (fun op ho => hd op (by simp [ho])) hRel hBase
      simpa only [upTranslateCode, List.flatMap_cons, runBlock_append, runBlock_cons] using hRest
theorem upTranslateCode_mem (rho : Equiv.Perm (Fin 16)) (E : RAMEnv)
    (code : List Instr) (t : RAMState) (hp : ∀ ins ∈ code, upPureInstruction ins) :
    (runBlock (upTranslateCode rho code) E t).mem = t.mem := by
  induction code generalizing t with
  | nil => rfl
  | cons ins rest ih =>
      rw [upTranslateCode, List.flatMap_cons, runBlock_append]
      exact (ih _ (fun op ho => hp op (by simp [ho]))).trans
        (upTranslateInstr_mem rho E t ins (hp ins (by simp)))
theorem upTranslateCode_frame (rho : Equiv.Perm (Fin 16)) (E : RAMEnv)
    (code : List Instr) (t : RAMState) (r : Fin 16)
    (hp : ∀ ins ∈ code, upPureInstruction ins)
    (hd : ∀ ins ∈ code, (upRegTarget ins).map rho ≠ some r) :
    (runBlock (upTranslateCode rho code) E t).regs r = t.regs r := by
  induction code generalizing t with
  | nil => rfl
  | cons ins rest ih =>
      rw [upTranslateCode, List.flatMap_cons, runBlock_append]
      exact (ih _ (fun op ho => hp op (by simp [ho])) (fun op ho => hd op (by simp [ho]))).trans
        (upTranslateInstr_frame rho E t ins r (hp ins (by simp)) (hd ins (by simp)))
theorem upNoBranch_append (a b : List Instr) : NoBranch (a ++ b) ↔ NoBranch a ∧ NoBranch b := by
  induction a with
  | nil => simp [NoBranch]
  | cons i rest ih => simp [NoBranch, ih, and_assoc]
theorem upTranslateCode_noBranch (rho : Equiv.Perm (Fin 16)) (code : List Instr)
    (hp : ∀ ins ∈ code, upPureInstruction ins) : NoBranch (upTranslateCode rho code) := by
  induction code with
  | nil => trivial
  | cons ins rest ih =>
      rw [upTranslateCode, List.flatMap_cons, upNoBranch_append]
      exact ⟨upTranslateInstr_noBranch rho ins (hp ins (by simp)),
        ih (fun op ho => hp op (by simp [ho]))⟩
end LinearSetReconciliation327.Main
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def upBaseRename : Equiv.Perm (Fin 16) := Equiv.swap 6 15
@[simp] theorem upBaseRename_0 : upBaseRename 0 = 0 := by decide
@[simp] theorem upBaseRename_1 : upBaseRename 1 = 1 := by decide
@[simp] theorem upBaseRename_2 : upBaseRename 2 = 2 := by decide
@[simp] theorem upBaseRename_3 : upBaseRename 3 = 3 := by decide
@[simp] theorem upBaseRename_4 : upBaseRename 4 = 4 := by decide
@[simp] theorem upBaseRename_5 : upBaseRename 5 = 5 := by decide
@[simp] theorem upBaseRename_6 : upBaseRename 6 = 15 := by decide
@[simp] theorem upBaseRename_7 : upBaseRename 7 = 7 := by decide
@[simp] theorem upBaseRename_8 : upBaseRename 8 = 8 := by decide
@[simp] theorem upBaseRename_9 : upBaseRename 9 = 9 := by decide
@[simp] theorem upBaseRename_10 : upBaseRename 10 = 10 := by decide
@[simp] theorem upBaseRename_11 : upBaseRename 11 = 11 := by decide
@[simp] theorem upBaseRename_12 : upBaseRename 12 = 12 := by decide
@[simp] theorem upBaseRename_13 : upBaseRename 13 = 13 := by decide
@[simp] theorem upBaseRename_14 : upBaseRename 14 = 14 := by decide
@[simp] theorem upBaseRename_15 : upBaseRename 15 = 6 := by decide
def upBasedCore : List Instr := upTranslateCode upBaseRename upCore
theorem upBasedCore_length : upBasedCore.length = 95 := rfl
theorem upCore_pure : ∀ ins ∈ upCore, upPureInstruction ins := by
  simp [upCore, upC1, upC2, upC3, upC4, upC5, upC6, upC7, upC8, upPureInstruction]
set_option maxHeartbeats 1600000 in
theorem upCore_protected (r : Fin 16) (hr : r = 0 ∨ r = 14 ∨ r = 15) :
    ∀ ins ∈ upCore, (upRegTarget ins).map upBaseRename ≠ some r := by
  rcases hr with rfl | rfl | rfl <;>
    simp [upCore, upC1, upC2, upC3, upC4, upC5, upC6, upC7, upC8,
      upRegTarget]
theorem upBasedCore_noBranch : NoBranch upBasedCore :=
  upTranslateCode_noBranch _ _ upCore_pure
def upBasedCoreRun (E : RAMEnv) (s : RAMState) : RAMState := runBlock upBasedCore E s
theorem upBasedCoreRun_eq (E : RAMEnv) (s : RAMState) :
    upBasedCoreRun E s = runBlock upBasedCore E s := by unfold upBasedCoreRun <;> rfl
attribute [irreducible] upBasedCoreRun
theorem upBasedCore_facts (E : RAMEnv) (p : RAMState) (beta i a : ℕ)
    (it : UpIt) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hb : p.regs 14 = beta)
    (h0 : p.regs 0 = i) (h6 : p.regs 6 = 1 % 2 ^ E.W)
    (h7 : p.regs 7 = a) (h8 : p.regs 8 = ab.c) (h9 : p.regs 9 = ab.f)
    (h16 : a + 16 < 2 ^ E.W)
    (hF : ∀ j, j < 16 → (upShiftDetEnv E beta).det (a + j) % 2 ^ E.W = it.fld j) :
    (upBasedCoreRun E p).pc = p.pc + 95 ∧
      (upBasedCoreRun E p).mem = p.mem ∧
      (upBasedCoreRun E p).regs 2 = upvBit (upShiftDetEnv E beta) i it ab ∧
      (upBasedCoreRun E p).regs 3 = upvMask0 (upShiftDetEnv E beta) i it ab ∧
      (upBasedCoreRun E p).regs 8 = upvCn (upShiftDetEnv E beta) i it ab ∧
      (upBasedCoreRun E p).regs 9 = upvFn (upShiftDetEnv E beta) i it ab ∧
      (∀ r, r = 0 ∨ r = 5 ∨ r = 6 ∨ r = 14 ∨ r = 15 →
        (upBasedCoreRun E p).regs r = p.regs r) := by
  let src : RAMState := { p with regs := fun r => p.regs (upBaseRename r), mem := ab.mem }
  have hSrc0 : src.regs r0 = i := by simpa [src] using h0
  have hSrc7 : src.regs r7 = a := by simpa [src] using h7
  have hSrc8 : src.regs r8 = ab.c := by simpa [src] using h8
  have hSrc9 : src.regs r9 = ab.f := by simpa [src] using h9
  have hSrc15 : src.regs r15 = 1 % 2 ^ E.W := by simpa [src] using h6
  have hOld := upCore_facts (upShiftDetEnv E beta) src i it ab a hW hSrc0 hSrc7 hSrc8 hSrc9
    rfl hSrc15 h16 hF
  have hRel := upTranslateCode_related upBaseRename E beta upCore src p upCore_pure
    (upCore_protected 14 (Or.inr (Or.inl rfl))) (fun _ => rfl) hb
  have h2 : (upBasedCoreRun E p).regs 2 = (upCoreRun (upShiftDetEnv E beta) src).regs 2 := by
    simpa only [upBasedCoreRun_eq, upBasedCore, upCoreRun_eq,
      show upBaseRename 2 = 2 from by decide] using hRel 2
  have h3 : (upBasedCoreRun E p).regs 3 = (upCoreRun (upShiftDetEnv E beta) src).regs 3 := by
    simpa only [upBasedCoreRun_eq, upBasedCore, upCoreRun_eq,
      show upBaseRename 3 = 3 from by decide] using hRel 3
  have h8' : (upBasedCoreRun E p).regs 8 = (upCoreRun (upShiftDetEnv E beta) src).regs 8 := by
    simpa only [upBasedCoreRun_eq, upBasedCore, upCoreRun_eq,
      show upBaseRename 8 = 8 from by decide] using hRel 8
  have h9' : (upBasedCoreRun E p).regs 9 = (upCoreRun (upShiftDetEnv E beta) src).regs 9 := by
    simpa only [upBasedCoreRun_eq, upBasedCore, upCoreRun_eq,
      show upBaseRename 9 = 9 from by decide] using hRel 9
  refine ⟨?_, ?_, h2.trans hOld.2.2.2.2.2.2.1, h3.trans hOld.2.2.2.2.2.2.2.1,
    h8'.trans hOld.2.2.2.2.1, h9'.trans hOld.2.2.2.2.2.1, ?_⟩
  · rw [upBasedCoreRun_eq, runBlock_pc _ E p upBasedCore_noBranch, upBasedCore_length]
  · rw [upBasedCoreRun_eq]
    exact upTranslateCode_mem _ _ _ _ upCore_pure
  · intro r hr
    rw [upBasedCoreRun_eq]
    apply upTranslateCode_frame _ _ _ _ r upCore_pure
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact upCore_protected 0 (Or.inl rfl)
    · simp [upCore, upC1, upC2, upC3, upC4, upC5, upC6, upC7, upC8,
        upRegTarget]
    · simp [upCore, upC1, upC2, upC3, upC4, upC5, upC6, upC7, upC8,
        upRegTarget]
    · exact upCore_protected 14 (Or.inr (Or.inl rfl))
    · exact upCore_protected 15 (Or.inr (Or.inr rfl))
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedWidth : List Instr :=
  [.imm 7 1, .add 7 14 7, .qDet 7 7, .mod 1 2 7, .imm 11 1, .shl 11 11 1, .mul 3 3 11]
theorem upBasedWidth_spec (E : RAMEnv) (s : RAMState) (w : ℕ)
    (hOne : 1 < 2 ^ E.W) (hWidth : E.det ((s.regs 14 + 1) % 2 ^ E.W) % 2 ^ E.W = w) :
    let out := runBlock upBasedWidth E s
    out.pc = s.pc + 7 ∧ out.mem = s.mem ∧ out.regs 7 = w ∧
      out.regs 3 = s.regs 3 * (2 ^ ((s.regs 2 % w) % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W ∧
      ∀ r, r ≠ 1 → r ≠ 3 → r ≠ 7 → r ≠ 11 → out.regs r = s.regs r := by
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [upBasedWidth, runBlock, execInstr, Nat.add_assoc]
  · simp [upBasedWidth, runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt hOne, hWidth]
  · simp [upBasedWidth, runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt hOne, hWidth]
  · intro r h1 h3 h7 h11
    simp [upBasedWidth, runBlock, execInstr, Function.update_apply, h1, h3, h7, h11]
def upBasedRead : List Instr := [.div 2 2 7, .add 11 15 2, .load 11 11, .bxor 11 11 3]
theorem upBasedRead_spec (E : RAMEnv) (s : RAMState) :
    let out := runBlock upBasedRead E s
    out.pc = s.pc + 4 ∧ out.mem = s.mem ∧
      out.regs 2 = s.regs 2 / s.regs 7 % 2 ^ E.W ∧
      out.regs 11 = ((s.mem ((s.regs 15 + s.regs 2 / s.regs 7 % 2 ^ E.W) % 2 ^ E.W)
        % 2 ^ E.W) ^^^ s.regs 3) % 2 ^ E.W ∧
      ∀ r, r ≠ 2 → r ≠ 11 → out.regs r = s.regs r := by
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [upBasedRead, runBlock, execInstr, Nat.add_assoc]
  · simp [upBasedRead, runBlock, execInstr, Function.update_apply]
  · simp [upBasedRead, runBlock, execInstr, Function.update_apply]
  · intro r h2 h11
    simp [upBasedRead, runBlock, execInstr, Function.update_apply, h2, h11]
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedFinishRun (E : RAMEnv) (s : RAMState) : RAMState :=
  runBlock upBasedRead E (runBlock upBasedWidth E s)
theorem upBasedFinishRun_eq (E : RAMEnv) (s : RAMState) :
    upBasedFinishRun E s = runBlock upBasedRead E (runBlock upBasedWidth E s) := by unfold upBasedFinishRun <;> rfl
attribute [irreducible] upBasedFinishRun
theorem upBasedFinish_data (E : RAMEnv) (s : RAMState) (w : ℕ)
    (hOne : 1 < 2 ^ E.W) (hWidth : E.det ((s.regs 14 + 1) % 2 ^ E.W) % 2 ^ E.W = w) :
    (upBasedFinishRun E s).pc = s.pc + 11 ∧ (upBasedFinishRun E s).mem = s.mem ∧
      (upBasedFinishRun E s).regs 2 = s.regs 2 / w % 2 ^ E.W ∧
      (upBasedFinishRun E s).regs 3 = s.regs 3 * (2 ^ ((s.regs 2 % w) % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W ∧
      (upBasedFinishRun E s).regs 11 =
        ((s.mem ((s.regs 15 + s.regs 2 / w % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W) ^^^
          (s.regs 3 * (2 ^ ((s.regs 2 % w) % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W)) % 2 ^ E.W ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 7 → r ≠ 11 →
        (upBasedFinishRun E s).regs r = s.regs r) := by
  let u := runBlock upBasedWidth E s
  have hW := upBasedWidth_spec E s w hOne hWidth
  have hR := upBasedRead_spec E u
  have hu2 : u.regs 2 = s.regs 2 := hW.2.2.2.2 2 (by decide) (by decide) (by decide) (by decide)
  have hu15 : u.regs 15 = s.regs 15 := hW.2.2.2.2 15 (by decide) (by decide) (by decide) (by decide)
  have hu7 : u.regs 7 = w := hW.2.2.1
  have hu3 : u.regs 3 = s.regs 3 * (2 ^ ((s.regs 2 % w) % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W := hW.2.2.2.1
  have huM : u.mem = s.mem := hW.2.1
  rw [upBasedFinishRun_eq]
  refine ⟨?_, hR.2.1.trans huM, ?_, ?_, ?_, ?_⟩
  · rw [hR.1, hW.1]
  · rw [hR.2.2.1, hu2, hu7]
  · exact (hR.2.2.2.2 3 (by decide) (by decide)).trans hu3
  · rw [hR.2.2.2.1, hu15, hu2, hu7, hu3, huM]
  · intro r h1 h2 h3 h7 h11
    exact (hR.2.2.2.2 r h2 h11).trans (hW.2.2.2.2 r h1 h3 h7 h11)
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedPrefixCode : List Instr :=
  [.add 5 5 6] ++ (upBasedCore ++ (upBasedWidth ++ upBasedRead))
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upBasedPrefixRun (E : RAMEnv) (s : RAMState) : RAMState := runBlock upBasedPrefixCode E s
theorem upBasedPrefixRun_eq (E : RAMEnv) (s : RAMState) :
    upBasedPrefixRun E s = runBlock upBasedPrefixCode E s := by unfold upBasedPrefixRun <;> rfl
attribute [irreducible] upBasedPrefixRun
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def upCyclicAddr (W beta a : ℕ) : ℕ := (beta + a) % 2 ^ W
def upVirtualMem (W beta : ℕ) (mem : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a < 2 ^ W then mem (upCyclicAddr W beta a) % 2 ^ W else 0
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def upvWw (E : RAMEnv) : ℕ := E.det (1 % 2 ^ E.W) % 2 ^ E.W
def upvB1 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvBit E i it ab % upvWw E) % 2 ^ E.W
def upvSh (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  ((1 % 2 ^ E.W) * 2 ^ upvB1 E i it ab) % 2 ^ E.W
def upvMask (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvMask0 E i it ab * upvSh E i it ab % 2 ^ E.W
def upvWi (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  upvBit E i it ab / upvWw E % 2 ^ E.W
def upvOld (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  ab.mem (upvWi E i it ab) % 2 ^ E.W
def upvNew (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs) : ℕ :=
  (upvOld E i it ab ^^^ upvMask E i it ab) % 2 ^ E.W
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure UpBasedView (W beta : ℕ) (ab : UpAbs) (p : RAMState) : Prop where
  mem : upVirtualMem W beta p.mem = ab.mem
  coord : p.regs 8 = ab.c
  flag : p.regs 9 = ab.f

structure UpBasedPrefixData (E : RAMEnv) (betaDet betaPay i : ℕ)
    (it : UpIt) (ab : UpAbs) (p q : RAMState) : Prop where
  mem : q.mem = p.mem
  word : q.regs 2 = upvWi (upShiftDetEnv E betaDet) i it ab
  mask : q.regs 3 = upvMask (upShiftDetEnv E betaDet) i it ab
  value : q.regs 11 = upvNew (upShiftDetEnv E betaDet) i it ab
  coord : q.regs 8 = upvCn (upShiftDetEnv E betaDet) i it ab
  flag : q.regs 9 = upvFn (upShiftDetEnv E betaDet) i it ab
  pay : q.regs 15 = betaPay
  det : q.regs 14 = betaDet

                                                                      
                                                                          
theorem upBasedPrefix_data (E : RAMEnv) (p : RAMState) (betaDet betaPay i a : ℕ)
    (it : UpIt) (ab : UpAbs) (hView : UpBasedView E.W betaPay ab p)
    (hW : 1 < 2 ^ E.W) (h0 : p.regs 0 = i) (h6 : p.regs 6 = 1 % 2 ^ E.W)
    (h7 : p.regs 7 = a) (h14 : p.regs 14 = betaDet) (h15 : p.regs 15 = betaPay)
    (h16 : a + 16 < 2 ^ E.W)
    (hFields : ∀ j, j < 16 → (upShiftDetEnv E betaDet).det (a + j) % 2 ^ E.W = it.fld j)
    (hWidth : upvWw (upShiftDetEnv E betaDet) = E.W) :
    UpBasedPrefixData E betaDet betaPay i it ab p (upBasedPrefixRun E p) := by
  let F := upShiftDetEnv E betaDet
  let z := execInstr (.add 5 5 6) E p
  let core := upBasedCoreRun E z
  have hC := upBasedCore_facts E z betaDet i a it ab hW
    (by simpa [z, execInstr, Function.update_apply] using h14)
    (by simpa [z, execInstr, Function.update_apply] using h0)
    (by simpa [z, execInstr, Function.update_apply] using h6)
    (by simpa [z, execInstr, Function.update_apply] using h7)
    (by simpa [z, execInstr, Function.update_apply] using hView.coord)
    (by simpa [z, execInstr, Function.update_apply] using hView.flag) h16 hFields
  have hCMem : core.mem = p.mem := hC.2.1
  have hCB : core.regs 2 = upvBit F i it ab := hC.2.2.1
  have hCM : core.regs 3 = upvMask0 F i it ab := hC.2.2.2.1
  have hCC : core.regs 8 = upvCn F i it ab := hC.2.2.2.2.1
  have hCF : core.regs 9 = upvFn F i it ab := hC.2.2.2.2.2.1
  have hCD : core.regs 14 = betaDet := (hC.2.2.2.2.2.2 14 (by tauto)).trans (by simpa [z, execInstr] using h14)
  have hCP : core.regs 15 = betaPay := (hC.2.2.2.2.2.2 15 (by tauto)).trans (by simpa [z, execInstr] using h15)
  have hReadWidth : E.det ((core.regs 14 + 1) % 2 ^ E.W) % 2 ^ E.W = E.W := by
    change E.det ((betaDet + 1 % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W = E.W at hWidth
    rw [Nat.mod_eq_of_lt hW] at hWidth
    rw [hCD]
    exact hWidth
  have hFinish := upBasedFinish_data E core E.W hW hReadWidth
  let wi := upvBit F i it ab / E.W % 2 ^ E.W
  let mask := upvMask0 F i it ab * (2 ^ ((upvBit F i it ab % E.W) % 2 ^ E.W) % 2 ^ E.W) % 2 ^ E.W
  have hWi : upvWi F i it ab = wi := by
    change upvBit F i it ab / upvWw F % 2 ^ E.W = wi
    rw [hWidth]
  have hMask : upvMask F i it ab = mask := by
    change upvMask0 F i it ab * (((1 % 2 ^ E.W) *
      2 ^ ((upvBit F i it ab % upvWw F) % 2 ^ E.W)) % 2 ^ E.W) % 2 ^ E.W = mask
    rw [hWidth, Nat.mod_eq_of_lt hW, Nat.one_mul]
  have hWiBound : wi < 2 ^ E.W := Nat.mod_lt _ (Nat.two_pow_pos E.W)
  have hOld : ab.mem wi = p.mem ((betaPay + wi) % 2 ^ E.W) % 2 ^ E.W := by
    have hh := congrFun hView.mem wi
    simpa only [upVirtualMem, if_pos hWiBound, upCyclicAddr] using hh.symm
  have hNew : upvNew F i it ab =
      ((p.mem ((betaPay + wi) % 2 ^ E.W) % 2 ^ E.W) ^^^ mask) % 2 ^ E.W := by
    change ((ab.mem (upvWi F i it ab) % 2 ^ E.W) ^^^ upvMask F i it ab) % 2 ^ E.W = _
    rw [hWi, hMask, hOld, Nat.mod_mod]
  have hQ : upBasedPrefixRun E p = upBasedFinishRun E core := by
    rw [upBasedPrefixRun_eq]
    simp only [upBasedPrefixCode, runBlock_append, runBlock_cons, runBlock_nil,
      upBasedFinishRun_eq, core, upBasedCoreRun_eq, z]
  rw [hQ]
  refine ⟨hFinish.2.1.trans hCMem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFinish.2.2.1, hCB, hWi]
  · rw [hFinish.2.2.2.1, hCB, hCM, hMask]
  · rw [hFinish.2.2.2.2.1, hCMem, hCB, hCM, hCP, hNew]
  · exact (hFinish.2.2.2.2.2 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hCC
  · exact (hFinish.2.2.2.2.2 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hCF
  · exact (hFinish.2.2.2.2.2 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hCP
  · exact (hFinish.2.2.2.2.2 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hCD

end LinearSetReconciliation327.Main



#print axioms LinearSetReconciliation327.Main.upBasedPrefix_data


