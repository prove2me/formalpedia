-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCRCompiler20261120
-- name    : LinearSetReconciliation327_Main_HintCRCompiler20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:08:39.707307+00:00
-- url     : https://prove2.me/theorems/31b054f8-7f11-4c6d-a8bb-b9e16364ee1d
-- title:
--   LinearSetReconciliation327 — HintCRCompiler (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCRCompiler20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateSource20261120
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
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
theorem getElem?_flatten_ofFn {α : Type} :
    ∀ (n : ℕ) (f : Fin n → List α) (s : Fin n) (j : ℕ), j < (f s).length →
      (List.ofFn f).flatten[((List.ofFn fun i : Fin n => (f i).length).take s.val).sum + j]?
        = (f s)[j]? := by
  intro n
  induction n with
  | zero => intro f s; exact absurd s.isLt (Nat.not_lt_zero _)
  | succ n ih =>
      intro f s
      refine Fin.cases ?_ ?_ s
      · intro j hj
        simp only [List.ofFn_succ, List.flatten_cons, Fin.val_zero, List.take_zero,
          List.sum_nil, Nat.zero_add]
        exact List.getElem?_append_left hj
      · intro s' j hj
        simp only [List.ofFn_succ, List.flatten_cons, Fin.val_succ, List.take_succ_cons,
          List.sum_cons]
        rw [List.getElem?_append_right (by omega)]
        have hsub : (f 0).length
              + (List.take (↑s') (List.ofFn fun i : Fin n => (f i.succ).length)).sum + j
              - (f 0).length
            = (List.take (↑s') (List.ofFn fun i : Fin n => (f i.succ).length)).sum + j := by omega
        rw [hsub]
        exact ih (fun i : Fin n => f (Fin.succ i)) s' j hj
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def crSpillLoad (dst src : Fin 16) : List Instr :=
  [.imm dst src.val, .add dst 8 dst, .load dst dst]
def crSpillWrite (dst src : Fin 16) : List Instr :=
  [.imm 2 dst.val, .add 2 8 2, .store 2 src]
def crSpillBin (op : Fin 16 → Fin 16 → Fin 16 → Instr) (dst a b : Fin 16) : List Instr :=
  crSpillLoad 0 a ++ crSpillLoad 1 b ++ [op 0 0 1, .mod 0 0 13] ++ crSpillWrite dst 0
def crSpillTarget (n base fail pc : ℕ) : ℕ := if pc < n then base + 16 * pc else fail
def crSpillPayload (n base fail ok : ℕ) : Instr → List Instr
  | .imm d v => [.imm 0 v, .mod 0 0 13] ++ crSpillWrite d 0
  | .add d a b => crSpillBin Instr.add d a b
  | .sub d a b => crSpillLoad 0 a ++ crSpillLoad 1 b ++
      [.add 0 0 13, .sub 0 0 1, .mod 0 0 13] ++ crSpillWrite d 0
  | .mul d a b => crSpillBin Instr.mul d a b
  | .div d a b => crSpillBin Instr.div d a b
  | .mod d a b => crSpillBin Instr.mod d a b
  | .band d a b => crSpillBin Instr.band d a b
  | .bor d a b => crSpillBin Instr.bor d a b
  | .bxor d a b => crSpillBin Instr.bxor d a b
  | .shl d a b => crSpillBin Instr.shl d a b
  | .shr d a b => crSpillBin Instr.shr d a b
  | .lt d a b => crSpillBin Instr.lt d a b
  | .load d a => crSpillLoad 0 a ++ [.add 0 9 0, .load 0 0, .mod 0 0 13] ++ crSpillWrite d 0
  | .store a v => crSpillLoad 0 a ++ crSpillLoad 1 v ++
      [.add 2 9 0, .store 2 1, .add 3 11 12, .store 3 2, .add 12 12 15]
  | .jz r pc => crSpillLoad 0 r ++ [.jz 0 (crSpillTarget n base fail pc)]
  | .jmp pc => [.jmp (crSpillTarget n base fail pc)]
  | .qDet d a => crSpillLoad 0 a ++ [.add 0 10 0, .qDet 0 0, .mod 0 0 13] ++ crSpillWrite d 0
  | .qPerm d _ _ => [.imm 0 0] ++ crSpillWrite d 0
  | .qPermInv d _ _ => [.imm 0 0] ++ crSpillWrite d 0
  | .qCoeff d _ _ => [.imm 0 0] ++ crSpillWrite d 0
  | .halt => [.jmp ok]
def crSpillPrefix (n base fail ok index : ℕ) (ins : Instr) : List Instr :=
  match ins with
  | .halt => [.jmp ok]
  | _ => [.jz 14 fail, .sub 14 14 15] ++ crSpillPayload n base fail ok ins ++
      [.jmp (crSpillTarget n base fail (index + 1))]
def crSpillBlock (n base fail ok index : ℕ) (ins : Instr) : List Instr :=
  let code := crSpillPrefix n base fail ok index ins
  code ++ List.replicate (16 - code.length) (.bor 7 7 7)
def crSpillCompile (source : Program) (base fail ok : ℕ) : Program :=
  (List.ofFn fun j : Fin source.length => crSpillBlock source.length base fail ok j.val (source.get j)).flatten
theorem crSpillPrefix_length (n base fail ok index : ℕ) (ins : Instr) :
    (crSpillPrefix n base fail ok index ins).length ≤ 16 := by
  cases ins <;> simp [crSpillPrefix, crSpillPayload, crSpillBin, crSpillLoad, crSpillWrite]
theorem crSpillBlock_length (n base fail ok index : ℕ) (ins : Instr) :
    (crSpillBlock n base fail ok index ins).length = 16 := by
  have h := crSpillPrefix_length n base fail ok index ins
  simp only [crSpillBlock, List.length_append, List.length_replicate]
  omega
theorem crSpillCompile_length (source : Program) (base fail ok : ℕ) :
    (crSpillCompile source base fail ok).length = 16 * source.length := by
  unfold crSpillCompile
  rw [flatten_length_eq_sum]
  simp only [crSpillBlock_length]
  simp [Nat.mul_comm]
theorem crSpillCompile_fetch (source : Program) (base fail ok : ℕ) (j : Fin source.length)
    (t : ℕ) (ht : t < 16) :
    (crSpillCompile source base fail ok)[16 * j.val + t]? =
      (crSpillBlock source.length base fail ok j.val (source.get j))[t]? := by
  have h := getElem?_flatten_ofFn source.length
    (fun a : Fin source.length => crSpillBlock source.length base fail ok a.val (source.get a))
    j t (by simpa only [crSpillBlock_length] using ht)
  have hPrefix : ((List.ofFn fun a : Fin source.length =>
      (crSpillBlock source.length base fail ok a.val (source.get a)).length).take j.val).sum = 16 * j.val := by
    simp only [crSpillBlock_length]
    simp [List.ofFn_const, List.take_replicate, Nat.min_eq_left j.isLt.le, Nat.mul_comm]
  rw [hPrefix] at h
  exact h
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
inductive CRBinKind where
  | add | mul | div | mod | band | bor | bxor | shl | shr | lt
def CRBinKind.ins : CRBinKind → Fin 16 → Fin 16 → Fin 16 → Instr
  | .add => Instr.add
  | .mul => Instr.mul
  | .div => Instr.div
  | .mod => Instr.mod
  | .band => Instr.band
  | .bor => Instr.bor
  | .bxor => Instr.bxor
  | .shl => Instr.shl
  | .shr => Instr.shr
  | .lt => Instr.lt
def CRBinKind.val : CRBinKind → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .band, a, b => a &&& b
  | .bor, a, b => a ||| b
  | .bxor, a, b => a ^^^ b
  | .shl, a, b => a * 2 ^ b
  | .shr, a, b => a / 2 ^ b
  | .lt, a, b => if a < b then 1 else 0
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
inductive CRReadKind where
  | memory | deterministic
def CRReadKind.ins : CRReadKind → Fin 16 → Fin 16 → Instr
  | .memory => Instr.load
  | .deterministic => Instr.qDet
end LinearSetReconciliation327.Main
end
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
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
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
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def CRNoWrite (r : Fin 16) : Instr → Prop
  | .imm d _ => r ≠ d
  | .add d _ _ | .sub d _ _ | .mul d _ _ | .div d _ _ | .mod d _ _ => r ≠ d
  | .band d _ _ | .bor d _ _ | .bxor d _ _ | .shl d _ _ | .shr d _ _ | .lt d _ _ => r ≠ d
  | .load d _ | .qDet d _ => r ≠ d
  | .qPerm d _ _ | .qPermInv d _ _ | .qCoeff d _ _ => r ≠ d
  | .store _ _ | .jz _ _ | .jmp _ | .halt => True
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crStep_fetch (P : Program) (E : RAMEnv) (s : RAMState) (ins : Instr)
    (hFetch : P[s.pc]? = some ins) : step P E s = execInstr ins E s := by
  unfold step
  rw [hFetch]
  cases ins <;> rfl
theorem crClock_dec_mod (B Q : ℕ) (hB : 0 < B) (hBQ : B < Q) :
    (B + Q - 1) % Q = B - 1 := by
  have hDiff : B + Q - 1 = (B - 1) + Q := by omega
  rw [hDiff, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)
theorem crGuard_positive (P : Program) (E : RAMEnv) (s : RAMState) (fail : ℕ)
    (hFetch : P[s.pc]? = some (.jz 14 fail))
    (hNext : P[s.pc + 1]? = some (.sub 14 14 15))
    (hClock : 0 < s.regs 14) (hClockWord : s.regs 14 < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    (step P E)^[2] s =
      {s with pc := s.pc + 2, regs := Function.update s.regs 14 (s.regs 14 - 1)} := by
  have hFirst : step P E s = {s with pc := s.pc + 1} := by
    rw [crStep_fetch P E s _ hFetch]
    simp [execInstr, Nat.ne_of_gt hClock]
  change step P E (step P E s) = _
  rw [hFirst, crStep_fetch P E {s with pc := s.pc + 1} _ hNext]
  simp only [execInstr, hOne, crClock_dec_mod _ _ hClock hClockWord]
theorem crGuard_zero (P : Program) (E : RAMEnv) (s : RAMState) (fail : ℕ)
    (hFetch : P[s.pc]? = some (.jz 14 fail)) (hClock : s.regs 14 = 0) :
    step P E s = {s with pc := fail} := by
  rw [crStep_fetch P E s _ hFetch]
  simp [execInstr, hClock]
def CRPayloadStable (r : Fin 16) : Prop := r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 12
theorem crSpillPayload_noWrite (r : Fin 16) (hR : CRPayloadStable r)
    (n base fail ok : ℕ) (ins : Instr) :
    ∀ op ∈ crSpillPayload n base fail ok ins, CRNoWrite r op := by
  obtain ⟨h0, h1, h2, h3, h12⟩ := hR
  cases ins <;>
    simp [crSpillPayload, crSpillBin, crSpillLoad, crSpillWrite, CRNoWrite, h0, h1, h2, h3, h12]
theorem crSpillPayload_clock_frame (n base fail ok : ℕ) (ins : Instr) :
    ∀ op ∈ crSpillPayload n base fail ok ins, CRNoWrite 14 op :=
  crSpillPayload_noWrite 14 (by unfold CRPayloadStable; decide) n base fail ok ins
end LinearSetReconciliation327.Main
end
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
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crCompiledBlock_at (P source : Program) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length) :
    At P (base + 16 * j.val) (crSpillBlock source.length base fail ok j.val (source.get j)) := by
  intro t ht
  have hT : t < 16 := by simpa only [crSpillBlock_length] using ht
  have hJ := j.isLt
  have hBound : 16 * j.val + t < (crSpillCompile source base fail ok).length := by
    rw [crSpillCompile_length]
    omega
  have h := hAt (16 * j.val + t) hBound
  rw [crSpillCompile_fetch source base fail ok j t hT] at h
  simpa only [Nat.add_assoc] using h
theorem crAt_prefix (P : Program) (a : ℕ) (first rest : List Instr)
    (hAt : At P a (first ++ rest)) : At P a first := by
  intro t ht
  have h := hAt t (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_left ht] at h
  exact h
theorem crAt_suffix (P : Program) (a : ℕ) (first rest : List Instr)
    (hAt : At P a (first ++ rest)) : At P (a + first.length) rest := by
  intro t ht
  have h := hAt (first.length + t) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega)] at h
  simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using h
theorem crCompiledPrefix_at (P source : Program) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length) :
    At P (base + 16 * j.val) (crSpillPrefix source.length base fail ok j.val (source.get j)) := by
  exact crAt_prefix P _ _ _ (crCompiledBlock_at P source base fail ok hAt j)
theorem crExecute_body_jump (P : Program) (E : RAMEnv) (s : RAMState)
    (body : List Instr) (target : ℕ) (hNo : NoBranch body)
    (hBody : At P s.pc body)
    (hJump : P[s.pc + body.length]? = some (.jmp target)) :
    (step P E)^[body.length + 1] s = {runBlock body E s with pc := target} := by
  rw [show body.length + 1 = 1 + body.length by omega, Function.iterate_add_apply]
  change step P E ((step P E)^[body.length] s) = _
  rw [iterate_runBlock_of_at P E body s hBody hNo]
  have hPc := runBlock_pc body E s hNo
  rw [crStep_fetch P E (runBlock body E s) (.jmp target) (by simpa only [hPc] using hJump)]
  rfl
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crExecute_halt_prefix (P source : Program) (E : RAMEnv)
    (base fail ok : ℕ) (j : Fin source.length) (s : RAMState)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hPc : s.pc = base + 16 * j.val) (hHalt : source.get j = .halt) :
    step P E s = {s with pc := ok} := by
  have hPre := crCompiledPrefix_at P source base fail ok hAt j
  rw [hHalt] at hPre
  have h := hPre 0 (by simp [crSpillPrefix])
  have hFetch : P[s.pc]? = some (.jmp ok) := by
    simpa only [crSpillPrefix, Nat.add_zero, List.getElem?_cons_zero, hPc] using h
  rw [crStep_fetch P E s _ hFetch]
  rfl
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def crGuardState (s : RAMState) : RAMState :=
  {s with pc := s.pc + 2, regs := Function.update s.regs 14 (s.regs 14 - 1)}
theorem crSpillPrefix_nonhalt (n base fail ok index : ℕ) (ins : Instr) (h : ins ≠ .halt) :
    crSpillPrefix n base fail ok index ins =
      [.jz 14 fail, .sub 14 14 15] ++ crSpillPayload n base fail ok ins ++
        [.jmp (crSpillTarget n base fail (index + 1))] := by
  cases ins <;> simp_all [crSpillPrefix]
theorem crSpillPayload_length (n base fail ok : ℕ) (ins : Instr) :
    (crSpillPayload n base fail ok ins).length ≤ 13 := by
  cases ins <;> simp [crSpillPayload, crSpillBin, crSpillLoad, crSpillWrite]
theorem crSpillPayload_regular (n base fail ok : ℕ) (ins : Instr) (h : ins.NoBranchI) :
    NoBranch (crSpillPayload n base fail ok ins) := by
  cases ins <;> simp_all [crSpillPayload, crSpillBin, crSpillLoad, crSpillWrite, NoBranch, Instr.NoBranchI]
theorem crCompiled_guard_fetch (P source : Program) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length)
    (hNot : source.get j ≠ .halt) :
    P[base + 16 * j.val]? = some (.jz 14 fail) ∧
      P[base + 16 * j.val + 1]? = some (.sub 14 14 15) := by
  have hPre := crCompiledPrefix_at P source base fail ok hAt j
  rw [crSpillPrefix_nonhalt _ _ _ _ _ _ hNot] at hPre
  have h0 := hPre 0 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have h1 := hPre 1 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  constructor
  · simpa only [List.cons_append, List.nil_append, List.getElem?_cons_zero, Nat.add_zero] using h0
  · simpa only [List.cons_append, List.nil_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero] using h1
theorem crCompiled_guard_positive (P source : Program) (E : RAMEnv) (s : RAMState)
    (base fail ok : ℕ) (hAt : At P base (crSpillCompile source base fail ok))
    (j : Fin source.length) (hPc : s.pc = base + 16 * j.val) (hNot : source.get j ≠ .halt)
    (hClock : 0 < s.regs 14) (hWord : s.regs 14 < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    (step P E)^[2] s = crGuardState s := by
  obtain ⟨h0, h1⟩ := crCompiled_guard_fetch P source base fail ok hAt j hNot
  exact crGuard_positive P E s fail (by rw [hPc]; exact h0) (by rw [hPc]; exact h1)
    hClock hWord hOne
theorem crCompiled_guard_zero (P source : Program) (E : RAMEnv) (s : RAMState)
    (base fail ok : ℕ) (hAt : At P base (crSpillCompile source base fail ok))
    (j : Fin source.length) (hPc : s.pc = base + 16 * j.val) (hNot : source.get j ≠ .halt)
    (hClock : s.regs 14 = 0) : step P E s = {s with pc := fail} := by
  have h := (crCompiled_guard_fetch P source base fail ok hAt j hNot).1
  exact crGuard_zero P E s fail (by rw [hPc]; exact h) hClock
theorem crCompiled_payload_at (P source : Program) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length)
    (hNot : source.get j ≠ .halt) :
    At P (base + 16 * j.val + 2)
      (crSpillPayload source.length base fail ok (source.get j) ++
        [.jmp (crSpillTarget source.length base fail (j.val + 1))]) := by
  have hPre := crCompiledPrefix_at P source base fail ok hAt j
  rw [crSpillPrefix_nonhalt _ _ _ _ _ _ hNot] at hPre
  have h := crAt_suffix P (base + 16 * j.val) [.jz 14 fail, .sub 14 14 15] _ hPre
  simpa using h
theorem crCompiled_regular_step (P source : Program) (E : RAMEnv) (s : RAMState)
    (base fail ok : ℕ) (hAt : At P base (crSpillCompile source base fail ok))
    (j : Fin source.length) (hPc : s.pc = base + 16 * j.val)
    (hNo : (source.get j).NoBranchI) (hClock : 0 < s.regs 14)
    (hWord : s.regs 14 < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    let body := crSpillPayload source.length base fail ok (source.get j)
    (step P E)^[body.length + 3] s =
      {runBlock body E (crGuardState s) with pc := crSpillTarget source.length base fail (j.val + 1)} := by
  let body := crSpillPayload source.length base fail ok (source.get j)
  let g := crGuardState s
  change (step P E)^[body.length + 3] s =
    {runBlock body E g with pc := crSpillTarget source.length base fail (j.val + 1)}
  have hGuard := crCompiled_guard_positive P source E s base fail ok hAt j hPc hNo.2.2 hClock hWord hOne
  have hGPc : g.pc = base + 16 * j.val + 2 := by change s.pc + 2 = _; rw [hPc]
  have hTail : At P g.pc (body ++ [.jmp (crSpillTarget source.length base fail (j.val + 1))]) := by
    rw [hGPc]
    exact crCompiled_payload_at P source base fail ok hAt j hNo.2.2
  have hBody := crAt_prefix P g.pc body [.jmp (crSpillTarget source.length base fail (j.val + 1))] hTail
  have hEnd := crAt_suffix P g.pc body [.jmp (crSpillTarget source.length base fail (j.val + 1))] hTail
  have hJump : P[g.pc + body.length]? = some (.jmp (crSpillTarget source.length base fail (j.val + 1))) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using hEnd 0 (by simp)
  have hExec := crExecute_body_jump P E g body (crSpillTarget source.length base fail (j.val + 1))
    (crSpillPayload_regular source.length base fail ok (source.get j) hNo) hBody hJump
  rw [show body.length + 3 = (body.length + 1) + 2 by omega, Function.iterate_add_apply, hGuard]
  exact hExec
theorem crCompiled_regular_cost (source : Program) (base fail ok : ℕ) (j : Fin source.length) :
    (crSpillPayload source.length base fail ok (source.get j)).length + 3 ≤ 16 := by
  have h := crSpillPayload_length source.length base fail ok (source.get j)
  omega
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crExec_reg_frame (i : Instr) (E : RAMEnv) (s : RAMState) (r : Fin 16)
    (h : CRNoWrite r i) : (execInstr i E s).regs r = s.regs r := by
  cases i <;> simp_all [CRNoWrite, execInstr, Function.update]
theorem crRunBlock_reg_frame (E : RAMEnv) (r : Fin 16) :
    ∀ (code : List Instr) (s : RAMState), (∀ i ∈ code, CRNoWrite r i) →
      (runBlock code E s).regs r = s.regs r
  | [], s, _ => rfl
  | i :: tl, s, h => by
    rw [runBlock_cons, crRunBlock_reg_frame E r tl (execInstr i E s)
      (fun j hj => h j (List.mem_cons_of_mem i hj))]
    exact crExec_reg_frame i E s r (h i (List.mem_cons_self))
theorem crExecute_conditional_any (P : Program) (E : RAMEnv) (s : RAMState)
    (body : List Instr) (target next : ℕ) (hNo : NoBranch body)
    (hAt : At P s.pc (body ++ [.jz 0 target, .jmp next])) :
    ∃ k : ℕ, k ≤ body.length + 2 ∧
      (step P E)^[k] s =
        {runBlock body E s with pc := if (runBlock body E s).regs 0 = 0 then target else next} := by
  have hLoadAt := crAt_prefix P s.pc body [.jz 0 target, .jmp next] hAt
  have hTailAt := crAt_suffix P s.pc body [.jz 0 target, .jmp next] hAt
  generalize hu : runBlock body E s = u
  have hRun : (step P E)^[body.length] s = u := by
    rw [iterate_runBlock_of_at P E body s hLoadAt hNo, hu]
  have hUpc : u.pc = s.pc + body.length := by rw [← hu]; exact runBlock_pc body E s hNo
  have hFetch : P[u.pc]? = some (.jz 0 target) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero, hUpc] using hTailAt 0 (by simp)
  have hNext : P[u.pc + 1]? = some (.jmp next) := by
    simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero, hUpc] using hTailAt 1 (by simp)
  by_cases hz : u.regs 0 = 0
  · refine ⟨body.length + 1, by omega, ?_⟩
    have hStep : step P E u = {u with pc := target} := by
      rw [crStep_fetch P E u _ hFetch]
      simp [execInstr, hz]
    rw [show body.length + 1 = 1 + body.length by omega, Function.iterate_add_apply]
    change step P E ((step P E)^[body.length] s) = _
    rw [hRun, hStep, if_pos hz]
  · refine ⟨body.length + 2, by omega, ?_⟩
    have hStep : step P E u = {u with pc := u.pc + 1} := by
      rw [crStep_fetch P E u _ hFetch]
      simp [execInstr, hz]
    have hJump : step P E {u with pc := u.pc + 1} = {u with pc := next} := by
      rw [crStep_fetch P E {u with pc := u.pc + 1} _ hNext]
      rfl
    rw [show body.length + 2 = 2 + body.length by omega, Function.iterate_add_apply]
    change step P E (step P E ((step P E)^[body.length] s)) = _
    rw [hRun, hStep, hJump, if_neg hz]
def CRBoundary (source : Program) (base fail ok pc : ℕ) : Prop :=
  pc = fail ∨ pc = ok ∨ ∃ j : Fin source.length, pc = base + 16 * j.val
def CRProgress (source : Program) (base fail ok : ℕ) (s out : RAMState) : Prop :=
  out.pc = fail ∨ out.pc = ok ∨
    ((∃ j : Fin source.length, out.pc = base + 16 * j.val) ∧
      out.regs 14 = s.regs 14 - 1 ∧ out.regs 15 = 1)
theorem crTarget_boundary (source : Program) (base fail ok pc : ℕ) :
    CRBoundary source base fail ok (crSpillTarget source.length base fail pc) := by
  unfold crSpillTarget CRBoundary
  split_ifs with h
  · exact Or.inr (Or.inr ⟨⟨pc, h⟩, rfl⟩)
  · exact Or.inl rfl
theorem crProgress_of_boundary (source : Program) (base fail ok : ℕ) (s out : RAMState)
    (hB : CRBoundary source base fail ok out.pc)
    (hClock : out.regs 14 = s.regs 14 - 1) (hOne : out.regs 15 = 1) :
    CRProgress source base fail ok s out := by
  rcases hB with hFail | hOk | hNext
  · exact Or.inl hFail
  · exact Or.inr (Or.inl hOk)
  · exact Or.inr (Or.inr ⟨hNext, hClock, hOne⟩)
theorem crInstr_cases (i : Instr) :
    i.NoBranchI ∨ i = .halt ∨ (∃ a target, i = .jz a target) ∨ ∃ target, i = .jmp target := by
  cases i <;> simp [Instr.NoBranchI]
theorem crCompiled_progress (P source : Program) (E : RAMEnv) (s : RAMState)
    (base fail ok : ℕ) (hAt : At P base (crSpillCompile source base fail ok))
    (j : Fin source.length) (hPc : s.pc = base + 16 * j.val)
    (hClock : 0 < s.regs 14) (hWord : s.regs 14 < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 ∧ (step P E)^[k] s = out ∧
      CRProgress source base fail ok s out := by
  rcases crInstr_cases (source.get j) with hRegular | hHalt | ⟨a, target, hJz⟩ | ⟨target, hJmp⟩
  · let body := crSpillPayload source.length base fail ok (source.get j)
    let out := {runBlock body E (crGuardState s) with pc := crSpillTarget source.length base fail (j.val + 1)}
    refine ⟨body.length + 3, out, crCompiled_regular_cost source base fail ok j,
      crCompiled_regular_step P source E s base fail ok hAt j hPc hRegular hClock hWord hOne, ?_⟩
    apply crProgress_of_boundary source base fail ok s out
    · exact crTarget_boundary source base fail ok (j.val + 1)
    · change (runBlock body E (crGuardState s)).regs 14 = s.regs 14 - 1
      rw [crRunBlock_reg_frame E 14 body _ (crSpillPayload_clock_frame _ _ _ _ _)]
      simp only [crGuardState, Function.update_self]
    · change (runBlock body E (crGuardState s)).regs 15 = 1
      rw [crRunBlock_reg_frame E 15 body _
        (crSpillPayload_noWrite 15 (by unfold CRPayloadStable; decide) source.length base fail ok (source.get j))]
      simpa only [crGuardState, Function.update_of_ne (by decide : (15 : Fin 16) ≠ 14)] using hOne
  · refine ⟨1, {s with pc := ok}, by omega, ?_, Or.inr (Or.inl rfl)⟩
    exact crExecute_halt_prefix P source E base fail ok j s hAt hPc hHalt
  · have hNot : source.get j ≠ .halt := by rw [hJz]; simp
    have hGuard := crCompiled_guard_positive P source E s base fail ok hAt j hPc hNot hClock hWord hOne
    let g := crGuardState s
    have hGPc : g.pc = base + 16 * j.val + 2 := by change s.pc + 2 = _; rw [hPc]
    have hTail : At P g.pc (crSpillLoad 0 a ++
        [.jz 0 (crSpillTarget source.length base fail target),
          .jmp (crSpillTarget source.length base fail (j.val + 1))]) := by
      have h := crCompiled_payload_at P source base fail ok hAt j hNot
      rw [hJz] at h
      simpa [crSpillPayload, List.append_assoc, hGPc] using h
    have hNo : NoBranch (crSpillLoad 0 a) := by simp [crSpillLoad, NoBranch, Instr.NoBranchI]
    obtain ⟨k, hK, hRun⟩ := crExecute_conditional_any P E g (crSpillLoad 0 a)
      (crSpillTarget source.length base fail target) (crSpillTarget source.length base fail (j.val + 1)) hNo hTail
    let out := {runBlock (crSpillLoad 0 a) E g with pc := if (runBlock (crSpillLoad 0 a) E g).regs 0 = 0 then crSpillTarget source.length base fail target else crSpillTarget source.length base fail (j.val + 1)}
    refine ⟨k + 2, out, ?_, ?_, ?_⟩
    · have hK' : k ≤ 5 := by simpa [crSpillLoad] using hK
      omega
    · rw [Function.iterate_add_apply, hGuard]
      exact hRun
    · apply crProgress_of_boundary source base fail ok s out
      · change CRBoundary source base fail ok (if _ then _ else _)
        split_ifs
        · exact crTarget_boundary source base fail ok target
        · exact crTarget_boundary source base fail ok (j.val + 1)
      · change (runBlock (crSpillLoad 0 a) E g).regs 14 = s.regs 14 - 1
        rw [crRunBlock_reg_frame E 14 (crSpillLoad 0 a) g (by intro i hi; simp [crSpillLoad, CRNoWrite] at hi ⊢; rcases hi with rfl | rfl | rfl <;> simp [CRNoWrite])]
        simp only [g, crGuardState, Function.update_self]
      · change (runBlock (crSpillLoad 0 a) E g).regs 15 = 1
        rw [crRunBlock_reg_frame E 15 (crSpillLoad 0 a) g (by intro i hi; simp [crSpillLoad, CRNoWrite] at hi ⊢; rcases hi with rfl | rfl | rfl <;> simp [CRNoWrite])]
        simpa only [g, crGuardState, Function.update_of_ne (by decide : (15 : Fin 16) ≠ 14)] using hOne
  · have hNot : source.get j ≠ .halt := by rw [hJmp]; simp
    have hGuard := crCompiled_guard_positive P source E s base fail ok hAt j hPc hNot hClock hWord hOne
    let g := crGuardState s
    have hGPc : g.pc = base + 16 * j.val + 2 := by change s.pc + 2 = _; rw [hPc]
    have hTail := crCompiled_payload_at P source base fail ok hAt j hNot
    rw [hJmp] at hTail
    have hFetch : P[g.pc]? = some (.jmp (crSpillTarget source.length base fail target)) := by
      have h := hTail 0 (by simp [crSpillPayload])
      simpa [crSpillPayload, hGPc] using h
    refine ⟨3, {g with pc := crSpillTarget source.length base fail target}, by omega, ?_, ?_⟩
    · rw [show 3 = 1 + 2 by omega, Function.iterate_add_apply]
      change step P E ((step P E)^[2] s) = _
      rw [hGuard, crStep_fetch P E g _ hFetch]
      rfl
    · apply crProgress_of_boundary source base fail ok s _ (crTarget_boundary source base fail ok target)
      · simp only [g, crGuardState, Function.update_self]
      · simpa only [g, crGuardState, Function.update_of_ne (by decide : (15 : Fin 16) ≠ 14)] using hOne
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crCompiled_exits (P source : Program) (E : RAMEnv) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok)) :
    ∀ (B : ℕ) (s : RAMState), s.regs 14 = B → B < 2 ^ E.W → s.regs 15 = 1 →
      (∃ j : Fin source.length, s.pc = base + 16 * j.val) →
      ∃ (k : ℕ) (out : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] s = out ∧
        (out.pc = fail ∨ out.pc = ok) := by
  intro B
  induction B with
  | zero =>
    intro s hB hWord hOne hEntry
    obtain ⟨j, hPc⟩ := hEntry
    by_cases hHalt : source.get j = .halt
    · refine ⟨1, {s with pc := ok}, by omega, ?_, Or.inr rfl⟩
      exact crExecute_halt_prefix P source E base fail ok j s hAt hPc hHalt
    · refine ⟨1, {s with pc := fail}, by omega, ?_, Or.inl rfl⟩
      exact crCompiled_guard_zero P source E s base fail ok hAt j hPc hHalt hB
  | succ B ih =>
    intro s hB hWord hOne hEntry
    obtain ⟨j, hPc⟩ := hEntry
    obtain ⟨k, out, hCost, hRun, hProgress⟩ := crCompiled_progress P source E s base fail ok hAt j hPc
      (by omega) (by omega) hOne
    rcases hProgress with hFail | hOk | ⟨hEntry', hClock', hOne'⟩
    · exact ⟨k, out, by omega, hRun, Or.inl hFail⟩
    · exact ⟨k, out, by omega, hRun, Or.inr hOk⟩
    · have hB' : out.regs 14 = B := by omega
      obtain ⟨k', out', hCost', hRun', hExit⟩ := ih out hB' (by omega) hOne' hEntry'
      refine ⟨k' + k, out', by omega, ?_, hExit⟩
      rw [Function.iterate_add_apply, hRun, hRun']
theorem crCompiled_halts (P source : Program) (E : RAMEnv) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hFail : P[fail]? = some .halt) (hOk : P[ok]? = some .halt)
    (B : ℕ) (s : RAMState) (hB : s.regs 14 = B) (hWord : B < 2 ^ E.W) (hOne : s.regs 15 = 1)
    (hEntry : ∃ j : Fin source.length, s.pc = base + 16 * j.val) :
    ∃ out : RAMState, HaltsWithin P E ((16 * B + 1 : ℕ) : ℝ) s out := by
  obtain ⟨k, out, hCost, hRun, hExit⟩ := crCompiled_exits P source E base fail ok hAt B s hB hWord hOne hEntry
  refine ⟨out, k, by exact_mod_cast hCost, hRun, ?_⟩
  rcases hExit with hExit | hExit
  · unfold Halted
    rw [hExit, hFail]
    trivial
  · unfold Halted
    rw [hExit, hOk]
    trivial
def crKernel (source : Program) : Program :=
  crSpillCompile source 0 (16 * source.length) (16 * source.length + 1) ++ [.halt, .halt]
theorem crKernel_at (source : Program) :
    At (crKernel source) 0 (crSpillCompile source 0 (16 * source.length) (16 * source.length + 1)) := by
  intro t ht
  simp only [crKernel, Nat.zero_add, List.getElem?_append_left ht]
theorem crKernel_fail (source : Program) : (crKernel source)[16 * source.length]? = some .halt := by
  unfold crKernel
  rw [List.getElem?_append_right (by rw [crSpillCompile_length])]
  simp only [crSpillCompile_length, Nat.sub_self, List.getElem?_cons_zero]
theorem crKernel_ok (source : Program) : (crKernel source)[16 * source.length + 1]? = some .halt := by
  unfold crKernel
  rw [List.getElem?_append_right (by rw [crSpillCompile_length]; omega)]
  simp only [crSpillCompile_length, Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero]
theorem crKernel_halts (source : Program) (E : RAMEnv) (B : ℕ) (s : RAMState)
    (hPc : s.pc = 0) (hB : s.regs 14 = B) (hWord : B < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    ∃ out : RAMState, HaltsWithin (crKernel source) E ((16 * B + 1 : ℕ) : ℝ) s out := by
  by_cases hEmpty : source.length = 0
  · refine ⟨s, 0, by exact_mod_cast (Nat.zero_le (16 * B + 1)), rfl, ?_⟩
    unfold Halted
    have h : (crKernel source)[s.pc]? = some .halt := by
      simpa only [hPc, hEmpty, Nat.mul_zero] using crKernel_fail source
    rw [h]
    trivial
  · apply crCompiled_halts (crKernel source) source E 0 (16 * source.length) (16 * source.length + 1)
      (crKernel_at source) (crKernel_fail source) (crKernel_ok source) B s hB hWord hOne
    exact ⟨⟨0, by omega⟩, by simpa using hPc⟩
end LinearSetReconciliation327.Main
end

#print axioms LinearSetReconciliation327.Main.crKernel_halts


