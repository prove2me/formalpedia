-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCRSimulation20261120
-- name    : LinearSetReconciliation327_Main_HintCRSimulation20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:12:20.725861+00:00
-- url     : https://prove2.me/theorems/eddac55c-4151-4250-be00-b624aa2903b9
-- title:
--   LinearSetReconciliation327 — HintCRSimulation (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCRSimulation20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRCompiler20261120
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
def CRWordClosed (W : ℕ) (s : RAMState) : Prop :=
  (∀ r, s.regs r ≤ 2 ^ W) ∧ ∀ a, s.mem a ≤ 2 ^ W
theorem crWordClosed_step (P : Program) (E : RAMEnv) (s : RAMState)
    (h : CRWordClosed E.W s) : CRWordClosed E.W (step P E s) := by
  classical
  have hWr : ∀ (d : Fin 16) (v : ℕ), CRWordClosed E.W
      {s with pc := s.pc + 1, regs := Function.update s.regs d (v % 2 ^ E.W)} := by
    intro d v
    refine ⟨?_, h.2⟩
    intro r
    by_cases hr : r = d
    · subst r
      simpa only [Function.update_self] using (Nat.mod_lt v (Nat.two_pow_pos E.W)).le
    · simpa only [Function.update_of_ne hr] using h.1 r
  have hStore : ∀ (a v : ℕ), v ≤ 2 ^ E.W → CRWordClosed E.W
      {s with pc := s.pc + 1, mem := Function.update s.mem a v} := by
    intro a v hv
    refine ⟨h.1, ?_⟩
    intro q
    by_cases hq : q = a
    · subst q
      simpa only [Function.update_self] using hv
    · simpa only [Function.update_of_ne hq] using h.2 q
  unfold step
  cases hp : P[s.pc]? with
  | none => exact h
  | some ins =>
      cases ins <;> first
      | exact h
      | exact hWr _ _
      | exact hStore _ _ (h.1 _)
theorem crClip_wide (w V a : ℕ) (hWV : w ≤ V) : a % 2 ^ V % 2 ^ w = a % 2 ^ w := by
  have hDiv : 2 ^ w ∣ 2 ^ V := by
    refine ⟨2 ^ (V - w), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  exact Nat.mod_mod_of_dvd a hDiv
end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crSpillLoad_spec (E : RAMEnv) (s : RAMState) (dst src : Fin 16)
    (hDst : dst ≠ 8) (h16 : 16 ≤ 2 ^ E.W)
    (hAddr : s.regs 8 + src.val < 2 ^ E.W) :
    let out := runBlock (crSpillLoad dst src) E s
    out.pc = s.pc + 3 ∧ out.mem = s.mem ∧
      out.regs dst = s.mem (s.regs 8 + src.val) % 2 ^ E.W ∧
      ∀ r, r ≠ dst → out.regs r = s.regs r := by
  classical
  have hSrc : src.val % 2 ^ E.W = src.val := Nat.mod_eq_of_lt (src.isLt.trans_le h16)
  have hA : (s.regs 8 + src.val) % 2 ^ E.W = s.regs 8 + src.val := Nat.mod_eq_of_lt hAddr
  dsimp only
  simp [crSpillLoad, runBlock, execInstr, Function.update, hDst, Ne.symm hDst,
    hSrc, hA, Nat.add_assoc]
  intro r hr he
  exact (hr he).elim
theorem crSpillWrite_spec (E : RAMEnv) (s : RAMState) (dst src : Fin 16)
    (hSrc : src ≠ 2) (h16 : 16 ≤ 2 ^ E.W)
    (hAddr : s.regs 8 + dst.val < 2 ^ E.W) :
    let out := runBlock (crSpillWrite dst src) E s
    out.pc = s.pc + 3 ∧ out.regs 2 = s.regs 8 + dst.val ∧
      (∀ r, r ≠ 2 → out.regs r = s.regs r) ∧
      out.mem = Function.update s.mem (s.regs 8 + dst.val) (s.regs src) := by
  classical
  have hDst : dst.val % 2 ^ E.W = dst.val := Nat.mod_eq_of_lt (dst.isLt.trans_le h16)
  have hA : (s.regs 8 + dst.val) % 2 ^ E.W = s.regs 8 + dst.val := Nat.mod_eq_of_lt hAddr
  dsimp only
  simp [crSpillWrite, runBlock, execInstr, Function.update, hSrc, hDst, hA, Nat.add_assoc]
  intro r hr he
  exact (hr he).elim
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crState_ext {s t : RAMState} (hp : s.pc = t.pc) (hr : s.regs = t.regs) (hm : s.mem = t.mem) : s = t := by
  cases s with
  | mk sp sr sm =>
      cases t with
      | mk tp tr tm =>
          cases hp
          cases hr
          cases hm
          rfl
theorem crExec_bin (k : CRBinKind) (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (k.ins d a b) E s =
      {s with pc := s.pc + 1, regs := Function.update s.regs d (k.val (s.regs a) (s.regs b) % 2 ^ E.W)} := by
  cases k <;> rfl
theorem crClip_wide_roundtrip (w V a : ℕ) (hWV : w ≤ V) :
    (a % 2 ^ V % 2 ^ w) % 2 ^ V = a % 2 ^ w := by
  rw [crClip_wide w V a hWV]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt a (Nat.two_pow_pos w)).trans_le
    (Nat.pow_le_pow_right (by norm_num) hWV))
theorem crBin_mod_spec (k : CRBinKind) (E : RAMEnv) (s : RAMState) (w : ℕ)
    (hWV : w ≤ E.W) (hMod : s.regs 13 = 2 ^ w) :
    runBlock [k.ins 0 0 1, .mod 0 0 13] E s =
      {s with pc := s.pc + 2, regs := Function.update s.regs 0 (k.val (s.regs 0) (s.regs 1) % 2 ^ w)} := by
  classical
  simp only [runBlock, List.foldl_cons, List.foldl_nil]
  rw [crExec_bin]
  apply crState_ext
  · simp [execInstr, Nat.add_assoc]
  · funext r
    by_cases hr : r = 0
    · subst r
      simp [execInstr, Function.update, hMod, crClip_wide_roundtrip w E.W _ hWV]
    · simp [execInstr, Function.update, hr]
  · rfl
theorem crSub_wide_value (a b small big : ℕ) (hSmall : 0 < small) (hSB : small ≤ big)
    (hb : b ≤ small) (ha : a + small < big) :
    ((((a + small) % big + big - b) % big) % small) % big = (a + small - b) % small := by
  rw [Nat.mod_eq_of_lt ha]
  have hDiff : a + small + big - b = (a + small - b) + big := by omega
  have hLt : a + small - b < big := lt_of_le_of_lt (Nat.sub_le _ _) ha
  rw [hDiff, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hLt]
  exact Nat.mod_eq_of_lt ((Nat.mod_lt _ hSmall).trans_le hSB)
theorem crSub_mod_spec (E : RAMEnv) (s : RAMState) (w : ℕ)
    (hMod : s.regs 13 = 2 ^ w) (hb : s.regs 1 ≤ 2 ^ w)
    (ha : s.regs 0 + 2 ^ w < 2 ^ E.W) (hWV : w ≤ E.W) :
    runBlock [.add 0 0 13, .sub 0 0 1, .mod 0 0 13] E s =
      {s with pc := s.pc + 3, regs := Function.update s.regs 0 ((s.regs 0 + 2 ^ w - s.regs 1) % 2 ^ w)} := by
  classical
  have hVal := crSub_wide_value (s.regs 0) (s.regs 1) (2 ^ w) (2 ^ E.W)
    (Nat.two_pow_pos w) (Nat.pow_le_pow_right (by norm_num) hWV) hb ha
  apply crState_ext
  · simp [runBlock, execInstr, Nat.add_assoc]
  · funext r
    by_cases hr : r = 0
    · subst r
      simpa only [runBlock, List.foldl_cons, List.foldl_nil, execInstr,
        Function.update_self, Function.update_of_ne (by decide : (13 : Fin 16) ≠ 0),
        Function.update_of_ne (by decide : (1 : Fin 16) ≠ 0), hMod] using hVal
    · simp [runBlock, execInstr, Function.update, hr]
  · rfl
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crSpillTwo_spec (ops : List Instr) (value : ℕ → ℕ → ℕ)
    (E : RAMEnv) (s : RAMState) (w : ℕ) (dst a b : Fin 16)
    (hWide : w < E.W) (hMod : s.regs 13 = 2 ^ w)
    (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w)
    (hBody : ∀ v : RAMState, v.regs 13 = 2 ^ w → v.regs 0 ≤ 2 ^ w → v.regs 1 ≤ 2 ^ w →
      runBlock ops E v =
        {v with pc := v.pc + ops.length, regs := Function.update v.regs 0 (value (v.regs 0) (v.regs 1))}) :
    let out := runBlock (crSpillLoad 0 a ++ crSpillLoad 1 b ++ ops ++ crSpillWrite dst 0) E s
    out.pc = s.pc + (ops.length + 9) ∧
      out.mem = Function.update s.mem (s.regs 8 + dst.val)
        (value (s.mem (s.regs 8 + a.val)) (s.mem (s.regs 8 + b.val))) ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → out.regs r = s.regs r := by
  classical
  have hPow : 2 ^ w < 2 ^ E.W := Nat.pow_lt_pow_right (by norm_num) hWide
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : ∀ r : Fin 16, s.regs 8 + r.val < 2 ^ E.W := by
    intro r
    have hr := r.isLt
    omega
  generalize hu : runBlock (crSpillLoad 0 a) E s = u
  have hU := crSpillLoad_spec E s 0 a (by decide) h16 (hAddr a)
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hUfr⟩ := hU
  have hU8 : u.regs 8 = s.regs 8 := hUfr 8 (by decide)
  have hUval : u.regs 0 = s.mem (s.regs 8 + a.val) := by
    rw [hU0, Nat.mod_eq_of_lt ((hRegs a).trans_lt hPow)]
  generalize hv : runBlock (crSpillLoad 1 b) E u = v
  have hV := crSpillLoad_spec E u 1 b (by decide) h16 (by rw [hU8]; exact hAddr b)
  rw [hv] at hV
  obtain ⟨hVpc, hVmem, hV1, hVfr⟩ := hV
  have hV8 : v.regs 8 = s.regs 8 := (hVfr 8 (by decide)).trans hU8
  have hV13 : v.regs 13 = 2 ^ w := (hVfr 13 (by decide)).trans ((hUfr 13 (by decide)).trans hMod)
  have hV0 : v.regs 0 = s.mem (s.regs 8 + a.val) := (hVfr 0 (by decide)).trans hUval
  have hVval : v.regs 1 = s.mem (s.regs 8 + b.val) := by
    rw [hV1, hUmem, hU8, Nat.mod_eq_of_lt ((hRegs b).trans_lt hPow)]
  generalize hq : runBlock ops E v = q
  have hQ : q = {v with pc := v.pc + ops.length, regs := Function.update v.regs 0 (value (v.regs 0) (v.regs 1))} := by
    rw [← hq]
    exact hBody v hV13 (by rw [hV0]; exact hRegs a) (by rw [hVval]; exact hRegs b)
  have hQpc : q.pc = v.pc + ops.length := congrArg RAMState.pc hQ
  have hQmem : q.mem = s.mem := (congrArg RAMState.mem hQ).trans (hVmem.trans hUmem)
  have hQfr : ∀ r : Fin 16, r ≠ 0 → q.regs r = v.regs r := by
    intro r hr
    simp only [hQ, Function.update_of_ne hr]
  have hQ8 : q.regs 8 = s.regs 8 := (hQfr 8 (by decide)).trans hV8
  have hQ0 : q.regs 0 = value (s.mem (s.regs 8 + a.val)) (s.mem (s.regs 8 + b.val)) := by
    simp only [hQ, Function.update_self]
    rw [hV0, hVval]
  generalize ho : runBlock (crSpillWrite dst 0) E q = out
  have hO := crSpillWrite_spec E q dst 0 (by decide) h16 (by rw [hQ8]; exact hAddr dst)
  rw [ho] at hO
  obtain ⟨hOpc, hO2, hOfr, hOmem⟩ := hO
  have hRun : runBlock (crSpillLoad 0 a ++ crSpillLoad 1 b ++ ops ++ crSpillWrite dst 0) E s = out := by
    simp only [runBlock_append]
    rw [hu, hv, hq, ho]
  dsimp only
  rw [hRun]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hOmem, hQmem, hQ8, hQ0]
  · intro r hr0 hr1 hr2
    exact (hOfr r hr2).trans ((hQfr r hr0).trans ((hVfr r hr1).trans (hUfr r hr0)))
theorem crSpillSub_spec (E : RAMEnv) (s : RAMState) (w : ℕ)
    (dst a b : Fin 16) (hWide : w + 1 < E.W) (hMod : s.regs 13 = 2 ^ w)
    (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w) :
    let out := runBlock (crSpillLoad 0 a ++ crSpillLoad 1 b ++
      [.add 0 0 13, .sub 0 0 1, .mod 0 0 13] ++ crSpillWrite dst 0) E s
    out.pc = s.pc + 12 ∧
      out.mem = Function.update s.mem (s.regs 8 + dst.val)
        ((s.mem (s.regs 8 + a.val) + 2 ^ w - s.mem (s.regs 8 + b.val)) % 2 ^ w) ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → out.regs r = s.regs r := by
  apply crSpillTwo_spec [.add 0 0 13, .sub 0 0 1, .mod 0 0 13]
    (fun x y => (x + 2 ^ w - y) % 2 ^ w) E s w dst a b
    (by omega) hMod hFile hRegs
  intro v hvMod hv0 hv1
  have hPow : 2 ^ (w + 1) < 2 ^ E.W := Nat.pow_lt_pow_right (by norm_num) hWide
  have hAdd : v.regs 0 + 2 ^ w < 2 ^ E.W := by
    rw [pow_succ] at hPow
    omega
  exact crSub_mod_spec E v w hvMod hv1 hAdd (by omega)
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crSpillOne_spec (ops : List Instr) (value : ℕ → ℕ)
    (E : RAMEnv) (s : RAMState) (w : ℕ) (dst a baseReg : Fin 16)
    (hBase : baseReg ≠ 0) (hWide : w < E.W) (hMod : s.regs 13 = 2 ^ w)
    (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w)
    (hBody : ∀ v : RAMState, v.mem = s.mem → v.regs baseReg = s.regs baseReg →
      v.regs 13 = 2 ^ w → v.regs 0 ≤ 2 ^ w →
      runBlock ops E v =
        {v with pc := v.pc + ops.length, regs := Function.update v.regs 0 (value (v.regs 0))}) :
    let out := runBlock (crSpillLoad 0 a ++ ops ++ crSpillWrite dst 0) E s
    out.pc = s.pc + (ops.length + 6) ∧
      out.mem = Function.update s.mem (s.regs 8 + dst.val) (value (s.mem (s.regs 8 + a.val))) ∧
      ∀ r, r ≠ 0 → r ≠ 2 → out.regs r = s.regs r := by
  classical
  have hPow : 2 ^ w < 2 ^ E.W := Nat.pow_lt_pow_right (by norm_num) hWide
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : ∀ r : Fin 16, s.regs 8 + r.val < 2 ^ E.W := by
    intro r
    have hr := r.isLt
    omega
  generalize hu : runBlock (crSpillLoad 0 a) E s = u
  have hU := crSpillLoad_spec E s 0 a (by decide) h16 (hAddr a)
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hUfr⟩ := hU
  have hU8 : u.regs 8 = s.regs 8 := hUfr 8 (by decide)
  have hUval : u.regs 0 = s.mem (s.regs 8 + a.val) := by
    rw [hU0, Nat.mod_eq_of_lt ((hRegs a).trans_lt hPow)]
  generalize hq : runBlock ops E u = q
  have hQ : q = {u with pc := u.pc + ops.length, regs := Function.update u.regs 0 (value (u.regs 0))} := by
    rw [← hq]
    exact hBody u hUmem (hUfr baseReg hBase)
      ((hUfr 13 (by decide)).trans hMod) (by rw [hUval]; exact hRegs a)
  have hQpc : q.pc = u.pc + ops.length := congrArg RAMState.pc hQ
  have hQmem : q.mem = s.mem := (congrArg RAMState.mem hQ).trans hUmem
  have hQfr : ∀ r : Fin 16, r ≠ 0 → q.regs r = u.regs r := by
    intro r hr
    simp only [hQ, Function.update_of_ne hr]
  have hQ8 : q.regs 8 = s.regs 8 := (hQfr 8 (by decide)).trans hU8
  have hQ0 : q.regs 0 = value (s.mem (s.regs 8 + a.val)) := by
    simp only [hQ, Function.update_self]
    rw [hUval]
  generalize ho : runBlock (crSpillWrite dst 0) E q = out
  have hO := crSpillWrite_spec E q dst 0 (by decide) h16 (by rw [hQ8]; exact hAddr dst)
  rw [ho] at hO
  obtain ⟨hOpc, hO2, hOfr, hOmem⟩ := hO
  have hRun : runBlock (crSpillLoad 0 a ++ ops ++ crSpillWrite dst 0) E s = out := by
    simp only [runBlock_append]
    rw [hu, hq, ho]
  dsimp only
  rw [hRun]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hOmem, hQmem, hQ8, hQ0]
  · intro r hr0 hr2
    exact (hOfr r hr2).trans ((hQfr r hr0).trans (hUfr r hr0))
def CRReadKind.value (k : CRReadKind) (E : RAMEnv) (mem : ℕ → ℕ) (a : ℕ) : ℕ :=
  match k with
  | .memory => mem a
  | .deterministic => E.det a
theorem crRead_mod_spec (k : CRReadKind) (E : RAMEnv) (s : RAMState) (w : ℕ)
    (baseReg : Fin 16) (hBase : baseReg ≠ 0) (hMod : s.regs 13 = 2 ^ w)
    (hAddr : s.regs baseReg + s.regs 0 < 2 ^ E.W) (hWide : w ≤ E.W) :
    runBlock [.add 0 baseReg 0, k.ins 0 0, .mod 0 0 13] E s =
      {s with pc := s.pc + 3, regs := Function.update s.regs 0 (k.value E s.mem (s.regs baseReg + s.regs 0) % 2 ^ w)} := by
  apply crState_ext
  · cases k <;> simp [runBlock, execInstr, CRReadKind.ins, Nat.add_assoc]
  · funext r
    by_cases hr : r = 0
    · subst r
      cases k <;> simp [runBlock, execInstr, CRReadKind.ins, CRReadKind.value,
        Function.update, hMod, Nat.mod_eq_of_lt hAddr, crClip_wide_roundtrip w E.W _ hWide]
    · cases k <;> simp [runBlock, execInstr, CRReadKind.ins, Function.update, hr]
  · cases k <;> rfl
theorem crSpillRead_spec (k : CRReadKind) (E : RAMEnv) (s : RAMState) (w : ℕ)
    (dst a baseReg : Fin 16) (hBase : baseReg ≠ 0) (hWide : w < E.W)
    (hMod : s.regs 13 = 2 ^ w) (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w)
    (hRead : s.regs baseReg + 2 ^ w < 2 ^ E.W) :
    let out := runBlock (crSpillLoad 0 a ++
      [.add 0 baseReg 0, k.ins 0 0, .mod 0 0 13] ++ crSpillWrite dst 0) E s
    out.pc = s.pc + 9 ∧
      out.mem = Function.update s.mem (s.regs 8 + dst.val)
        (k.value E s.mem (s.regs baseReg + s.mem (s.regs 8 + a.val)) % 2 ^ w) ∧
      ∀ r, r ≠ 0 → r ≠ 2 → out.regs r = s.regs r := by
  apply crSpillOne_spec [.add 0 baseReg 0, k.ins 0 0, .mod 0 0 13]
    (fun a => k.value E s.mem (s.regs baseReg + a) % 2 ^ w)
    E s w dst a baseReg hBase hWide hMod hFile hRegs
  intro v hvMem hvBase hvMod hv0
  have hAddr : v.regs baseReg + v.regs 0 < 2 ^ E.W := by rw [hvBase]; omega
  have h := crRead_mod_spec k E v w baseReg hBase hvMod hAddr hWide.le
  simpa only [hvMem, hvBase, List.length_cons, List.length_nil] using h
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
theorem crSpillFetchTwo_spec (E : RAMEnv) (s : RAMState) (w : ℕ) (a b : Fin 16)
    (hWide : w < E.W) (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w) :
    let out := runBlock (crSpillLoad 0 a ++ crSpillLoad 1 b) E s
    out.pc = s.pc + 6 ∧ out.mem = s.mem ∧
      out.regs 0 = s.mem (s.regs 8 + a.val) ∧
      out.regs 1 = s.mem (s.regs 8 + b.val) ∧
      ∀ r, r ≠ 0 → r ≠ 1 → out.regs r = s.regs r := by
  have hPow : 2 ^ w < 2 ^ E.W := Nat.pow_lt_pow_right (by norm_num) hWide
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : ∀ r : Fin 16, s.regs 8 + r.val < 2 ^ E.W := by
    intro r
    have hr := r.isLt
    omega
  generalize hu : runBlock (crSpillLoad 0 a) E s = u
  have hU := crSpillLoad_spec E s 0 a (by decide) h16 (hAddr a)
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hUfr⟩ := hU
  have hU8 : u.regs 8 = s.regs 8 := hUfr 8 (by decide)
  generalize hv : runBlock (crSpillLoad 1 b) E u = v
  have hV := crSpillLoad_spec E u 1 b (by decide) h16 (by rw [hU8]; exact hAddr b)
  rw [hv] at hV
  obtain ⟨hVpc, hVmem, hV1, hVfr⟩ := hV
  dsimp only
  rw [runBlock_append, hu, hv]
  refine ⟨by omega, hVmem.trans hUmem, ?_, ?_, ?_⟩
  · rw [hVfr 0 (by decide), hU0, Nat.mod_eq_of_lt ((hRegs a).trans_lt hPow)]
  · rw [hV1, hU8, hUmem, Nat.mod_eq_of_lt ((hRegs b).trans_lt hPow)]
  · intro r hr0 hr1
    exact (hVfr r hr1).trans (hUfr r hr0)
theorem crStore_log_spec (E : RAMEnv) (s : RAMState)
    (hAddr : s.regs 9 + s.regs 0 < 2 ^ E.W)
    (hLog : s.regs 11 + s.regs 12 < 2 ^ E.W)
    (hCount : s.regs 12 + 1 < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    runBlock [.add 2 9 0, .store 2 1, .add 3 11 12, .store 3 2, .add 12 12 15] E s =
      {s with pc := s.pc + 5, regs := Function.update (Function.update (Function.update s.regs 2 (s.regs 9 + s.regs 0)) 3 (s.regs 11 + s.regs 12)) 12 (s.regs 12 + 1), mem := Function.update (Function.update s.mem (s.regs 9 + s.regs 0) (s.regs 1)) (s.regs 11 + s.regs 12) (s.regs 9 + s.regs 0)} := by
  apply crState_ext
  · simp [runBlock, execInstr, Nat.add_assoc]
  · funext r
    simp [runBlock, execInstr, Function.update, hOne, Nat.mod_eq_of_lt hAddr,
      Nat.mod_eq_of_lt hLog, Nat.mod_eq_of_lt hCount]
  · simp [runBlock, execInstr, Function.update, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hLog]
theorem crSpillStore_spec (E : RAMEnv) (s : RAMState) (w : ℕ) (a b : Fin 16)
    (hWide : w < E.W) (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w)
    (hAddr : s.regs 9 + 2 ^ w < 2 ^ E.W)
    (hLog : s.regs 11 + s.regs 12 < 2 ^ E.W)
    (hCount : s.regs 12 + 1 < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    let out := runBlock ((crSpillLoad 0 a ++ crSpillLoad 1 b) ++
      [.add 2 9 0, .store 2 1, .add 3 11 12, .store 3 2, .add 12 12 15]) E s
    out.pc = s.pc + 11 ∧
      out.mem = Function.update
        (Function.update s.mem (s.regs 9 + s.mem (s.regs 8 + a.val)) (s.mem (s.regs 8 + b.val)))
        (s.regs 11 + s.regs 12) (s.regs 9 + s.mem (s.regs 8 + a.val)) ∧
      out.regs 12 = s.regs 12 + 1 ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = s.regs r := by
  generalize hu : runBlock (crSpillLoad 0 a ++ crSpillLoad 1 b) E s = u
  have hU := crSpillFetchTwo_spec E s w a b hWide hFile hRegs
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hU1, hUfr⟩ := hU
  have hU9 : u.regs 9 = s.regs 9 := hUfr 9 (by decide) (by decide)
  have hU11 : u.regs 11 = s.regs 11 := hUfr 11 (by decide) (by decide)
  have hU12 : u.regs 12 = s.regs 12 := hUfr 12 (by decide) (by decide)
  have hU15 : u.regs 15 = 1 := (hUfr 15 (by decide) (by decide)).trans hOne
  have hUa : u.regs 9 + u.regs 0 < 2 ^ E.W := by rw [hU9, hU0]; have h := hRegs a; omega
  have hUl : u.regs 11 + u.regs 12 < 2 ^ E.W := by rw [hU11, hU12]; exact hLog
  have hUc : u.regs 12 + 1 < 2 ^ E.W := by rw [hU12]; exact hCount
  have hBody := crStore_log_spec E u hUa hUl hUc hU15
  dsimp only
  rw [runBlock_append, hu, hBody]
  refine ⟨by simpa only [hUpc] using Nat.add_assoc s.pc 6 5, ?_, ?_, ?_⟩
  · simp only [hUmem, hU9, hU0, hU1, hU11, hU12]
  · simp only [Function.update_self, hU12]
  · intro r hr0 hr1 hr2 hr3 hr12
    simp only [Function.update_of_ne hr12, Function.update_of_ne hr3, Function.update_of_ne hr2]
    exact hUfr r hr0 hr1
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
def CRSpillStable (r : Fin 16) : Prop :=
  r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 7 ∧ r ≠ 12 ∧ r ≠ 14
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
theorem crSpillBin_spec (k : CRBinKind) (E : RAMEnv) (s : RAMState) (w : ℕ)
    (dst a b : Fin 16) (hWide : w < E.W) (hMod : s.regs 13 = 2 ^ w)
    (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w) :
    let out := runBlock (crSpillBin k.ins dst a b) E s
    out.pc = s.pc + 11 ∧
      out.mem = Function.update s.mem (s.regs 8 + dst.val)
        (k.val (s.mem (s.regs 8 + a.val)) (s.mem (s.regs 8 + b.val)) % 2 ^ w) ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → out.regs r = s.regs r := by
  classical
  have hPow : 2 ^ w < 2 ^ E.W := Nat.pow_lt_pow_right (by norm_num) hWide
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : ∀ r : Fin 16, s.regs 8 + r.val < 2 ^ E.W := by
    intro r
    have hr := r.isLt
    omega
  generalize hu : runBlock (crSpillLoad 0 a) E s = u
  have hU := crSpillLoad_spec E s 0 a (by decide) h16 (hAddr a)
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hUfr⟩ := hU
  have hU8 : u.regs 8 = s.regs 8 := hUfr 8 (by decide)
  have hU13 : u.regs 13 = 2 ^ w := (hUfr 13 (by decide)).trans hMod
  have hUval : u.regs 0 = s.mem (s.regs 8 + a.val) := by
    rw [hU0, Nat.mod_eq_of_lt ((hRegs a).trans_lt hPow)]
  generalize hv : runBlock (crSpillLoad 1 b) E u = v
  have hV := crSpillLoad_spec E u 1 b (by decide) h16 (by rw [hU8]; exact hAddr b)
  rw [hv] at hV
  obtain ⟨hVpc, hVmem, hV1, hVfr⟩ := hV
  have hV8 : v.regs 8 = s.regs 8 := (hVfr 8 (by decide)).trans hU8
  have hV13 : v.regs 13 = 2 ^ w := (hVfr 13 (by decide)).trans hU13
  have hV0 : v.regs 0 = s.mem (s.regs 8 + a.val) := (hVfr 0 (by decide)).trans hUval
  have hVval : v.regs 1 = s.mem (s.regs 8 + b.val) := by
    rw [hV1, hUmem, hU8, Nat.mod_eq_of_lt ((hRegs b).trans_lt hPow)]
  generalize hq : runBlock [k.ins 0 0 1, .mod 0 0 13] E v = q
  have hQ : q = {v with pc := v.pc + 2, regs := Function.update v.regs 0 (k.val (v.regs 0) (v.regs 1) % 2 ^ w)} := by
    rw [← hq]
    exact crBin_mod_spec k E v w hWide.le hV13
  have hQpc : q.pc = v.pc + 2 := congrArg RAMState.pc hQ
  have hQmem : q.mem = s.mem := (congrArg RAMState.mem hQ).trans (hVmem.trans hUmem)
  have hQfr : ∀ r : Fin 16, r ≠ 0 → q.regs r = v.regs r := by
    intro r hr
    simp only [hQ, Function.update_of_ne hr]
  have hQ8 : q.regs 8 = s.regs 8 := (hQfr 8 (by decide)).trans hV8
  have hQ0 : q.regs 0 = k.val (s.mem (s.regs 8 + a.val)) (s.mem (s.regs 8 + b.val)) % 2 ^ w := by
    simp only [hQ, Function.update_self]
    rw [hV0, hVval]
  generalize ho : runBlock (crSpillWrite dst 0) E q = out
  have hO := crSpillWrite_spec E q dst 0 (by decide) h16 (by rw [hQ8]; exact hAddr dst)
  rw [ho] at hO
  obtain ⟨hOpc, hO2, hOfr, hOmem⟩ := hO
  have hRun : runBlock (crSpillBin k.ins dst a b) E s = out := by
    simp only [crSpillBin, runBlock_append]
    rw [hu, hv, hq, ho]
  dsimp only
  rw [hRun]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hOmem, hQmem, hQ8, hQ0]
  · intro r hr0 hr1 hr2
    exact (hOfr r hr2).trans ((hQfr r hr0).trans ((hVfr r hr1).trans (hUfr r hr0)))
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crExecute_conditional (P : Program) (E : RAMEnv) (s : RAMState)
    (w : ℕ) (a : Fin 16) (target next : ℕ)
    (hWide : w < E.W) (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, s.mem (s.regs 8 + r.val) ≤ 2 ^ w)
    (hAt : At P s.pc (crSpillLoad 0 a ++ [.jz 0 target, .jmp next])) :
    ∃ k : ℕ, k ≤ 5 ∧
      (step P E)^[k] s =
        {runBlock (crSpillLoad 0 a) E s with
          pc := if s.mem (s.regs 8 + a.val) = 0 then target else next} := by
  have hPow : 2 ^ w < 2 ^ E.W := Nat.pow_lt_pow_right (by norm_num) hWide
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : s.regs 8 + a.val < 2 ^ E.W := by have h := a.isLt; omega
  have hLoadAt := crAt_prefix P s.pc (crSpillLoad 0 a) [.jz 0 target, .jmp next] hAt
  have hTailAt := crAt_suffix P s.pc (crSpillLoad 0 a) [.jz 0 target, .jmp next] hAt
  have hNo : NoBranch (crSpillLoad 0 a) := by simp [crSpillLoad, NoBranch, Instr.NoBranchI]
  generalize hu : runBlock (crSpillLoad 0 a) E s = u
  have hRun : (step P E)^[3] s = u := by
    have h := iterate_runBlock_of_at P E (crSpillLoad 0 a) s hLoadAt hNo
    rw [hu] at h
    simpa only [crSpillLoad, List.length_cons, List.length_nil] using h
  have hU := crSpillLoad_spec E s 0 a (by decide) h16 hAddr
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hUfr⟩ := hU
  have hVal : u.regs 0 = s.mem (s.regs 8 + a.val) := by
    rw [hU0, Nat.mod_eq_of_lt ((hRegs a).trans_lt hPow)]
  have hFetch : P[u.pc]? = some (.jz 0 target) := by
    have h := hTailAt 0 (by simp)
    simpa only [crSpillLoad, List.length_cons, List.length_nil, Nat.add_zero, List.getElem?_cons_zero,
      hUpc] using h
  have hNext : P[u.pc + 1]? = some (.jmp next) := by
    have h := hTailAt 1 (by simp)
    simpa only [crSpillLoad, List.length_cons, List.length_nil, List.getElem?_cons_succ,
      List.getElem?_cons_zero, hUpc] using h
  by_cases hz : s.mem (s.regs 8 + a.val) = 0
  · refine ⟨4, by omega, ?_⟩
    have hStep : step P E u = {u with pc := target} := by
      rw [crStep_fetch P E u _ hFetch]
      simp [execInstr, hVal, hz]
    rw [show 4 = 1 + 3 by omega, Function.iterate_add_apply]
    change step P E ((step P E)^[3] s) = _
    rw [hRun, hStep, if_pos hz]
  · refine ⟨5, by omega, ?_⟩
    have hStep : step P E u = {u with pc := u.pc + 1} := by
      rw [crStep_fetch P E u _ hFetch]
      simp only [execInstr, hVal, if_neg hz]
    have hJump : step P E {u with pc := u.pc + 1} = {u with pc := next} := by
      rw [crStep_fetch P E {u with pc := u.pc + 1} _ hNext]
      rfl
    rw [show 5 = 2 + 3 by omega, Function.iterate_add_apply]
    change step P E (step P E ((step P E)^[3] s)) = _
    rw [hRun, hStep, hJump, if_neg hz]
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
theorem crSpillCommit_spec (ops : List Instr) (E : RAMEnv) (s : RAMState)
    (dst : Fin 16) (value : ℕ) (hFile : s.regs 8 + 16 ≤ 2 ^ E.W)
    (hBody : runBlock ops E s =
      {s with pc := s.pc + ops.length, regs := Function.update s.regs 0 value}) :
    let out := runBlock (ops ++ crSpillWrite dst 0) E s
    out.pc = s.pc + (ops.length + 3) ∧
      out.mem = Function.update s.mem (s.regs 8 + dst.val) value ∧
      ∀ r, r ≠ 0 → r ≠ 2 → out.regs r = s.regs r := by
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : s.regs 8 + dst.val < 2 ^ E.W := by have h := dst.isLt; omega
  generalize hq : runBlock ops E s = q
  have hQ : q = {s with pc := s.pc + ops.length, regs := Function.update s.regs 0 value} :=
    hq.symm.trans hBody
  have hQpc : q.pc = s.pc + ops.length := congrArg RAMState.pc hQ
  have hQmem : q.mem = s.mem := by simp only [hQ]
  have hQ8 : q.regs 8 = s.regs 8 := by simp only [hQ, Function.update_of_ne (by decide : (8 : Fin 16) ≠ 0)]
  have hQ0 : q.regs 0 = value := by simp only [hQ, Function.update_self]
  have hQfr : ∀ r : Fin 16, r ≠ 0 → q.regs r = s.regs r := by
    intro r hr
    simp only [hQ, Function.update_of_ne hr]
  generalize ho : runBlock (crSpillWrite dst 0) E q = out
  have hO := crSpillWrite_spec E q dst 0 (by decide) h16 (by rw [hQ8]; exact hAddr)
  rw [ho] at hO
  obtain ⟨hOpc, hO2, hOfr, hOmem⟩ := hO
  dsimp only
  rw [runBlock_append, hq, ho]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hOmem, hQmem, hQ8, hQ0]
  · intro r hr0 hr2
    exact (hOfr r hr2).trans (hQfr r hr0)
theorem crImm_mod_spec (E : RAMEnv) (s : RAMState) (w value : ℕ)
    (hWide : w ≤ E.W) (hMod : s.regs 13 = 2 ^ w) :
    runBlock [.imm 0 value, .mod 0 0 13] E s =
      {s with pc := s.pc + 2, regs := Function.update s.regs 0 (value % 2 ^ w)} := by
  apply crState_ext
  · simp [runBlock, execInstr, Nat.add_assoc]
  · funext r
    by_cases hr : r = 0
    · subst r
      simp [runBlock, execInstr, Function.update, hMod, crClip_wide_roundtrip w E.W value hWide]
    · simp [runBlock, execInstr, Function.update, hr]
  · rfl
theorem crSpillImm_spec (E : RAMEnv) (s : RAMState) (w value : ℕ) (dst : Fin 16)
    (hWide : w ≤ E.W) (hMod : s.regs 13 = 2 ^ w)
    (hFile : s.regs 8 + 16 ≤ 2 ^ E.W) :
    let out := runBlock ([.imm 0 value, .mod 0 0 13] ++ crSpillWrite dst 0) E s
    out.pc = s.pc + 5 ∧ out.mem = Function.update s.mem (s.regs 8 + dst.val) (value % 2 ^ w) ∧
      ∀ r, r ≠ 0 → r ≠ 2 → out.regs r = s.regs r := by
  apply crSpillCommit_spec [.imm 0 value, .mod 0 0 13] E s dst (value % 2 ^ w) hFile
  simpa only [List.length_cons, List.length_nil] using crImm_mod_spec E s w value hWide hMod
theorem crSpillZero_spec (E : RAMEnv) (s : RAMState) (dst : Fin 16)
    (hFile : s.regs 8 + 16 ≤ 2 ^ E.W) :
    let out := runBlock ([.imm 0 0] ++ crSpillWrite dst 0) E s
    out.pc = s.pc + 4 ∧ out.mem = Function.update s.mem (s.regs 8 + dst.val) 0 ∧
      ∀ r, r ≠ 0 → r ≠ 2 → out.regs r = s.regs r := by
  apply crSpillCommit_spec [.imm 0 0] E s dst 0 hFile
  simp [runBlock, execInstr]
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
def CRView (w file memBase : ℕ) (src physical : RAMState) : Prop :=
  (∀ r : Fin 16, physical.mem (file + r.val) = src.regs r) ∧
    ∀ a : ℕ, a ≤ 2 ^ (w + 1) → physical.mem (memBase + a) = src.mem a
theorem crView_physical_mem {w file memBase : ℕ} {src p q : RAMState}
    (h : CRView w file memBase src p) (hm : q.mem = p.mem) : CRView w file memBase src q := by
  constructor
  · intro r
    rw [hm]
    exact h.1 r
  · intro a ha
    rw [hm]
    exact h.2 a ha
theorem crView_write_reg {w file memBase : ℕ} {src p : RAMState}
    (h : CRView w file memBase src p) (hFile : file + 16 ≤ memBase) (d : Fin 16) (value : ℕ) :
    CRView w file memBase {src with regs := Function.update src.regs d value}
      {p with mem := Function.update p.mem (file + d.val) value} := by
  constructor
  · intro r
    by_cases hr : r = d
    · subst r
      simp only [Function.update_self]
    · have hAddr : file + r.val ≠ file + d.val := by
        intro he
        exact hr (Fin.ext (Nat.add_left_cancel he))
      simp only [Function.update_of_ne hAddr, Function.update_of_ne hr]
      exact h.1 r
  · intro a ha
    have hLt : file + d.val < memBase + a :=
      ((Nat.add_lt_add_left d.isLt file).trans_le hFile).trans_le (Nat.le_add_right memBase a)
    have hAddr : memBase + a ≠ file + d.val := (Nat.ne_of_lt hLt).symm
    simp only [Function.update_of_ne hAddr]
    exact h.2 a ha
theorem crView_store {w file memBase : ℕ} {src p : RAMState}
    (h : CRView w file memBase src p) (hFile : file + 16 ≤ memBase)
    (addr value logAddr : ℕ) (hLog : memBase + 2 ^ (w + 1) < logAddr) :
    CRView w file memBase {src with mem := Function.update src.mem addr value}
      {p with mem := Function.update (Function.update p.mem (memBase + addr) value) logAddr (memBase + addr)} := by
  constructor
  · intro r
    have hRlt : file + r.val < memBase := (Nat.add_lt_add_left r.isLt file).trans_le hFile
    have hTop : memBase < logAddr := (Nat.le_add_right memBase (2 ^ (w + 1))).trans_lt hLog
    have hM : file + r.val ≠ memBase + addr :=
      Nat.ne_of_lt (hRlt.trans_le (Nat.le_add_right memBase addr))
    have hL : file + r.val ≠ logAddr := Nat.ne_of_lt (hRlt.trans hTop)
    simp only [Function.update_of_ne hL, Function.update_of_ne hM]
    exact h.1 r
  · intro a ha
    have hL : memBase + a ≠ logAddr := Nat.ne_of_lt ((Nat.add_le_add_left ha memBase).trans_lt hLog)
    simp only [Function.update_of_ne hL]
    by_cases hA : a = addr
    · subst a
      simp only [Function.update_self]
    · have hM : memBase + a ≠ memBase + addr := by omega
      simp only [Function.update_of_ne hM, Function.update_of_ne hA]
      exact h.2 a ha
theorem crView_source_pc {w file memBase pc : ℕ} {src p : RAMState} :
    CRView w file memBase {src with pc := pc} p ↔ CRView w file memBase src p := Iff.rfl
theorem crView_regs_bound {w file memBase : ℕ} {src p : RAMState}
    (h : CRView w file memBase src p) (hWord : CRWordClosed w src) :
    ∀ r : Fin 16, p.mem (file + r.val) ≤ 2 ^ w := by
  intro r
  rw [h.1 r]
  exact hWord.1 r
theorem crView_source_address {w file memBase : ℕ} {src p : RAMState}
    (h : CRView w file memBase src p) (hWord : CRWordClosed w src) (r : Fin 16) :
    p.mem (memBase + src.regs r) = src.mem (src.regs r) := by
  apply h.2
  exact (hWord.1 r).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crView_reg_of_mem {w file memBase : ℕ} {src p out : RAMState}
    (h : CRView w file memBase src p) (hFile : file + 16 ≤ memBase) (d : Fin 16) (value : ℕ)
    (hm : out.mem = Function.update p.mem (file + d.val) value) :
    CRView w file memBase {src with pc := src.pc + 1, regs := Function.update src.regs d value} out := by
  change CRView w file memBase {src with regs := Function.update src.regs d value} out
  exact crView_physical_mem (crView_write_reg h hFile d value) hm
theorem crView_file_bound {w file memBase : ℕ} {src p : RAMState}
    (h : CRView w file memBase src p) (hWord : CRWordClosed w src) (hPtr : p.regs 8 = file) :
    ∀ r : Fin 16, p.mem (p.regs 8 + r.val) ≤ 2 ^ w := by
  intro r
  rw [hPtr]
  exact crView_regs_bound h hWord r
theorem crSpillBin_view (k : CRBinKind) (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ)
    (det : ℕ → ℕ) (dst a b : Fin 16)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w < E.W) (hMod : p.regs 13 = 2 ^ w) (hPtr : p.regs 8 = file)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase (execInstr (k.ins dst a b) (detEnv w det) src)
      (runBlock (crSpillBin k.ins dst a b) E p) := by
  generalize ho : runBlock (crSpillBin k.ins dst a b) E p = out
  have hSpec := crSpillBin_spec k E p w dst a b hWide hMod
    (by rw [hPtr]; exact hFile) (crView_file_bound hView hSource hPtr)
  rw [ho] at hSpec
  obtain ⟨hPc, hMem, hRegs⟩ := hSpec
  rw [crExec_bin]
  apply crView_reg_of_mem hView hSeparate
  rw [hPtr, hView.1 a, hView.1 b] at hMem
  exact hMem
theorem crSpillSub_view (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ)
    (det : ℕ → ℕ) (dst a b : Fin 16)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w + 1 < E.W) (hMod : p.regs 13 = 2 ^ w) (hPtr : p.regs 8 = file)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase (execInstr (.sub dst a b) (detEnv w det) src)
      (runBlock (crSpillLoad 0 a ++ crSpillLoad 1 b ++
        [.add 0 0 13, .sub 0 0 1, .mod 0 0 13] ++ crSpillWrite dst 0) E p) := by
  generalize ho : runBlock (crSpillLoad 0 a ++ crSpillLoad 1 b ++
    [.add 0 0 13, .sub 0 0 1, .mod 0 0 13] ++ crSpillWrite dst 0) E p = out
  have hSpec := crSpillSub_spec E p w dst a b hWide hMod
    (by rw [hPtr]; exact hFile) (crView_file_bound hView hSource hPtr)
  rw [ho] at hSpec
  obtain ⟨hPc, hMem, hRegs⟩ := hSpec
  change CRView w file memBase
    {src with pc := src.pc + 1, regs := Function.update src.regs dst ((src.regs a + 2 ^ w - src.regs b) % 2 ^ w)} out
  apply crView_reg_of_mem hView hSeparate
  rw [hPtr, hView.1 a, hView.1 b] at hMem
  exact hMem
theorem crSpillImm_view (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ)
    (det : ℕ → ℕ) (dst : Fin 16) (value : ℕ)
    (hView : CRView w file memBase src p) (hWide : w ≤ E.W)
    (hMod : p.regs 13 = 2 ^ w) (hPtr : p.regs 8 = file)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase (execInstr (.imm dst value) (detEnv w det) src)
      (runBlock ([.imm 0 value, .mod 0 0 13] ++ crSpillWrite dst 0) E p) := by
  generalize ho : runBlock ([.imm 0 value, .mod 0 0 13] ++ crSpillWrite dst 0) E p = out
  have hSpec := crSpillImm_spec E p w value dst hWide hMod (by rw [hPtr]; exact hFile)
  rw [ho] at hSpec
  obtain ⟨hPc, hMem, hRegs⟩ := hSpec
  change CRView w file memBase
    {src with pc := src.pc + 1, regs := Function.update src.regs dst (value % 2 ^ w)} out
  apply crView_reg_of_mem hView hSeparate
  rw [hPtr] at hMem
  exact hMem
theorem crSpillLoad_view (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ)
    (det : ℕ → ℕ) (dst a : Fin 16)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w < E.W) (hMod : p.regs 13 = 2 ^ w) (hPtr : p.regs 8 = file)
    (hMemPtr : p.regs 9 = memBase) (hRead : memBase + 2 ^ w < 2 ^ E.W)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase (execInstr (.load dst a) (detEnv w det) src)
      (runBlock (crSpillLoad 0 a ++ [.add 0 9 0, .load 0 0, .mod 0 0 13] ++ crSpillWrite dst 0) E p) := by
  generalize ho : runBlock (crSpillLoad 0 a ++ [.add 0 9 0, .load 0 0, .mod 0 0 13] ++ crSpillWrite dst 0) E p = out
  have hSpec := crSpillRead_spec .memory E p w dst a 9 (by decide) hWide hMod
    (by rw [hPtr]; exact hFile) (crView_file_bound hView hSource hPtr) (by rw [hMemPtr]; exact hRead)
  simp only [CRReadKind.ins] at hSpec
  rw [ho] at hSpec
  obtain ⟨hPc, hMem, hRegs⟩ := hSpec
  change CRView w file memBase
    {src with pc := src.pc + 1, regs := Function.update src.regs dst (src.mem (src.regs a) % 2 ^ w)} out
  apply crView_reg_of_mem hView hSeparate
  simp only [CRReadKind.value] at hMem
  rw [hPtr, hMemPtr, hView.1 a, crView_source_address hView hSource a] at hMem
  exact hMem
theorem crSpillDet_view (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ)
    (det : ℕ → ℕ) (dst a : Fin 16)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w < E.W) (hMod : p.regs 13 = 2 ^ w) (hPtr : p.regs 8 = file)
    (hRead : p.regs 10 + 2 ^ w < 2 ^ E.W)
    (hDet : ∀ q, q ≤ 2 ^ w → E.det (p.regs 10 + q) = det q)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase (execInstr (.qDet dst a) (detEnv w det) src)
      (runBlock (crSpillLoad 0 a ++ [.add 0 10 0, .qDet 0 0, .mod 0 0 13] ++ crSpillWrite dst 0) E p) := by
  generalize ho : runBlock (crSpillLoad 0 a ++ [.add 0 10 0, .qDet 0 0, .mod 0 0 13] ++ crSpillWrite dst 0) E p = out
  have hSpec := crSpillRead_spec .deterministic E p w dst a 10 (by decide) hWide hMod
    (by rw [hPtr]; exact hFile) (crView_file_bound hView hSource hPtr) hRead
  simp only [CRReadKind.ins] at hSpec
  rw [ho] at hSpec
  obtain ⟨hPc, hMem, hRegs⟩ := hSpec
  change CRView w file memBase
    {src with pc := src.pc + 1, regs := Function.update src.regs dst (det (src.regs a) % 2 ^ w)} out
  apply crView_reg_of_mem hView hSeparate
  simp only [CRReadKind.value] at hMem
  rw [hPtr, hView.1 a, hDet (src.regs a) (hSource.1 a)] at hMem
  exact hMem
theorem crSpillStore_view (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ)
    (det : ℕ → ℕ) (a b : Fin 16)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w < E.W) (hPtr : p.regs 8 = file) (hMemPtr : p.regs 9 = memBase)
    (hRead : memBase + 2 ^ w < 2 ^ E.W) (hOne : p.regs 15 = 1)
    (hLog : p.regs 11 + p.regs 12 < 2 ^ E.W) (hCount : p.regs 12 + 1 < 2 ^ E.W)
    (hLogSeparate : memBase + 2 ^ (w + 1) < p.regs 11 + p.regs 12)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase (execInstr (.store a b) (detEnv w det) src)
      (runBlock ((crSpillLoad 0 a ++ crSpillLoad 1 b) ++
        [.add 2 9 0, .store 2 1, .add 3 11 12, .store 3 2, .add 12 12 15]) E p) := by
  generalize ho : runBlock ((crSpillLoad 0 a ++ crSpillLoad 1 b) ++
    [.add 2 9 0, .store 2 1, .add 3 11 12, .store 3 2, .add 12 12 15]) E p = out
  have hSpec := crSpillStore_spec E p w a b hWide (by rw [hPtr]; exact hFile)
    (crView_file_bound hView hSource hPtr) (by rw [hMemPtr]; exact hRead) hLog hCount hOne
  rw [ho] at hSpec
  obtain ⟨hPc, hMem, hCounter, hRegs⟩ := hSpec
  change CRView w file memBase {src with pc := src.pc + 1, mem := Function.update src.mem (src.regs a) (src.regs b)} out
  change CRView w file memBase {src with mem := Function.update src.mem (src.regs a) (src.regs b)} out
  apply crView_physical_mem (crView_store hView hSeparate (src.regs a) (src.regs b) _ hLogSeparate)
  rw [hPtr, hMemPtr, hView.1 a, hView.1 b] at hMem
  exact hMem
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crSpillZero_view (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ) (dst : Fin 16)
    (hView : CRView w file memBase src p) (hPtr : p.regs 8 = file)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase {src with pc := src.pc + 1, regs := Function.update src.regs dst 0}
      (runBlock ([.imm 0 0] ++ crSpillWrite dst 0) E p) := by
  generalize ho : runBlock ([.imm 0 0] ++ crSpillWrite dst 0) E p = out
  have hSpec := crSpillZero_spec E p dst (by rw [hPtr]; exact hFile)
  rw [ho] at hSpec
  obtain ⟨hPc, hMem, hRegs⟩ := hSpec
  apply crView_reg_of_mem hView hSeparate
  rw [hPtr] at hMem
  exact hMem
theorem crSpillPayload_view (ins : Instr) (E : RAMEnv) (p src : RAMState) (w file memBase : ℕ)
    (det : ℕ → ℕ) (n base fail ok : ℕ) (hNo : ins.NoBranchI)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w + 1 < E.W) (hMod : p.regs 13 = 2 ^ w) (hPtr : p.regs 8 = file)
    (hMemPtr : p.regs 9 = memBase) (hRead : memBase + 2 ^ w < 2 ^ E.W)
    (hDetRead : p.regs 10 + 2 ^ w < 2 ^ E.W)
    (hDet : ∀ q, q ≤ 2 ^ w → E.det (p.regs 10 + q) = det q)
    (hOne : p.regs 15 = 1)
    (hLog : p.regs 11 + p.regs 12 < 2 ^ E.W) (hCount : p.regs 12 + 1 < 2 ^ E.W)
    (hLogSeparate : memBase + 2 ^ (w + 1) < p.regs 11 + p.regs 12)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    CRView w file memBase (execInstr ins (detEnv w det) src)
      (runBlock (crSpillPayload n base fail ok ins) E p) := by
  have hw : w < E.W := by omega
  cases ins with
  | imm d v => exact crSpillImm_view E p src w file memBase det d v hView hw.le hMod hPtr hFile hSeparate
  | add d a b => exact crSpillBin_view .add E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | sub d a b => exact crSpillSub_view E p src w file memBase det d a b hView hSource hWide hMod hPtr hFile hSeparate
  | mul d a b => exact crSpillBin_view .mul E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | div d a b => exact crSpillBin_view .div E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | mod d a b => exact crSpillBin_view .mod E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | band d a b => exact crSpillBin_view .band E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | bor d a b => exact crSpillBin_view .bor E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | bxor d a b => exact crSpillBin_view .bxor E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | shl d a b => exact crSpillBin_view .shl E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | shr d a b => exact crSpillBin_view .shr E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | lt d a b => exact crSpillBin_view .lt E p src w file memBase det d a b hView hSource hw hMod hPtr hFile hSeparate
  | load d a => exact crSpillLoad_view E p src w file memBase det d a hView hSource hw hMod hPtr hMemPtr hRead hFile hSeparate
  | store a b =>
    simpa only [crSpillPayload, List.append_assoc] using
      crSpillStore_view E p src w file memBase det a b hView hSource hw hPtr hMemPtr hRead hOne hLog hCount hLogSeparate hFile hSeparate
  | qDet d a => exact crSpillDet_view E p src w file memBase det d a hView hSource hw hMod hPtr hDetRead hDet hFile hSeparate
  | qPerm d k a =>
    simpa only [execInstr, detEnv, Nat.zero_mod, crSpillPayload] using
      crSpillZero_view E p src w file memBase d hView hPtr hFile hSeparate
  | qPermInv d k a =>
    simpa only [execInstr, detEnv, Nat.zero_mod, crSpillPayload] using
      crSpillZero_view E p src w file memBase d hView hPtr hFile hSeparate
  | qCoeff d k a =>
    simpa only [execInstr, detEnv, Nat.zero_mod, crSpillPayload] using
      crSpillZero_view E p src w file memBase d hView hPtr hFile hSeparate
  | jz a t => exact (hNo.2.1 a t rfl).elim
  | jmp t => exact (hNo.1 t rfl).elim
  | halt => exact (hNo.2.2 rfl).elim
theorem crPayload_noStore12 (n base fail ok : ℕ) (ins : Instr)
    (h : ∀ a b, ins ≠ .store a b) :
    ∀ op ∈ crSpillPayload n base fail ok ins, CRNoWrite 12 op := by
  cases ins <;> simp_all [crSpillPayload, crSpillBin, crSpillLoad, crSpillWrite, CRNoWrite]
theorem crSpillPayload_log_bound (ins : Instr) (E : RAMEnv) (p : RAMState) (w : ℕ)
    (n base fail ok : ℕ) (hWide : w < E.W) (hFile : p.regs 8 + 16 ≤ 2 ^ E.W)
    (hRegs : ∀ r : Fin 16, p.mem (p.regs 8 + r.val) ≤ 2 ^ w)
    (hRead : p.regs 9 + 2 ^ w < 2 ^ E.W) (hOne : p.regs 15 = 1)
    (hLog : p.regs 11 + p.regs 12 < 2 ^ E.W) (hCount : p.regs 12 + 1 < 2 ^ E.W) :
    (runBlock (crSpillPayload n base fail ok ins) E p).regs 12 ≤ p.regs 12 + 1 := by
  by_cases hStore : ∃ a b, ins = .store a b
  · obtain ⟨a, b, rfl⟩ := hStore
    have h := crSpillStore_spec E p w a b hWide hFile hRegs hRead hLog hCount hOne
    have hC := h.2.2.1
    have hEq : (runBlock (crSpillPayload n base fail ok (.store a b)) E p).regs 12 = p.regs 12 + 1 := by
      simpa only [crSpillPayload, List.append_assoc] using hC
    exact hEq.le
  · rw [crRunBlock_reg_frame E 12 _ p
      (crPayload_noStore12 n base fail ok ins (fun a b he => hStore ⟨a, b, he⟩))]
    omega
theorem crCompiled_regular_simulation (P source : Program) (E : RAMEnv) (p src : RAMState)
    (w file memBase : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok))
    (j : Fin source.length) (hPc : p.pc = base + 16 * j.val) (hSrcPc : src.pc = j.val)
    (hNo : (source.get j).NoBranchI)
    (hClock : 0 < p.regs 14) (hClockWord : p.regs 14 < 2 ^ E.W)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w + 1 < E.W) (hMod : p.regs 13 = 2 ^ w) (hPtr : p.regs 8 = file)
    (hMemPtr : p.regs 9 = memBase) (hRead : memBase + 2 ^ w < 2 ^ E.W)
    (hDetRead : p.regs 10 + 2 ^ w < 2 ^ E.W)
    (hDet : ∀ q, q ≤ 2 ^ w → E.det (p.regs 10 + q) = det q)
    (hOne : p.regs 15 = 1)
    (hLog : p.regs 11 + p.regs 12 < 2 ^ E.W) (hCount : p.regs 12 + 1 < 2 ^ E.W)
    (hLogSeparate : memBase + 2 ^ (w + 1) < p.regs 11 + p.regs 12)
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 ∧ (step P E)^[k] p = out ∧
      CRView w file memBase (step source (detEnv w det) src) out ∧
      out.pc = crSpillTarget source.length base fail (src.pc + 1) ∧
      out.regs 14 = p.regs 14 - 1 ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ out.regs 12 ≤ p.regs 12 + 1 := by
  let body := crSpillPayload source.length base fail ok (source.get j)
  let g := crGuardState p
  have hG8 : g.regs 8 = p.regs 8 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (8 : Fin 16) ≠ 14)]
  have hG9 : g.regs 9 = p.regs 9 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (9 : Fin 16) ≠ 14)]
  have hG10 : g.regs 10 = p.regs 10 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (10 : Fin 16) ≠ 14)]
  have hG11 : g.regs 11 = p.regs 11 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (11 : Fin 16) ≠ 14)]
  have hG12 : g.regs 12 = p.regs 12 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (12 : Fin 16) ≠ 14)]
  have hG13 : g.regs 13 = p.regs 13 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (13 : Fin 16) ≠ 14)]
  have hG15 : g.regs 15 = p.regs 15 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (15 : Fin 16) ≠ 14)]
  have hVG : CRView w file memBase src g := crView_physical_mem hView rfl
  have hPayload := crSpillPayload_view (source.get j) E g src w file memBase det source.length base fail ok hNo
    hVG hSource hWide (hG13.trans hMod) (hG8.trans hPtr) (hG9.trans hMemPtr) hRead
    (by rw [hG10]; exact hDetRead) (by intro q hq; rw [hG10]; exact hDet q hq)
    (hG15.trans hOne) (by rw [hG11, hG12]; exact hLog) (by rw [hG12]; exact hCount)
    (by rw [hG11, hG12]; exact hLogSeparate) hFile hSeparate
  let out := {runBlock body E g with pc := crSpillTarget source.length base fail (j.val + 1)}
  refine ⟨body.length + 3, out, crCompiled_regular_cost source base fail ok j,
    crCompiled_regular_step P source E p base fail ok hAt j hPc hNo hClock hClockWord hOne, ?_, ?_, ?_, ?_, ?_⟩
  · have hFetch : source[src.pc]? = some (source.get j) := by
      rw [hSrcPc]
      exact List.getElem?_eq_getElem j.isLt
    rw [crStep_fetch source (detEnv w det) src _ hFetch]
    exact crView_physical_mem hPayload rfl
  · change crSpillTarget source.length base fail (j.val + 1) = _
    rw [hSrcPc]
  · change (runBlock body E g).regs 14 = p.regs 14 - 1
    rw [crRunBlock_reg_frame E 14 body g (crSpillPayload_clock_frame _ _ _ _ _)]
    simp only [g, crGuardState, Function.update_self]
  · intro r hr
    obtain ⟨h0, h1, h2, h3, h7, h12, h14⟩ := hr
    change (runBlock body E g).regs r = p.regs r
    rw [crRunBlock_reg_frame E r body g
      (crSpillPayload_noWrite r ⟨h0, h1, h2, h3, h12⟩ source.length base fail ok (source.get j))]
    simp only [g, crGuardState, Function.update_of_ne h14]
  · change (runBlock body E g).regs 12 ≤ p.regs 12 + 1
    have h := crSpillPayload_log_bound (source.get j) E g w source.length base fail ok (by omega)
      (by rw [hG8, hPtr]; exact hFile) (crView_file_bound hVG hSource (hG8.trans hPtr))
      (by rw [hG9, hMemPtr]; exact hRead) (hG15.trans hOne)
      (by rw [hG11, hG12]; exact hLog) (by rw [hG12]; exact hCount)
    simpa only [hG12] using h
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
theorem crCompiled_conditional_simulation (P source : Program) (E : RAMEnv) (p src : RAMState)
    (w file memBase : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length)
    (a : Fin 16) (target : ℕ) (hIns : source.get j = .jz a target)
    (hPc : p.pc = base + 16 * j.val) (hSrcPc : src.pc = j.val)
    (hClock : 0 < p.regs 14) (hClockWord : p.regs 14 < 2 ^ E.W)
    (hView : CRView w file memBase src p) (hSource : CRWordClosed w src)
    (hWide : w < E.W) (hPtr : p.regs 8 = file) (hOne : p.regs 15 = 1)
    (hFile : file + 16 ≤ 2 ^ E.W) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 7 ∧ (step P E)^[k] p = out ∧
      CRView w file memBase (step source (detEnv w det) src) out ∧
      out.pc = crSpillTarget source.length base fail (step source (detEnv w det) src).pc ∧
      out.regs 14 = p.regs 14 - 1 ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ out.regs 12 = p.regs 12 := by
  have hNot : source.get j ≠ .halt := by rw [hIns]; simp
  have hGuard := crCompiled_guard_positive P source E p base fail ok hAt j hPc hNot hClock hClockWord hOne
  let g := crGuardState p
  have hG8 : g.regs 8 = p.regs 8 := by simp only [g, crGuardState, Function.update_of_ne (by decide : (8 : Fin 16) ≠ 14)]
  have hGPc : g.pc = base + 16 * j.val + 2 := by change p.pc + 2 = _; rw [hPc]
  have hVG : CRView w file memBase src g := crView_physical_mem hView rfl
  have hRegs : ∀ r : Fin 16, g.mem (g.regs 8 + r.val) ≤ 2 ^ w := by
    intro r
    rw [hG8, hPtr]
    exact crView_regs_bound hVG hSource r
  have hTail : At P g.pc (crSpillLoad 0 a ++
      [.jz 0 (crSpillTarget source.length base fail target),
        .jmp (crSpillTarget source.length base fail (j.val + 1))]) := by
    have h := crCompiled_payload_at P source base fail ok hAt j hNot
    rw [hIns] at h
    simpa [crSpillPayload, List.append_assoc, hGPc] using h
  obtain ⟨k, hK, hRun⟩ := crExecute_conditional P E g w a
    (crSpillTarget source.length base fail target) (crSpillTarget source.length base fail (j.val + 1))
    hWide (by rw [hG8, hPtr]; exact hFile) hRegs hTail
  generalize hu : runBlock (crSpillLoad 0 a) E g = u at hRun
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : g.regs 8 + a.val < 2 ^ E.W := by rw [hG8, hPtr]; have h := a.isLt; omega
  have hU := crSpillLoad_spec E g 0 a (by decide) h16 hAddr
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hUfr⟩ := hU
  have hA : g.mem (g.regs 8 + a.val) = src.regs a := by rw [hG8, hPtr]; exact hVG.1 a
  rw [hA] at hRun
  have hFetch : source[src.pc]? = some (source.get j) := by rw [hSrcPc]; exact List.getElem?_eq_getElem j.isLt
  have hSrcStep : step source (detEnv w det) src =
      {src with pc := if src.regs a = 0 then target else src.pc + 1} := by
    rw [crStep_fetch source (detEnv w det) src _ hFetch, hIns]
    rfl
  let out := {u with pc := if src.regs a = 0 then crSpillTarget source.length base fail target else crSpillTarget source.length base fail (j.val + 1)}
  refine ⟨k + 2, out, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hGuard]
    exact hRun
  · rw [hSrcStep, crView_source_pc]
    exact crView_physical_mem hView hUmem
  · rw [hSrcStep]
    change (if src.regs a = 0 then _ else _) = crSpillTarget source.length base fail (if _ then _ else _)
    split_ifs
    · rfl
    · rw [hSrcPc]
  · change u.regs 14 = p.regs 14 - 1
    rw [hUfr 14 (by decide)]
    simp only [g, crGuardState, Function.update_self]
  · intro r hr
    obtain ⟨h0, h1, h2, h3, h7, h12, h14⟩ := hr
    change u.regs r = p.regs r
    rw [hUfr r h0]
    simp only [g, crGuardState, Function.update_of_ne h14]
  · change u.regs 12 = p.regs 12
    rw [hUfr 12 (by decide)]
    simp only [g, crGuardState, Function.update_of_ne (by decide : (12 : Fin 16) ≠ 14)]
theorem crCompiled_jump_simulation (P source : Program) (E : RAMEnv) (p src : RAMState)
    (w file memBase : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length)
    (target : ℕ) (hIns : source.get j = .jmp target)
    (hPc : p.pc = base + 16 * j.val) (hSrcPc : src.pc = j.val)
    (hClock : 0 < p.regs 14) (hClockWord : p.regs 14 < 2 ^ E.W)
    (hView : CRView w file memBase src p) (hOne : p.regs 15 = 1) :
    ∃ out : RAMState, (step P E)^[3] p = out ∧
      CRView w file memBase (step source (detEnv w det) src) out ∧
      out.pc = crSpillTarget source.length base fail (step source (detEnv w det) src).pc ∧
      out.regs 14 = p.regs 14 - 1 ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ out.regs 12 = p.regs 12 := by
  have hNot : source.get j ≠ .halt := by rw [hIns]; simp
  have hGuard := crCompiled_guard_positive P source E p base fail ok hAt j hPc hNot hClock hClockWord hOne
  let g := crGuardState p
  have hGPc : g.pc = base + 16 * j.val + 2 := by change p.pc + 2 = _; rw [hPc]
  have hTail := crCompiled_payload_at P source base fail ok hAt j hNot
  rw [hIns] at hTail
  have hPhysical : P[g.pc]? = some (.jmp (crSpillTarget source.length base fail target)) := by
    have h := hTail 0 (by simp [crSpillPayload])
    simpa [crSpillPayload, hGPc] using h
  have hFetch : source[src.pc]? = some (source.get j) := by rw [hSrcPc]; exact List.getElem?_eq_getElem j.isLt
  have hSrcStep : step source (detEnv w det) src = {src with pc := target} := by
    rw [crStep_fetch source (detEnv w det) src _ hFetch, hIns]
    rfl
  let out := {g with pc := crSpillTarget source.length base fail target}
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 3 = 1 + 2 by omega, Function.iterate_add_apply]
    change step P E ((step P E)^[2] p) = _
    rw [hGuard, crStep_fetch P E g _ hPhysical]
    rfl
  · rw [hSrcStep, crView_source_pc]
    exact crView_physical_mem hView rfl
  · rw [hSrcStep]
  · simp only [out, g, crGuardState, Function.update_self]
  · intro r hr
    obtain ⟨h0, h1, h2, h3, h7, h12, h14⟩ := hr
    simp only [out, g, crGuardState, Function.update_of_ne h14]
  · simp only [out, g, crGuardState, Function.update_of_ne (by decide : (12 : Fin 16) ≠ 14)]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
structure CRSimLayout (E : RAMEnv) (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) : Prop where
  wide : w + 1 < E.W
  file_before : file + 16 ≤ memBase
  mem_before_log : memBase + 2 ^ (w + 1) < logBase
  log_word : logBase + limit + 1 < 2 ^ E.W
  det_word : detBase + 2 ^ w < 2 ^ E.W
  table : ∀ q, q ≤ 2 ^ w → E.det (detBase + q) = det q
structure CRSimState (w file memBase detBase logBase limit : ℕ) (src p : RAMState) : Prop where
  view : CRView w file memBase src p
  closed : CRWordClosed w src
  file_ptr : p.regs 8 = file
  mem_ptr : p.regs 9 = memBase
  det_ptr : p.regs 10 = detBase
  log_ptr : p.regs 11 = logBase
  modulus : p.regs 13 = 2 ^ w
  one : p.regs 15 = 1
  room : p.regs 12 + p.regs 14 ≤ limit
theorem crSim_clock_word {E : RAMEnv} {w file memBase detBase logBase limit : ℕ}
    {det : ℕ → ℕ} {src p : RAMState}
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p) : p.regs 14 < 2 ^ E.W := by
  have hTop := hL.log_word
  have hRoom := hS.room
  omega
theorem crSimulation_step (P source : Program) (E : RAMEnv) (src p : RAMState)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length)
    (hPc : p.pc = base + 16 * j.val) (hSrcPc : src.pc = j.val)
    (hNot : source.get j ≠ .halt) (hClock : 0 < p.regs 14) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 ∧ (step P E)^[k] p = out ∧
      CRSimState w file memBase detBase logBase limit (step source (detEnv w det) src) out ∧
      out.pc = crSpillTarget source.length base fail (step source (detEnv w det) src).pc ∧
      out.regs 14 = p.regs 14 - 1 ∧ (∀ r, CRSpillStable r → out.regs r = p.regs r) := by
  have hWord := crSim_clock_word hL hS
  have hLogTop : logBase < 2 ^ E.W := by have h := hL.log_word; omega
  have hMemLog : memBase + 2 ^ w < logBase :=
    (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) memBase).trans_lt hL.mem_before_log
  have hRead : memBase + 2 ^ w < 2 ^ E.W := hMemLog.trans hLogTop
  have hFile : file + 16 ≤ 2 ^ E.W := hL.file_before.trans ((Nat.le_add_right memBase (2 ^ w)).trans hRead.le)
  have hDetRead : p.regs 10 + 2 ^ w < 2 ^ E.W := by rw [hS.det_ptr]; exact hL.det_word
  have hDet : ∀ q, q ≤ 2 ^ w → E.det (p.regs 10 + q) = det q := by
    intro q hq
    rw [hS.det_ptr]
    exact hL.table q hq
  have hLog : p.regs 11 + p.regs 12 < 2 ^ E.W := by
    rw [hS.log_ptr]
    have hTop := hL.log_word
    have hRoom := hS.room
    omega
  have hCount : p.regs 12 + 1 < 2 ^ E.W := by
    have hTop := hL.log_word
    have hRoom := hS.room
    omega
  have hLogSeparate : memBase + 2 ^ (w + 1) < p.regs 11 + p.regs 12 := by
    rw [hS.log_ptr]
    exact hL.mem_before_log.trans_le (Nat.le_add_right logBase _)
  have hRaw : ∃ (k : ℕ) (out : RAMState), k ≤ 16 ∧ (step P E)^[k] p = out ∧
      CRView w file memBase (step source (detEnv w det) src) out ∧
      out.pc = crSpillTarget source.length base fail (step source (detEnv w det) src).pc ∧
      out.regs 14 = p.regs 14 - 1 ∧ (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧
      out.regs 12 ≤ p.regs 12 + 1 := by
    rcases crInstr_cases (source.get j) with hNo | hHalt | ⟨a, target, hJz⟩ | ⟨target, hJmp⟩
    · obtain ⟨k, out, hK, hRun, hV, hPC, hC, hFrame, hLogBound⟩ := crCompiled_regular_simulation
        P source E p src w file memBase det base fail ok hAt j hPc hSrcPc hNo hClock hWord
        hS.view hS.closed hL.wide hS.modulus hS.file_ptr hS.mem_ptr hRead hDetRead hDet hS.one
        hLog hCount hLogSeparate hFile hL.file_before
      refine ⟨k, out, hK, hRun, hV, ?_, hC, hFrame, hLogBound⟩
      have hFetch : source[src.pc]? = some (source.get j) := by rw [hSrcPc]; exact List.getElem?_eq_getElem j.isLt
      have hPostPc : (step source (detEnv w det) src).pc = src.pc + 1 := by
        rw [crStep_fetch source (detEnv w det) src _ hFetch]
        exact execInstr_pc _ _ _ hNo
      rw [hPostPc]
      exact hPC
    · exact (hNot hHalt).elim
    · obtain ⟨k, out, hK, hRun, hV, hPC, hC, hFrame, hLogEq⟩ := crCompiled_conditional_simulation
        P source E p src w file memBase det base fail ok hAt j a target hJz hPc hSrcPc
        hClock hWord hS.view hS.closed (by have h := hL.wide; omega) hS.file_ptr hS.one hFile
      exact ⟨k, out, hK.trans (by decide : 7 ≤ 16), hRun, hV, hPC, hC, hFrame,
        hLogEq.le.trans (Nat.le_succ _)⟩
    · obtain ⟨out, hRun, hV, hPC, hC, hFrame, hLogEq⟩ := crCompiled_jump_simulation
        P source E p src w file memBase det base fail ok hAt j target hJmp hPc hSrcPc
        hClock hWord hS.view hS.one
      exact ⟨3, out, by decide, hRun, hV, hPC, hC, hFrame, hLogEq.le.trans (Nat.le_succ _)⟩
  obtain ⟨k, out, hK, hRun, hV, hPC, hC, hFrame, hLogBound⟩ := hRaw
  refine ⟨k, out, hK, hRun, ?_, hPC, hC, hFrame⟩
  refine ⟨hV, crWordClosed_step source (detEnv w det) src hS.closed,
    (hFrame 8 (by unfold CRSpillStable; decide)).trans hS.file_ptr,
    (hFrame 9 (by unfold CRSpillStable; decide)).trans hS.mem_ptr,
    (hFrame 10 (by unfold CRSpillStable; decide)).trans hS.det_ptr,
    (hFrame 11 (by unfold CRSpillStable; decide)).trans hS.log_ptr,
    (hFrame 13 (by unfold CRSpillStable; decide)).trans hS.modulus,
    (hFrame 15 (by unfold CRSpillStable; decide)).trans hS.one, ?_⟩
  have hRoom := hS.room
  omega
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def CRHaltsBy (P : Program) (E : RAMEnv) (B : ℕ) (src : RAMState) : Prop :=
  ∃ k : ℕ, k ≤ B ∧ Halted P ((step P E)^[k] src)
theorem crHalted_fetch_iff (P : Program) (s : RAMState) :
    Halted P s ↔ P[s.pc]? = some .halt := by
  unfold Halted
  cases h : P[s.pc]? with
  | none => simp
  | some i => cases i <;> simp
theorem crSource_stays (P : Program) (E : RAMEnv) (src : RAMState)
    (h : Halted P src) : ∀ k : ℕ, (step P E)^[k] src = src := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show k + 1 = 1 + k by omega, Function.iterate_add_apply]
    change step P E ((step P E)^[k] src) = src
    rw [ih, crStep_halted P E src h]
theorem crHaltsBy_pc (P : Program) (E : RAMEnv) (B : ℕ) (src : RAMState)
    (h : CRHaltsBy P E B src) : src.pc < P.length := by
  by_contra hc
  have hNone : P[src.pc]? = none := List.getElem?_eq_none_iff.mpr (by omega)
  have hStep : step P E src = src := by simp only [step, hNone]
  have hStay : ∀ k : ℕ, (step P E)^[k] src = src := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show k + 1 = 1 + k by omega, Function.iterate_add_apply]
      change step P E ((step P E)^[k] src) = src
      rw [ih, hStep]
  obtain ⟨k, hk, hHalt⟩ := h
  rw [hStay k] at hHalt
  have hFetch := (crHalted_fetch_iff P src).mp hHalt
  rw [hNone] at hFetch
  contradiction
theorem crHaltsBy_step (P : Program) (E : RAMEnv) (B : ℕ) (src : RAMState)
    (h : CRHaltsBy P E (B + 1) src) (hNo : ¬ Halted P src) :
    CRHaltsBy P E B (step P E src) := by
  obtain ⟨k, hk, hHalt⟩ := h
  cases k with
  | zero => exact (hNo hHalt).elim
  | succ k =>
    refine ⟨k, by omega, ?_⟩
    simpa only [iterate_succ_apply_front] using hHalt
theorem crHaltsBy_of_within (P : Program) (E : RAMEnv) (T : ℝ) (B : ℕ) (src out : RAMState)
    (h : HaltsWithin P E T src out) (hB : T ≤ (B : ℝ)) : CRHaltsBy P E B src := by
  obtain ⟨k, hk, hRun, hHalt⟩ := h
  refine ⟨k, by exact_mod_cast hk.trans hB, ?_⟩
  rw [hRun]
  exact hHalt
theorem crSimState_physical_pc {w file memBase detBase logBase limit pc : ℕ} {src p : RAMState}
    (hS : CRSimState w file memBase detBase logBase limit src p) :
    CRSimState w file memBase detBase logBase limit src {p with pc := pc} := by
  exact ⟨crView_physical_mem hS.view rfl, hS.closed, hS.file_ptr, hS.mem_ptr, hS.det_ptr,
    hS.log_ptr, hS.modulus, hS.one, hS.room⟩
theorem crSimulation_halted (P source : Program) (E : RAMEnv) (src p : RAMState)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok B : ℕ)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hPc : p.pc = crSpillTarget source.length base fail src.pc) (hHalt : Halted source src) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] p = out ∧ out.pc = ok ∧
      CRSimState w file memBase detBase logBase limit ((step source (detEnv w det))^[B] src) out ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) := by
  have hValid : src.pc < source.length := crHaltsBy_pc source (detEnv w det) 0 src ⟨0, le_rfl, hHalt⟩
  let j : Fin source.length := ⟨src.pc, hValid⟩
  have hSrcFetch : source[src.pc]? = some (source.get j) := List.getElem?_eq_getElem hValid
  have hIns : source.get j = .halt :=
    Option.some.inj (hSrcFetch.symm.trans ((crHalted_fetch_iff source src).mp hHalt))
  have hPc' : p.pc = base + 16 * j.val := by simpa only [crSpillTarget, if_pos hValid] using hPc
  refine ⟨1, {p with pc := ok}, by omega,
    crExecute_halt_prefix P source E base fail ok j p hAt hPc' hIns, rfl, ?_, ?_⟩
  · rw [crSource_stays source (detEnv w det) src hHalt B]
    exact crSimState_physical_pc hS
  · intro r hr
    rfl
theorem crSimulation_halts (P source : Program) (E : RAMEnv)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hAt : At P base (crSpillCompile source base fail ok)) :
    ∀ (B : ℕ) (src p : RAMState), CRSimState w file memBase detBase logBase limit src p →
      p.regs 14 = B → p.pc = crSpillTarget source.length base fail src.pc →
      CRHaltsBy source (detEnv w det) B src →
      ∃ (k : ℕ) (out : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] p = out ∧ out.pc = ok ∧
        CRSimState w file memBase detBase logBase limit ((step source (detEnv w det))^[B] src) out ∧
        (∀ r, CRSpillStable r → out.regs r = p.regs r) := by
  intro B
  induction B with
  | zero =>
    intro src p hS hBudget hPc hTime
    obtain ⟨k, hk, hHalt⟩ := hTime
    have hk0 : k = 0 := by omega
    subst k
    exact crSimulation_halted P source E src p w file memBase detBase logBase limit det base fail ok 0 hS hAt hPc hHalt
  | succ B ih =>
    intro src p hS hBudget hPc hTime
    by_cases hHalt : Halted source src
    · exact crSimulation_halted P source E src p w file memBase detBase logBase limit det base fail ok (B + 1) hS hAt hPc hHalt
    · have hValid := crHaltsBy_pc source (detEnv w det) (B + 1) src hTime
      let j : Fin source.length := ⟨src.pc, hValid⟩
      have hSrcFetch : source[src.pc]? = some (source.get j) := List.getElem?_eq_getElem hValid
      have hNot : source.get j ≠ .halt := by
        intro he
        apply hHalt
        apply (crHalted_fetch_iff source src).mpr
        rw [hSrcFetch, he]
      have hPc' : p.pc = base + 16 * j.val := by simpa only [crSpillTarget, if_pos hValid] using hPc
      obtain ⟨k, mid, hCost, hRun, hMid, hMidPc, hClock, hFrame⟩ := crSimulation_step
        P source E src p w file memBase detBase logBase limit det base fail ok hL hS hAt j hPc' rfl hNot (by omega)
      have hBudget' : mid.regs 14 = B := by omega
      have hTime' := crHaltsBy_step source (detEnv w det) B src hTime hHalt
      obtain ⟨k', out, hCost', hRun', hOk, hFinal, hFrame'⟩ := ih (step source (detEnv w det) src) mid
        hMid hBudget' hMidPc hTime'
      refine ⟨k' + k, out, by omega, ?_, hOk, ?_, ?_⟩
      · rw [Function.iterate_add_apply, hRun, hRun']
      · rw [iterate_succ_apply_front]
        exact hFinal
      · intro r hr
        exact (hFrame' r hr).trans (hFrame r hr)
theorem crSimulation_of_within (P source : Program) (E : RAMEnv) (src sourceOut p : RAMState)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok B : ℕ) (T : ℝ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hBudget : p.regs 14 = B) (hPc : p.pc = crSpillTarget source.length base fail src.pc)
    (hSource : HaltsWithin source (detEnv w det) T src sourceOut) (hTime : T ≤ (B : ℝ)) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] p = out ∧ out.pc = ok ∧
      CRSimState w file memBase detBase logBase limit sourceOut out ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) := by
  obtain ⟨k, out, hK, hRun, hOk, hState, hFrame⟩ := crSimulation_halts P source E
    w file memBase detBase logBase limit det base fail ok hL hAt B src p hS hBudget hPc
    (crHaltsBy_of_within source (detEnv w det) T B src sourceOut hSource hTime)
  rw [crClock_result_of_halts source (detEnv w det) src sourceOut T B hSource hTime] at hState
  exact ⟨k, out, hK, hRun, hOk, hState, hFrame⟩
end LinearSetReconciliation327.Main
end

#print axioms LinearSetReconciliation327.Main.crSimulation_step


