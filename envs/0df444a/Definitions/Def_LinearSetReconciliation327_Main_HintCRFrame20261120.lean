-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCRFrame20261120
-- name    : LinearSetReconciliation327_Main_HintCRFrame20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:29:53.175747+00:00
-- url     : https://prove2.me/theorems/0dde44d0-2d8f-4cb3-8456-81dfff4141fe
-- title:
--   LinearSetReconciliation327 — HintCRFrame (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCRFrame20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRCall20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def CRMemFrame (lo hi : ℕ) (before after : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < lo ∨ hi ≤ addr) → after addr = before addr

theorem crMemFrame_refl (lo hi : ℕ) (m : ℕ → ℕ) : CRMemFrame lo hi m m := by
  intro addr _
  rfl

theorem crMemFrame_trans {lo hi : ℕ} {a b c : ℕ → ℕ}
    (hAB : CRMemFrame lo hi a b) (hBC : CRMemFrame lo hi b c) : CRMemFrame lo hi a c := by
  intro addr hOutside
  exact (hBC addr hOutside).trans (hAB addr hOutside)

theorem crMemFrame_update (lo hi pos value : ℕ) (m : ℕ → ℕ)
    (hLo : lo ≤ pos) (hHi : pos < hi) : CRMemFrame lo hi m (Function.update m pos value) := by
  intro addr hOutside
  exact Function.update_of_ne (by omega : addr ≠ pos) _ _

theorem crSpillPayload_mem_frame (ins : Instr) (E : RAMEnv) (p src : RAMState)
    (w file memBase detBase logBase limit n base fail ok : ℕ) (det : ℕ → ℕ)
    (hNo : ins.NoBranchI)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p) :
    CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillPayload n base fail ok ins) E p).mem := by
  have hWide : w < E.W := by have h := hL.wide; omega
  have hPow : 2 ^ w ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hRoom := hS.room
  have hTop := hL.log_word
  have hBefore := hL.mem_before_log
  have hSeparate := hL.file_before
  have hFile : p.regs 8 + 16 ≤ 2 ^ E.W := by rw [hS.file_ptr]; omega
  have hRegs := crView_file_bound hS.view hS.closed hS.file_ptr
  have hRead : p.regs 9 + 2 ^ w < 2 ^ E.W := by rw [hS.mem_ptr]; omega
  have hDetRead : p.regs 10 + 2 ^ w < 2 ^ E.W := by rw [hS.det_ptr]; exact hL.det_word
  have hLog : p.regs 11 + p.regs 12 < 2 ^ E.W := by rw [hS.log_ptr]; omega
  have hCount : p.regs 12 + 1 < 2 ^ E.W := by omega
  have hRF : ∀ (dst : Fin 16) value, CRMemFrame file (logBase + limit + 1) p.mem
      (Function.update p.mem (p.regs 8 + dst.val) value) := by
    intro dst value
    apply crMemFrame_update
    · rw [hS.file_ptr]; omega
    · rw [hS.file_ptr]; have h := dst.isLt; omega
  cases ins with
  | imm d v =>
      simpa only [crSpillPayload, (crSpillImm_spec E p w v d hWide.le hS.modulus hFile).2.1] using hRF d (v % 2 ^ w)
  | add d a b =>
      have h := (crSpillBin_spec .add E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.add d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .add (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | mul d a b =>
      have h := (crSpillBin_spec .mul E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.mul d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .mul (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | div d a b =>
      have h := (crSpillBin_spec .div E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.div d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .div (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | mod d a b =>
      have h := (crSpillBin_spec .mod E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.mod d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .mod (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | band d a b =>
      have h := (crSpillBin_spec .band E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.band d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .band (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | bor d a b =>
      have h := (crSpillBin_spec .bor E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.bor d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .bor (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | bxor d a b =>
      have h := (crSpillBin_spec .bxor E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.bxor d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .bxor (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | shl d a b =>
      have h := (crSpillBin_spec .shl E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.shl d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .shl (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | shr d a b =>
      have h := (crSpillBin_spec .shr E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.shr d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .shr (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | lt d a b =>
      have h := (crSpillBin_spec .lt E p w d a b hWide hS.modulus hFile hRegs).2.1
      simp only [CRBinKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillBin Instr.lt d a b) E p).mem
      rw [h]
      exact hRF d (CRBinKind.val .lt (p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | sub d a b =>
      have h := (crSpillSub_spec E p w d a b hL.wide hS.modulus hFile hRegs).2.1
      simpa only [crSpillPayload, h] using
        hRF d ((p.mem (p.regs 8 + a.val) + 2 ^ w - p.mem (p.regs 8 + b.val)) % 2 ^ w)
  | load d a =>
      have h := (crSpillRead_spec .memory E p w d a 9 (by decide) hWide hS.modulus hFile hRegs hRead).2.1
      simp only [CRReadKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillLoad 0 a ++ [.add 0 9 0, .load 0 0, .mod 0 0 13] ++ crSpillWrite d 0) E p).mem
      rw [h]
      exact hRF d (CRReadKind.value .memory E p.mem (p.regs 9 + p.mem (p.regs 8 + a.val)) % 2 ^ w)
  | qDet d a =>
      have h := (crSpillRead_spec .deterministic E p w d a 10 (by decide) hWide hS.modulus hFile hRegs hDetRead).2.1
      simp only [CRReadKind.ins] at h
      change CRMemFrame file (logBase + limit + 1) p.mem (runBlock (crSpillLoad 0 a ++ [.add 0 10 0, .qDet 0 0, .mod 0 0 13] ++ crSpillWrite d 0) E p).mem
      rw [h]
      exact hRF d (CRReadKind.value .deterministic E p.mem (p.regs 10 + p.mem (p.regs 8 + a.val)) % 2 ^ w)
  | store a b =>
      have h := (crSpillStore_spec E p w a b hWide hFile hRegs hRead hLog hCount hS.one).2.1
      have hFirst := crMemFrame_update file (logBase + limit + 1)
        (p.regs 9 + p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)) p.mem
        (by rw [hS.mem_ptr]; omega) (by rw [hS.mem_ptr]; have hh := hRegs a; omega)
      have hSecond := crMemFrame_update file (logBase + limit + 1)
        (p.regs 11 + p.regs 12) (p.regs 9 + p.mem (p.regs 8 + a.val))
        (Function.update p.mem (p.regs 9 + p.mem (p.regs 8 + a.val)) (p.mem (p.regs 8 + b.val)))
        (by rw [hS.log_ptr]; omega) (by rw [hS.log_ptr]; omega)
      simp only [List.append_assoc] at h
      simp only [crSpillPayload, List.append_assoc]
      rw [h]
      exact crMemFrame_trans hFirst hSecond
  | qPerm d k a =>
      simpa only [crSpillPayload, (crSpillZero_spec E p d hFile).2.1] using hRF d 0
  | qPermInv d k a =>
      simpa only [crSpillPayload, (crSpillZero_spec E p d hFile).2.1] using hRF d 0
  | qCoeff d k a =>
      simpa only [crSpillPayload, (crSpillZero_spec E p d hFile).2.1] using hRF d 0
  | jz a t => exact (hNo.2.1 a t rfl).elim
  | jmp t => exact (hNo.1 t rfl).elim
  | halt => exact (hNo.2.2 rfl).elim

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem crSimState_guard {w file memBase detBase logBase limit : ℕ} {src p : RAMState}
    (hS : CRSimState w file memBase detBase logBase limit src p) :
    CRSimState w file memBase detBase logBase limit src (crGuardState p) := by
  refine ⟨crView_physical_mem hS.view rfl, hS.closed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [crGuardState, Function.update_of_ne (by decide : (8 : Fin 16) ≠ 14)] using hS.file_ptr
  · simpa only [crGuardState, Function.update_of_ne (by decide : (9 : Fin 16) ≠ 14)] using hS.mem_ptr
  · simpa only [crGuardState, Function.update_of_ne (by decide : (10 : Fin 16) ≠ 14)] using hS.det_ptr
  · simpa only [crGuardState, Function.update_of_ne (by decide : (11 : Fin 16) ≠ 14)] using hS.log_ptr
  · simpa only [crGuardState, Function.update_of_ne (by decide : (13 : Fin 16) ≠ 14)] using hS.modulus
  · simpa only [crGuardState, Function.update_of_ne (by decide : (15 : Fin 16) ≠ 14)] using hS.one
  · change Function.update p.regs 14 (p.regs 14 - 1) 12 + Function.update p.regs 14 (p.regs 14 - 1) 14 ≤ limit
    simp only [Function.update_of_ne (by decide : (12 : Fin 16) ≠ 14), Function.update_self]
    have hRoom := hS.room
    omega

theorem crCompiled_regular_simulation_frame (P source : Program) (E : RAMEnv) (p src : RAMState)
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
    (hFile : file + 16 ≤ 2 ^ E.W) (hSeparate : file + 16 ≤ memBase)
    (detBase logBase limit : ℕ) (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 ∧ (step P E)^[k] p = out ∧
      CRView w file memBase (step source (detEnv w det) src) out ∧
      out.pc = crSpillTarget source.length base fail (src.pc + 1) ∧
      out.regs 14 = p.regs 14 - 1 ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ out.regs 12 ≤ p.regs 12 + 1 ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem := by
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
    crCompiled_regular_step P source E p base fail ok hAt j hPc hNo hClock hClockWord hOne, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · change CRMemFrame file (logBase + limit + 1) p.mem (runBlock body E g).mem
    exact crSpillPayload_mem_frame (source.get j) E g src w file memBase detBase logBase limit
      source.length base fail ok det hNo hL (crSimState_guard hS)

theorem crCompiled_conditional_simulation_frame (P source : Program) (E : RAMEnv) (p src : RAMState)
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
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ out.regs 12 = p.regs 12 ∧ out.mem = p.mem := by
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
  refine ⟨k + 2, out, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact hUmem

theorem crCompiled_jump_simulation_frame (P source : Program) (E : RAMEnv) (p src : RAMState)
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
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ out.regs 12 = p.regs 12 ∧ out.mem = p.mem := by
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
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
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

theorem crSimulation_step_frame (P source : Program) (E : RAMEnv) (src p : RAMState)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok)) (j : Fin source.length)
    (hPc : p.pc = base + 16 * j.val) (hSrcPc : src.pc = j.val)
    (hNot : source.get j ≠ .halt) (hClock : 0 < p.regs 14) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 ∧ (step P E)^[k] p = out ∧
      CRSimState w file memBase detBase logBase limit (step source (detEnv w det) src) out ∧
      out.pc = crSpillTarget source.length base fail (step source (detEnv w det) src).pc ∧
      out.regs 14 = p.regs 14 - 1 ∧ (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem := by
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
      out.regs 12 ≤ p.regs 12 + 1 ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem := by
    rcases crInstr_cases (source.get j) with hNo | hHalt | ⟨a, target, hJz⟩ | ⟨target, hJmp⟩
    · obtain ⟨k, out, hK, hRun, hV, hPC, hC, hFrame, hLogBound, hMemFrame⟩ := crCompiled_regular_simulation_frame
        P source E p src w file memBase det base fail ok hAt j hPc hSrcPc hNo hClock hWord
        hS.view hS.closed hL.wide hS.modulus hS.file_ptr hS.mem_ptr hRead hDetRead hDet hS.one
        hLog hCount hLogSeparate hFile hL.file_before detBase logBase limit hL hS
      refine ⟨k, out, hK, hRun, hV, ?_, hC, hFrame, hLogBound, hMemFrame⟩
      have hFetch : source[src.pc]? = some (source.get j) := by rw [hSrcPc]; exact List.getElem?_eq_getElem j.isLt
      have hPostPc : (step source (detEnv w det) src).pc = src.pc + 1 := by
        rw [crStep_fetch source (detEnv w det) src _ hFetch]
        exact execInstr_pc _ _ _ hNo
      rw [hPostPc]
      exact hPC
    · exact (hNot hHalt).elim
    · obtain ⟨k, out, hK, hRun, hV, hPC, hC, hFrame, hLogEq, hMemEq⟩ := crCompiled_conditional_simulation_frame
        P source E p src w file memBase det base fail ok hAt j a target hJz hPc hSrcPc
        hClock hWord hS.view hS.closed (by have h := hL.wide; omega) hS.file_ptr hS.one hFile
      exact ⟨k, out, hK.trans (by decide : 7 ≤ 16), hRun, hV, hPC, hC, hFrame,
        hLogEq.le.trans (Nat.le_succ _), by rw [hMemEq]; exact crMemFrame_refl _ _ _⟩
    · obtain ⟨out, hRun, hV, hPC, hC, hFrame, hLogEq, hMemEq⟩ := crCompiled_jump_simulation_frame
        P source E p src w file memBase det base fail ok hAt j target hJmp hPc hSrcPc
        hClock hWord hS.view hS.one
      exact ⟨3, out, by decide, hRun, hV, hPC, hC, hFrame, hLogEq.le.trans (Nat.le_succ _), by rw [hMemEq]; exact crMemFrame_refl _ _ _⟩
  obtain ⟨k, out, hK, hRun, hV, hPC, hC, hFrame, hLogBound, hMemFrame⟩ := hRaw
  refine ⟨k, out, hK, hRun, ?_, hPC, hC, hFrame, hMemFrame⟩
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
namespace LinearSetReconciliation327.Main
theorem crSimulation_halted_frame (P source : Program) (E : RAMEnv) (src p : RAMState)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok B : ℕ)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hPc : p.pc = crSpillTarget source.length base fail src.pc) (hHalt : Halted source src) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] p = out ∧ out.pc = ok ∧
      CRSimState w file memBase detBase logBase limit ((step source (detEnv w det))^[B] src) out ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem := by
  have hValid : src.pc < source.length := crHaltsBy_pc source (detEnv w det) 0 src ⟨0, le_rfl, hHalt⟩
  let j : Fin source.length := ⟨src.pc, hValid⟩
  have hSrcFetch : source[src.pc]? = some (source.get j) := List.getElem?_eq_getElem hValid
  have hIns : source.get j = .halt :=
    Option.some.inj (hSrcFetch.symm.trans ((crHalted_fetch_iff source src).mp hHalt))
  have hPc' : p.pc = base + 16 * j.val := by simpa only [crSpillTarget, if_pos hValid] using hPc
  refine ⟨1, {p with pc := ok}, by omega,
    crExecute_halt_prefix P source E base fail ok j p hAt hPc' hIns, rfl, ?_, ?_, crMemFrame_refl _ _ _⟩
  · rw [crSource_stays source (detEnv w det) src hHalt B]
    exact crSimState_physical_pc hS
  · intro r hr
    rfl

theorem crSimulation_halts_frame (P source : Program) (E : RAMEnv)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hAt : At P base (crSpillCompile source base fail ok)) :
    ∀ (B : ℕ) (src p : RAMState), CRSimState w file memBase detBase logBase limit src p →
      p.regs 14 = B → p.pc = crSpillTarget source.length base fail src.pc →
      CRHaltsBy source (detEnv w det) B src →
      ∃ (k : ℕ) (out : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] p = out ∧ out.pc = ok ∧
        CRSimState w file memBase detBase logBase limit ((step source (detEnv w det))^[B] src) out ∧
        (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem := by
  intro B
  induction B with
  | zero =>
    intro src p hS hBudget hPc hTime
    obtain ⟨k, hk, hHalt⟩ := hTime
    have hk0 : k = 0 := by omega
    subst k
    exact crSimulation_halted_frame P source E src p w file memBase detBase logBase limit det base fail ok 0 hS hAt hPc hHalt
  | succ B ih =>
    intro src p hS hBudget hPc hTime
    by_cases hHalt : Halted source src
    · exact crSimulation_halted_frame P source E src p w file memBase detBase logBase limit det base fail ok (B + 1) hS hAt hPc hHalt
    · have hValid := crHaltsBy_pc source (detEnv w det) (B + 1) src hTime
      let j : Fin source.length := ⟨src.pc, hValid⟩
      have hSrcFetch : source[src.pc]? = some (source.get j) := List.getElem?_eq_getElem hValid
      have hNot : source.get j ≠ .halt := by
        intro he
        apply hHalt
        apply (crHalted_fetch_iff source src).mpr
        rw [hSrcFetch, he]
      have hPc' : p.pc = base + 16 * j.val := by simpa only [crSpillTarget, if_pos hValid] using hPc
      obtain ⟨k, mid, hCost, hRun, hMid, hMidPc, hClock, hFrame, hMemory⟩ := crSimulation_step_frame
        P source E src p w file memBase detBase logBase limit det base fail ok hL hS hAt j hPc' rfl hNot (by omega)
      have hBudget' : mid.regs 14 = B := by omega
      have hTime' := crHaltsBy_step source (detEnv w det) B src hTime hHalt
      obtain ⟨k', out, hCost', hRun', hOk, hFinal, hFrame', hMemory'⟩ := ih (step source (detEnv w det) src) mid
        hMid hBudget' hMidPc hTime'
      refine ⟨k' + k, out, by omega, ?_, hOk, ?_, ?_, crMemFrame_trans hMemory hMemory'⟩
      · rw [Function.iterate_add_apply, hRun, hRun']
      · rw [iterate_succ_apply_front]
        exact hFinal
      · intro r hr
        exact (hFrame' r hr).trans (hFrame r hr)

theorem crSimulation_of_within_frame (P source : Program) (E : RAMEnv) (src sourceOut p : RAMState)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok B : ℕ) (T : ℝ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hBudget : p.regs 14 = B) (hPc : p.pc = crSpillTarget source.length base fail src.pc)
    (hSource : HaltsWithin source (detEnv w det) T src sourceOut) (hTime : T ≤ (B : ℝ)) :
    ∃ (k : ℕ) (out : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] p = out ∧ out.pc = ok ∧
      CRSimState w file memBase detBase logBase limit sourceOut out ∧
      (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem := by
  obtain ⟨k, out, hK, hRun, hOk, hState, hFrame, hMemory⟩ := crSimulation_halts_frame P source E
    w file memBase detBase logBase limit det base fail ok hL hAt B src p hS hBudget hPc
    (crHaltsBy_of_within source (detEnv w det) T B src sourceOut hSource hTime)
  rw [crClock_result_of_halts source (detEnv w det) src sourceOut T B hSource hTime] at hState
  exact ⟨k, out, hK, hRun, hOk, hState, hFrame, hMemory⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
theorem crSimulation_returns_frame (P source : Program) (E : RAMEnv) (src sourceOut p : RAMState)
    (w file memBase detBase logBase limit N : ℕ) (det : ℕ → ℕ) (base fail ok B : ℕ) (T : ℝ)
    (x : Fin N → ZMod 2)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hOutputAt : At P ok crOutputPrepare)
    (hBudget : p.regs 14 = B) (hPc : p.pc = crSpillTarget source.length base fail src.pc)
    (hSource : HaltsWithin source (detEnv w det) T src sourceOut) (hTime : T ≤ (B : ℝ))
    (hOutput : OutputsSupport sourceOut x) :
    Sem P E (crSpillTarget source.length base fail src.pc) (ok + 7) p
      (fun k out => k ≤ 16 * B + 8 ∧ OutputsSupport out x ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem) := by
  obtain ⟨k, mid, hK, hRun, hOk, hState, hFrame, hMemory⟩ := crSimulation_of_within_frame P source E src sourceOut p
    w file memBase detBase logBase limit det base fail ok B T hL hS hAt hBudget hPc hSource hTime
  have hLogTop : logBase < 2 ^ E.W := by have h := hL.log_word; omega
  have hMemLog : memBase + 2 ^ w < logBase :=
    (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) memBase).trans_lt hL.mem_before_log
  have hRead : memBase + 2 ^ w < 2 ^ E.W := hMemLog.trans hLogTop
  have hFile : file + 16 ≤ 2 ^ E.W := hL.file_before.trans ((Nat.le_add_right memBase (2 ^ w)).trans hRead.le)
  have hWide : w < E.W := by have h := hL.wide; omega
  have hNo : NoBranch crOutputPrepare := by simp [crOutputPrepare, crSpillLoad, NoBranch, Instr.NoBranchI]
  have hAtMid : At P mid.pc crOutputPrepare := by rw [hOk]; exact hOutputAt
  generalize hPrep : runBlock crOutputPrepare E mid = out
  have hExec : (step P E)^[7] mid = out := by
    have h := iterate_runBlock_of_at P E crOutputPrepare mid hAtMid hNo
    rw [hPrep] at h
    simpa only [crOutputPrepare_length] using h
  have hSpec := crOutputPrepare_spec E mid sourceOut w file memBase hState.view hState.closed
    hWide hState.file_ptr hState.mem_ptr hFile hRead
  rw [hPrep] at hSpec
  obtain ⟨hOutPc, hOutMem, h0, h1, hOutFrame⟩ := hSpec
  have hSupport := crOutputPrepare_support E mid sourceOut w file memBase N x hState.view hState.closed
    hWide hState.file_ptr hState.mem_ptr hFile hRead hOutput
  rw [hPrep] at hSupport
  have hEndPc : out.pc = ok + 7 := by rw [hOutPc, hOk]
  refine ⟨hPc, 7 + k, out, ?_, hEndPc, by omega, hSupport, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hRun, hExec]
  · exact (hOutFrame 6 (by decide) (by decide)).trans (hFrame 6 (by unfold CRSpillStable; decide))
  · rw [hOutMem]
    exact hMemory

theorem crSource_native_returns_frame (S : CRSourceBundle) (P : Program) (E : RAMEnv)
    (N t file memBase detBase logBase limit base fail ok : ℕ) (p : RAMState)
    (x : Fin N → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase limit (S.data N t).det)
    (hS : CRSimState (S.data N t).W file memBase detBase logBase limit
      (decoderStart (S.data N t).W ((S.data N t).H x) []) p)
    (hAt : At P base (crSpillCompile S.progDec base fail ok))
    (hOutputAt : At P ok crOutputPrepare)
    (hBudget : p.regs 14 = crSourceSteps S N t)
    (hPc : p.pc = base) :
    Sem P E base (ok + 7) p
      (fun k out => k ≤ 16 * crSourceSteps S N t + 8 ∧ OutputsSupport out x ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + limit + 1) p.mem out.mem) := by
  obtain ⟨sourceOut, hRun, hOutput⟩ := (S.spec N t hN ht).2.2.2.2.2 x hSupport
  have hNative := crSimulation_returns_frame P S.progDec E
    (decoderStart (S.data N t).W ((S.data N t).H x) []) sourceOut p
    (S.data N t).W file memBase detBase logBase limit N (S.data N t).det
    base fail ok (crSourceSteps S N t)
    (S.K * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2))) x
    hL hS hAt hOutputAt hBudget (by simpa only [decoderStart, initState, crSource_entry_zero] using hPc)
    hRun (crSourceSteps_ge S N t) hOutput
  simpa only [decoderStart, initState, crSource_entry_zero] using hNative

theorem crSource_call_returns_frame (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (x : Fin N → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hVM : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) →
      p.mem (memBase + a) = (decoderStart (S.data N t).W ((S.data N t).H x) []).mem a)
    (hInit : At G base crCallInit)
    (hCode : At G (base + 90) (crSpillCompile S.progDec (base + 90) fail ok))
    (hOutput : At G ok crOutputPrepare) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 16 * crSourceSteps S N t + 98 ∧ OutputsSupport out x ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  have hSpec := S.spec N t hN ht
  have hw : 0 < (S.data N t).W := by have hh := hSpec.1.1; omega
  have hStart := crCallInit_sem G E p base (S.data N t).W (S.data N t).R off file memBase detBase
    logBase (crSourceSteps S N t) metaBase (S.data N t).det ((S.data N t).H x)
    hInit hPc hw hSpec.2.1 hL h6 hSpan hHeader hVM
  obtain ⟨_, ki, mid, hRunInit, hMidPc, hKi, hState, hBudget, hSix, hInitFrame⟩ := hStart
  have hInitMemory : CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem mid.mem := by
    intro addr hOutside
    apply hInitFrame addr
    have h1 := hL.file_before
    have h2 := hL.mem_before_log
    have hOrder : file + 16 ≤ logBase :=
      hL.file_before.trans ((Nat.le_add_right memBase _).trans hL.mem_before_log.le)
    rcases hOutside with hBefore | hAfter
    · exact Or.inl hBefore
    · exact Or.inr (by omega)
  have hNative := crSource_native_returns_frame S G E N t file memBase detBase logBase
    (crSourceSteps S N t) (base + 90) fail ok mid x hN ht hSupport hL hState hCode hOutput hBudget hMidPc
  obtain ⟨_, kd, out, hRunDecode, hOutPc, hKd, hRecover, hSixOut, hNativeMemory⟩ := hNative
  refine ⟨hPc, kd + ki, out, ?_, hOutPc, by omega, hRecover, hSixOut.trans hSix, crMemFrame_trans hInitMemory hNativeMemory⟩
  rw [Function.iterate_add_apply, hRunInit, hRunDecode]

theorem crSource_input_call_returns_frame (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (x : Fin N → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hInputSpan : off + (S.data N t).R < 2 ^ E.W)
    (hBelow : (off + (S.data N t).R) / E.W < memBase)
    (hBits : ∀ i : Fin (S.data N t).R, bitAt p.mem E.W 0 (off + i.val) =
      if (S.data N t).H x i = 1 then 1 else 0)
    (hFresh : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → p.mem (memBase + a) = 0)
    (hPrepare : At G base crCallPrepare)
    (hCopy : At G (base + 24) (crCopyInputLoop (base + 24) (base + 41)))
    (hInit : At G (base + 41) crCallInit)
    (hCode : At G (base + 131) (crSpillCompile S.progDec (base + 131) fail ok))
    (hOutput : At G ok crOutputPrepare) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      OutputsSupport out x ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  have hSpec := S.spec N t hN ht
  have hw : 0 < (S.data N t).W := by have hh := hSpec.1.1; omega
  have hWide : (S.data N t).W < E.W := by have hh := hL.wide; omega
  have hMem : memBase + 2 ^ (S.data N t).W < 2 ^ E.W := by
    have hPow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : (S.data N t).W ≤ (S.data N t).W + 1)
    have hh := hL.mem_before_log
    have hh' := hL.log_word
    omega
  have hPrep := crCallPrepare_spec E p metaBase (S.data N t).W (S.data N t).R off file memBase detBase
    logBase (crSourceSteps S N t) h6 hSpan hHeader
  have hAtP : At G p.pc crCallPrepare := by rw [hPc]; exact hPrepare
  have hRunPrep := iterate_runBlock_of_at G E crCallPrepare p hAtP crCallPrepare_noBranch
  rw [crCallPrepare_length, crCallPrepare_run] at hRunPrep
  have hPcPrep : (crCallPreparedRun E p).pc = base + 24 := by rw [hPrep.1, hPc]
  have hBitsPrep : ∀ i : Fin (S.data N t).R,
      bitAt (crCallPreparedRun E p).mem E.W 0 (off + i.val) =
        if (S.data N t).H x i = 1 then 1 else 0 := by
    rw [hPrep.2.1]
    exact hBits
  have hFreshPrep : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → (crCallPreparedRun E p).mem (memBase + a) = 0 := by
    rw [hPrep.2.1]
    exact hFresh
  obtain ⟨mid, hRunCopy, hMidPc, _, _, hVM, hRegs, hCopyFrame⟩ :=
    crCopyInput_full G E (crCallPreparedRun E p) (S.data N t).W (S.data N t).R off memBase
      (base + 24) (base + 41) ((S.data N t).H x) hw hWide hSpec.2.1 hInputSpan hMem hBelow
      hBitsPrep hCopy hPcPrep hPrep.2.2.1 hPrep.2.2.2.2.2.1 hFreshPrep
  have hSix : mid.regs 6 = metaBase :=
    (hRegs 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hPrep.2.2.2.2.2.2.1
  have hCode' : At G ((base + 41) + 90) (crSpillCompile S.progDec ((base + 41) + 90) fail ok) := by
    simpa only [Nat.add_assoc] using hCode
  have hBeforeMemory : CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem mid.mem := by
    intro addr hOutside
    have h1 := hL.file_before
    have h2 := hL.mem_before_log
    have hCopyOutside : addr < memBase ∨ memBase + 2 ^ ((S.data N t).W + 1) < addr := by
      rcases hOutside with hBefore | hAfter
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact (hCopyFrame addr hCopyOutside).trans (congrFun hPrep.2.1 addr)
  have hNative := crSource_call_returns_frame S G E N t off file memBase detBase logBase metaBase
    (base + 41) fail ok mid x hN ht hSupport hL hSix hSpan hHeader hVM hInit hCode' hOutput hMidPc
  obtain ⟨_, kd, out, hRunNative, hOutPc, hKd, hRecover, hSixOut, hNativeMemory⟩ := hNative
  refine ⟨hPc, (kd + (17 * (S.data N t).R + 2)) + 24, out, ?_, hOutPc,
    by omega, hRecover, hSixOut.trans (hSix.trans h6.symm), crMemFrame_trans hBeforeMemory hNativeMemory⟩
  rw [Function.iterate_add_apply, hRunPrep, Function.iterate_add_apply, hRunCopy, hRunNative]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
theorem crSimulation_exits_frame (P source : Program) (E : RAMEnv)
    (w file memBase detBase logBase limit : ℕ) (det : ℕ → ℕ) (base fail ok : ℕ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hAt : At P base (crSpillCompile source base fail ok)) :
    ∀ (B : ℕ) (src p : RAMState), CRSimState w file memBase detBase logBase limit src p →
      p.regs 14 = B → p.pc = crSpillTarget source.length base fail src.pc →
      ∃ (k : ℕ) (out srcOut : RAMState), k ≤ 16 * B + 1 ∧ (step P E)^[k] p = out ∧
        (out.pc = fail ∨ out.pc = ok) ∧ CRSimState w file memBase detBase logBase limit srcOut out ∧
        (∀ r, CRSpillStable r → out.regs r = p.regs r) ∧
        CRMemFrame file (logBase + limit + 1) p.mem out.mem := by
  intro B
  induction B with
  | zero =>
    intro src p hS hBudget hPc
    by_cases hValid : src.pc < source.length
    · let j : Fin source.length := ⟨src.pc, hValid⟩
      have hPc' : p.pc = base + 16 * j.val := by simpa only [crSpillTarget, if_pos hValid] using hPc
      by_cases hHalt : Halted source src
      · obtain ⟨k, out, hK, hRun, hOk, hState, hRegs, hMemory⟩ :=
          crSimulation_halted_frame P source E src p w file memBase detBase logBase limit det
            base fail ok 0 hS hAt hPc hHalt
        exact ⟨k, out, src, hK, hRun, Or.inr hOk, hState, hRegs, hMemory⟩
      · have hNot : source.get j ≠ .halt := by
          intro hIns
          apply hHalt
          apply (crHalted_fetch_iff source src).mpr
          rw [List.getElem?_eq_getElem hValid]
          exact congrArg some hIns
        refine ⟨1, {p with pc := fail}, src, by omega, ?_, Or.inl rfl,
          crSimState_physical_pc hS, ?_, crMemFrame_refl _ _ _⟩
        · simpa only [Function.iterate_one] using
            crCompiled_guard_zero P source E p base fail ok hAt j hPc' hNot hBudget
        · intro r _
          rfl
    · refine ⟨0, p, src, by omega, rfl, Or.inl ?_, hS, ?_, crMemFrame_refl _ _ _⟩
      · simpa only [crSpillTarget, if_neg hValid] using hPc
      · intro r _
        rfl
  | succ B ih =>
    intro src p hS hBudget hPc
    by_cases hValid : src.pc < source.length
    · let j : Fin source.length := ⟨src.pc, hValid⟩
      have hPc' : p.pc = base + 16 * j.val := by simpa only [crSpillTarget, if_pos hValid] using hPc
      by_cases hHalt : Halted source src
      · obtain ⟨k, out, hK, hRun, hOk, hState, hRegs, hMemory⟩ :=
          crSimulation_halted_frame P source E src p w file memBase detBase logBase limit det
            base fail ok (B + 1) hS hAt hPc hHalt
        exact ⟨k, out, (step source (detEnv w det))^[B + 1] src, hK, hRun, Or.inr hOk, hState, hRegs, hMemory⟩
      · have hNot : source.get j ≠ .halt := by
          intro hIns
          apply hHalt
          apply (crHalted_fetch_iff source src).mpr
          rw [List.getElem?_eq_getElem hValid]
          exact congrArg some hIns
        obtain ⟨k, mid, hK, hRun, hMid, hMidPc, hClock, hRegs, hMemory⟩ :=
          crSimulation_step_frame P source E src p w file memBase detBase logBase limit det
            base fail ok hL hS hAt j hPc' rfl hNot (by omega)
        have hBudget' : mid.regs 14 = B := by omega
        obtain ⟨k', out, srcOut, hK', hRun', hExit, hFinal, hRegs', hMemory'⟩ :=
          ih (step source (detEnv w det) src) mid hMid hBudget' hMidPc
        refine ⟨k' + k, out, srcOut, by omega, ?_, hExit, hFinal, ?_, crMemFrame_trans hMemory hMemory'⟩
        · rw [Function.iterate_add_apply, hRun, hRun']
        · intro r hr
          exact (hRegs' r hr).trans (hRegs r hr)
    · refine ⟨0, p, src, by omega, rfl, Or.inl ?_, hS, ?_, crMemFrame_refl _ _ _⟩
      · simpa only [crSpillTarget, if_neg hValid] using hPc
      · intro r _
        rfl

def crFailureReturn (target : ℕ) : List Instr := [.imm 0 0, .imm 1 0, .jmp target]
def crFailureState (p : RAMState) (target : ℕ) : RAMState :=
  {p with pc := target, regs := Function.update (Function.update p.regs 0 0) 1 0}

theorem crFailureReturn_exec (P : Program) (E : RAMEnv) (p : RAMState) (base target : ℕ)
    (hAt : At P base (crFailureReturn target)) (hPc : p.pc = base) :
    (step P E)^[3] p = crFailureState p target := by
  have hBody : At P p.pc [.imm 0 0, .imm 1 0] := by
    rw [hPc]
    exact crAt_prefix P base [.imm 0 0, .imm 1 0] [.jmp target] hAt
  have hJump : P[p.pc + 2]? = some (.jmp target) := by
    have h := hAt 2 (by simp [crFailureReturn])
    simpa only [crFailureReturn, hPc, List.getElem?_cons_succ, List.getElem?_cons_zero] using h
  have hExec := crExecute_body_jump P E p [.imm 0 0, .imm 1 0] target
    (by simp [NoBranch, Instr.NoBranchI]) hBody hJump
  simpa [crFailureState, runBlock, execInstr] using hExec

/-- A bounded CR call returns also on invalid input; the failure path emits an
    empty list and the success path exposes only source-width bounded outputs. -/
theorem crSimulation_total_returns_frame (P source : Program) (E : RAMEnv)
    (src p : RAMState) (w file memBase detBase logBase limit base fail ok B : ℕ) (det : ℕ → ℕ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hOutputAt : At P ok crOutputPrepare) (hFailAt : At P fail (crFailureReturn (ok + 7)))
    (hBudget : p.regs 14 = B) (hPc : p.pc = crSpillTarget source.length base fail src.pc) :
    Sem P E (crSpillTarget source.length base fail src.pc) (ok + 7) p (fun k out =>
      k ≤ 16 * B + 8 ∧ out.regs 1 ≤ 2 ^ w ∧ out.regs 6 = p.regs 6 ∧
      CRMemFrame file (logBase + limit + 1) p.mem out.mem) := by
  obtain ⟨k, mid, srcOut, hK, hRun, hExit, hState, hRegs, hMemory⟩ :=
    crSimulation_exits_frame P source E w file memBase detBase logBase limit det base fail ok
      hL hAt B src p hS hBudget hPc
  have hSix : mid.regs 6 = p.regs 6 := hRegs 6 (by unfold CRSpillStable; decide)
  rcases hExit with hFail | hOk
  · have hFailRun := crFailureReturn_exec P E mid fail (ok + 7) hFailAt hFail
    refine ⟨hPc, 3 + k, crFailureState mid (ok + 7), ?_, rfl, by omega, ?_, ?_, hMemory⟩
    · rw [Function.iterate_add_apply, hRun, hFailRun]
    · simp [crFailureState]
    · simpa only [crFailureState, Function.update_of_ne (by decide : (6 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (6 : Fin 16) ≠ 0)] using hSix
  · have hLogTop : logBase < 2 ^ E.W := by have h := hL.log_word; omega
    have hMemLog : memBase + 2 ^ w < logBase :=
      (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) memBase).trans_lt hL.mem_before_log
    have hRead : memBase + 2 ^ w < 2 ^ E.W := hMemLog.trans hLogTop
    have hFile : file + 16 ≤ 2 ^ E.W := hL.file_before.trans ((Nat.le_add_right memBase (2 ^ w)).trans hRead.le)
    have hWide : w < E.W := by have h := hL.wide; omega
    have hNo : NoBranch crOutputPrepare := by simp [crOutputPrepare, crSpillLoad, NoBranch, Instr.NoBranchI]
    have hAtMid : At P mid.pc crOutputPrepare := by rw [hOk]; exact hOutputAt
    generalize hPrep : runBlock crOutputPrepare E mid = out
    have hExec : (step P E)^[7] mid = out := by
      have h := iterate_runBlock_of_at P E crOutputPrepare mid hAtMid hNo
      rw [hPrep] at h
      simpa only [crOutputPrepare_length] using h
    have hSpec := crOutputPrepare_spec E mid srcOut w file memBase hState.view hState.closed
      hWide hState.file_ptr hState.mem_ptr hFile hRead
    rw [hPrep] at hSpec
    obtain ⟨hOutPc, hOutMem, h0, h1, hOutFrame⟩ := hSpec
    have hEndPc : out.pc = ok + 7 := by rw [hOutPc, hOk]
    refine ⟨hPc, 7 + k, out, ?_, hEndPc, by omega, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hRun, hExec]
    · rw [h1]
      exact hState.closed.1 1
    · exact (hOutFrame 6 (by decide) (by decide)).trans hSix
    · rw [hOutMem]
      exact hMemory


/-- The initialized call is total for every binary source sketch, irrespective
    of whether that sketch represents a sparse input. -/
theorem crSource_call_total_returns_frame (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (y : Fin (S.data N t).R → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hVM : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) →
      p.mem (memBase + a) = (decoderStart (S.data N t).W y []).mem a)
    (hInit : At G base crCallInit)
    (hCode : At G (base + 90) (crSpillCompile S.progDec (base + 90) fail ok))
    (hOutput : At G ok crOutputPrepare) (hFail : At G fail (crFailureReturn (ok + 7))) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 16 * crSourceSteps S N t + 98 ∧ out.regs 1 ≤ 2 ^ (S.data N t).W ∧ out.regs 6 = p.regs 6 ∧
      CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  have hSpec := S.spec N t hN ht
  have hw : 0 < (S.data N t).W := by have hh := hSpec.1.1; omega
  have hStart := crCallInit_sem G E p base (S.data N t).W (S.data N t).R off file memBase detBase
    logBase (crSourceSteps S N t) metaBase (S.data N t).det y
    hInit hPc hw hSpec.2.1 hL h6 hSpan hHeader hVM
  obtain ⟨_, ki, mid, hRunInit, hMidPc, hKi, hState, hBudget, hSix, hInitFrame⟩ := hStart
  have hInitMemory : CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem mid.mem := by
    intro addr hOutside
    apply hInitFrame addr
    have hOrder : file + 16 ≤ logBase :=
      hL.file_before.trans ((Nat.le_add_right memBase _).trans hL.mem_before_log.le)
    rcases hOutside with hBefore | hAfter
    · exact Or.inl hBefore
    · exact Or.inr (by omega)
  have hNative := crSimulation_total_returns_frame G S.progDec E (decoderStart (S.data N t).W y []) mid
    (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (base + 90) fail ok
    (crSourceSteps S N t) (S.data N t).det hL hState hCode hOutput hFail hBudget
    (by simpa only [decoderStart, initState, crSource_entry_zero] using hMidPc)
  obtain ⟨_, kd, out, hRunDecode, hOutPc, hKd, hCount, hSixOut, hNativeMemory⟩ := hNative
  refine ⟨hPc, kd + ki, out, ?_, hOutPc, by omega, hCount, hSixOut.trans hSix,
    crMemFrame_trans hInitMemory hNativeMemory⟩
  rw [Function.iterate_add_apply, hRunInit, hRunDecode]

theorem crSource_input_total_returns_frame (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (y : Fin (S.data N t).R → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hInputSpan : off + (S.data N t).R < 2 ^ E.W)
    (hBelow : (off + (S.data N t).R) / E.W < memBase)
    (hBits : ∀ i : Fin (S.data N t).R, bitAt p.mem E.W 0 (off + i.val) =
      if y i = 1 then 1 else 0)
    (hFresh : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → p.mem (memBase + a) = 0)
    (hPrepare : At G base crCallPrepare)
    (hCopy : At G (base + 24) (crCopyInputLoop (base + 24) (base + 41)))
    (hInit : At G (base + 41) crCallInit)
    (hCode : At G (base + 131) (crSpillCompile S.progDec (base + 131) fail ok))
    (hOutput : At G ok crOutputPrepare) (hFail : At G fail (crFailureReturn (ok + 7))) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      out.regs 1 ≤ 2 ^ (S.data N t).W ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  have hSpec := S.spec N t hN ht
  have hw : 0 < (S.data N t).W := by have hh := hSpec.1.1; omega
  have hWide : (S.data N t).W < E.W := by have hh := hL.wide; omega
  have hMem : memBase + 2 ^ (S.data N t).W < 2 ^ E.W := by
    have hPow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : (S.data N t).W ≤ (S.data N t).W + 1)
    have hh := hL.mem_before_log
    have hh' := hL.log_word
    omega
  have hPrep := crCallPrepare_spec E p metaBase (S.data N t).W (S.data N t).R off file memBase detBase
    logBase (crSourceSteps S N t) h6 hSpan hHeader
  have hAtP : At G p.pc crCallPrepare := by rw [hPc]; exact hPrepare
  have hRunPrep := iterate_runBlock_of_at G E crCallPrepare p hAtP crCallPrepare_noBranch
  rw [crCallPrepare_length, crCallPrepare_run] at hRunPrep
  have hPcPrep : (crCallPreparedRun E p).pc = base + 24 := by rw [hPrep.1, hPc]
  have hBitsPrep : ∀ i : Fin (S.data N t).R,
      bitAt (crCallPreparedRun E p).mem E.W 0 (off + i.val) =
        if y i = 1 then 1 else 0 := by
    rw [hPrep.2.1]
    exact hBits
  have hFreshPrep : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → (crCallPreparedRun E p).mem (memBase + a) = 0 := by
    rw [hPrep.2.1]
    exact hFresh
  obtain ⟨mid, hRunCopy, hMidPc, _, _, hVM, hRegs, hCopyFrame⟩ :=
    crCopyInput_full G E (crCallPreparedRun E p) (S.data N t).W (S.data N t).R off memBase
      (base + 24) (base + 41) (y) hw hWide hSpec.2.1 hInputSpan hMem hBelow
      hBitsPrep hCopy hPcPrep hPrep.2.2.1 hPrep.2.2.2.2.2.1 hFreshPrep
  have hSix : mid.regs 6 = metaBase :=
    (hRegs 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hPrep.2.2.2.2.2.2.1
  have hCode' : At G ((base + 41) + 90) (crSpillCompile S.progDec ((base + 41) + 90) fail ok) := by
    simpa only [Nat.add_assoc] using hCode
  have hBeforeMemory : CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem mid.mem := by
    intro addr hOutside
    have h1 := hL.file_before
    have h2 := hL.mem_before_log
    have hCopyOutside : addr < memBase ∨ memBase + 2 ^ ((S.data N t).W + 1) < addr := by
      rcases hOutside with hBefore | hAfter
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact (hCopyFrame addr hCopyOutside).trans (congrFun hPrep.2.1 addr)
  have hNative := crSource_call_total_returns_frame S G E N t off file memBase detBase logBase metaBase
    (base + 41) fail ok mid y hN ht hL hSix hSpan hHeader hVM hInit hCode' hOutput hFail hMidPc
  obtain ⟨_, kd, out, hRunNative, hOutPc, hKd, hRecover, hSixOut, hNativeMemory⟩ := hNative
  refine ⟨hPc, (kd + (17 * (S.data N t).R + 2)) + 24, out, ?_, hOutPc,
    by omega, hRecover, hSixOut.trans (hSix.trans h6.symm), crMemFrame_trans hBeforeMemory hNativeMemory⟩
  rw [Function.iterate_add_apply, hRunPrep, Function.iterate_add_apply, hRunCopy, hRunNative]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.crSource_input_total_returns_frame


