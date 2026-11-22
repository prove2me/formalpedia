-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCRCode20261120
-- name    : LinearSetReconciliation327_Main_HintCRCode20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:33:18.022119+00:00
-- url     : https://prove2.me/theorems/02a3e7cf-9223-4b22-9b67-72d12f5a6e70
-- title:
--   LinearSetReconciliation327 — HintCRCode (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCRCode20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRFrame20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def crInputFail (S : CRSourceBundle) (base : ℕ) : ℕ := base + 131 + 16 * S.progDec.length
def crInputOk (S : CRSourceBundle) (base : ℕ) : ℕ := crInputFail S base + 3

def crSourceInputCode (S : CRSourceBundle) (base : ℕ) : List Instr :=
  crCallPrepare ++ (crCopyInputLoop (base + 24) (base + 41) ++ (crCallInit ++
    (crSpillCompile S.progDec (base + 131) (crInputFail S base) (crInputOk S base) ++
      (crFailureReturn (crInputOk S base + 7) ++ crOutputPrepare))))

theorem crCopyInputLoop_length (base done : ℕ) : (crCopyInputLoop base done).length = 17 := by
  simp [crCopyInputLoop, crCopyInputBit_length]

theorem crFailureReturn_length (target : ℕ) : (crFailureReturn target).length = 3 := rfl

theorem crSourceInputCode_length (S : CRSourceBundle) (base : ℕ) :
    (crSourceInputCode S base).length = 131 + 16 * S.progDec.length + 10 := by
  simp only [crSourceInputCode, List.length_append, crCallPrepare_length, crCopyInputLoop_length,
    crCallInit_length, crSpillCompile_length, crFailureReturn_length, crOutputPrepare_length]
  omega

theorem crSourceInputCode_end (S : CRSourceBundle) (base : ℕ) :
    crInputOk S base + 7 = base + (crSourceInputCode S base).length := by
  rw [crSourceInputCode_length]
  simp only [crInputOk, crInputFail]
  omega

theorem crSourceInputCode_at_parts (G : Program) (S : CRSourceBundle) (base : ℕ)
    (hAt : At G base (crSourceInputCode S base)) :
    At G base crCallPrepare ∧
    At G (base + 24) (crCopyInputLoop (base + 24) (base + 41)) ∧
    At G (base + 41) crCallInit ∧
    At G (base + 131) (crSpillCompile S.progDec (base + 131) (crInputFail S base) (crInputOk S base)) ∧
    At G (crInputFail S base) (crFailureReturn (crInputOk S base + 7)) ∧
    At G (crInputOk S base) crOutputPrepare := by
  have h41 : base + 24 + 17 = base + 41 := by omega
  have h131 : base + 41 + 90 = base + 131 := by omega
  simpa only [crSourceInputCode, At.append, crCallPrepare_length, crCopyInputLoop_length,
    crCallInit_length, crSpillCompile_length, crFailureReturn_length, crInputFail, crInputOk,
    h41, h131] using hAt

theorem crSourceInputCode_total (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base : ℕ) (p : RAMState)
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
    (hAt : At G base (crSourceInputCode S base)) (hPc : p.pc = base) :
    Sem G E base (base + (crSourceInputCode S base).length) p (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      out.regs 1 ≤ 2 ^ (S.data N t).W ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  obtain ⟨hPrepare, hCopy, hInit, hKernel, hFail, hOutput⟩ := crSourceInputCode_at_parts G S base hAt
  rw [← crSourceInputCode_end]
  exact crSource_input_total_returns_frame S G E N t off file memBase detBase logBase metaBase base
    (crInputFail S base) (crInputOk S base) p y hN ht hL h6 hSpan hHeader hInputSpan hBelow hBits
    hFresh hPrepare hCopy hInit hKernel hOutput hFail hPc

theorem crSourceInputCode_correct (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base : ℕ) (p : RAMState)
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
    (hAt : At G base (crSourceInputCode S base)) (hPc : p.pc = base) :
    Sem G E base (base + (crSourceInputCode S base).length) p (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      OutputsSupport out x ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  obtain ⟨hPrepare, hCopy, hInit, hKernel, hFail, hOutput⟩ := crSourceInputCode_at_parts G S base hAt
  rw [← crSourceInputCode_end]
  exact crSource_input_call_returns_frame S G E N t off file memBase detBase logBase metaBase base
    (crInputFail S base) (crInputOk S base) p x hN ht hSupport hL h6 hSpan hHeader hInputSpan hBelow hBits
    hFresh hPrepare hCopy hInit hKernel hOutput hPc

def crSourceInputProgram (S : CRSourceBundle) : Program := crSourceInputCode S 0 ++ [.halt]

theorem crSourceInputProgram_at (S : CRSourceBundle) :
    At (crSourceInputProgram S) 0 (crSourceInputCode S 0) := by
  intro index hIndex
  simp only [crSourceInputProgram, Nat.zero_add, List.getElem?_append_left hIndex]

theorem crSourceInputProgram_halt (S : CRSourceBundle) (out : RAMState)
    (hPc : out.pc = (crSourceInputCode S 0).length) : Halted (crSourceInputProgram S) out := by
  apply (crHalted_fetch_iff _ _).mpr
  simp [crSourceInputProgram, hPc]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.crSourceInputCode_total
#print axioms LinearSetReconciliation327.Main.crSourceInputCode_correct


