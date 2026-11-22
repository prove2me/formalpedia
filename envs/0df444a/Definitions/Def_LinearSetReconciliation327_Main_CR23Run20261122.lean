-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CR23Run20261122
-- name    : LinearSetReconciliation327_Main_CR23Run20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T06:46:23.204854+00:00
-- url     : https://prove2.me/theorems/14e4a891-99e3-45bd-ad7d-64744f6cae93
-- title:
--   The decoding-run vocabulary of Proposition 2.3, and the layered expander
-- statement:
--   This bundle publishes the small definition layer that the *concrete decoding run* of Proposition 2.3 needs, which the accepted development kept local to its own file: the layered-expander predicate $\mathrm{IsLayeredExpander}\ C\ K\ \varepsilon$ (every layered sub-multiset of at most $K$ labels has an image of size at most $(1-\varepsilon)K$ under some layer of the sketch $C$), the neighbour map $\mathrm{cr23Neigh}$, the writer $\mathrm{writeList}$, and the straight-line-block interface that the run's step budget is phrased in (`runBlock`'s recursion, the `NoBranch`/`NoBranchI` predicates and the per-instruction `execInstr` equations).  Everything else the run refers to was already published: `Stmt`, `Cond`, `Sem`, `At`, `runBlock` and the instruction abbreviations in `Def_LinearSetReconciliation327_Main_DecoderModel`, and the CR23 sketch ($\mathrm{cr23Word}$, $\mathrm{cr23D}$, $\mathrm{cr23M}$, $\mathrm{cr23R}$, $\mathrm{cr23Sketch}$) plus the decoder `Stmt`/`Program` in `Def_LinearSetReconciliation327_Main_CR23` and `..._CR23Dec`.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.3 (Proposition 2.3) and §3.1 (the CR23 layered expander). Skeleton subtraction from the accepted development `Solutions/Sol_proposition_2_3.lean` (lines 199–487 and 1020–1030), copied byte-identically.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_CR23
import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec

set_option autoImplicit false
set_option linter.all false
namespace LinearSetReconciliation327.Main
open Finset
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
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
@[simp] theorem execInstr_band (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.band d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) &&& (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_bor (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.bor d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) ||| (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_bxor (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.bxor d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) ^^^ (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_shl (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.shl d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) * 2 ^ (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_shr (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.shr d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d (((s.regs a) / 2 ^ (s.regs b)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_lt (E : RAMEnv) (s : RAMState) (d a b : Fin 16) :
    execInstr (.lt d a b) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((if (s.regs a) < (s.regs b) then 1 else 0) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_load (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.load d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((s.mem (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_store (E : RAMEnv) (s : RAMState) (a v : Fin 16) :
    execInstr (.store a v) E s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.regs a) (s.regs v) } := rfl
@[simp] theorem execInstr_jz (E : RAMEnv) (s : RAMState) (c : Fin 16) (t : ℕ) :
    execInstr (.jz c t) E s = { s with pc := if (s.regs c) = 0 then t else s.pc + 1 } := rfl
@[simp] theorem execInstr_jmp (E : RAMEnv) (s : RAMState) (t : ℕ) :
    execInstr (.jmp t) E s = { s with pc := t } := rfl
@[simp] theorem execInstr_qDet (E : RAMEnv) (s : RAMState) (d a : Fin 16) :
    execInstr (.qDet d a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.det (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_qPerm (E : RAMEnv) (s : RAMState) (d k a : Fin 16) :
    execInstr (.qPerm d k a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.perm (s.regs k) (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_qPermInv (E : RAMEnv) (s : RAMState) (d k a : Fin 16) :
    execInstr (.qPermInv d k a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.permInv (s.regs k) (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem execInstr_qCoeff (E : RAMEnv) (s : RAMState) (d k a : Fin 16) :
    execInstr (.qCoeff d k a) E s = { s with pc := s.pc + 1, regs := Function.update s.regs d ((E.coeff (s.regs k) (s.regs a)) % 2 ^ E.W) } := rfl
@[simp] theorem noBranch_nil : NoBranch ([] : List Instr) ↔ True := by simp [NoBranch]
@[simp] theorem noBranch_cons (i : Instr) (c : List Instr) :
    NoBranch (i :: c) ↔ i.NoBranchI ∧ NoBranch c := by simp [NoBranch]
@[simp] theorem noBranch_append (a b : List Instr) : NoBranch (a ++ b) ↔ NoBranch a ∧ NoBranch b := by
  induction a with
  | nil => simp
  | cons i t ih => simp [ih, and_assoc]
@[simp] theorem noBranchI_imm (d : Fin 16) (v : ℕ) : (iImm d v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_add (d a b : Fin 16) : (iAdd d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_sub (d a b : Fin 16) : (iSub d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_mul (d a b : Fin 16) : (iMul d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_div (d a b : Fin 16) : (iDiv d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_mod (d a b : Fin 16) : (iMod d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_band (d a b : Fin 16) : (iBand d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_bor (d a b : Fin 16) : (iBor d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_bxor (d a b : Fin 16) : (iBxor d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_shl (d a b : Fin 16) : (iShl d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_shr (d a b : Fin 16) : (iShr d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_lt (d a b : Fin 16) : (iLt d a b).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_load (d a : Fin 16) : (iLd d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_store (a v : Fin 16) : (iSt a v).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qDet (d a : Fin 16) : (iTbl d a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qPerm (d k a : Fin 16) : (Instr.qPerm d k a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qPermInv (d k a : Fin 16) : (Instr.qPermInv d k a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem noBranchI_qCoeff (d k a : Fin 16) : (Instr.qCoeff d k a).NoBranchI := by
  refine ⟨fun t h => ?_, fun d' t h => ?_, fun h => ?_⟩ <;> cases h
@[simp] theorem runBlock_nil (E : RAMEnv) (s : RAMState) : runBlock [] E s = s := rfl
@[simp] theorem runBlock_cons (i : Instr) (code : List Instr) (E : RAMEnv) (s : RAMState) :
    runBlock (i :: code) E s = runBlock code E (execInstr i E s) := by
  simp [runBlock, List.foldl_cons]
@[simp] theorem At.nil {P : Program} {a : ℕ} : At P a ([] : List Instr) ↔ True := by
  unfold At
  simp
end LinearSetReconciliation327.Main
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
/-- `Γ_s(S)`, the neighbourhood of `S` in layer `s`: the set of buckets of seed `s` hit by `S`. -/
def cr23Neigh {N D M : ℕ} (C : Fin N → Fin D → Fin M) (S : Finset (Fin N)) (s : Fin D) : ℕ :=
  (S.image (fun v => C v s)).card
/-- **CR23 Definition 2, layered form.**  `C : [N] → [D] → [M]` is a layered
`(D, K, ε)`-bipartite expander when every `S` with `|S| ≤ K` satisfies
`|Γ(S)| = ∑_s |Γ_s(S)| ≥ (1-ε)·D·|S|`.  (Every left vertex has degree exactly one in each layer
by construction, and `|R_i| = M`, so this is exactly Definition 2 specialised to a function `C`.) -/
def IsLayeredExpander {N D M : ℕ} (C : Fin N → Fin D → Fin M) (K : ℕ) (eps : ℝ) : Prop :=
  ∀ S : Finset (Fin N), S.card ≤ K →
    (1 - eps) * ((D : ℝ) * (S.card : ℝ)) ≤ ∑ s : Fin D, ((cr23Neigh C S s : ℕ) : ℝ)
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
noncomputable section
end
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
variable {N' t' : ℕ}
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
/-- Apply a list of writes left to right. -/
def writeList (m : ℕ → ℕ) : List (ℕ × ℕ) → ℕ → ℕ
  | [], a => m a
  | p :: tl, a => writeList (Function.update m p.1 p.2) tl a
@[simp] theorem writeList_nil (m : ℕ → ℕ) (a : ℕ) : writeList m [] a = m a := rfl
@[simp] theorem writeList_cons (m : ℕ → ℕ) (p : ℕ × ℕ) (tl : List (ℕ × ℕ)) (a : ℕ) :
    writeList m (p :: tl) a = writeList (Function.update m p.1 p.2) tl a := rfl
/-- The ten registers the store half must not disturb: `r0` (the value of the last slot), `r2` (the
increment), and the nine values the fifteen slots are filled from. -/
structure DecPSKeep (st st0 : RAMState) : Prop where
  k0 : st.regs r0 = st0.regs r0
  k2 : st.regs r2 = st0.regs r2
  k3 : st.regs r3 = st0.regs r3
  k4 : st.regs r4 = st0.regs r4
  k8 : st.regs r8 = st0.regs r8
  k9 : st.regs r9 = st0.regs r9
  k10 : st.regs r10 = st0.regs r10
  k11 : st.regs r11 = st0.regs r11
  k13 : st.regs r13 = st0.regs r13
  k14 : st.regs r14 = st0.regs r14
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecXorPay
end DecXorPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
namespace DecCandPay
end DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LinearSetReconciliation327.Main
open DecCandPay
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
set_option maxRecDepth 8000
namespace LinearSetReconciliation327.Main
end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open Finset
end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.IsLayeredExpander


