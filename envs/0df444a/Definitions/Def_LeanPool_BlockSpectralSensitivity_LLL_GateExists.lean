-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
-- name    : LeanPool_BlockSpectralSensitivity_LLL_GateExists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:59:20.658042+00:00
-- url     : https://prove2.me/theorems/1d7c47a6-0337-4cf5-886f-58e37a2f5e2b
-- title:
--   Gate Exists
-- statement:
--   Definitions and structural lemmas for Gate Exists, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
namespace LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
def BadIdx (Arc : ι → ι → Bool) : Type _ :=
  {F : Flag1 ι // F.Active Arc} ⊕ {S : Finset ι // S.card = 9}
noncomputable instance : Fintype (BadIdx Arc) := by
  classical
  unfold BadIdx
  infer_instance
instance : DecidableEq (BadIdx Arc) := by
  classical
  unfold BadIdx
  infer_instance
def badVerts : BadIdx Arc → Finset ι :=
  Sum.elim (fun F => F.1.supp) (fun S => S.1)
def badSupp (i : BadIdx Arc) : Finset (ι × ι) := (badVerts i).offDiag
def badTy : BadIdx Arc → Bool := Sum.elim (fun _ => false) (fun _ => true)
noncomputable def badEvent (Arc : ι → ι → Bool) : BadIdx Arc → Finset (GateCfg ι r) :=
  Sum.elim (fun F => flagEvent Arc F.1) (fun S => radiusTwoEvent Arc S.1)
noncomputable def badP : Bool → ℝ
  | false => p1
  | true => p2
noncomputable def badX : Bool → ℝ
  | false => x1
  | true => x2
def badD : Bool → Bool → ℕ
  | false, false => D11
  | false, true => D12
  | true, false => D21
  | true, true => D22
def headOut (Arc : ι → ι → Bool) (q : ι × Option ι) : Finset ι :=
  q.2.elim (outNbrs Arc q.1) (commonOut Arc q.1)
end LLL
end BSLambda


