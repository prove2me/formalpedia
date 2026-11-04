-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
-- name    : Submission_Weighted_Global_LightTernaryArenaTemplate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:38:54.14069+00:00
-- url     : https://prove2.me/theorems/7128939f-7059-41a8-ab37-743a51f8553e
-- title:
--   Light Ternary Arena Template
-- statement:
--   Definitions and structural lemmas for Light Ternary Arena Template, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryArenaTemplate.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightWeightedGlobalArenaTemplate
open Light WeightedGlobalArenaLayout
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
inductive Field where
  | arg (index : ℕ)
  | ptr (slot : ℕ)
  | num (value : ℕ)
  | square (index : ℕ)
  deriving DecidableEq
def value (inputs : ℕ → ℤ) (free C : ℕ) : Field → ℤ
  | .arg i => inputs i
  | .ptr s => (addr free C s : ℕ)
  | .num n => n
  | .square i => inputs i*inputs i
def hostFields : List Field :=[
  .ptr 30,.ptr 31,.ptr 32,.ptr 33,.ptr 34,.ptr 35,.num 0,.arg 13,.arg 14,.arg 15,
  .ptr 16,.arg 3,.num 1,.ptr 36,.ptr 13,.num 0,.ptr 14,.num 0,.ptr 37,.ptr 38,.ptr 28,.num 1,.num 1,
  .ptr 39,.ptr 40,.ptr 41,.ptr 42,.ptr 43,.ptr 44,.num 0,.arg 13,.arg 14,.arg 15,
  .ptr 17,.arg 5,.num 1,.ptr 45,.ptr 13,.num 0,.ptr 14,.num 0,.ptr 46,.ptr 47,.ptr 29,.num 1,.num 1,
  .num 0,.ptr 13,.num 0,.ptr 49,.num 0,.ptr 48,.num 1,.ptr 38,.ptr 47,.ptr 50,.ptr 51,.ptr 52,
  .num 0,.ptr 54,.num 0,.ptr 57,.ptr 13,.num 0,.ptr 50,.num 0,.num 0,.ptr 56,.ptr 58,.ptr 59,.ptr 60,.num 0,.num 0,.ptr 61,.ptr 61,
  .num 0,.ptr 54,.num 0,.ptr 57,.ptr 13,.num 0,.ptr 51,.num 0,.num 0,.ptr 56,.ptr 62,.ptr 63,.ptr 64,.num 0,.num 0,.ptr 65,.ptr 65,
  .ptr 66,.num 0,.ptr 52,.num 0,.ptr 55,.ptr 19,.ptr 53,.ptr 50,.ptr 51,.ptr 52,.num 0,.num 0,.num 0,.ptr 53]
def seedFields : List Field :=[
  .arg 11,.num 0,.arg 12,.ptr 7,.num 1,.arg 13,.num 1,
  .arg 2,.ptr 4,.ptr 16,.arg 3,.arg 4,.ptr 5,.ptr 17,.arg 5,
  .arg 6,.ptr 6,.ptr 18,.arg 7,.arg 8,.ptr 19,.ptr 20,.ptr 21,.ptr 22,
  .ptr 1,.arg 9,.arg 10,.ptr 28,.ptr 29,.ptr 23,.ptr 53,.ptr 24,.ptr 25,.ptr 26,.ptr 27,
  .ptr 9,.ptr 10,.ptr 11,.ptr 12,.num 0,
  .square 16,.num 1,.num 1,.num 1,.num 0,.num 0,.num 0,.ptr 8]
def hostValues (inputs : ℕ → ℤ) (free C : ℕ) : List ℤ :=hostFields.map (value inputs free C)
def seedValues (inputs : ℕ → ℤ) (free C : ℕ) : List ℤ :=seedFields.map (value inputs free C)
def ptrExpr (slot : ℕ) : Expr :=v 1 +' k slot *' v 24
def fieldExpr : Field → Expr
  | .arg i =>v i
  | .ptr s =>ptrExpr s
  | .num n =>k n
  | .square i =>v i *' v i
def stores (dstSlot : ℕ) : ℕ → List Field → Stmt
  | _,[] =>.skip
  | offset,f::fs =>.store (ptrExpr dstSlot +' k offset) (fieldExpr f) ;; stores dstSlot (offset+1) fs
def Good : Field → Prop
  | .arg i =>i<23
  | .ptr s =>s<67
  | .num n =>n≤1
  | .square i =>i=16
instance (f : Field) : Decidable (Good f) := by cases f <;> unfold Good <;> infer_instance
def body (D E : ℕ) : Stmt :=
  .call 0 [v 0 +' k 1,k E] 23 ;;
  .set 24 (k (256*(D+1)) *' v 23) ;;
  stores 0 0 hostFields ;;
  stores 2 0 seedFields ;;
  .set 0 (v 1)
def program (D E : ℕ) : Program :=LightNatPower.program++[body D E]
def time (E : ℕ) : ℕ :=LightNatPower.time E+4000
def args (U free Bmatrix nB Cmatrix nC Omatrix nO positions taggedB taggedC menu
    J p wordRadix F q dB dC dP tB tC tP : ℕ) : List ℤ :=
  [U,free,Bmatrix,nB,Cmatrix,nC,Omatrix,nO,positions,taggedB,taggedC,menu,J,p,wordRadix,F,q,dB,dC,dP,tB,tC,tP]
end ThreeSum.LightWeightedGlobalArenaTemplate


