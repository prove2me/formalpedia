-- Prove2me | Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
-- name    : Submission_ThreeSum_LightFixedArithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:33:29.641195+00:00
-- url     : https://prove2.me/theorems/ba2dc58f-4ea3-499e-baa9-34bbdf921e70
-- title:
--   Light Fixed Arithmetic
-- statement:
--   Definitions and structural lemmas for Light Fixed Arithmetic, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedArithmetic.lean

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.LightFixedArithmetic
open Light
inductive Circuit where
  | literal (z : ℤ)
  | atom (i : ℕ)
  | add (a b : Circuit)
  | sub (a b : Circuit)
  | mul (a b : Circuit)
def Circuit.eval (x : ℕ → ℤ) : Circuit → ℤ
  | .literal z => z
  | .atom i => x i
  | .add a b => a.eval x+b.eval x
  | .sub a b => a.eval x-b.eval x
  | .mul a b => a.eval x*b.eval x
def Circuit.compile (atoms : ℕ → Expr) : Circuit → Expr
  | .literal z => LightSignedFiniteTable.literal z
  | .atom i => atoms i
  | .add a b => a.compile atoms +' b.compile atoms
  | .sub a b => a.compile atoms -' b.compile atoms
  | .mul a b => a.compile atoms *' b.compile atoms
def Circuit.bound (U : ℤ) : Circuit → ℤ
  | .literal z => |z|+1
  | .atom _ => U+1
  | .add a b => a.bound U+b.bound U
  | .sub a b => a.bound U+b.bound U
  | .mul a b => a.bound U*b.bound U
def Circuit.coefficient : Circuit → ℤ
  | .literal z => |z|+1
  | .atom _ => 1
  | .add a b => a.coefficient+b.coefficient
  | .sub a b => a.coefficient+b.coefficient
  | .mul a b => a.coefficient*b.coefficient
def Circuit.degree : Circuit → ℕ
  | .literal _ => 0
  | .atom _ => 1
  | .add a b => max a.degree b.degree
  | .sub a b => max a.degree b.degree
  | .mul a b => a.degree+b.degree
end ThreeSum.LightFixedArithmetic


