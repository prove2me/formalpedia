-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryEuler
-- name    : Submission_ThreeSum_TernaryEuler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:35:58.195546+00:00
-- url     : https://prove2.me/theorems/2b5cf505-29c7-448d-83b5-51aa3f614eeb
-- title:
--   Ternary Euler
-- statement:
--   Definitions and structural lemmas for Ternary Euler, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean

import Definitions.Def_Submission_ThreeSum_TernaryQuery
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
def predDigit (d : Fin 3) : Fin 3 := ⟨d.val - 1, by omega⟩
def predecessor {N : ℕ} (R : TritWord N) (i : Fin N) : TritWord N :=
  Function.update R i (predDigit (R i))
def digitChoose (r a : Fin 3) : ℤ := Nat.choose r.val a.val
def weight {N : ℕ} (R A : TritWord N) : ℤ := ∏ i, digitChoose (R i) (A i)
def binomialZeta {N : ℕ} (f : TritWord N → ℤ) (R : TritWord N) : ℤ :=
  ∑ A, weight R A * f A
end ThreeSum.TernaryEuler


