-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryQuery
-- name    : Submission_ThreeSum_TernaryQuery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:34:06.517349+00:00
-- url     : https://prove2.me/theorems/2ed5fc18-3df1-4d93-9191-21fbf7b06e23
-- title:
--   Ternary Query
-- statement:
--   Definitions and structural lemmas for Ternary Query, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean

import Definitions.Def_Submission_ThreeSum_TernaryBank
set_option autoImplicit false
namespace ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank
def zetaDigit (f : Fin 3 → ℤ) (d : Fin 3) : ℤ :=
  if d = 0 then f 0 else if d = 1 then f 0 + f 1 else f 0 + 2 * f 1 + f 2
def inverseDigit (f : Fin 3 → ℤ) (d : Fin 3) : ℤ :=
  if d = 0 then f 0 else if d = 1 then f 1 - f 0 else f 2 - 2 * f 1 + f 0
def coordinateZeta {N : ℕ} (i : Fin N) (f : TritWord N → ℤ) (R : TritWord N) : ℤ :=
  zetaDigit (fun d => f (Function.update R i d)) (R i)
def coordinateInverse {N : ℕ} (i : Fin N) (f : TritWord N → ℤ)
    (R : TritWord N) : ℤ :=
  inverseDigit (fun d => f (Function.update R i d)) (R i)
def runZeta {N : ℕ} : List (Fin N) → (TritWord N → ℤ) → (TritWord N → ℤ)
  | [], f => f
  | i :: rest, f => coordinateZeta i (runZeta rest f)
def runInverse {N : ℕ} : List (Fin N) → (TritWord N → ℤ) → (TritWord N → ℤ)
  | [], f => f
  | i :: rest, f => runInverse rest (coordinateInverse i f)
end ThreeSum.TernaryQuery


