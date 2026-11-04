-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryReconstruction
-- name    : Submission_ThreeSum_TernaryReconstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:37:56.555196+00:00
-- url     : https://prove2.me/theorems/22f51074-604c-460a-ba61-4c51b9368348
-- title:
--   Ternary Reconstruction
-- statement:
--   Definitions and structural lemmas for Ternary Reconstruction, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean

import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
namespace ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler
def recover {N : ℕ} (seed : TritWord N → ℤ) (h T : ℕ) :
    ℕ → TritWord N → ℤ
  | 0, R => seed R
  | k + 1, R =>
      if rank R ≤ T then seed R else
        (∑ i : Fin N, if (R i).val = 0 then 0 else
          (R i).val * recover seed h T k (predecessor R i)) /
          ((rank R : ℤ) - (h : ℤ))
def frozenInverse {N : ℕ} : List (Fin N) → (TritWord N → ℤ) → TritWord N → ℤ
  | [], H, R => H R
  | i :: rest, H, R =>
      inverseDigit (fun d => frozenInverse rest H (Function.update R i d)) (R i)
def firstCross {N : ℕ} (T : ℕ) (H : TritWord N → ℤ) :
    List (Fin N) → TritWord N → ℤ
  | [], R => H R
  | i :: rest, R =>
      if rank R ≤ T then frozenInverse (i :: rest) H R else
        inverseDigit (fun d => firstCross T H rest (Function.update R i d)) (R i)
def inverseCoefficient (q r : Fin 3) : ℤ :=
  if r ≤ q then (-1 : ℤ) ^ (q.val - r.val) * Nat.choose q.val r.val else 0
end ThreeSum.TernaryReconstruction


