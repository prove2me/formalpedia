-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
-- name    : Submission_ThreeSumApsp_Spec_Sec3_Problems
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:57:42.789824+00:00
-- url     : https://prove2.me/theorems/15b467ae-b961-4ab7-a78a-0cbdd9d9cbaf
-- title:
--   Problems
-- statement:
--   Supporting definitions from the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Spec/Sec3/Problems.lean

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
set_option autoImplicit false
section
namespace ThreeSumApsp.Spec
abbrev entry (n : ℕ) (L : List ℤ) (i j : ℕ) : ℤ := L.getD (i * n + j) 0
def vecOf (N : ℕ) (x : List ℤ) : Fin N → ℤ := fun i => x.getD i 0
def triOf (n : ℕ) (AB BC AC : List ℤ) : TriangleInstance ℤ n where
  wAB a b := AB.getD (a * n + b) 0
  wBC b c := BC.getD (b * n + c) 0
  wAC a c := AC.getD (a * n + c) 0
def graphOf (n : ℕ) (adj w : List ℤ) : Fin n → Fin n → WithTop ℤ := fun i j =>
  if adj.getD (i * n + j) 0 = 1 then ((w.getD (i * n + j) 0 : ℤ) : WithTop ℤ) else ⊤
def affL (m c : ℤ) (l : List ℤ) : List ℤ := l.map fun x => m * x + c
def subMat (s h r0 c0 : ℕ) (L : List ℤ) : List ℤ :=
  (List.range (h * h)).map fun q => entry s L (r0 + q / h) (c0 + q % h)
def minPlusEntry (n : ℕ) (A B : List ℤ) (i j : ℕ) : ℤ :=
  (List.range (n - 1)).foldl
    (fun acc k => min acc (entry n A i (k + 1) + entry n B (k + 1) j))
    (entry n A i 0 + entry n B 0 j)
def minPlusList (n : ℕ) (A B : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => minPlusEntry n A B (q / n) (q % n)
end ThreeSumApsp.Spec


