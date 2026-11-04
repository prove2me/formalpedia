-- Prove2me | Definitions.Def_Submission_ThreeSum_LightKaratsuba
-- name    : Submission_ThreeSum_LightKaratsuba
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:09.430414+00:00
-- url     : https://prove2.me/theorems/ae44145f-87c7-4c28-a717-8c3ce3395dff
-- title:
--   Light Karatsuba
-- statement:
--   Definitions and structural lemmas for Light Karatsuba, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightKaratsuba.lean

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
abbrev Len : ℕ := 0
abbrev Left : ℕ := 1
abbrev Right : ℕ := 2
abbrev Out : ℕ := 3
abbrev Work : ℕ := 4
abbrev Half : ℕ := 5
abbrev Unused : ℕ := 6
def joinBody (pLinear pFill : ℕ) : Stmt :=
  .call pLinear [v Work +' k 2 *' v Len, v Work, v Work +' k 2 *' v Len,
    v Len, k 0 -' k 1] Unused ;;
  .call pLinear [v Work +' k 2 *' v Len, v Work +' v Len,
    v Work +' k 2 *' v Len, v Len, k 0 -' k 1] Unused ;;
  .call pFill [v Out, k 2 *' v Len, k 0] Unused ;;
  .call pLinear [v Out, v Work, v Out, v Len, k 1] Unused ;;
  .call pLinear [v Out +' v Half, v Work +' k 2 *' v Len,
    v Out +' v Half, v Len, k 1] Unused ;;
  .call pLinear [v Out +' v Len, v Work +' v Len,
    v Out +' v Len, v Len, k 1] Unused
def recurseBody (pSelf pHalf pLinear pFill : ℕ) : Stmt :=
  .call pHalf [v Len] Half ;;
  .call pLinear [v Left, v Left +' v Half, v Work +' k 3 *' v Len,
    v Half, k 1] Unused ;;
  .call pLinear [v Right, v Right +' v Half,
    v Work +' k 3 *' v Len +' v Half, v Half, k 1] Unused ;;
  .call pSelf [v Half, v Left, v Right, v Work,
    v Work +' k 4 *' v Len] Unused ;;
  .call pSelf [v Half, v Left +' v Half, v Right +' v Half,
    v Work +' v Len, v Work +' k 4 *' v Len] Unused ;;
  .call pSelf [v Half, v Work +' k 3 *' v Len,
    v Work +' k 3 *' v Len +' v Half, v Work +' k 2 *' v Len,
    v Work +' k 4 *' v Len] Unused ;;
  joinBody pLinear pFill
def baseBody : Stmt :=
  .store (v Out) (M (v Left) *' M (v Right)) ;;
  .store (v Out +' k 1) (k 0)
def body (pSelf pHalf pLinear pFill : ℕ) : Stmt :=
  .ite (k 1 <' v Len) (recurseBody pSelf pHalf pLinear pFill) baseBody
structure Procs (P : Program) (pSelf pHalf pLinear pFill : ℕ) : Prop where
  self : P[pSelf]? = some (body pSelf pHalf pLinear pFill)
  half : P[pHalf]? = some halfBody
  linear : P[pLinear]? = some LightArray.linearBody
  fill : P[pFill]? = some fillBody
def time : ℕ → ℕ
  | 0 => 30
  | k + 1 => 3 * time k + 2500 * 2 ^ k
def ProductAt (μ : ℕ → ℤ) (out n : ℕ) (as bs : List ℤ) : Prop :=
  ∀ j < 2 * n, μ (out + j) = (asPolynomial as * asPolynomial bs).coeff j
def Result (μ : ℕ → ℤ) (out n work : ℕ) (as bs : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  ProductAt μ' out n as bs ∧ KeptBut μ μ' work out (2 * n)
def wordBound (n U : ℕ) : ℕ := 128 * n ^ 3 * (U + 1) ^ 2
def window (f : ℕ → ℤ) (offset n j : ℕ) : ℤ :=
  if offset ≤ j ∧ j < offset + n then f (j - offset) else 0
def joined (μ : ℕ → ℤ) (work n half j : ℕ) : ℤ :=
  window (fun i => μ (work + i)) 0 n j +
  window (fun i => μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i)) half n j +
  window (fun i => μ (work + n + i)) n n j
def joinTime (n : ℕ) : ℕ := 200 * n + 300
section Join
variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}
end Join
section BaseCase
variable {lim : Limits} {P : Program} {d : ℕ}
end BaseCase
section RecursiveExecution
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}
end RecursiveExecution
section CompleteProcedure
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}
def program : Program := [body 0 1 2 3, halfBody, LightArray.linearBody, fillBody]
end CompleteProcedure
end ThreeSum.LightKaratsuba


