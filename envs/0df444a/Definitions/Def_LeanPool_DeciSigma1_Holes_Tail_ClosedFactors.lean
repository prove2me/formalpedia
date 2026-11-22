-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
-- name    : LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:43:42.432909+00:00
-- url     : https://prove2.me/theorems/7777e399-c6c9-420b-ab1f-b913c934e6ab
-- title:
--   Closed Factors
-- statement:
--   Definitions and structural lemmas for Closed Factors, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/ClosedFactors.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
def suffixLengthBound (m N : ℕ) : List ℕ → ℕ → ℕ
  | [] => fun b => factorLengthBound m N b + 1
  | S :: Ss => fun b =>
      2 * suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b) +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
          suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) + 2
def suffixLengthEnvelope (m N : ℕ) : List ℕ → ℕ → ℕ
  | [] => fun b => b
  | S :: Ss => fun b =>
      suffixLengthEnvelope m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b))
section ClosedFactors
variable [DecidableEq α] [Fintype S]
variable (T : Readers.Table α S k) (q0 : S) (x : List α)
end ClosedFactors
end DeciSigma1.Holes.Tail


