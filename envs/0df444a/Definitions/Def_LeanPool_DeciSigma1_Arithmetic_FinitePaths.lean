-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
-- name    : LeanPool_DeciSigma1_Arithmetic_FinitePaths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:41:37.415164+00:00
-- url     : https://prove2.me/theorems/66902c4c-2186-4b7d-afee-3aa1c057bcb2
-- title:
--   Finite Paths
-- statement:
--   Definitions and structural lemmas for Finite Paths, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Arithmetic
variable {β : Type*}
section Runs
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
end Runs
end DeciSigma1.Arithmetic


