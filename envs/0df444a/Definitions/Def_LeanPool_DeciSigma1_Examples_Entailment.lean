-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Examples_Entailment
-- name    : LeanPool_DeciSigma1_Examples_Entailment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:38:52.516859+00:00
-- url     : https://prove2.me/theorems/edd2160b-54f5-40b4-a33f-2a02eb580803
-- title:
--   Entailment
-- statement:
--   Definitions and structural lemmas for Entailment, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Entailment.lean

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Mathlib.Tactic.FinCases
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Examples
open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics DeciSigma1.Constraints
def swapQueries : Fin 2 → Fin 2 × Fin 2 := ![(0, 1), (1, 0)]
def arrow : Fin 2 → Bool := ![true, false]
def pinned (s : Fin 2 → Fin 4) : List (LitT 2 (Fin 4)) :=
  [.eqBot 1, .eqTop 2, .fLe s 3, .leF 3 s]
def leastQueries : Fin 2 → Fin 4 × Fin 4 := ![(0, 1), (3, 0)]
end DeciSigma1.Examples


