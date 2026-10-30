-- Prove2me | Definitions.Def_DerivativeChainContinuation_SchurExtension
-- name    : DerivativeChainContinuation_SchurExtension
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:03:25.848826+00:00
-- url     : https://prove2.me/theorems/51a962e8-b398-4c52-8f9c-03e6b1e08968
-- title:
--   One-coordinate unitary block extension
-- statement:
--   Extend a square complex matrix $U$ to the block matrix $\operatorname{diag}(1,U)$. This operation fixes the first coordinate in the inductive construction of a unitary triangularization.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SchurExtension.lean#L8-L11

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

noncomputable def extendFirstUnitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  Matrix.of (Fin.cases (Fin.cases 1 (fun _ => 0))
    (fun i => Fin.cases 0 (fun j => U i j)))







end DerivativeChainContinuation


