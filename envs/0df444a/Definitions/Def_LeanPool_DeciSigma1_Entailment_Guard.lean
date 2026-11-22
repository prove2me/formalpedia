-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
-- name    : LeanPool_DeciSigma1_Entailment_Guard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:18:54.255026+00:00
-- url     : https://prove2.me/theorems/52e554a2-d901-491f-9f7f-abbb02671228
-- title:
--   Guard
-- statement:
--   Definitions and structural lemmas for Guard, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Constraints.TopFree
open DeciSigma1.Semantics
variable {n : ℕ} {V : Type}
def Lit.toLitT : Lit n V → LitT n V
  | .le u v => .le u v
  | .fLe a u => .fLe a u
  | .leF u a => .leF u a
  | .eqBot u => .eqBot u
end DeciSigma1.Constraints.TopFree
namespace DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}
def guarded (vs : List V) (Γ : List (Lit n V)) : List (LitT n (Option V)) :=
  .leF none (fun _ => none) ::
    (vs.map (fun v => .le (some v) none) ++ Γ.map (fun l => l.toLitT.map some))
def guardedQueries (q : Fin k → V × V) (i : Fin k) : Option V × Option V :=
  (some (q i).1, some (q i).2)
end DeciSigma1.Entailment


