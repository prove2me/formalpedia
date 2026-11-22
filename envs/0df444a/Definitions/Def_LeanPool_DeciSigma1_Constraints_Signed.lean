-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
-- name    : LeanPool_DeciSigma1_Constraints_Signed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:36:30.786099+00:00
-- url     : https://prove2.me/theorems/ef57b20b-f208-4583-9ede-6015e3588ec6
-- title:
--   Signed
-- statement:
--   Definitions and structural lemmas for Signed, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.Bound.Init
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
abbrev signedVar (u : V) (p : Bool) : V × Bool := (u, p)
abbrev base (z : V × Bool) : V := z.1
abbrev sign (z : V × Bool) : Bool := z.2
def signedLit (c : Fin n → Bool) : LitT n V → List (LitT n (V × Bool))
  | .le u v => [.le (u, false) (v, false), .le (v, true) (u, true)]
  | .leF u a => [.leF (signedVar u false) (fun i => signedVar (a i) (c i)),
      .fLe (fun i => signedVar (a i) (!(c i))) (signedVar u true)]
  | .fLe a u => [.fLe (fun i => signedVar (a i) (c i)) (signedVar u false),
      .leF (signedVar u true) (fun i => signedVar (a i) (!(c i)))]
  | .eqBot u => [.eqBot (signedVar u false), .eqTop (signedVar u true)]
  | .eqTop u => [.eqTop (signedVar u false), .eqBot (signedVar u true)]
def signed (c : Fin n → Bool) (Γ : List (LitT n V)) : List (LitT n (V × Bool)) :=
  Γ.flatMap (signedLit c)
def Signed.dual (A : (V × Bool) → Semantics.Tree n) (z : (V × Bool)) : Semantics.Tree n :=
  Tree.dual (A (signedVar (base z) (!(sign z))))
def normalized (c : Fin n → Bool) (ρ : V → Semantics.Tree n) (z : (V × Bool)) : Semantics.Tree n :=
  Tree.normalize c (sign z) (ρ (base z))
def decoded (c : Fin n → Bool) (A : (V × Bool) → Semantics.Tree n) (u : V) : Semantics.Tree n :=
  Tree.normalize c false (A (signedVar u false))
end DeciSigma1.Constraints


