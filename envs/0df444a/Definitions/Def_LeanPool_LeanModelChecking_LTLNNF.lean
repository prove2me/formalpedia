-- Prove2me | Definitions.Def_LeanPool_LeanModelChecking_LTLNNF
-- name    : LeanPool_LeanModelChecking_LTLNNF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:43:34.445295+00:00
-- url     : https://prove2.me/theorems/1680ed25-df90-4ef3-96ef-b74acd3d0eda
-- title:
--   LTLNNF
-- statement:
--   Definitions and structural lemmas for LTLNNF, from György Kurucz; maintained by LeanPool contributors's pinned Formalizations of theorems related to model checking development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LeanModelChecking/LTLNNF.lean

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Push
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanModelChecking
inductive NNF (AP : Type) where
| atom (p : AP)
| not_atom (p : AP)
| and (f g : NNF AP)
| or (f g : NNF AP)
| next (f : NNF AP)
| until (f g : NNF AP)
| release (f g : NNF AP)
deriving DecidableEq
def NNF.language {AP} (f : NNF AP) (w : Nat → Letter AP) : Prop :=
  match f with
  | .atom p => p ∈ w 0
  | .not_atom p => p ∉ w 0
  | .and f g => NNF.language f w ∧ NNF.language g w
  | .or f g => NNF.language f w ∨ NNF.language g w
  | .next f => NNF.language f (fun j => w (j + 1))
  | .until f g =>
    ∃ i, NNF.language g (fun j => w (j + i)) ∧ ∀ k < i, NNF.language f (fun j => w (j + k))
  | .release f g =>
    ∀ i, NNF.language g (fun j => w (j + i)) ∨ ∃ k < i, NNF.language f (fun j => w (j + k))
namespace LTL
def toNNFCore {AP} : Bool → LTL AP → NNF AP
  | false, .atom p => .atom p
  | true, .atom p => .not_atom p
  | false, .not f => toNNFCore true f
  | true, .not f => toNNFCore false f
  | false, .or f g => .or (toNNFCore false f) (toNNFCore false g)
  | true, .or f g => .and (toNNFCore true f) (toNNFCore true g)
  | false, .next f => .next (toNNFCore false f)
  | true, .next f => .next (toNNFCore true f)
  | false, .until f g => .until (toNNFCore false f) (toNNFCore false g)
  | true, .until f g => .release (toNNFCore true f) (toNNFCore true g)
def toNNF {AP} (f : LTL AP) : NNF AP := toNNFCore false f
def toNNFNeg {AP} (f : LTL AP) : NNF AP := toNNFCore true f
end LTL
end LeanModelChecking


