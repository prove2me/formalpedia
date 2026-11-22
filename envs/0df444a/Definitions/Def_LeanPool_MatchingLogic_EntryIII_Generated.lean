-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Generated
-- name    : LeanPool_MatchingLogic_EntryIII_Generated
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:25:07.803312+00:00
-- url     : https://prove2.me/theorems/dfae4cf5-5022-4d2b-bc67-dcb2517b3be3
-- title:
--   Generated
-- statement:
--   Definitions and structural lemmas for Generated, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Generated.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
public import Theorems.Thm_MatchingLogic_Pattern_AlphaEq_refl

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
local instance instDecidableEqPatternNatGenerated : DecidableEq (Pattern S Nat) :=
  Classical.decEq _
namespace AppCtx
def comp {Var : Type} (outer inner : AppCtx S Var) : AppCtx S Var :=
  match outer with
  | .hole => inner
  | .node sigma i args tail => .node sigma i args (comp tail inner)
end AppCtx
def canonicalStep (parent child : CanonicalCarrier S) : Prop :=
  ∃ (sigma : S.Sym)
    (components : Fin (S.arity sigma) → CanonicalCarrier S)
    (i : Fin (S.arity sigma)),
    parent ∈ canonicalInterp sigma components ∧ child = components i
def Generated (root world : CanonicalCarrier S) : Prop :=
  Relation.ReflTransGen canonicalStep root world
abbrev GeneratedCarrier (root : CanonicalCarrier S) :=
  {world : CanonicalCarrier S // Generated root world}
namespace GeneratedCarrier
end GeneratedCarrier
def generatedRoot (root : CanonicalCarrier S) : GeneratedCarrier root :=
  ⟨root, Relation.ReflTransGen.refl⟩
def generatedInterp (root : CanonicalCarrier S) (sigma : S.Sym)
    (components : Fin (S.arity sigma) → GeneratedCarrier root) :
    Set (GeneratedCarrier root) :=
  {world | world.val ∈ canonicalInterp sigma (fun i => (components i).val)}
abbrev generatedModel (root : CanonicalCarrier S) : Model S where
  carrier := GeneratedCarrier root
  nonempty := ⟨generatedRoot root⟩
  interp := generatedInterp root
inductive GeneratingPath (root : CanonicalCarrier S) :
    CanonicalCarrier S → List (Coord S) → Prop
  | root : GeneratingPath root root []
  | tail {parent : CanonicalCarrier S} {path : List (Coord S)}
      {sigma : S.Sym}
      {components : Fin (S.arity sigma) → CanonicalCarrier S}
      {i : Fin (S.arity sigma)} :
      GeneratingPath root parent path →
      parent ∈ canonicalInterp sigma components →
      GeneratingPath root (components i) (path ++ [⟨sigma, i⟩])
def generatingStepContext (e : Coord S) : AppCtx S Nat :=
  .node e.1 e.2 (fun _ => Pattern.tp) .hole
def generatingContext (path : List (Coord S)) : AppCtx S Nat :=
  path.foldl (fun C e => C.comp (generatingStepContext e)) .hole
end
end MatchingLogic


