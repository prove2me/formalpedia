-- Prove2me | Definitions.Def_LeanPool_Parikh_GrammarTrees
-- name    : LeanPool_Parikh_GrammarTrees
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:47:48.497104+00:00
-- url     : https://prove2.me/theorems/a951028a-7a54-4bf4-be0a-1265a93c30a6
-- title:
--   Grammar Trees
-- statement:
--   Definitions and structural lemmas for Grammar Trees, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/GrammarTrees.lean

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Set.Finite.List
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
inductive ParseTree (T N : Type*) where
  | terminal (a : T)
  | hole (A : N)
  | node (rule : ContextFreeRule T N) (children : List (ParseTree T N))
namespace ParseTree
variable {T N : Type*}
@[expose] def root : ParseTree T N → Symbol T N
  | .terminal a => .terminal a
  | .hole A => .nonterminal A
  | .node r _ => .nonterminal r.input
@[expose] def frontier : ParseTree T N → List (Symbol T N)
  | .terminal a => [.terminal a]
  | .hole A => [.nonterminal A]
  | .node _ children => (children.map frontier).flatten
@[expose] def yield : ParseTree T N → List T
  | .terminal a => [a]
  | .hole _ => []
  | .node _ children => (children.map yield).flatten
@[expose] def holes : ParseTree T N → List N
  | .terminal _ => []
  | .hole A => [A]
  | .node _ children => (children.map holes).flatten
@[expose] def productionSize : ParseTree T N → ℕ
  | .terminal _ | .hole _ => 0
  | .node _ children => 1 + (children.map productionSize).sum
@[expose] def height : ParseTree T N → ℕ
  | .terminal _ | .hole _ => 0
  | .node _ children => 1 + (children.map height).foldl max 0
@[expose] def productionLabels : ParseTree T N → List N
  | .terminal _ | .hole _ => []
  | .node r children => r.input :: (children.map productionLabels).flatten
@[expose] def support (t : ParseTree T N) : Set N := {A | A ∈ t.productionLabels}
@[expose] def weight [DecidableEq T] (t : ParseTree T N) : Vector T := counts t.yield
@[expose] def labelPaths : ParseTree T N → List (List N)
  | .terminal _ | .hole _ => [[]]
  | .node r children => [r.input] ::
      ((children.map labelPaths).flatten.map (r.input :: ·))
@[expose] def Simple (t : ParseTree T N) : Prop := ∀ path ∈ t.labelPaths, path.Nodup
@[expose] def plug : ParseTree T N → ParseTree T N → ParseTree T N
  | .terminal a, _ => .terminal a
  | .hole _, t => t
  | .node r children, t => .node r (children.map (fun c => plug c t))
@[expose] def subtree : ParseTree T N → List ℕ → Option (ParseTree T N)
  | t, [] => some t
  | .node _ children, i :: q => children[i]?.bind (fun t => subtree t q)
  | _, _ :: _ => none
@[expose] def replaceAt : ParseTree T N → List ℕ → ParseTree T N → Option (ParseTree T N)
  | _, [], replacement => some replacement
  | .node r children, i :: q, replacement => do
      let child ← children[i]?
      let newChild ← replaceAt child q replacement
      return .node r (children.set i newChild)
  | _, _ :: _, _ => none
end ParseTree
variable {T : Type*}
inductive Valid (g : ContextFreeGrammar T) : ParseTree T g.NT → Prop where
  | terminal (a) : Valid g (.terminal a)
  | hole (A) : Valid g (.hole A)
  | node (r children) (rule_mem : r ∈ g.rules)
      (children_valid : ∀ t ∈ children, Valid g t)
      (roots_match : children.map ParseTree.root = r.output) : Valid g (.node r children)
@[expose] def Complete (g : ContextFreeGrammar T) (t : ParseTree T g.NT) : Prop :=
  Valid g t ∧ t.holes = []
@[expose] def OneHole (g : ContextFreeGrammar T) (E : ParseTree T g.NT) (A : g.NT) : Prop :=
  Valid g E ∧ E.holes = [A]
@[expose] def Cycle (g : ContextFreeGrammar T) (C : ParseTree T g.NT) (A : g.NT) : Prop :=
  OneHole g C A ∧ C.root = .nonterminal A ∧ 0 < C.productionSize
@[expose] noncomputable def activeNonterminals (g : ContextFreeGrammar T) : Finset g.NT := by
  classical
  exact {g.initial} ∪ g.rules.biUnion (fun r =>
    {r.input} ∪ (r.output.filterMap fun s => match s with
      | .terminal _ => none
      | .nonterminal A => some A).toFinset)
@[expose] def ActiveOpen (g : ContextFreeGrammar T) (t : ParseTree T g.NT) : Prop :=
  Valid g t ∧ ∀ A ∈ t.holes, A ∈ activeNonterminals g
variable {N : Type*}
namespace ParseTree
end ParseTree
end Parikh


