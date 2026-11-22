-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
-- name    : LeanPool_DeciSigma1_Full_Models_Observations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:18:37.835798+00:00
-- url     : https://prove2.me/theorems/54761933-fc1d-41dc-8ea2-3606689f1a0b
-- title:
--   Observations
-- statement:
--   Definitions and structural lemmas for Observations, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_dual
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_node
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_normalize
public import Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_bot_le
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_node
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_node_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_hasLabel_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_le_top
public import Theorems.Thm_DeciSigma1_Semantics_Tree_node_le_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_top_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_bot
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_cons
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_nil
public import Theorems.Thm_DeciSigma1_Semantics_Tree_trace_top
public import Theorems.Thm_DeciSigma1_Semantics_bot_treeLe
public import Theorems.Thm_DeciSigma1_Semantics_dual_bot
public import Theorems.Thm_DeciSigma1_Semantics_dual_fn
public import Theorems.Thm_DeciSigma1_Semantics_dual_involutive
public import Theorems.Thm_DeciSigma1_Semantics_dual_le_iff
public import Theorems.Thm_DeciSigma1_Semantics_dual_node
public import Theorems.Thm_DeciSigma1_Semantics_dual_top
public import Theorems.Thm_DeciSigma1_Semantics_node_treeLe_node_iff
public import Theorems.Thm_DeciSigma1_Semantics_normalize_bot
public import Theorems.Thm_DeciSigma1_Semantics_normalize_false_variance
public import Theorems.Thm_DeciSigma1_Semantics_normalize_fn
public import Theorems.Thm_DeciSigma1_Semantics_normalize_involutive
public import Theorems.Thm_DeciSigma1_Semantics_normalize_node
public import Theorems.Thm_DeciSigma1_Semantics_normalize_top
public import Theorems.Thm_DeciSigma1_Semantics_normalize_true
public import Theorems.Thm_DeciSigma1_Semantics_top_treeLe_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_bot_iff
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_top
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Constraints.holdsT_map
attribute [local simp] DeciSigma1.Constraints.holds_false
attribute [local simp] DeciSigma1.Constraints.sat_false
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_bot
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_dual
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_node
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_normalize
attribute [local simp] DeciSigma1.Semantics.FTree.toTree_top
attribute [local simp] DeciSigma1.Semantics.Tree.bot_le
attribute [local simp] DeciSigma1.Semantics.Tree.descend_bot
attribute [local simp] DeciSigma1.Semantics.Tree.descend_node
attribute [local simp] DeciSigma1.Semantics.Tree.descend_top
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_bot
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_nil
attribute [local simp] DeciSigma1.Semantics.Tree.hasLabel_top
attribute [local simp] DeciSigma1.Semantics.Tree.le_bot_iff
attribute [local simp] DeciSigma1.Semantics.Tree.le_top
attribute [local simp] DeciSigma1.Semantics.Tree.node_le_node_iff
attribute [local simp] DeciSigma1.Semantics.Tree.top_le_iff
attribute [local simp] DeciSigma1.Semantics.Tree.trace_bot
attribute [local simp] DeciSigma1.Semantics.Tree.trace_cons
attribute [local simp] DeciSigma1.Semantics.Tree.trace_nil
attribute [local simp] DeciSigma1.Semantics.Tree.trace_top
attribute [local simp] DeciSigma1.Semantics.bot_treeLe
attribute [local simp] DeciSigma1.Semantics.dual_bot
attribute [local simp] DeciSigma1.Semantics.dual_fn
attribute [local simp] DeciSigma1.Semantics.dual_involutive
attribute [local simp] DeciSigma1.Semantics.dual_le_iff
attribute [local simp] DeciSigma1.Semantics.dual_node
attribute [local simp] DeciSigma1.Semantics.dual_top
attribute [local simp] DeciSigma1.Semantics.node_treeLe_node_iff
attribute [local simp] DeciSigma1.Semantics.normalize_bot
attribute [local simp] DeciSigma1.Semantics.normalize_false_variance
attribute [local simp] DeciSigma1.Semantics.normalize_fn
attribute [local simp] DeciSigma1.Semantics.normalize_involutive
attribute [local simp] DeciSigma1.Semantics.normalize_node
attribute [local simp] DeciSigma1.Semantics.normalize_top
attribute [local simp] DeciSigma1.Semantics.normalize_true
attribute [local simp] DeciSigma1.Semantics.top_treeLe_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_bot_iff
attribute [local simp] DeciSigma1.Semantics.treeLe_false_iff_le
attribute [local simp] DeciSigma1.Semantics.treeLe_top
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
def HasTopPrefix (t : Semantics.Tree n) (w : List (Fin n)) : Prop :=
  Semantics.Tree.HasLabel t w Sym.top
def nonBottomPrefixes (t : Semantics.Tree n) : PrefixSet n where
  carrier := {w | ¬ Semantics.Tree.HasLabel t w Sym.bot}
  prefix_closed := by
    rintro u v h ⟨p, ⟨s, hs⟩, hp⟩
    apply h
    exact ⟨p, ⟨s ++ v, by simpa only [List.append_assoc] using congrArg (fun q => q ++ v) hs⟩, hp⟩
@[simp] theorem mem_nonBottomPrefixes (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ (nonBottomPrefixes t).carrier ↔ ¬ Semantics.Tree.HasLabel t w Sym.bot := Iff.rfl
@[simp] theorem not_hasTopPrefix_bot (w : List (Fin n)) :
    ¬ HasTopPrefix Tree.bot w := by simp [HasTopPrefix]
@[simp] theorem hasTopPrefix_top (w : List (Fin n)) :
    HasTopPrefix Tree.top w := by simp [HasTopPrefix]
@[simp] theorem nonBottomPrefixes_bot :
    nonBottomPrefixes (Tree.bot : Semantics.Tree n) = PrefixSet.bot := by ext w; simp
@[simp] theorem nonBottomPrefixes_top :
    nonBottomPrefixes (Tree.top : Semantics.Tree n) = PrefixSet.univ := by ext w; simp
@[simp] theorem nonBottomPrefixes_node (a : Fin n → Semantics.Tree n) :
    nonBottomPrefixes (Semantics.Tree.node a) = PrefixSet.node (nonBottomPrefixes ∘ a) := by
  ext w
  cases w with
  | nil => simp [Semantics.Tree.HasLabel]
  | cons i w =>
      simp [Semantics.Tree.hasLabel_node_cons _ _ _ Sym.bot (by decide)]
structure PrefixPair (n : ℕ) where
  /-- Paths whose prefixes carry no bottom label. -/
  nonBottom : PrefixSet n
  /-- Paths whose prefixes carry no top label. -/
  nonTop : PrefixSet n
  cover : ∀ w, w ∈ nonBottom.carrier ∨ w ∈ nonTop.carrier
def PrefixPair.child (p : PrefixPair n) (b : Fin n) : PrefixPair n :=
  ⟨p.nonBottom.subtree b, p.nonTop.subtree b, fun w => p.cover (b :: w)⟩
attribute [local instance] Classical.propDecidable
noncomputable def pairFn (p : PrefixPair n) : List (Fin n) → Option Semantics.Sym
  | [] => if [] ∉ p.nonBottom.carrier then some Sym.bot else
      if [] ∉ p.nonTop.carrier then some Sym.top else some Sym.f
  | b :: w =>
      if [] ∈ p.nonBottom.carrier ∧ [] ∈ p.nonTop.carrier then pairFn (p.child b) w else none
theorem pairFn_child (p : PrefixPair n) (w : List (Fin n)) (b : Fin n) :
    (pairFn p (w ++ [b])).isSome ↔ pairFn p w = some Sym.f := by
  classical
  induction w generalizing p with
  | nil => simp only [List.nil_append, pairFn]; split_ifs <;> simp_all
  | cons a w ih =>
    simp only [List.cons_append, pairFn]
    split_ifs <;> simp_all
noncomputable def PrefixPair.realize (p : PrefixPair n) : Semantics.Tree n where
  fn := pairFn p
  wf := by
    constructor
    · classical
      simp only [pairFn]
      split_ifs <;> simp
    · exact pairFn_child p
end DeciSigma1.Full.Models
namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
structure Observation (n : ℕ) (X : Type*) where
  /-- Whether to observe the dual of the selected tree. -/
  dual : Bool
  /-- Variable whose tree is observed. -/
  var : X
  /-- Path at which the leaf observation is made. -/
  word : List (Fin n)
  /-- Required Boolean leaf label. -/
  value : Bool
def Observation.Holds {X : Type*} (ρ : X → Semantics.Tree n) (o : Observation n X) : Prop :=
  let t := if o.dual then Tree.dual (ρ o.var) else ρ o.var
  if o.value then o.word ∈ (nonBottomPrefixes t).carrier else o.word ∉ (nonBottomPrefixes t).carrier
structure GroundBound (n : ℕ) (V : Type*) where
  /-- Variable constrained by the finite tree. -/
  var : V
  /-- True for a lower bound; false for an upper bound. -/
  lower : Bool
  /-- Finite tree giving the bound. -/
  tree : FTree n
def GroundBound.Holds {V : Type*} (ρ : V → Semantics.Tree n) (b : GroundBound n V) : Prop :=
  if b.lower then b.tree.toTree ≤ ρ b.var else ρ b.var ≤ b.tree.toTree
end DeciSigma1.Full.Models
namespace DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}
def pathBound : List (Fin n) → FTree n → FTree n
  | [], g => g
  | i :: w, g => .node (fun j => if j = i then pathBound w g else .bot)
def GroundBound.map {V W : Type*} (f : V → W) (b : GroundBound n V) : GroundBound n W :=
  ⟨f b.var, b.lower, b.tree⟩
def Observation.bound {V : Type*} (o : Observation n V) : GroundBound n V :=
  match o.dual, o.value with
  | false, true => ⟨o.var, true, pathBound o.word (.node (fun _ => .bot))⟩
  | false, false => ⟨o.var, false, (pathBound o.word .top).dual⟩
  | true, true => ⟨o.var, false, (pathBound o.word (.node (fun _ => .bot))).dual⟩
  | true, false => ⟨o.var, true, pathBound o.word .top⟩
end DeciSigma1.Full.Models
namespace DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ}
def RegularTop (t : Semantics.Tree n) : Prop := (Characterization.subtrees t).Finite
def FiniteTop (t : Semantics.Tree n) : Prop := ∃ g : FTree n, g.toTree = t
def SatisfiableIn {V : Type*} (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) : Prop :=
  ∃ ρ, (∀ v, C (ρ v)) ∧ SatT c ρ Γ
abbrev SatFin {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop c Γ
def FiniteBoundPinning {V : Type*} (Γ : List (LitT n V)) : Prop :=
  SatisfiableIn FiniteTop (fun _ => false) Γ →
    ∀ B : List (GroundBound n V),
      (∃ ρ, SatT (fun _ => false) ρ Γ ∧ ∀ b ∈ B, b.Holds ρ) →
      ∃ τ, (∀ v, FiniteTop (τ v)) ∧ SatT (fun _ => false) τ Γ ∧
        ∀ b ∈ B, b.Holds τ
end DeciSigma1.Full.Models


