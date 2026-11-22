-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
-- name    : LeanPool_DeciSigma1_Full_Closure_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:37:40.311793+00:00
-- url     : https://prove2.me/theorems/6e987a38-cfa9-490a-b440-aaa38a169cd3
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Constraints_holdsT_map
public import Theorems.Thm_DeciSigma1_Constraints_holds_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Full_Models_GroundBound_holds_map
public import Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_nonBottomPrefixes_realize
public import Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_realize_observations
public import Theorems.Thm_DeciSigma1_Full_Models_mem_nonBottomPrefixes_dual
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
attribute [local simp] DeciSigma1.Full.Models.GroundBound.holds_map
attribute [local simp] DeciSigma1.Full.Models.PrefixPair.nonBottomPrefixes_realize
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
namespace DeciSigma1.Full.Closure
open DeciSigma1.Full.Models DeciSigma1.Semantics
variable {n : ℕ}
def leaf (c : Fin n → Bool) (t : Semantics.Tree n) (s : Bool) : Set (List (Fin n)) :=
  {w | HasTopPrefix (Tree.normalize c s t) w}
theorem leaf_minus (c : Fin n → Bool) (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ leaf c t true ↔ w ∉ (nonBottomPrefixes (Tree.normalize c false t)).carrier := by
  classical
  rw [leaf, Set.mem_ofPred, normalize_true]
  have h := mem_nonBottomPrefixes_dual (Tree.dual (Tree.normalize c false t)) w
  simpa using h.not.symm
def ExtensionClosed (A : Set (List (Fin n))) : Prop := ∀ u v, u ∈ A → u ++ v ∈ A
structure LeafPair (n : ℕ) where
  /-- Extension-closed paths for each of the two leaf labels. -/
  cone : Bool → Set (List (Fin n))
  extension : ∀ s, ExtensionClosed (cone s)
  disjoint : ∀ w, w ∈ cone false → w ∈ cone true → False
def LeafPair.toPrefixPair (p : LeafPair n) : PrefixPair n where
  nonBottom := ⟨(p.cone true)ᶜ, fun u v h hu => h (p.extension true u v hu)⟩
  nonTop := ⟨(p.cone false)ᶜ, fun u v h hu => h (p.extension false u v hu)⟩
  cover w := by
    classical
    by_cases hp : w ∈ p.cone false
    · exact Or.inl (fun hm => p.disjoint w hp hm)
    · exact Or.inr hp
noncomputable def decode (c : Fin n → Bool) (p : LeafPair n) : Semantics.Tree n :=
  Tree.normalize c false (PrefixPair.realize p.toPrefixPair)
@[simp] theorem leaf_decode (c : Fin n → Bool) (p : LeafPair n) (s : Bool) :
    leaf c (decode c p) s = p.cone s := by
  classical
  ext w
  cases s with
  | false =>
    change HasTopPrefix (Tree.normalize c false (Tree.normalize c false _)) w ↔ _
    rw [normalize_involutive, (PrefixPair.realize_observations p.toPrefixPair w).2]
    simp [LeafPair.toPrefixPair]
  | true =>
    rw [leaf_minus]
    simp [decode, LeafPair.toPrefixPair]
@[simp] theorem leaf_node_nil (c : Fin n → Bool) (a : Fin n → Semantics.Tree n) (s : Bool) :
    [] ∉ leaf c (Semantics.Tree.node a) s := by
  simp [leaf, HasTopPrefix]
@[simp] theorem leaf_node_cons (c : Fin n → Bool) (a : Fin n → Semantics.Tree n)
    (s : Bool) (i : Fin n) (w : List (Fin n)) :
    i :: w ∈ leaf c (Semantics.Tree.node a) s ↔
      w ∈ leaf c (a i) (Bool.xor s (c i)) := by
  simp only [leaf, Set.mem_ofPred_eq, HasTopPrefix, normalize_node,
    Semantics.Tree.hasLabel_node_cons _ _ _ Sym.top (by decide)]
@[simp] theorem leaf_root_minus (c : Fin n → Bool) (t : Semantics.Tree n) :
    [] ∈ leaf c t true ↔ t = Tree.bot := by
  classical
  rw [leaf_minus]
  simp [nonBottomPrefixes]
@[simp] theorem leaf_root_plus (c : Fin n → Bool) (t : Semantics.Tree n) :
    [] ∈ leaf c t false ↔ t = Tree.top := by
  simp [leaf, HasTopPrefix]
end DeciSigma1.Full.Closure
namespace DeciSigma1.Full.Closure
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ}
abbrev Config (n : ℕ) (V : Type*) := V × Bool × List (Fin n)
def configSet {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n) : Set (Config n V) :=
  {p | p.2.2 ∈ leaf c (ρ p.1) p.2.1}
inductive Move {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) :
    Config n V → Config n V → Prop
  | copyPlus {u v w} : LitT.le u v ∈ Γ → Move c Γ (u, false, w) (v, false, w)
  | copyMinus {u v w} : LitT.le u v ∈ Γ → Move c Γ (v, true, w) (u, true, w)
  | fLePush {a u w} (i : Fin n) : LitT.fLe a u ∈ Γ →
      Move c Γ (a i, c i, w) (u, false, i :: w)
  | fLePop {a u w} (i : Fin n) : LitT.fLe a u ∈ Γ →
      Move c Γ (u, true, i :: w) (a i, !(c i), w)
  | leFPop {u a w} (i : Fin n) : LitT.leF u a ∈ Γ →
      Move c Γ (u, false, i :: w) (a i, c i, w)
  | leFPush {u a w} (i : Fin n) : LitT.leF u a ∈ Γ →
      Move c Γ (a i, !(c i), w) (u, true, i :: w)
inductive Clause {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) :
    Config n V → Config n V → Prop
  | move {p q} : Move c Γ p q → Clause c Γ p q
  | extend (v : V) (s : Bool) (w : List (Fin n)) (i : Fin n) :
      Clause c Γ (v, s, w) (v, s, w ++ [i])
inductive Fact {V : Type*} (Γ : List (LitT n V)) : Config n V → Prop
  | bot {v} : LitT.eqBot v ∈ Γ → Fact Γ (v, true, [])
  | top {v} : LitT.eqTop v ∈ Γ → Fact Γ (v, false, [])
inductive Neg {V : Type*} (Γ : List (LitT n V)) : Config n V → Prop
  | fLe {a u} : LitT.fLe a u ∈ Γ → Neg Γ (u, true, [])
  | leF {u a} : LitT.leF u a ∈ Γ → Neg Γ (u, false, [])
inductive OppositeSigns {V : Type*} : Config n V → Config n V → Prop
  | pair (v : V) (w : List (Fin n)) : OppositeSigns (v, false, w) (v, true, w)
def Closed {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V))
    (S : Set (Config n V)) : Prop := ∀ ⦃p q⦄, Clause c Γ p q → p ∈ S → q ∈ S
def Avoids {V : Type*} (Γ : List (LitT n V)) (S : Set (Config n V)) : Prop :=
  ∀ ⦃p⦄, p ∈ S → ¬ Neg Γ p
def Consistent {V : Type*} (S : Set (Config n V)) : Prop :=
  ∀ ⦃p q⦄, OppositeSigns p q → p ∈ S → q ∈ S → False
structure IsSolution {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V))
    (S : Set (Config n V)) : Prop where
  closed : Closed c Γ S
  facts : ∀ ⦃p⦄, Fact Γ p → p ∈ S
  avoids : Avoids Γ S
  consistent : Consistent S
variable {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
theorem Closed.extension {S : Set (Config n V)} (h : Closed c Γ S)
    (v : V) (s : Bool) : ExtensionClosed {w | (v, s, w) ∈ S} := by
  intro u w hu
  induction w using List.reverseRecOn with
  | nil => simpa using hu
  | append_singleton w i ih =>
    simpa [List.append_assoc] using h (.extend v s (u ++ w) i) ih
noncomputable def assignmentOf (S : Set (Config n V)) (hc : Closed c Γ S)
    (hd : Consistent S) : V → Semantics.Tree n := fun v =>
  decode c ⟨fun s => {w | (v, s, w) ∈ S}, hc.extension v,
    fun w hp hm => hd (.pair v w) hp hm⟩
abbrev Reach (c : Fin n → Bool) (Γ : List (LitT n V)) :=
  Relation.ReflTransGen (Clause c Γ)
def hull (c : Fin n → Bool) (Γ : List (LitT n V)) (A : Set (Config n V)) : Set (Config n V) :=
  {b | ∃ a, (Fact Γ a ∨ a ∈ A) ∧ Reach c Γ a b}
end DeciSigma1.Full.Closure
namespace DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}
abbrev Moves (c : Fin n → Bool) (Γ : List (LitT n V)) :=
  Relation.ReflTransGen (Move c Γ)
def flipC (p : Config n V) : Config n V := (p.1, !p.2.1, p.2.2)
def leastClosure (c : Fin n → Bool) (Γ : List (LitT n V)) : Set (Config n V) := hull c Γ ∅
def seedClosure (c : Fin n → Bool) (Γ : List (LitT n V)) (a : Config n V) : Set (Config n V) :=
  hull c Γ {a}
def Live (c : Fin n → Bool) (Γ : List (LitT n V)) (a : Config n V) : Prop :=
  ∃ S, IsSolution c Γ S ∧ a ∈ S
end DeciSigma1.Full.Closure


