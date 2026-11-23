-- Prove2me | Definitions.Def_Bdd_Basic
-- name    : Bdd_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:54:38.628977+00:00
-- url     : https://prove2.me/theorems/1c8849f8-fc9b-4e8a-9fd5-1831ade6866c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Eshel Yaron and contributors's pinned Correctness of binary decision diagrams for CNF formulas development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Theorems.Thm_DecisionTree_usesVar_iff
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
instance {α : Type u} [ToString α] : ToString (Vector α k) := ⟨fun v ↦ v.toList.toString⟩
inductive Pointer m where
  | terminal : Bool → Pointer _
  | node : Fin m → Pointer m
deriving Fintype, DecidableEq, Repr, Hashable
instance Pointer.instToString : ToString (Pointer m) := ⟨fun p =>
  match p with
  | .terminal true => "⊤"
  | .terminal false => "⊥"
  | .node j => "→" ++ toString j⟩
inductive Pointer.le : Pointer m → Pointer m → Prop where
  | terminal_le_terminal : b ≤ c → le (terminal b) (terminal c)
  | terminal_le_node : le (terminal b) (node j)
  | node_le_node : j ≤ i → le (node j) (node i)
instance Pointer.instLE : LE (Pointer m) := {le := Pointer.le}
instance Pointer.instDecidableLe : DecidableLE (Pointer m) :=
  fun p q ↦ match p with
  | terminal b => match q with
    | terminal c => match Bool.instDecidableLe b c with
      | isTrue ht => isTrue  (.terminal_le_terminal ht)
      | isFalse hf => isFalse (by intro contra; cases contra; contradiction)
    | node i => isTrue (.terminal_le_node)
  | node j => match q with
    | terminal c => isFalse (by intro contra; contradiction)
    | node i => match Fin.decLe j i with
      | isTrue ht => isTrue (.node_le_node ht)
      | isFalse hf => isFalse (by intro contra; cases contra; contradiction)
open Pointer
structure Node (n) (m) where
  var  : Fin n
  low  : Pointer m
  high : Pointer m
deriving DecidableEq, Repr
instance Node.instToString : ToString (Node n m) := ⟨fun N => "⟨" ++ (toString N.var) ++ ", " ++ (toString N.low) ++ ", " ++ (toString N.high) ++ "⟩"⟩
structure Bdd (n) (m) where
  heap : Vector (Node n m) m
  root : Pointer m
deriving DecidableEq
instance Bdd.instToString : ToString (Bdd n m) := ⟨fun B => "⟨" ++ (toString B.heap) ++ ", " ++ (toString B.root)  ++ "⟩"⟩
open Bdd
inductive Edge (M : Vector (Node n m) m) : Pointer m → Pointer m → Prop where
  | low  : M[j].low  = p → Edge M (node j) p
  | high : M[j].high = p → Edge M (node j) p
lemma not_terminal_edge {q} : ¬ Edge w (terminal b) q := by
  intro contra
  contradiction
def Pointer.toVar (M : Vector (Node n m) m) : Pointer m → Fin n.succ
  | terminal _ => Fin.last n
  | node j     => ⟨M[j].var.1, .trans M[j].var.2 (Nat.lt_add_one n)⟩
@[simp]
lemma Pointer.toVar_terminal_eq {n m} (w : Vector (Node n m) m) : toVar w (terminal b) = ⟨n, Nat.lt_add_one n⟩ := rfl
@[simp]
lemma Pointer.toVar_node_eq {n m} (w : Vector (Node n m) m) {j} : (toVar w (node j)).1 = w[j].var.1 := rfl
@[simp]
def Pointer.MayPrecede (M : Vector (Node n m) m) (p q : Pointer m) := toVar M p < toVar M q
def Pointer.Reachable {n m} (w : Vector (Node n m) m) := Relation.ReflTransGen (Edge w)
@[trans]
theorem Pointer.Reachable.trans (hab : Reachable v a b) (hbc : Reachable v b c) : Reachable v a c := Relation.ReflTransGen.trans hab hbc
abbrev Bdd.RelevantPointer {n m} (B : Bdd n m) := { q // Reachable B.heap B.root q}
instance Bdd.instDecidableEqRelevantPointer : DecidableEq (Bdd.RelevantPointer B) :=
  fun _ _ ↦ decidable_of_iff _ (symm Subtype.ext_iff)
def Bdd.toRelevantPointer {n m} (B : Bdd n m) : B.RelevantPointer :=
  ⟨B.root, Relation.ReflTransGen.refl⟩
@[simp]
abbrev Bdd.RelevantEdge (B : Bdd n m) (p q : B.RelevantPointer) := Edge B.heap p.1 q.1
lemma Bdd.relevantEdge_of_edge_of_reachable  {B : Bdd n m}
    (e : Edge B.heap p q) (hp : Reachable B.heap B.root p) :
  RelevantEdge B ⟨p, hp⟩ ⟨q, .tail hp e⟩ := e
@[simp]
def Bdd.RelevantMayPrecede (B : Bdd n m) (p q : B.RelevantPointer) := MayPrecede B.heap p.1 q.1
def Bdd.Ordered (B : Bdd n m) := Subrelation (RelevantEdge B) (RelevantMayPrecede B)
lemma Bdd.Ordered_of_terminal : Bdd.Ordered ⟨M, terminal b⟩ := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ h
  cases Relation.reflTransGen_swap.mp hp <;> exfalso <;> apply not_terminal_edge <;> assumption
def OBdd n m := { B : Bdd n m // B.Ordered }
attribute [local instance_reducible] OBdd Bdd.Ordered
def OEdge (O U : OBdd n m) := O.1.heap = U.1.heap ∧ Edge O.1.heap O.1.root U.1.root
@[simp]
def Bdd.var {n m} (B : Bdd n m) : Fin n.succ := B.root.toVar B.heap
@[simp]
def OBdd.var {n m} (O : OBdd n m) : Nat := O.1.var
@[simp]
def OBdd.rav {n m} (B : OBdd n m) : Nat := n - B.var
theorem OEdge.flip_wellFounded {n m} : @WellFounded (OBdd n m) (flip OEdge) := by
  refine Subrelation.wf ?_ (InvImage.wf OBdd.rav (Nat.lt_wfRel.wf))
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
  simp_all only
  rw [← h1] at h2
  let ys := y.toRelevantPointer
  let xs : y.RelevantPointer := ⟨x.root, .tail .refl h2⟩
  have h3 : RelevantEdge y ys xs := h2
  apply hy at h3
  simp only [RelevantMayPrecede, Bdd.toRelevantPointer, xs, ys] at h3
  simp only [InvImage, OBdd.rav, OBdd.var, Nat.succ_eq_add_one]
  cases hp : y.root with
  | terminal => rw [hp] at h2; contradiction
  | node j => cases _ : x.root <;> refine Nat.sub_lt_sub_left ?_ ?_ <;> simp_all [toVar]
instance OEdge.instWellFoundedRelation {n m} : WellFoundedRelation (OBdd n m) where
  rel := flip OEdge
  wf  := flip_wellFounded
lemma Bdd.ordered_of_reachable' {B : Bdd n m} :
    B.Ordered → Reachable B.heap B.root p → Ordered ⟨B.heap, p⟩ :=
  fun ho hr x _ _ ↦ ho (Bdd.relevantEdge_of_edge_of_reachable (by simp_all) (.trans hr x.2))
lemma Bdd.ordered_of_reachable {O : OBdd n m} :
    Reachable O.1.heap O.1.root p → Ordered ⟨O.1.heap, p⟩ :=
  fun hp ⟨_, hx⟩ _ _ ↦ O.2 (Bdd.relevantEdge_of_edge_of_reachable (by simp_all) (.trans hp hx))
lemma Bdd.ordered_of_relevant (O : OBdd n m) (S : O.1.RelevantPointer) :
    Ordered {heap := O.1.heap, root := S.1} := ordered_of_reachable S.2
def Bdd.low (B : Bdd n m) : B.root = node j → Bdd n m
  | _ => {heap := B.heap, root := B.heap[j].low}
lemma Bdd.edge_of_low (B : Bdd n m) {h : B.root = node j} : Edge B.heap B.root (B.low h).root := by
  simp only [low, h]
  exact Edge.low rfl
def Bdd.high (B : Bdd n m) : B.root = node j → Bdd n m
  | _ => {heap := B.heap, root := B.heap[j].high}
lemma Bdd.edge_of_high (B : Bdd n m) {h : B.root = node j} : Edge B.heap B.root (B.high h).root := by
  simp only [high, h]
  exact Edge.high rfl
lemma Bdd.reachable_of_edge : Edge M p q → Reachable M p q := Relation.ReflTransGen.tail Relation.ReflTransGen.refl
lemma Bdd.ordered_of_edge {B : Bdd n m} : B.Ordered → Edge B.heap B.root p → Bdd.Ordered ⟨B.heap, p⟩ := by
  exact fun o e ↦ ordered_of_reachable' o (reachable_of_edge e)
lemma Bdd.high_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.high h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge o
  rw [h]
  right
  rfl
lemma Bdd.low_ordered {B : Bdd n m} (h : B.root = node j) : B.Ordered → (B.low h).Ordered := by
  intro o
  apply Bdd.ordered_of_edge o
  rw [h]
  left
  rfl
lemma Bdd.low_heap_eq_heap {B : Bdd n m} {h : B.root = node j} : (B.low h).heap = B.heap := rfl
lemma Bdd.high_heap_eq_heap {B : Bdd n m} {h : B.root = node j} : (B.high h).heap = B.heap := rfl
def OBdd.high (O : OBdd n m) : O.1.root = node j → OBdd n m
  | h => ⟨O.1.high h, Bdd.high_ordered h O.2⟩
def OBdd.low (O : OBdd n m) : O.1.root = node j → OBdd n m
  | h => ⟨O.1.low h, Bdd.low_ordered h O.2⟩
@[simp]
lemma OBdd.low_heap_eq_heap {O : OBdd n m} {h : O.1.root = node j} : (O.low h).1.heap = O.1.heap := rfl
@[simp]
lemma OBdd.high_heap_eq_heap {O : OBdd n m} {h : O.1.root = node j} : (O.high h).1.heap = O.1.heap := rfl
lemma oedge_of_low  {h : O.1.root = node j} : OEdge O (O.low h)  := ⟨rfl, edge_of_low  (h := h)⟩
lemma oedge_of_high {h : O.1.root = node j} : OEdge O (O.high h) := ⟨rfl, edge_of_high (h := h)⟩
def OBdd.toTree (O : OBdd n m) : DecisionTree n :=
  match h : O.1.root with
  | terminal b => .leaf b
  | node j     => .branch O.1.heap[j].var (toTree (O.low h)) (toTree (O.high h))
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
def OBdd.evaluate : OBdd n m → Vector Bool n → Bool := DecisionTree.evaluate ∘ OBdd.toTree
def OBdd.HSimilar (O : OBdd n m) (U : OBdd n m') := O.toTree = U.toTree
def OBdd.Similar : OBdd n m → OBdd n m → Prop := HSimilar
instance OBdd.instDecidableSimilar {n m} : DecidableRel (β := OBdd n m) OBdd.Similar :=
  fun O U ↦ decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [Similar, HSimilar])
instance OBdd.instDecidableHSimilar (O : OBdd n m) (U : OBdd n m') : Decidable (OBdd.HSimilar O U) :=
  decidable_of_decidable_of_iff (show O.toTree = U.toTree ↔ _ by simp [HSimilar])
def OBdd.SimilarRP (O : OBdd n m) (p q : O.1.RelevantPointer) :=
  Similar ⟨{heap := O.1.heap, root := p.1}, ordered_of_reachable p.2⟩
          ⟨{heap := O.1.heap, root := q.1}, ordered_of_reachable q.2⟩
instance OBdd.instDecidableSimilarRP : Decidable (OBdd.SimilarRP O l r) := by
  exact OBdd.instDecidableSimilar _ _
def OBdd.Similar.instEquivalence {n m} : Equivalence (α := OBdd n m) OBdd.Similar := by
  apply InvImage.equivalence
  constructor <;> simp_all [HSimilar]
inductive Pointer.Redundant (M : Vector (Node n m) m) : Pointer m → Prop where
  | red : M[j].low = M[j].high → Redundant M (node j)
instance Pointer.Redundant.instDecidable {n m} (w : Vector (Node n m) m) : DecidablePred (Redundant w) := by
  intro p
  cases p
  case terminal => apply isFalse; intro; contradiction
  case node j =>
    cases decEq w[j].low w[j].high
    case isFalse => apply isFalse; intro contra; cases contra; contradiction
    case isTrue h => exact isTrue ⟨h⟩
def Bdd.NoRedundancy (B : Bdd n m) := ∀ (p : B.RelevantPointer), ¬ Redundant B.heap p.1
def OBdd.Reduced {n m} (O : OBdd n m) : Prop
  -- No redundant pointers.
  := NoRedundancy O.1
  -- Similarity implies pointer-equality.
   ∧ Subrelation (SimilarRP O) (InvImage Eq Subtype.val)
lemma transGen_iff_single_and_reflTransGen : (Relation.TransGen r a b) ↔ ∃ c, r a c ∧ Relation.ReflTransGen r c b := by
  constructor
  case mp =>
    intro h
    apply Relation.transGen_swap.mp at h
    induction h
    case single c e => use b
    case tail a' b' c e ih =>
      use a'
      constructor
      assumption
      rcases ih with ⟨z, h1, h2⟩
      apply Relation.reflTransGen_swap.mp at h2
      apply Relation.reflTransGen_swap.mp
      apply Relation.ReflTransGen.tail h2 h1
  case mpr =>
    rintro ⟨z, h1, h2⟩
    induction h2
    case refl => exact Relation.TransGen.single h1
    case tail a' b' t e ih => exact Relation.TransGen.tail ih e
@[simp]
def RelevantPointer.var {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := p.1.toVar B.heap
@[simp]
def RelevantPointer.gap {n m} {B : Bdd n m} (p : B.RelevantPointer) : Nat := n - (RelevantPointer.var p)
theorem RelevantEdge.flip_wellFounded (o : Ordered B) : WellFounded (flip (RelevantEdge B)) := by
  have : Subrelation (flip (RelevantEdge B)) (InvImage Nat.lt RelevantPointer.gap) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ e
    simp_all only [InvImage, flip, RelevantPointer.gap]
    refine Nat.sub_lt_sub_left ?_ ?_
    cases e <;> simp
    exact o e
  exact Subrelation.wf this (InvImage.wf _ (Nat.lt_wfRel.wf))
instance RelevantEdge.instWellFoundedRelation {n m} (O : OBdd n m) : WellFoundedRelation O.1.RelevantPointer where
  rel := flip O.1.RelevantEdge
  wf  := (RelevantEdge.flip_wellFounded O.2)
@[implicit_reducible]
instance OBdd.instDecidableReflTransGen {n m} (O : OBdd n m) (p : O.1.RelevantPointer) (q) :
    Decidable (Relation.ReflTransGen (Edge O.1.heap) p.1 q) := by
  convert decidable_of_iff _ (symm Relation.reflTransGen_iff_eq_or_transGen)
  convert instDecidableOr
  · exact decEq q p.1
  · convert decidable_of_iff _ (symm transGen_iff_single_and_reflTransGen)
    rcases h : p.1
    case terminal =>
      apply isFalse
      rintro ⟨x, contra1, contra2⟩
      contradiction
    case node j =>
      let low := O.1.heap[j].low
      have hlow : Relation.ReflTransGen (Edge O.1.heap) O.1.root low :=
        Relation.ReflTransGen.tail p.2 (by rw [h]; exact Edge.low rfl)
      cases OBdd.instDecidableReflTransGen O ⟨low, hlow⟩ q
      case isFalse hfl =>
        let high := O.1.heap[j].high
        have hhigh : Relation.ReflTransGen (Edge O.1.heap) O.1.root high :=
          Relation.ReflTransGen.tail p.2 (by rw [h]; exact Edge.high rfl)
        cases OBdd.instDecidableReflTransGen O ⟨high, hhigh⟩ q
        case isFalse hfh =>
          apply isFalse
          rintro ⟨c, contra1, contra2⟩
          simp_all only [Ordered]
          cases contra1
          case low contra =>
            apply hfl
            apply Relation.reflTransGen_swap.mp
            apply Relation.ReflTransGen.tail
            apply Relation.reflTransGen_swap.mpr
            exact contra2
            simp_all only [Ordered, not_true_eq_false, low]
          case high contra =>
            apply hfh
            apply Relation.reflTransGen_swap.mp
            apply Relation.ReflTransGen.tail
            apply Relation.reflTransGen_swap.mpr
            exact contra2
            simp_all only [Ordered, not_true_eq_false, low, high]
        case isTrue hth =>
          apply isTrue
          use high
          constructor
          · simp only [Ordered, high, Edge.high rfl]
          · apply hth
      case isTrue hth =>
        apply isTrue
        use low
        constructor
        · simp only [Ordered, low, Edge.low rfl]
        · apply hth
termination_by p
decreasing_by
  all_goals simp_all only [Ordered, flip, RelevantEdge, Fin.getElem_fin, Edge.low, Edge.high]
instance Pointer.instDecidableReachable {n m} (O : OBdd n m) :
    DecidablePred (Reachable O.1.heap O.1.root) :=
  OBdd.instDecidableReflTransGen O ⟨O.1.root, Relation.ReflTransGen.refl⟩
def OBdd.size {n m} (O : OBdd n m) := Fintype.card { j // Reachable O.1.heap O.1.root (.node j) }
instance OBdd.instFintypeRelevantPointer {n m} (O : OBdd n m) : Fintype (O.1.RelevantPointer) := by
  convert Subtype.fintype _ <;> infer_instance
@[instance_reducible] def Pointer.instDecidableEitherReachable {n m} (O U : OBdd n m) (h : O.1.heap = U.1.heap) :
    DecidablePred (fun q ↦ (Reachable O.1.heap O.1.root q) ∨ (Reachable O.1.heap U.1.root q)) := by
  intro p
  simp
  cases instDecidableReachable O p with
  | isFalse hf =>
    cases instDecidableReachable U p with
    | isFalse hhf =>
      apply isFalse
      simp_all only [or_self, not_false_eq_true]
    | isTrue  hht =>
      apply isTrue
      simp_all only [or_true]
  | isTrue  ht =>
    apply isTrue
    simp_all only [true_or]
@[instance_reducible] def OBdd.instFintypeEitherRelevantPointer (O U : OBdd n m) (h : O.1.heap = U.1.heap) : Fintype {q // Reachable O.1.heap O.1.root q ∨ Reachable O.1.heap U.1.root q} := by
  convert Subtype.fintype _
  · exact instDecidableEitherReachable O U h
  · infer_instance
instance my_decidableRel_of_invImage2 {r : β → β → Prop} [DecidableRel r] {f : α → β} :
    DecidableRel (InvImage r f) :=
  fun a b ↦ decidable_of_decidable_of_iff (show (r (f a) (f b)) ↔ _ by simp [InvImage])
instance OBdd.instReducedDecidable {n m} : DecidablePred (α := OBdd n m) Reduced :=
  fun _ ↦ (instDecidableAnd (dp := Fintype.decidableForallFintype) (dq := Fintype.decidableForallFintype))
def OBdd.isTerminal {n m} (O : OBdd n m) := ∃ b, O.1.root = terminal b
lemma OBdd.reachable_of_edge : Edge w p q → Reachable w p q := Relation.ReflTransGen.tail Relation.ReflTransGen.refl
lemma OBdd.ordered_of_low_edge {j : Fin n} : Bdd.Ordered {heap := v, root := node j} → Bdd.Ordered {heap := v, root := v[j].low} := by
  intro o x y h
  apply ordered_of_relevant ⟨{ heap := v, root := node j }, o⟩ ⟨v[j].low, (reachable_of_edge (Edge.low rfl))⟩
  simpa
lemma OBdd.ordered_of_high_edge {j : Fin n} : Bdd.Ordered {heap := v, root := node j} → Bdd.Ordered {heap := v, root := v[j].high} := by
  intro o x y h
  apply ordered_of_relevant ⟨{ heap := v, root := node j }, o⟩ ⟨v[j].high, (reachable_of_edge (Edge.high rfl))⟩
  simpa
@[simp]
lemma OBdd.evaluate_node {n m} {v : Vector (Node n m) m} {I : Vector Bool n} {j : Fin m} {h} : OBdd.evaluate ⟨{ heap := v, root := node j }, h⟩ I =
    if I[v[j].var]
    then OBdd.evaluate ⟨{ heap := v, root := v[j].high }, OBdd.ordered_of_high_edge h⟩ I
    else OBdd.evaluate ⟨{ heap := v, root := v[j].low }, OBdd.ordered_of_low_edge h⟩ I := by
    -- else OBdd.evaluate ⟨{ heap := v, root := v[j].low }, OBdd.ordered_of_low_edge ordered_of_relevant ⟨{ heap := v, root := node j }, h⟩ ⟨v[j].low, (reachable_of_edge (Edge.low rfl))⟩⟩ I := by
      conv =>
        lhs
        simp only [OBdd.evaluate, Function.comp_apply]
        unfold OBdd.toTree
        simp only [Fin.getElem_fin, Ordered, DecisionTree.evaluate]
      rfl
@[simp]
lemma OBdd.evaluate_terminal {n m} {v : Vector (Node n m) m} {h} : OBdd.evaluate ⟨{ heap := v, root := terminal b }, h⟩ = Function.const _ b := by
  simp only [evaluate, Function.comp_apply, toTree, DecisionTree.evaluate]
  rfl
@[simp]
lemma OBdd.toTree_terminal {n m} {v : Vector (Node n m) m} {h} : OBdd.toTree ⟨{ heap := v, root := terminal b }, h⟩ = .leaf b := by simp [toTree]
lemma OBdd.toTree_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.toTree = .branch O.1.heap[j].var (toTree (O.low h)) (toTree (O.high h)) := by
  conv => lhs; unfold toTree
  split
  next _  heq => rw [h] at heq; contradiction
  next j' heq => rw [h] at heq; injection heq with heq; subst heq; rfl
def OBdd.size' {n m} : OBdd n m → Nat := DecisionTree.size ∘ OBdd.toTree
lemma OBdd.size_node {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) : O.size' = 1 + (O.low h).size' + (O.high h).size' := by
  simp only [size', Function.comp_apply, toTree_node h]
  rfl
def OBdd.HIsomorphism (O : OBdd n m) (U : OBdd n' m') :=
  ∃ (f : O.1.RelevantPointer → U.1.RelevantPointer),
    (Function.Bijective f) ∧
    (∀ (p : O.1.RelevantPointer),
       (∀ j, (h : p.1 = node j) → ∃ i hi, f p = ⟨node i, hi⟩
       ∧ O.1.heap[j].var.1 = U.1.heap[i].var.1
       ∧ f ⟨O.1.heap[j].low , Reachable.trans p.2 (reachable_of_edge (h ▸ Edge.low  rfl))⟩ = ⟨U.1.heap[i].low , Reachable.trans hi (reachable_of_edge (Edge.low  rfl))⟩
       ∧ f ⟨O.1.heap[j].high, Reachable.trans p.2 (reachable_of_edge (h ▸ Edge.high rfl))⟩ = ⟨U.1.heap[i].high, Reachable.trans hi (reachable_of_edge (Edge.high rfl))⟩)
     ∧ (∀ b, p.1 = terminal b → ∃   hb, f p = ⟨terminal b, hb⟩))
def OBdd.Isomorphism : OBdd n m → OBdd n m → Prop := HIsomorphism
def OBdd.RelevantIsomorphism (O : OBdd n m) (p q : O.1.RelevantPointer) :=
  Isomorphism ⟨{heap := O.1.heap, root := p.1}, ordered_of_reachable p.2⟩
              ⟨{heap := O.1.heap, root := q.1}, ordered_of_reachable q.2⟩
def OBdd.Reduced' (O : OBdd n m) : Prop
  -- No redundant pointers.
  := NoRedundancy O.1
  -- Isomorphism implies pointer-equality.
   ∧ Subrelation (RelevantIsomorphism O) (InvImage Eq Subtype.val)
def OBdd.OReachable {n m} := Relation.ReflTransGen (@OEdge n m)
instance OBdd.instFintypeReachableFromNode (O : OBdd n m) (h : O.1.root = node j) : Fintype {q // (q = O.1.root ∨ (Reachable O.1.heap (O.low  h).1.root q ∨ Reachable O.1.heap (O.high h).1.root q))} := by
  convert Subtype.fintype _
  · intro p
    simp only
    cases decEq p O.1.root with
    | isFalse hf =>
      cases instDecidableReachable (O.low h) p with
      | isFalse hhf =>
        cases instDecidableReachable (O.high h) p with
        | isFalse hhhf =>
          apply isFalse
          simp
          exact ⟨hf, hhf, hhhf⟩
        | isTrue hhht =>
          apply isTrue
          right
          right
          assumption
      | isTrue hht =>
        apply isTrue
        right
        left
        assumption
    | isTrue h =>
      apply isTrue
      left
      assumption
  · infer_instance
lemma Pointer.mayPrecede_of_reachable {B : Bdd n m} :
    B.Ordered → Reachable B.heap B.root p → Pointer.toVar B.heap B.root ≤ Pointer.toVar B.heap p := by
  intro ho hp
  induction hp with
  | refl => simp
  | tail r e ih =>
    rename_i b c
    trans toVar B.heap b
    exact ih
    suffices s : B.RelevantMayPrecede ⟨b, r⟩ ⟨c, by trans b; exact r; exact reachable_of_edge e⟩ by
      simp only [RelevantMayPrecede, MayPrecede, Nat.succ_eq_add_one] at s
      omega
    apply ho
    exact e
def Bdd.usesVar (B : Bdd n m) (i : Fin n) := ∃ j, Reachable B.heap B.root (node j) ∧ B.heap[j].var = i
lemma Bdd.usesVar_of_high_usesVar {B : Bdd n m} {h : B.root = node j} :
    (B.high h).usesVar i → B.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (B.high h).root
    · apply reachable_of_edge
      have := edge_of_high (h := h)
      simp_all
    · exact h1
  · simp_all [high_heap_eq_heap]
lemma Bdd.usesVar_of_low_usesVar {B : Bdd n m} {h : B.root = node j} :
    (B.low h).usesVar i → B.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (B.low h).root
    · apply reachable_of_edge
      have := edge_of_low (h := h)
      simp_all
    · exact h1
  · simp_all [low_heap_eq_heap]
lemma OBdd.usesVar_of_high_usesVar {O : OBdd n m} {h : O.1.root = node j} :
    (O.high h).1.usesVar i → O.1.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (O.high h).1.root
    · apply reachable_of_edge
      have := oedge_of_high (h := h)
      simp [OEdge] at this
      assumption
    · exact h1
  · simp_all
lemma OBdd.usesVar_of_low_usesVar {O : OBdd n m} {h : O.1.root = node j} :
    (O.low h).1.usesVar i → O.1.usesVar i := by
  rintro ⟨j, h1, h2⟩
  use j
  constructor
  · trans (O.low h).1.root
    · apply reachable_of_edge
      have := oedge_of_low (h := h)
      simp [OEdge] at this
      assumption
    · exact h1
  · simp_all
lemma OBdd.usesVar_iff (i : Fin n) (O : OBdd n m) : O.1.usesVar i ↔ (∃ j, ∃ (hj : O.1.root = node j), (O.1.heap[j].var = i ∨ ((O.low hj).1.usesVar i ∨ (O.high hj).1.usesVar i))) := by
  constructor
  · rintro ⟨j, hj, hi⟩
    rcases O_def : O with ⟨⟨heap, root⟩, o⟩
    simp_all
    cases root with
    | terminal _ =>
      cases Relation.ReflTransGen.swap _ _ hj with
      | tail _ e => exact False.elim (not_terminal_edge e)
    | node j' =>
      use j', rfl
      cases Relation.ReflTransGen.swap _ _ hj with
      | refl => left; assumption
      | tail r e =>
        cases e with
        | low hl =>
          right
          left
          use j
          simp only [Fin.getElem_fin] at hl
          simp only [Fin.getElem_fin, low, Bdd.low, hl]
          constructor
          · exact Relation.ReflTransGen.swap _ _ r
          · exact hi
        | high hh =>
          right
          right
          use j
          simp only [Fin.getElem_fin] at hh
          simp only [Fin.getElem_fin, high, Bdd.high, hh]
          constructor
          · exact Relation.ReflTransGen.swap _ _ r
          · exact hi
  · rintro ⟨j, hj, h⟩
    cases h with
    | inl h =>
      use j
      rw [hj]
      constructor
      · left
      · exact h
    | inr h =>
      cases h with
      | inl h => exact usesVar_of_low_usesVar h
      | inr h => exact usesVar_of_high_usesVar h
lemma Pointer.eq_terminal_of_reachable : Pointer.Reachable w (.terminal b) p → p = (.terminal b) := by
  intro h
  cases Relation.reflTransGen_swap.mp h with
  | refl => rfl
  | tail => contradiction
lemma Bdd.not_usesVar_of_terminal : ¬ Bdd.usesVar ⟨M, .terminal b⟩ i := by
  simp only [usesVar, not_exists]
  intro j
  simp only [Fin.getElem_fin, not_and]
  intro hr
  apply eq_terminal_of_reachable at hr
  contradiction
lemma Bdd.not_usesVar_of_var_gt {M : Vector (Node n m) m} {j : Fin m} : Bdd.Ordered ⟨M, .node j⟩ → M[j].var > i → ¬ Bdd.usesVar ⟨M, .node j⟩ i := by
  intro o h
  simp only [usesVar, not_exists]
  intro j'
  simp only [Fin.getElem_fin, not_and]
  intro hr
  have := mayPrecede_of_reachable (B := ⟨M, .node j⟩) (p := .node j') o hr
  simp_all only [Fin.getElem_fin, gt_iff_lt, Nat.succ_eq_add_one]
  simp_all only [toVar, Nat.succ_eq_add_one, Fin.getElem_fin, Fin.mk_le_mk, Fin.val_fin_le]
  omega
def usesVar_helper
    (O : OBdd n m) (i : Fin n) (p : Pointer m) (hpr : Pointer.Reachable O.1.heap O.1.root p) :
  StateM
    { s : Std.HashSet (Fin m) //
      ∀ j ∈ s, Pointer.Reachable O.1.heap O.1.root (.node j) ∧ ¬ Bdd.usesVar ⟨O.1.heap, .node j⟩ i }
    (Decidable (Bdd.usesVar ⟨O.1.heap, p⟩ i)) := do
  match (dependent := true) (generalizing := true) hp : p with
  | .terminal b => return isFalse not_usesVar_of_terminal
  | .node j =>
    if hgt : O.1.heap[j].var > i
    then return isFalse (not_usesVar_of_var_gt (Bdd.ordered_of_reachable hpr) hgt)
    else
    if hv : O.1.heap[j].var = i
      then return isTrue ⟨j, .refl, hv⟩
      else
        let s ← get
        if hh : j ∈ s.1
        then return isFalse (s.2 j hh).2
        else
          match ← usesVar_helper O i O.1.heap[j].low (.tail hpr (.low rfl)) with
          | isTrue ht => return isTrue (by apply usesVar_of_low_usesVar; simp only [Bdd.low]; exact ht; rfl)
          | isFalse hf =>
          -- TODO : why is the type annotation needed here? Note that only `←` does not work, for some reason `:= ←` is needed
          let h : Decidable (Bdd.usesVar ⟨O.val.heap, O.val.heap[j].high⟩ i) := ← usesVar_helper O i O.1.heap[j].high (.tail hpr (.high rfl))
            match h with
            | isTrue htt => return isTrue (by apply usesVar_of_high_usesVar; simp only [Bdd.high]; exact htt; rfl)
            | isFalse hff =>
              have : ¬ Bdd.usesVar { heap := O.1.heap, root := node j } i := by
                intro contra
                subst hp
                rw [OBdd.usesVar_iff (O := ⟨⟨O.1.heap, .node j⟩, Bdd.ordered_of_reachable hpr⟩)] at contra
                rcases contra with ⟨j', hj', c⟩
                simp only [node.injEq] at hj'
                subst hj'
                cases c with
                | inl c => simp_all only [Fin.getElem_fin]
                | inr c =>
                  cases c with
                  | inl c => simp_all only [Fin.getElem_fin, OBdd.low, low]
                  | inr c => simp_all only [Fin.getElem_fin, OBdd.high, high]
              set ( ⟨ s.1.insert j,
                      by
                        intro j'
                        rw [Std.HashSet.mem_insert, beq_iff_eq]
                        intro hj'
                        cases hj' with
                        | inl h =>
                          subst h
                          exact ⟨hpr, this⟩
                        | inr h => exact (s.2 j' h)
                    ⟩ : { s : Std.HashSet (Fin m) // ∀ j, j ∈ s → Pointer.Reachable O.1.heap O.1.root (.node j) ∧ ¬ Bdd.usesVar ⟨O.1.heap, .node j⟩ i }
                  )
              return isFalse this
termination_by OBdd.size' (⟨⟨O.1.heap, p⟩, Bdd.ordered_of_reachable hpr⟩ : OBdd n m)
decreasing_by
  · simp [OBdd.size_node, OBdd.low, Bdd.low]; omega
  · simp [OBdd.size_node, OBdd.high, Bdd.high]
instance OBdd.instDecidableUsesVar {O : OBdd n m} : DecidablePred O.1.usesVar :=
  fun i ↦ (usesVar_helper O i O.1.root .refl ⟨Std.HashSet.emptyWithCapacity, by simp⟩).1
def Pointer.equiv (p : Pointer m) (p' : Pointer m') :=
  (∀ b, p = .terminal b → p' = .terminal b) ∧ (∀ j, p = .node j → ∃ (j' : Fin m'), p' = .node j' ∧ j.1 = j'.1)
def Node.equiv (N : Node n m) (N' : Node n' m') :=
  N.var.1 = N'.var.1 ∧ Pointer.equiv N.low N'.low ∧ Pointer.equiv N.high N'.high
namespace RawBdd
def RawPointer := Bool ⊕ Nat
structure RawNode (n) where
  va : Fin n
  lo : RawPointer
  hi : RawPointer
def RawPointer.Bounded (m : Nat) (p : RawPointer) := ∀ {i}, p = .inr i → i < m
def RawPointer.bounded_of_le {p : RawPointer} (hm : p.Bounded m) (h : m ≤ m') : p.Bounded m' := by
  intro i hi
  cases hp : p with
  | inl val => simp_all
  | inr val =>
    have := hm hp
    simp_all
    injection hi with heq
    subst heq
    omega
def RawPointer.cook (p : RawPointer) (h : p.Bounded m) : Pointer m :=
  match p with
  | .inl b => .terminal b
  | .inr i => .node ⟨i, h rfl⟩
def RawPointer.fromPointer : Pointer m → RawPointer
  | .terminal b => .inl b
  | .node j => .inr j.1
def RawNode.Bounded (m : Nat) (N : RawNode n) := N.lo.Bounded m ∧ N.hi.Bounded m
def RawNode.bounded_of_le {N : RawNode n} (hm : N.Bounded m) (h : m ≤ m') : N.Bounded m' :=
  ⟨RawPointer.bounded_of_le hm.1 h, RawPointer.bounded_of_le hm.2 h⟩
def RawNode.cook (N : RawNode n) (h : N.Bounded m) : Node n m := ⟨N.va, N.lo.cook h.1, N.hi.cook h.2⟩
def cook_heap (v : Vector (RawNode n) c) (hh : ∀ i : Fin c, v[i].Bounded i) : Vector (Node n c) c :=
  Vector.ofFn (fun i ↦ v[i].cook (RawNode.bounded_of_le (hh i) (by omega)))
def toVar_or (M : Vector (Node n m) m) : Pointer m → Nat → Nat
  | .terminal _, i => i
  | .node j, _     => M[j].var
end RawBdd


