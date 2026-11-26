-- Prove2me | Definitions.Def_BKAR_Forest
-- name    : BKAR_Forest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:01:55.519574+00:00
-- url     : https://prove2.me/theorems/358bd4f1-0961-543d-9564-fbb5fc3d0185
-- title:
--   Forest
-- statement:
--   Definitions and structural lemmas for Forest, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
set_option autoImplicit false
namespace BKAR
abbrev Edge (V : Type*) [DecidableEq V] : Type _ :=
  { e : Sym2 V // ¬ e.IsDiag }
noncomputable instance instFintypeEdge {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype (Edge V) :=
  Fintype.ofFinite (Edge V)
namespace Edge
variable {V} [DecidableEq V]
def mk (i j : V) (hij : i ≠ j) : Edge V :=
  ⟨Sym2.mk i j, by
    intro hdiag
    exact hij ((Sym2.mk_isDiag_iff).mp hdiag)⟩
@[simp]
theorem mk_val (i j : V) (hij : i ≠ j) :
    (mk i j hij : Edge V).val = Sym2.mk i j :=
  rfl
def Between (e : Edge V) (i j : V) : Prop :=
  e.val = Sym2.mk i j
noncomputable def left (e : Edge V) : V :=
  e.val.out.1
noncomputable def right (e : Edge V) : V :=
  e.val.out.2
theorem mk_left_right_eq (e : Edge V) :
    Sym2.mk e.left e.right = e.val := by
  change Sym2.mk e.val.out.1 e.val.out.2 = e.val
  exact e.val.out_eq
theorem between_left_right (e : Edge V) : e.Between e.left e.right :=
  (e.mk_left_right_eq).symm
theorem not_between_self (e : Edge V) (i : V) :
    ¬ e.Between i i := by
  intro h
  exact e.property (by
    rw [Between] at h
    rw [h]
    exact (Sym2.mk_isDiag_iff).mpr rfl)
theorem Between.symm {e : Edge V} {i j : V} (h : e.Between i j) :
    e.Between j i := by
  rw [Between] at h ⊢
  rw [h]
  exact Sym2.eq_swap
end Edge
namespace EdgePath
variable {V} [DecidableEq V]
inductive IsPath (S : Finset (Edge V)) :
    List (Edge V) → V → V → Prop
  | nil (i : V) : IsPath S [] i i
  | cons {i j k : V} {e : Edge V} {γ : List (Edge V)} :
      e ∈ S → e.Between i j → IsPath S γ j k →
        IsPath S (e :: γ) i k
def IsSimplePath (S : Finset (Edge V))
    (γ : List (Edge V)) (i j : V) : Prop :=
  IsPath S γ i j ∧ γ.Nodup
namespace IsPath
theorem edge_mem {S : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j → ∀ e ∈ γ, e ∈ S
  | [], _i, _j, hpath, e, he => by
      cases hpath
      cases he
  | e₀ :: γ, _i, _j, hpath, e, he => by
      cases hpath with
      | cons he₀ _hbetween htail =>
          rw [List.mem_cons] at he
          exact he.elim (fun heq => heq ▸ he₀)
            (fun htail_mem => edge_mem htail e htail_mem)
theorem append {S : Finset (Edge V)} :
    ∀ {γ₁ γ₂ : List (Edge V)} {i j k : V},
      IsPath S γ₁ i j → IsPath S γ₂ j k →
        IsPath S (γ₁ ++ γ₂) i k
  | [], _γ₂, _i, _j, _k, hnil, htail => by
      cases hnil
      exact htail
  | _e :: _γ, _γ₂, _i, _j, _k, hcons, htail₂ => by
      cases hcons with
      | cons he hbetween htail₁ =>
          exact IsPath.cons he hbetween (append htail₁ htail₂)
theorem reverse {S : Finset (Edge V)} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsPath S γ i j → IsPath S γ.reverse j i
  | [], _i, _j, hnil => by
      cases hnil
      exact IsPath.nil _
  | _e :: _γ, _i, _k, hcons => by
      cases hcons with
      | cons he hbetween htail =>
          simpa using
            append (reverse htail)
              (IsPath.cons he hbetween.symm (IsPath.nil _))
end IsPath
namespace IsSimplePath
theorem edge_mem {S : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    ∀ e ∈ γ, e ∈ S :=
  h.1.edge_mem
end IsSimplePath
theorem isSimplePath_empty_iff {γ : List (Edge V)} {i j : V} :
    IsSimplePath (∅ : Finset (Edge V)) γ i j ↔ γ = [] ∧ i = j := by
  constructor
  · intro h
    cases h.1 with
    | nil i =>
        exact ⟨rfl, rfl⟩
    | cons he _hbetween _htail =>
        exact False.elim (Finset.notMem_empty _ he)
  · intro h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨IsPath.nil i, List.nodup_nil⟩
theorem isPath_singleton_tail_nil {e₀ : Edge V} :
    ∀ {γ : List (Edge V)} {i j : V},
      IsSimplePath ({e₀} : Finset (Edge V)) γ i j →
      γ = [] ∨ γ = [e₀]
  | [], _i, _j, _h => Or.inl rfl
  | e :: γ, _i, _j, h => by
      cases h.1 with
      | cons he _hbetween htail =>
          have heq : e = e₀ := Finset.mem_singleton.mp he
          cases γ with
          | nil =>
              exact Or.inr (by simp [heq])
          | cons e' γ' =>
              have he'_mem : e' ∈ ({e₀} : Finset (Edge V)) :=
                htail.edge_mem e' (by simp)
              have heq' : e' = e₀ := Finset.mem_singleton.mp he'_mem
              have hnot : e ∉ e' :: γ' :=
                (List.nodup_cons.mp h.2).1
              exact False.elim (hnot (by simp [heq, heq']))
theorem isSimplePath_singleton_iff {e₀ : Edge V}
    {γ : List (Edge V)} {i j : V} :
    IsSimplePath ({e₀} : Finset (Edge V)) γ i j ↔
      (γ = [] ∧ i = j) ∨ (γ = [e₀] ∧ e₀.Between i j) := by
  constructor
  · intro h
    rcases isPath_singleton_tail_nil h with hnil | hsingle
    · subst γ
      cases h.1
      exact Or.inl ⟨rfl, rfl⟩
    · subst γ
      cases h.1 with
      | cons he hbetween htail =>
          cases htail
          have heq : _ = e₀ := Finset.mem_singleton.mp he
          exact Or.inr ⟨rfl, heq ▸ hbetween⟩
  · intro h
    rcases h with hnil | hsingle
    · rcases hnil with ⟨rfl, rfl⟩
      exact ⟨IsPath.nil i, List.nodup_nil⟩
    · rcases hsingle with ⟨rfl, hbetween⟩
      exact
        ⟨IsPath.cons (Finset.mem_singleton_self e₀) hbetween
          (IsPath.nil j), by simp⟩
end EdgePath
structure AcyclicEdgeSetData {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Edge V)) where
  inSameComponent : V → V → Prop
  isSimplePath : List (Edge V) → V → V → Prop
  pathIn : (i j : V) → inSameComponent i j → List (Edge V)
  pathIn_isSimple :
    ∀ {i j : V} (h : inSameComponent i j), isSimplePath (pathIn i j h) i j
  isSimplePath_iff :
    ∀ {i j : V} {γ : List (Edge V)},
      isSimplePath γ i j ↔ EdgePath.IsSimplePath S γ i j
  sameComponent_of_simplePath :
    ∀ {i j : V} {γ : List (Edge V)}, isSimplePath γ i j → inSameComponent i j
  path_unique :
    ∀ {i j : V} {γ₁ γ₂ : List (Edge V)},
      isSimplePath γ₁ i j → isSimplePath γ₂ i j → γ₁ = γ₂
  path_edges_mem :
    ∀ {i j : V} {γ : List (Edge V)}, isSimplePath γ i j → ∀ e ∈ γ, e ∈ S
  edge_isSimplePath :
    ∀ {e : Edge V}, e ∈ S → isSimplePath [e] e.left e.right
def IsAcyclicEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset (Edge V)) : Prop :=
  Nonempty (AcyclicEdgeSetData S)
namespace IsAcyclicEdgeSet
variable {V} [Fintype V] [DecidableEq V]
end IsAcyclicEdgeSet
namespace AcyclicEdgeSetData
variable {V} [Fintype V] [DecidableEq V]
end AcyclicEdgeSetData
structure ForestIndex (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Edge V)
  acyclic : IsAcyclicEdgeSet edges
namespace ForestIndex
variable {V} [Fintype V] [DecidableEq V]
noncomputable instance instFintype : Fintype (ForestIndex V) := by
  classical
  letI : DecidablePred (fun S : Finset (Edge V) => IsAcyclicEdgeSet S) :=
    fun _ => Classical.propDecidable _
  let e :
      ForestIndex V ≃ {S : Finset (Edge V) // IsAcyclicEdgeSet S} := {
    toFun := fun F => ⟨F.edges, F.acyclic⟩
    invFun := fun S => ⟨S.val, S.property⟩
    left_inv := by
      intro F
      cases F
      rfl
    right_inv := by
      intro S
      cases S
      rfl }
  exact Fintype.ofEquiv {S : Finset (Edge V) // IsAcyclicEdgeSet S} e.symm
noncomputable instance instDecidableEq : DecidableEq (ForestIndex V) :=
  Classical.decEq _
end ForestIndex
structure Forest (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Edge V)
  acyclic : AcyclicEdgeSetData edges
  acyclic_insert_iff' :
    ∀ {i j : V} (hij : i ≠ j), Edge.mk i j hij ∉ edges →
      (IsAcyclicEdgeSet (insert (Edge.mk i j hij) edges) ↔
        ¬ acyclic.inSameComponent i j)
namespace Forest
variable {V} [Fintype V] [DecidableEq V]
def emptyAcyclicEdgeSetData :
    AcyclicEdgeSetData (∅ : Finset (Edge V)) where
  inSameComponent := fun i j => i = j
  isSimplePath := fun γ i j => γ = [] ∧ i = j
  pathIn := fun _ _ _ => []
  pathIn_isSimple := by
    intro i j h
    exact ⟨rfl, h⟩
  isSimplePath_iff := by
    intro i j γ
    constructor
    · intro h
      exact EdgePath.isSimplePath_empty_iff.mpr h
    · intro h
      exact EdgePath.isSimplePath_empty_iff.mp h
  sameComponent_of_simplePath := by
    intro i j γ hγ
    exact hγ.2
  path_unique := by
    intro i j γ₁ γ₂ hγ₁ hγ₂
    rw [hγ₁.1, hγ₂.1]
  path_edges_mem := by
    intro i j γ hγ e he
    rw [hγ.1] at he
    cases he
  edge_isSimplePath := by
    intro e he
    exact False.elim (Finset.notMem_empty e he)
def singletonAcyclicEdgeSetData (e₀ : Edge V) :
    AcyclicEdgeSetData ({e₀} : Finset (Edge V)) where
  inSameComponent := fun i j => i = j ∨ e₀.Between i j
  isSimplePath := fun γ i j =>
    (γ = [] ∧ i = j) ∨ (γ = [e₀] ∧ e₀.Between i j)
  pathIn := fun i j h =>
    if i = j then [] else [e₀]
  pathIn_isSimple := by
    intro i j h
    by_cases hij : i = j
    · rw [if_pos hij]
      exact Or.inl ⟨rfl, hij⟩
    · rw [if_neg hij]
      apply Or.inr
      constructor
      · rfl
      · exact h.elim (fun heq => False.elim (hij heq)) id
  isSimplePath_iff := by
    intro i j γ
    constructor
    · intro h
      exact EdgePath.isSimplePath_singleton_iff.mpr h
    · intro h
      exact EdgePath.isSimplePath_singleton_iff.mp h
  sameComponent_of_simplePath := by
    intro i j γ hγ
    exact hγ.elim (fun hnil => Or.inl hnil.2) (fun hedge => Or.inr hedge.2)
  path_unique := by
    intro i j γ₁ γ₂ hγ₁ hγ₂
    cases hγ₁ with
    | inl hnil₁ =>
        cases hγ₂ with
        | inl hnil₂ =>
            rw [hnil₁.1, hnil₂.1]
        | inr hedge₂ =>
            have hbetween : e₀.Between j j := by
              rw [hnil₁.2] at hedge₂
              exact hedge₂.2
            exact False.elim (e₀.not_between_self j hbetween)
    | inr hedge₁ =>
        cases hγ₂ with
        | inl hnil₂ =>
            have hbetween : e₀.Between j j := by
              rw [hnil₂.2] at hedge₁
              exact hedge₁.2
            exact False.elim (e₀.not_between_self j hbetween)
        | inr hedge₂ =>
            rw [hedge₁.1, hedge₂.1]
  path_edges_mem := by
    intro i j γ hγ e he
    cases hγ with
    | inl hnil =>
        rw [hnil.1] at he
        cases he
    | inr hedge =>
        rw [hedge.1] at he
        rw [List.mem_singleton] at he
        rw [he]
        exact Finset.mem_singleton_self e₀
  edge_isSimplePath := by
    intro e he
    have heq : e = e₀ := Finset.mem_singleton.mp he
    rw [heq]
    exact Or.inr ⟨rfl, e₀.between_left_right⟩
def empty (V : Type*) [Fintype V] [DecidableEq V] : Forest V where
  edges := ∅
  acyclic := emptyAcyclicEdgeSetData
  acyclic_insert_iff' := by
    intro i j hij he
    constructor
    · intro _ hcomp
      exact hij hcomp
    · intro _
      change IsAcyclicEdgeSet ({Edge.mk i j hij} : Finset (Edge V))
      exact ⟨singletonAcyclicEdgeSetData (Edge.mk i j hij)⟩
theorem isAcyclicEdgeSet (F : Forest V) : IsAcyclicEdgeSet F.edges :=
  ⟨F.acyclic⟩
def support (F : Forest V) : ForestIndex V where
  edges := F.edges
  acyclic := F.isAcyclicEdgeSet
def inSameComponent (F : Forest V) (i j : V) : Prop :=
  F.acyclic.inSameComponent i j
noncomputable instance instDecidableInSameComponent (F : Forest V) (i j : V) :
    Decidable (F.inSameComponent i j) :=
  Classical.propDecidable _
def pathInF (F : Forest V) (i j : V) (h : F.inSameComponent i j) :
    List (Edge V) :=
  F.acyclic.pathIn i j h
end Forest
def IsSimplePath {V : Type*} [Fintype V] [DecidableEq V]
    (F : Forest V) (γ : List (Edge V)) (i j : V) : Prop :=
  F.acyclic.isSimplePath γ i j
namespace Forest
variable {V} [Fintype V] [DecidableEq V]
theorem inSameComponent_of_isSimplePath (F : Forest V) {i j : V}
    {γ : List (Edge V)} (hγ : IsSimplePath F γ i j) :
    F.inSameComponent i j :=
  F.acyclic.sameComponent_of_simplePath hγ
theorem edge_isSimplePath (F : Forest V) {e : Edge V} (he : e ∈ F.edges) :
    IsSimplePath F [e] e.left e.right :=
  F.acyclic.edge_isSimplePath he
theorem edge_inSameComponent (F : Forest V) {e : Edge V} (he : e ∈ F.edges) :
    F.inSameComponent e.left e.right :=
  F.inSameComponent_of_isSimplePath (F.edge_isSimplePath he)
structure EdgeExtension (F F' : Forest V) (e₀ : Edge V) where
  new_not_mem : e₀ ∉ F.edges
  edges_eq : F'.edges = insert e₀ F.edges
  old_component :
    ∀ {i j : V}, F.inSameComponent i j → F'.inSameComponent i j
  old_path :
    ∀ {i j : V} (h : F.inSameComponent i j),
      F'.pathInF i j (old_component h) = F.pathInF i j h
  new_path_uses :
    ∀ {i j : V} (_ : ¬ F.inSameComponent i j)
      (hF' : F'.inSameComponent i j), e₀ ∈ F'.pathInF i j hF'
namespace EdgeExtension
variable {F F' : Forest V} {e₀ e : Edge V}
end EdgeExtension
end Forest
namespace ForestIndex
variable {V} [Fintype V] [DecidableEq V]
def singleton (e : Edge V) : ForestIndex V where
  edges := {e}
  acyclic := ⟨Forest.singletonAcyclicEdgeSetData e⟩
end ForestIndex
end BKAR


