-- Prove2me | Definitions.Def_DeletionCode_SupportComponents
-- name    : DeletionCode_SupportComponents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T04:59:01.211578+00:00
-- url     : https://prove2.me/theorems/00214127-2b8b-4334-8271-08566afaccb8
-- title:
--   Support Components
-- statement:
--   Definitions and structural lemmas for Support Components, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportComponents.lean

import Definitions.Def_DeletionCode_RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
set_option autoImplicit true
namespace DeletionCode.SupportComponents
open Windows RootSelection
abbrev Vertex (L : ℕ) := Fin (L - 1) → Bool
def vertex {B : Type*} (F : Family B) (L : ℕ) (b : B) (side : Bool)
    (i : ℕ) : Vertex L :=
  fun q => F.path b side (i + q.val)
def HasVertex {B : Type*} (F : Family B) (L : ℕ) (b : B) (v : Vertex L) : Prop :=
  ∃ side i, i ≤ F.extra b side + 1 ∧ v = vertex F L b side i
def Edge {B : Type*} (F : Family B) (L : ℕ) (u v : Vertex L) : Prop :=
  ∃ b side i, i ≤ F.extra b side ∧
    u = vertex F L b side i ∧ v = vertex F L b side (i + 1)
def GraphConnected {B : Type*} (F : Family B) (L : ℕ) : Vertex L → Vertex L → Prop :=
  Relation.EqvGen (Edge F L)
def representative {B : Type*} (F : Family B) (L : ℕ) (b : B) : Vertex L :=
  vertex F L b false 0
theorem vertex_eq_iff_agree {B : Type*} (F : Family B) (L : ℕ)
    (a b : B) (sa sb : Bool) (i j : ℕ) :
    vertex F L a sa i = vertex F L b sb j ↔
      Agree (F.path a sa) i (F.path b sb) j (L - 1) := by
  constructor
  · intro h q hq
    exact congrFun h ⟨q, hq⟩
  · intro h
    funext q
    exact h q.val q.isLt
theorem path_connected {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (side : Bool) (i : ℕ) (hi : i ≤ F.extra b side + 1) :
    GraphConnected F L (vertex F L b side 0) (vertex F L b side i) := by
  induction i with
  | zero => exact Relation.EqvGen.refl _
  | succ i ih =>
    have hprev := ih (by omega)
    have he : Edge F L (vertex F L b side i) (vertex F L b side (i + 1)) :=
      ⟨b, side, i, by omega, rfl, rfl⟩
    exact Relation.EqvGen.trans _ _ _ hprev (Relation.EqvGen.rel _ _ he)
theorem representative_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (b : B) (side : Bool) (i : ℕ) (hi : i ≤ F.extra b side + 1) :
    GraphConnected F L (representative F L b) (vertex F L b side i) := by
  cases side with
  | false => exact path_connected F L b false i hi
  | true =>
    change GraphConnected F L (vertex F L b false 0) (vertex F L b true i)
    rw [hstart b]
    exact path_connected F L b true i hi
theorem same_vertex_adjacent {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (a b : B) (v : Vertex L) (ha : HasVertex F L a v) (hb : HasVertex F L b v) :
    F.Adjacent L a b := by
  obtain ⟨sa, i, hi, hai⟩ := ha
  obtain ⟨sb, j, hj, hbj⟩ := hb
  refine ⟨sa, sb, i, j, hi, hj, by omega, by omega, ?_⟩
  exact (vertex_eq_iff_agree F L a b sa sb i j).mp (hai.symm.trans hbj)
theorem edge_owners {B : Type*} (F : Family B) (L : ℕ)
    {u v : Vertex L} (h : Edge F L u v) :
    ∃ b, HasVertex F L b u ∧ HasVertex F L b v := by
  obtain ⟨b, side, i, hi, hu, hv⟩ := h
  exact ⟨b, ⟨side, i, by omega, hu⟩, ⟨side, i + 1, by omega, hv⟩⟩
theorem supported_iff {B : Type*} (F : Family B) (L : ℕ)
    {u v : Vertex L} (h : GraphConnected F L u v) :
    (∃ b, HasVertex F L b u) ↔ (∃ b, HasVertex F L b v) := by
  induction h with
  | rel u v he =>
    obtain ⟨b, hu, hv⟩ := edge_owners F L he
    exact ⟨fun _ => ⟨b, hv⟩, fun _ => ⟨b, hu⟩⟩
  | refl u => exact Iff.rfl
  | symm u v h ih => exact ih.symm
  | trans u v w huv hvw ihu ihv => exact ihu.trans ihv
theorem graph_connected_owners {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    {u v : Vertex L} (h : GraphConnected F L u v) :
    ∀ a b, HasVertex F L a u → HasVertex F L b v → F.Connected L a b := by
  induction h with
  | rel u v he =>
    intro a b ha hb
    obtain ⟨c, hcU, hcV⟩ := edge_owners F L he
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL a c u ha hcU))
      (Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL c b v hcV hb))
  | refl u =>
    intro a b ha hb
    exact Relation.EqvGen.rel _ _ (same_vertex_adjacent F L hL a b u ha hb)
  | symm u v h ih =>
    intro a b ha hb
    exact Relation.EqvGen.symm _ _ (ih b a hb ha)
  | trans u v w huv hvw ihu ihv =>
    intro a b ha hb
    obtain ⟨c, hc⟩ := (supported_iff F L huv).mp ⟨a, ha⟩
    exact Relation.EqvGen.trans _ _ _ (ihu a c ha hc) (ihv c b hc hb)
theorem adjacent_representatives_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    {a b : B} (h : F.Adjacent L a b) :
    GraphConnected F L (representative F L a) (representative F L b) := by
  obtain ⟨sa, sb, i, j, hi, hj, _, _, hagree⟩ := h
  have heq := (vertex_eq_iff_agree F L a b sa sb i j).mpr hagree
  have ha := representative_connected F L hstart a sa i hi
  have hb := representative_connected F L hstart b sb j hj
  rw [heq] at ha
  exact Relation.EqvGen.trans _ _ _ ha (Relation.EqvGen.symm _ _ hb)
theorem connected_iff_graph_connected {B : Type*} (F : Family B) (L : ℕ)
    (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (a b : B) :
    F.Connected L a b ↔
      GraphConnected F L (representative F L a) (representative F L b) := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact adjacent_representatives_connected F L hstart hab
    | refl a => exact Relation.EqvGen.refl _
    | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
  · intro h
    exact graph_connected_owners F L hL h a b
      ⟨false, 0, by omega, rfl⟩ ⟨false, 0, by omega, rfl⟩
def componentSetoid {B : Type*} (F : Family B) (L : ℕ) : Setoid B where
  r := F.Connected L
  iseqv := ⟨fun b => Relation.EqvGen.refl b,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩
def SupportedVertex {B : Type*} (F : Family B) (L : ℕ) :=
  {v : Vertex L // ∃ b, HasVertex F L b v}
def supportedGraphSetoid {B : Type*} (F : Family B) (L : ℕ) :
    Setoid (SupportedVertex F L) where
  r := fun u v => GraphConnected F L u.val v.val
  iseqv := ⟨fun v => Relation.EqvGen.refl v.val,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩
abbrev Components {B : Type*} (F : Family B) (L : ℕ) :=
  Quotient (componentSetoid F L)
abbrev GraphComponents {B : Type*} (F : Family B) (L : ℕ) :=
  Quotient (supportedGraphSetoid F L)
def supportedRepresentative {B : Type*} (F : Family B) (L : ℕ) (b : B) :
    SupportedVertex F L :=
  ⟨representative F L b, b, false, 0, by omega, rfl⟩
def componentMap {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Components F L → GraphComponents F L :=
  Quotient.map (supportedRepresentative F L) (fun a b hab =>
    (connected_iff_graph_connected F L hL hstart a b).mp hab)
theorem componentMap_injective {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Function.Injective (componentMap F L hL hstart) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro a b h
  apply Quotient.sound
  apply (connected_iff_graph_connected F L hL hstart a b).mpr
  exact Quotient.exact h
theorem componentMap_surjective {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Function.Surjective (componentMap F L hL hstart) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  refine ⟨Quotient.mk (componentSetoid F L) b, ?_⟩
  apply Quotient.sound
  change GraphConnected F L (representative F L b) v.val
  rw [hv]
  exact representative_connected F L hstart b side i hi
noncomputable def componentEquiv {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0) :
    Components F L ≃ GraphComponents F L :=
  Equiv.ofBijective (componentMap F L hL hstart)
    ⟨componentMap_injective F L hL hstart, componentMap_surjective F L hL hstart⟩
end DeletionCode.SupportComponents


