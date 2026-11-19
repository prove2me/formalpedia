-- Prove2me | Definitions.Def_DeletionCode_SignedSupport
-- name    : DeletionCode_SignedSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:07:33.975602+00:00
-- url     : https://prove2.me/theorems/cba91061-b7e0-4247-82b5-eedcc7f4462e
-- title:
--   Signed Support
-- statement:
--   Definitions and structural lemmas for Signed Support, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
set_option autoImplicit true
namespace DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
abbrev Gram (L : ℕ) := Fin L → Bool
def gram (p : Letters) (L i : ℕ) : Gram L := fun q => p (i + q.val)
def windowSet (p : Letters) (L D : ℕ) : Set (Gram L) :=
  Set.range (fun i : Fin (D + 1) => gram p L i.val)
noncomputable def pathSpectrum (p : Letters) (L D : ℕ) (g : Gram L) : ℤ := by
  classical
  exact ∑ i : Fin (D + 1), if gram p L i.val = g then 1 else 0
noncomputable def wordSpectrum (x : Letters) (n L : ℕ) (g : Gram L) : ℤ := by
  classical
  exact ∑ i : Fin (n + 1), if i.val + L ≤ n ∧ gram x L i.val = g then 1 else 0
structure BubbleGeometry {B : Type*} (F : Family B) (L : ℕ) : Prop where
  simple : ∀ b side, Function.Injective
    (fun i : Fin (F.extra b side + 2) => SupportComponents.vertex F L b side i.val)
  endpoints : ∀ b i j, i ≤ F.extra b false + 1 → j ≤ F.extra b true + 1 →
    SupportComponents.vertex F L b false i = SupportComponents.vertex F L b true j →
      (i = 0 ∧ j = 0) ∨ (i = F.extra b false + 1 ∧ j = F.extra b true + 1)
  differentLengths : ∀ b, F.extra b false ≠ F.extra b true
noncomputable def bubbleSpectrum {B : Type*} (F : Family B) (L : ℕ)
    (b : B) (g : Gram L) : ℤ :=
  pathSpectrum (F.path b true) L (F.extra b true) g -
    pathSpectrum (F.path b false) L (F.extra b false) g
def HasGram {B : Type*} (F : Family B) (L : ℕ) (b : B) (g : Gram L) : Prop :=
  ∃ side, g ∈ windowSet (F.path b side) L (F.extra b side)
def VertexDisjointOn {B : Type*} (F : Family B) (L : ℕ) (S : Finset B) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ sa sb i j,
    i ≤ F.extra a sa + 1 → j ≤ F.extra b sb + 1 →
    SupportComponents.vertex F L a sa i ≠ SupportComponents.vertex F L b sb j
noncomputable def ruleSpectrum {B : Type*} (F : Family B) (L : ℕ)
    (S : Finset B) (g : Gram L) : ℤ :=
  ∑ b ∈ S, bubbleSpectrum F L b g
def ruleBubbles {B : Type*} [Fintype B] (F : Family B) (i : ℕ) : Finset B :=
  Finset.univ.filter (fun b => F.rank b = i)
def SignedGenerating {B : Type*} [Fintype B] (F : Family B)
    (x : Letters) (n L : ℕ) : Prop :=
  ∀ i g, ruleSpectrum F L (ruleBubbles F i) g = -1 →
    wordSpectrum x n L g ≠ 0 ∨
      ∃ j, j < i ∧ ruleSpectrum F L (ruleBubbles F j) g ≠ 0
def gramPrefix {L : ℕ} (g : Gram L) : SupportComponents.Vertex L :=
  fun q => g ⟨q.val, by have := q.isLt; omega⟩
def gramSuffix {L : ℕ} (g : Gram L) : SupportComponents.Vertex L :=
  fun q => g ⟨q.val + 1, by have := q.isLt; omega⟩
def signedSupportEdge {B : Type*} [Fintype B] (F : Family B) (L : ℕ)
    (u v : SupportComponents.Vertex L) : Prop :=
  ∃ (i : ℕ) (g : Gram L), ruleSpectrum F L (ruleBubbles F i) g ≠ 0 ∧
    u = gramPrefix g ∧ v = gramSuffix g
def SignedGraphConnected {B : Type*} [Fintype B] (F : Family B) (L : ℕ) :
    SupportComponents.Vertex L → SupportComponents.Vertex L → Prop :=
  Relation.EqvGen (signedSupportEdge F L)
def signedSupportedGraphSetoid {B : Type*} [Fintype B] (F : Family B) (L : ℕ) :
    Setoid (SupportComponents.SupportedVertex F L) where
  r := fun u v => SignedGraphConnected F L u.val v.val
  iseqv := ⟨fun v => Relation.EqvGen.refl v.val,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩
end DeletionCode.SignedSupport


