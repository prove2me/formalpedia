-- Prove2me | Definitions.Def_HajnalSzemeredi_Defs
-- name    : HajnalSzemeredi_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:43:38.706489+00:00
-- url     : https://prove2.me/theorems/7e65fcec-2942-4324-bb5f-e2d4acc0d4e4
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Juan Pablo Traverso Gianini (jtraverso/hajnal-szemeredi; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hajnal-Szemeredi theorem on equitable vertex colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Defs.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Classical Finset
namespace HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
def cls (S : Finset V) (c : V → ℕ) (i : ℕ) : Finset V := S.filter fun v => c v = i
def nbr (S : Finset V) (v : V) : Finset V := S.filter fun w => G.Adj v w
def Proper (S : Finset V) (c : V → ℕ) : Prop := ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → c v ≠ c w
def Into (S : Finset V) (c : V → ℕ) (P : Finset ℕ) : Prop := ∀ v ∈ S, c v ∈ P
def DegLe (S : Finset V) (r : ℕ) : Prop := ∀ v ∈ S, (nbr G S v).card ≤ r
def edgeCount (S : Finset V) : ℕ := (S.offDiag.filter fun p => G.Adj p.1 p.2).card
structure IsEq (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (s : ℕ) : Prop where
  proper : Proper G S c
  into : Into S c P
  card : ∀ i ∈ P, (cls S c i).card = s
structure IsNear (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (s lo hi : ℕ) : Prop where
  proper : Proper G S c
  into : Into S c P
  lo_mem : lo ∈ P
  hi_mem : hi ∈ P
  lo_ne_hi : lo ≠ hi
  card_lo : (cls S c lo).card + 1 = s
  card_hi : (cls S c hi).card = s + 1
  card : ∀ i ∈ P, i ≠ lo → i ≠ hi → (cls S c i).card = s
def Movable (S : Finset V) (c : V → ℕ) (v : V) (j : ℕ) : Prop :=
  ∀ w ∈ cls S c j, ¬ G.Adj v w
def Mov (S : Finset V) (c : V → ℕ) (i j : ℕ) : Prop := ∃ v ∈ cls S c i, Movable G S c v j
def acc (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (lo : ℕ) : Finset ℕ :=
  P.filter fun i => Relation.ReflTransGen (Mov G S c) i lo
variable {G}
section Move
variable {S : Finset V} {c : V → ℕ} {v : V} {j : ℕ}
end Move
end HajnalSzemeredi


