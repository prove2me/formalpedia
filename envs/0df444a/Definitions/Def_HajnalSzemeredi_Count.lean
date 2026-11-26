-- Prove2me | Definitions.Def_HajnalSzemeredi_Count
-- name    : HajnalSzemeredi_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:43:55.694066+00:00
-- url     : https://prove2.me/theorems/fb51d53b-991e-4e97-bc1b-3adfeee45c66
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Juan Pablo Traverso Gianini (jtraverso/hajnal-szemeredi; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hajnal-Szemeredi theorem on equitable vertex colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Count.lean

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Classical Finset
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
def part (S : Finset V) (c : V → ℕ) (Q : Finset ℕ) : Finset V := S.filter fun v => c v ∈ Q
def nIn (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (y : V) (W : ℕ) : Finset V :=
  nbr G S y ∩ cls S c W
def IsSolo (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V)
    (z y : V) : Prop :=
  z ∈ S ∧ c z ∈ TU ∧ y ∈ B ∧ nIn G S c y (c z) = {z}
def Sz (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V) (z : V) :
    Finset V := B.filter fun y => IsSolo G S c TU B z y
def Sy (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (TU : Finset ℕ) (B : Finset V) (y : V) :
    Finset V := S.filter fun z => IsSolo G S c TU B z y
structure CountHyp (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (PA PB TU : Finset ℕ)
    (r s : ℕ) : Prop where
  disj : Disjoint PA PB
  cover : ∀ v ∈ S, c v ∈ PA ∪ PB
  sub : TU ⊆ PA
  ne : TU.Nonempty
  card_r : r + 1 = PA.card + PB.card
  deg : DegLe G S r
  size : ∀ W ∈ TU, (cls S c W).card = s
  card_B : (part S c PB).card = PB.card * s + 1
  /-- (2.1) -/
  h21 : ∀ y ∈ part S c PB, ∀ X ∈ PA, (nIn G S c y X).Nonempty
  /-- (2.2) -/
  h22 : ∀ x ∈ S, c x ∈ TU → PA.card ≤ (nbr G (part S c PA) x).card + TU.card + 1
namespace CountHyp
variable {S : Finset V} {c : V → ℕ} {PA PB TU : Finset ℕ} {r s : ℕ}
end CountHyp
end HajnalSzemeredi


