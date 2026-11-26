-- Prove2me | Definitions.Def_AME125_GraphState
-- name    : AME125_GraphState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:02:29.809601+00:00
-- url     : https://prove2.me/theorems/e6888a93-33fe-4961-871a-2c5398212e06
-- title:
--   Graph State
-- statement:
--   Definitions and structural lemmas for Graph State, from Zayn Blore (zblore/fc-ame-12-5; definitions and statement reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and source headers)'s pinned Existence of a twelve-party absolutely maximally entangled state in local dimension five (AME(12,5)) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean

module
public import Definitions.Def_AME125_Defs
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace AME125
open OpenQuantumProblem35
open scoped Matrix
noncomputable abbrev χ : AddChar (ZMod 5) ℂ := ZMod.stdAddChar
def quad {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (x : Fin n → ZMod 5) : ZMod 5 :=
  ∑ i, ∑ j, U i j * x i * x j
def toZ {n : ℕ} (x : Config n 5) : Fin n → ZMod 5 := x
def configEquiv (n : ℕ) : Config n 5 ≃ (Fin n → ZMod 5) where
  toFun := toZ
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def graphState {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) : StateVector n 5 :=
  mkStateVector fun x ↦ ((5 : ℂ) ^ (n / 2))⁻¹ * χ (quad U (toZ x))
def CutInj {n : ℕ} (S : Matrix (Fin n) (Fin n) (ZMod 5)) (A : Finset (Fin n)) : Prop :=
  ∀ w : Fin n → ZMod 5, (∀ i ∉ A, w i = 0) → (∀ j ∉ A, ∑ i, w i * S i j = 0) → w = 0
def firstHalf (n m : ℕ) : Finset (Fin n) := Finset.univ.filter fun i ↦ i.1 < m
def lift {n m : ℕ} (v : Fin m → ZMod 5) : Fin n → ZMod 5 :=
  fun i ↦ if hi : i.1 < m then v ⟨i.1, hi⟩ else 0
def coeff {n m : ℕ} (hm : m ≤ n) (S : Matrix (Fin n) (Fin n) (ZMod 5)) (d : Fin m → ZMod 5) :
    Fin (n - m) → ZMod 5 :=
  fun k ↦ ∑ i, lift d i * S i (rightIndex hm k)
end AME125


