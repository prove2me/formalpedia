-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:09.803106+00:00
-- url     : https://prove2.me/theorems/1b338808-7d86-4475-ad36-664bd9b4b865
-- title:
--   Ch LApply
-- statement:
--   Definitions and structural lemmas for Ch LApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ChLApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace GlobalTheory.PartRed
open GlobalTheory.SplitWeil GlobalTheory.RootEx
section Gen
variable {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
def fillAt (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) : Matrix R Q k :=
  Matrix.of fun r q => if h : (r, q) ∈ I then y ⟨(r, q), h⟩ else if (r, q) ∈ E then β r q else x r q
variable [TopologicalSpace k] [MeasurableSpace k]
def red (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k) : ℂ :=
  ∫ y : I → k, Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) ∂(Measure.pi fun _ => ν)
variable {M : Type} [AddCommGroup M] [Module ℂ M]
def Kills (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) : Prop :=
  ∀ Φ : SB (Matrix R Q k), red ψ ν w β E I Φ.1 = 0 → L Φ = 0
def EvalLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (b : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = (ψ (b * (x e.1 e.2 - β e.1 e.2)) : ℂ) * red ψ ν w β E I Φ.1 x
def IntLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (a : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 a)
end Gen
section Flat
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def chL : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k →ₗ[k] k where
  toFun := ch
  map_add' x y := by simp [ch, Finset.sum_add_distrib]
  map_smul' a x := by simp [ch, Finset.mul_sum]
open Classical in

def fixSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)
open Classical in

def transSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val
open Classical in

def lowSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val
open Classical in

def upSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ
def colIx (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : ℕ := Sum.elim (fun _ => 0) (fun i => i.val) e.2
end Flat
end GlobalTheory.PartRed


