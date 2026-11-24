-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:18:16.400802+00:00
-- url     : https://prove2.me/theorems/5bfad344-df8b-47b8-81ba-d2334025e17f
-- title:
--   Is Read
-- statement:
--   Definitions and structural lemmas for Is Read, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsRead.lean

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
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.FlatFactor
section Gen
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
def fill (ev it : Finset (m × m')) (β t : Matrix m m' k) (a : {e : m × m' // e ∈ it} → k) : Matrix m m' k :=
  Matrix.of fun r q => if h : (r, q) ∈ it then a ⟨(r, q), h⟩ else if (r, q) ∈ ev then β r q else t r q
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
def red (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (t : Matrix m m' k) : ℂ :=
  ∫ a, Θ (fill ev it β t a) ∂(Measure.pi fun _ => ν)
def KerRed {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (ev it : Finset (m × m')) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : Prop :=
  ∀ Θ : SB (Matrix m m' k), (∀ t, red ν ev it β Θ.1 t = 0) → l Θ = 0
end Gen
section Pos
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)
open Classical in

def evC : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e =>
    (∃ i, e.2 = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l, e.1 = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, e.2 = Sum.inr i → i.val = ρ)
open Classical in

def itB : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ ≤ i.val
def IsRead : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → Prop
  | (.inl _, .inl _) => True
  | (.inl _, .inr i) => i.val = ρ
  | (.inr _, _) => False
open Classical in

def evAll : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ¬ Free (ρ + 1) e ∧ ¬ IsRead n n' c ρ e
open Classical in

def itFree : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e
variable {n n' c}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def TwLaw {M : Type} [AddCommGroup M] [Module ℂ M] (ψ : AddChar k Circle)
    (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M) : Prop :=
  ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ i j : Fin c, i.val < ρ → ρ ≤ j.val → u.val i j = 0) →
    ∀ Θ Θ' Θ'' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ t, Θ'.1 t = Θ.1 (((embA n u)⁻¹).val * t)) →
      (∀ t, Θ''.1 t = (ψ (ch ((embA n u).val * t) - ch t) : ℂ) * Θ.1 t) →
      l Θ' = (ψ (-simpleSum (embA n u)) : ℂ) • l Θ''
end Pos
end GlobalTheory.FlatFactor


