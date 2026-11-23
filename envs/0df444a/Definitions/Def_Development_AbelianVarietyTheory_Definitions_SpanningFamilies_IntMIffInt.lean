-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
-- name    : Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:46.25718+00:00
-- url     : https://prove2.me/theorems/8c9f6f48-38f4-447c-b2dd-30afb4c0be6d
-- title:
--   Int MIff Int
-- statement:
--   Definitions and structural lemmas for Int MIff Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
namespace GlobalTheory.Phase
noncomputable section
def IsMu (c : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ c ^ m = 1
def Ph (c : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ c ^ m = ((‖c‖ : ℝ) : ℂ) ^ m
def Quad {M : Type} [AddCommGroup M] (S : AddSubgroup M) (f : M → ℂ) : Prop :=
  (∀ x ∈ S, IsMu (f x)) ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
    f (x + y + z) * f x * f y * f z = f (x + y) * f (y + z) * f (x + z) * f 0
variable {κ ι : Type} [Fintype κ] [Fintype ι]
open Classical in

def Shape (φ : Matrix κ ι ℚ → ℂ) : Prop :=
  IsSB φ ∧ ∃ (c : ℂ) (a : Matrix κ ι ℚ) (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ),
    Ph c ∧ Quad S f ∧ ∀ x, φ x = if x - a ∈ S then c * f (x - a) else 0
def om (y y' : Matrix κ ι ℚ × Matrix κ ι ℚ) : ℚ := ∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k)
def chr (y x : Matrix κ ι ℚ) : ℂ := cexp (2 * Real.pi * I * ((∑ k, x k ⬝ᵥ y k : ℚ) : ℂ))
structure VacS (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)) (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ)
    (φ : Matrix κ ι ℚ → ℂ) : Prop where
  fg : A.FG
  dual : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, om y y' = m
  norm : ∀ y ∈ A, ‖ε y‖ = 1
  semi : ∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * cexp (Real.pi * I * ((om y y' : ℚ) : ℂ))
  ord : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ A, ε (m • y) = 1
  sb : IsSB φ
  fix : ∀ y ∈ A, ε y • heisS y.1 y.2 φ = φ
def PV (φ : Matrix κ ι ℚ → ℂ) : Prop := (∃ A ε, VacS A ε φ) ∧ ∀ x, Ph (φ x)
variable {n g : ℕ}
def dup (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) : Matrix (Fin 2) (Fin n × Fin g) ℚ → ℂ := fun x =>
  φ (Matrix.of fun k i => x 0 (k, i)) * φ (Matrix.of fun k i => x 1 (k, i))
def blk (n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin n × Fin g) (Fin n × Fin g) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then τ p.2 q.2 else 0
def intPairs (κ ι : Type) : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ) :=
  (AddMonoidHom.prodMap (Int.castAddHom ℚ).mapMatrix (Int.castAddHom ℚ).mapMatrix :
    Matrix κ ι ℤ × Matrix κ ι ℤ →+ Matrix κ ι ℚ × Matrix κ ι ℚ).range
open Classical in

def intInd : Matrix κ ι ℚ → ℂ := fun x => if ∀ k i, ∃ z : ℤ, x k i = z then 1 else 0
end
end GlobalTheory.Phase


