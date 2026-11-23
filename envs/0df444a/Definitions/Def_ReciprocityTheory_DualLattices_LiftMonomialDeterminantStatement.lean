-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
-- name    : ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:58.135348+00:00
-- url     : https://prove2.me/theorems/567ecc4b-3940-4a01-a0fa-3f29bdc5cc9c
-- title:
--   Lift Monomial Determinant Statement
-- statement:
--   Definitions and structural lemmas for Lift Monomial Determinant Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/LiftMonomialDeterminantStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobeniusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section FrobDefs
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
def xL (D : Lifts H U X) (j : Ix g) (y : Nb p g) : C := algebraMap R C (D.ε j) * D.u j y
def monX (D : Lifts H U X) (α y : Nb p g) : C := ∏ j, xL D j y ^ (α j).val
def valM (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) C := Matrix.of fun y α => monX D α y
def coefX (D : Lifts H U X) (f : Nb p g → C) : Nb p g → C := (valM D)⁻¹ *ᵥ f
def linX (D : Lifts H U X) (f : Nb p g → C) (k : Ix g) : C := coefX D f (Pi.single k 1)
def blockL (D : Lifts H U X) (τ : Fin U.m) : Submodule R (Ix g → R) where
  carrier := {c | ∀ k, D.κ k ≠ τ → c k = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; rfl
  smul_mem' := by intro r a ha k hk; simp [ha k hk]
end FrobDefs
def LiftMonomialDeterminantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X), (valM D).det ≠ 0
def FrobeniusBlockStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    (∀ j l, D.κ l ≠ U.φ (D.κ j) → linX D (fun y => xL D j y ^ p) l = 0) ∧
    ∀ i (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}),
      v (Matrix.of fun j l : {j // D.κ j = i} => linX D (fun y => xL D j.1 y ^ p) (e l).1).det =
        X i ^ p / X (U.φ i)
def FrobeniusLengthBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    (valM D).det ≠ 0 →
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) →
    ∀ (τ : Fin U.m) (N : Submodule R (Ix g → R)) (z : NNReal), N ≤ blockL D τ →
      (∀ c ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier), ∀ k, algebraMap R C (c k) = linX D f k) →
      HasLen v R (blockL D τ ⧸ N.comap (blockL D τ).subtype) z →
      z ≤ v (algebraMap R C (p : R)) ^ U.r τ
end ReciprocityTheory.PGsh.Up


