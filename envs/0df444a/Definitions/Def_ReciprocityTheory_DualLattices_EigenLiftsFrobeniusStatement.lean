-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobeniusStatement
-- name    : ReciprocityTheory_DualLattices_EigenLiftsFrobeniusStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:30.663671+00:00
-- url     : https://prove2.me/theorems/c155524d-53de-4b3a-bf22-86c4a7ffdfed
-- title:
--   Eigen Lifts Frobenius Statement
-- statement:
--   Definitions and structural lemmas for Eigen Lifts Frobenius Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenLiftsFrobeniusStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
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
structure Lifts {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) where
  κ : Ix g → Fin U.m
  card_phi : ∀ i, (Finset.univ.filter fun j => κ j = U.φ i).card =
    (Finset.univ.filter fun j => κ j = i).card
  r_zero : ∀ i, (∀ j, κ j ≠ i) → U.r i = 0
  Λ : Matrix (Ix g) (Ix g) R
  Λ_det : IsUnit Λ.det
  Λ_block : ∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j
  ε : Ix g → R
  ε_ne : ∀ j, ε j ≠ 0
  ε_prod : ∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i
  u : Ix g → Nb p g → C
  u_int : ∀ j y, v (u j y) ≤ 1
  u_cong : ∀ j (y : Nb p g), v (u j y - algebraMap R C (∑ k, Λ j k * ((y k).val : R))) < 1
  x_mem : ∀ j, (fun y => algebraMap R C (ε j) * u j y) ∈ augIdeal H.AA.carrier
  s : ℕ
  b : Fin s → O
  eig : ∀ j k (t : TT p g),
    u j (red p g (H.ρ (b k) *ᵥ t)) = algebraMap R C (U.sg (κ j) (b k)) * u j (red p g t)
  frobChar : ∀ j k, U.sg (U.φ (κ j)) (b k) = U.sg (κ j) (b k) ^ p
  sep : ∀ j j', κ j ≠ κ j' → ∃ k, v (algebraMap R C (U.sg (κ j) (b k) - U.sg (κ j') (b k))) = 1
def EigenLiftsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) → Nonempty (Lifts H U X)
def EigenLiftsBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    ∏ i, X i = v (algebraMap R C cp) ^ g → ∀ D : Lifts H U X,
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val)
def EigenLiftsFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)
end ReciprocityTheory.PGsh.Up


