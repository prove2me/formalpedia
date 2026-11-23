-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
-- name    : ReciprocityTheory_DualLattices_NearIdentityColengthStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:30.501568+00:00
-- url     : https://prove2.me/theorems/9f4680db-892f-42b6-88d9-1eaedf710b35
-- title:
--   Near Identity Colength Statement
-- statement:
--   Definitions and structural lemmas for Near Identity Colength Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NearIdentityColengthStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
open Matrix
def CharTableStatement : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (e : G ≃ AddChar G K),
    (Matrix.of fun g h : G => e h g).det ^ 2 = (Fintype.card G : K) ^ Fintype.card G ∨
    (Matrix.of fun g h : G => e h g).det ^ 2 = -(Fintype.card G : K) ^ Fintype.card G
def ColengthSumStatement : Prop :=
  ∀ (K : Type) [Field K] (v : Valuation K NNReal) (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (e : G ≃ AddChar G K) (B₁ B₂ : Matrix G G K),
    (Matrix.of fun g h : G => e h g) = B₁ * B₂ᵀ →
    (v B₁.det * v B₂.det) ^ 2 = v (Fintype.card G : K) ^ Fintype.card G
def GaussCongruenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (O : Type) [CommRing O] [IsDomain O] (m : Ideal O) [m.IsPrime]
    (ι : F →+* O ⧸ m) (ω : MulChar F O) (ζ : O),
    Fintype.card F ≠ 2 → ζ ^ p = 1 → (∀ a, Ideal.Quotient.mk m (ω a) = ι a) →
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)
def DigitCountStatement : Prop :=
  ∀ (R : Type) [CommRing R] (p h : ℕ) (e : Fin h → R),
    2 * ∑ α : Fin h → Fin p, ∑ j, ((α j : ℕ) : R) * e j =
      (p : R) ^ h * ((p : R) - 1) * ∑ j, e j
def LinearMonomialBasisStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : ℕ) (k : Type) [Field k] [CharP k p]
    (A : Matrix (Fin h) (Fin h) k), IsUnit A.det →
    ∀ e : (Fin h → Fin p) ≃ (Fin h → ZMod p),
      (Matrix.of fun x y : Fin h → ZMod p =>
        ∏ j, (∑ i, A j i * ZMod.castHom (dvd_refl p) k (x i)) ^ ((e.symm y j : Fin p) : ℕ)).det ≠ 0
def NearIdentityColengthStatement : Prop :=
  ∀ (K : Type) [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι K) (s : ι → K),
    (∀ i j, v (U i j) ≤ 1) → (∀ i j, v (U i j - (1 : Matrix ι ι K) i j) < 1) →
    v (U * Matrix.diagonal s).det = ∏ i, v (s i)
def ColengthZeroStatement : Prop :=
  ∀ (K : Type) [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι K),
    (∀ i j, v (T i j) ≤ 1) → v T.det = 1 → ∀ i j, v (T⁻¹ i j) ≤ 1
end ReciprocityTheory.PGsh


