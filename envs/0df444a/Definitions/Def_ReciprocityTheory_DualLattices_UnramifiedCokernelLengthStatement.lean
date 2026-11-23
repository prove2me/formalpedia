-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthStatement
-- name    : ReciprocityTheory_DualLattices_UnramifiedCokernelLengthStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:14.138802+00:00
-- url     : https://prove2.me/theorems/a55ad692-777f-435f-9894-7ffb8933a15d
-- title:
--   Unramified Cokernel Length Statement
-- statement:
--   Definitions and structural lemmas for Unramified Cokernel Length Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UnramifiedCokernelLengthStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
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
abbrev cokE {g : ℕ} {R : Type} [CommRing R] {m : ℕ} (Ht : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :=
  LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT j))).map (Matrix.mulVecLin Ht)).comap
      (LinearMap.range (Matrix.mulVecLin (εL i)ᵀ)).subtype
structure UnramData (p : ℕ) [Fact p.Prime] (g : ℕ) {C : Type} [Field C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O]
    [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) (H : HodgeTateDatum p g v R O σ cp) where
  m : ℕ
  sg : Fin m → (O →+* R)
  εT : Fin m → Matrix (Ix g) (Ix g) R
  εL : Fin m → Matrix (Fin g) (Fin g) R
  cj : Equiv.Perm (Fin m)
  φ : Equiv.Perm (Fin m)
  r : Fin m → ℕ
  noPad : H.P = 0 ∧ H.PL = 0
  εT_orth : ∀ i j, εT i * εT j = if i = j then εT i else 0
  εT_sum : ∑ i, εT i = 1
  εL_orth : ∀ i j, εL i * εL j = if i = j then εL i else 0
  εL_sum : ∑ i, εL i = 1
  εT_eig : ∀ a i, (H.ρ a).map (algebraMap ℤ_[p] R) * εT i = sg i a • εT i
  εL_eig : ∀ a i, H.ρL a * εL i = sg i a • εL i
  conj : ∀ i a, sg (cj i) a = sg i (σ a)
  frob : ∀ i a, v (algebraMap R C (sg (φ i) a - sg i a ^ p)) < 1
  distinct : ∀ i j, i ≠ j → ∃ a, v (algebraMap R C (sg i a - sg j a)) = 1
  rank : ∀ i, Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin (r i) → R))
def frobSum {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) : ℝ :=
  ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * U.r ((U.φ ^ (n + 1)) i)
def UnramifiedCokernelLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (V1 V2 : NNReal),
    HasLen v R (cokE H.Ht U.εT U.εL i (U.cj i)) V1 →
    HasLen v R (cokE H.Ht U.εT U.εL (U.cj i) i) V2 →
    (V1 : ℝ) = V2 * (v (algebraMap R C (p : R)) : ℝ) ^
      ((U.r i : ℝ) / (p - 1) - frobSum U i)
end ReciprocityTheory.PGsh.Up


