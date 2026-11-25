-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
-- name    : ReciprocityTheory_DualLattices_EigenLiftsFrobenius
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:12.090659+00:00
-- url     : https://prove2.me/theorems/c7439bc8-9923-5a16-9870-d2214782f874
-- title:
--   Eigen Lifts Frobenius
-- statement:
--   Definitions and structural lemmas for Eigen Lifts Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EigenLiftsFrobenius.lean

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
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
section FrobA
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
def blockEquiv (D : Lifts H U X) (τ : Fin U.m) :
    blockL D τ ≃ₗ[R] ({l // D.κ l = τ} → R) where
  toFun c l := c.1 l.1
  invFun d := ⟨fun k => if h : D.κ k = τ then d ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases h : D.κ k = τ
    · simp [h]
    · simp [h, c.2 k h]
  right_inv d := by funext l; simp [l.2]
  map_add' c c' := rfl
  map_smul' r c := rfl
end FrobA
end ReciprocityTheory.PGsh.Up


