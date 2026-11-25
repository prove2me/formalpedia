-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:42:21.259794+00:00
-- url     : https://prove2.me/theorems/fc39d5f9-32d0-48d5-997f-a2d2cb9ca797
-- title:
--   Mem Mixed Tsub
-- statement:
--   Definitions and structural lemmas for Mem Mixed Tsub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
namespace GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
def mixed (ε : PreTilt O p) (h : ℕ) (S : Finset (Fin h)) : Datum ε h (Fin h → ℤ_[p]) where
  F := diagonal fun i => if i ∈ S then mu ε else 1
  G := diagonal fun i => if i ∈ S then 1 else mu ε
  Ψ := diagonal fun i => if i ∈ S then xi ε else 1
  Ψ' := diagonal fun i => if i ∈ S then 1 else xi ε
  ρT := Matrix.diagonalAlgHom ℤ_[p]
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (Matrix.diagonalRingHom _ _)
  G_mul_F := by
    rw [diagonal_mul_diagonal, smul_one_eq_diagonal]
    refine congrArg diagonal (funext fun i => ?_); split_ifs <;> simp
  F_eq := by
    rw [diagonal_map (map_zero _), diagonal_mul_diagonal]
    refine congrArg diagonal (funext fun i => ?_)
    split_ifs <;> simp [phiInv_mu, xi_mul_nu]
  Ψ_mul := by
    rw [diagonal_mul_diagonal, smul_one_eq_diagonal]
    refine congrArg diagonal (funext fun i => ?_); split_ifs <;> simp
  F_act := by
    intro a
    simp [diagonal_map (map_zero _), diagonal_mul_diagonal, mul_comm]
section Field
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)
end Field
end GlobalTheory.Sandwich.Model


