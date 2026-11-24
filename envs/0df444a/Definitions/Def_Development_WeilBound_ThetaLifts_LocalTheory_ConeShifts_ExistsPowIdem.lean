-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:20.968104+00:00
-- url     : https://prove2.me/theorems/a7135d4c-ba9b-4a3d-a872-ec2c8bddebb7
-- title:
--   Exists Pow Idem
-- statement:
--   Definitions and structural lemmas for Exists Pow Idem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/ExistsPowIdem.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
def Adj (J M M' : Matrix β β A) : Prop := Mᵀ * J = J * M'.map c
variable {c} {J : Matrix β β A}
theorem mapc_mul {ι κ μ : Type} [Fintype κ] (M : Matrix ι κ A) (N : Matrix κ μ A) : (M * N).map c = M.map c * N.map c :=
  Matrix.map_mul (f := (c : A →+* A))
theorem mapc_add {ι κ : Type} (M N : Matrix ι κ A) : (M + N).map c = M.map c + N.map c := Matrix.map_add _ (map_add c) _ _
theorem mapc_neg {ι κ : Type} (M : Matrix ι κ A) : (-M).map c = -M.map c := Matrix.map_neg _ (map_neg c) _
theorem mapc_sub {ι κ : Type} (M N : Matrix ι κ A) : (M - N).map c = M.map c - N.map c := by
  rw [sub_eq_add_neg, mapc_add, mapc_neg, ← sub_eq_add_neg]
theorem mapc_one {ι : Type} [DecidableEq ι] : (1 : Matrix ι ι A).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
def CC (b : Matrix β β A) : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks 1 (1 + b) 1 b
def Ci (b : Matrix β β A) : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks (-b) (1 + b) 1 (-1)
theorem Ci_CC (b : Matrix β β A) : Ci b * CC b = 1 := by
  rw [Ci, CC, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> noncomm_ring
theorem CC_Ci (b : Matrix β β A) : CC b * Ci b = 1 := mul_eq_one_comm.1 (Ci_CC b)
theorem gram_CC {b b' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) :
    (CC b)ᵀ * dbl J * (CC b).map c = fromBlocks 0 J J 0 := by
  have e : b'.map c = -1 - b.map c := by
    rw [← mapc_one (c := c), ← mapc_neg, ← mapc_sub, ← hb]; congr 1; abel
  have b1' : bᵀ * J = -J - J * b.map c := by rw [b1, e]; noncomm_ring
  rw [CC, dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_add, mapc_one, transpose_add,
    transpose_one]
  congr 1
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · have : ((1 + bᵀ) * J + bᵀ * 0) * (1 + b.map c) + ((1 + bᵀ) * 0 + bᵀ * -J) * b.map c = J + J * b.map c + bᵀ * J := by
      noncomm_ring
    rw [this, b1']; abel
def mkU {b b' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g g' : Matrix (β ⊕ β) (β ⊕ β) A) (h : g * g' = 1)
    (hg : gᵀ * fromBlocks 0 J J 0 * g.map c = fromBlocks 0 J J 0) : UG c (dbl J) :=
  have e : CC b * g * Ci b * (CC b * g' * Ci b) = 1 := by
    calc CC b * g * Ci b * (CC b * g' * Ci b) = CC b * (g * (Ci b * CC b) * g') * Ci b := by noncomm_ring
      _ = 1 := by rw [Ci_CC, Matrix.mul_one, h, Matrix.mul_one, CC_Ci]
  ⟨⟨CC b * g * Ci b, CC b * g' * Ci b, e, mul_eq_one_comm.1 e⟩, by
    change (CC b * g * Ci b)ᵀ * dbl J * (CC b * g * Ci b).map c = dbl J
    have e2 : (Ci b)ᵀ * fromBlocks 0 J J 0 * (Ci b).map c = dbl J := by
      rw [← gram_CC b1 hb]
      calc (Ci b)ᵀ * ((CC b)ᵀ * dbl J * (CC b).map c) * (Ci b).map c
          = ((Ci b)ᵀ * (CC b)ᵀ) * dbl J * ((CC b).map c * (Ci b).map c) := by noncomm_ring
        _ = dbl J := by rw [← transpose_mul, ← mapc_mul, CC_Ci, transpose_one, mapc_one, Matrix.one_mul, Matrix.mul_one]
    rw [mapc_mul, mapc_mul, transpose_mul, transpose_mul]
    calc (Ci b)ᵀ * (gᵀ * (CC b)ᵀ) * dbl J * ((CC b).map c * g.map c * (Ci b).map c)
        = (Ci b)ᵀ * (gᵀ * ((CC b)ᵀ * dbl J * (CC b).map c) * g.map c) * (Ci b).map c := by noncomm_ring
      _ = dbl J := by rw [gram_CC b1 hb, hg, e2]⟩
def SS (ε : A) : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks ((1 - ε) • 1) (ε • 1) (ε • 1) ((1 - ε) • 1)
end PositivityTheory.ThKG.Loc.Cone.Vf
end


