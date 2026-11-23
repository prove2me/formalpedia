-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PieceEqPieceT
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_PieceEqPieceT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:31.433125+00:00
-- url     : https://prove2.me/theorems/251477f9-2def-4a6a-ac3d-9354aa4b1835
-- title:
--   Piece Eq Piece T
-- statement:
--   Definitions and structural lemmas for Piece Eq Piece T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PieceEqPieceT.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Integral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical
namespace GlobalTheory.KummerEisensteinGalois
variable {K : Type*} [Field K] [CharZero K]
def rowT (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val + (p : ℤ) ^ n * w.1,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * w.2)
def pieceT (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r
def pieceTRaw (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r
end GlobalTheory.KummerEisensteinGalois


