-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:24.637704+00:00
-- url     : https://prove2.me/theorems/434329e0-52b1-4ad9-ab16-ba3a87c9dc5e
-- title:
--   W8 Add Transpose Eq E8
-- statement:
--   Definitions and structural lemmas for W8 Add Transpose Eq E8, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/W8AddTransposeEqE8.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
namespace GlobalTheory
def E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈
def W8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  0, -1,  0,  0,  0,  0,  0;
       0,  1,  0, -1,  0,  0,  0,  0;
       0,  0,  1, -1,  0,  0,  0,  0;
       0,  0,  0,  1, -1,  0,  0,  0;
       0,  0,  0,  0,  1, -1,  0,  0;
       0,  0,  0,  0,  0,  1, -1,  0;
       0,  0,  0,  0,  0,  0,  1, -1;
       0,  0,  0,  0,  0,  0,  0,  1]
def E8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  7, 10,  8,  6,  4,  2;
       5,  8, 10, 15, 12,  9,  6,  3;
       7, 10, 14, 20, 16, 12,  8,  4;
      10, 15, 20, 30, 24, 18, 12,  6;
       8, 12, 16, 24, 20, 15, 10,  5;
       6,  9, 12, 18, 15, 12,  8,  4;
       4,  6,  8, 12, 10,  8,  6,  3;
       2,  3,  4,  6,  5,  4,  3,  2]
def w8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  3, -2, -2, -2, -2, -2;
       5,  8,  5, -3, -3, -3, -3, -3;
       7, 10,  7, -4, -4, -4, -4, -4;
      10, 15, 10, -5, -6, -6, -6, -6;
       8, 12,  8, -4, -4, -5, -5, -5;
       6,  9,  6, -3, -3, -3, -4, -4;
       4,  6,  4, -2, -2, -2, -2, -3;
       2,  3,  2, -1, -1, -1, -1, -1]
def E8roots : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  2, -2,  0,  0,  0,  0,  0;
      -1,  2,  2, -2,  0,  0,  0,  0;
      -1,  0,  0,  2, -2,  0,  0,  0;
      -1,  0,  0,  0,  2, -2,  0,  0;
      -1,  0,  0,  0,  0,  2, -2,  0;
      -1,  0,  0,  0,  0,  0,  2, -2;
      -1,  0,  0,  0,  0,  0,  0,  2;
       1,  0,  0,  0,  0,  0,  0,  0]
end GlobalTheory


