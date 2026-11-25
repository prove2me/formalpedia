-- Prove2me | Definitions.Def_DetDLP_S8M_AtomMapModel_v2
-- name    : DetDLP_S8M_AtomMapModel_v2
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T23:30:42.996482+00:00
-- url     : https://prove2.me/theorems/a866eb33-61a9-4e91-83da-e63de03be003

import Definitions.Def_DetDLP_S8M_PacketCode

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.AtomMapModel

open S8H0.RegisterMap S8H0.NamedBlocks S8H0.GateRoutes
open DetDLP.S8M.Routes
open DetDLP.S8M.MakePacket

variable {m d e : ℕ}

/-- The left half of the interleaved atom bank uses its unshifted index. -/
theorem left_offset (i : Fin m) : (Routes.L i).val = i.val := rfl

/-- The right half begins at offset `m`; the bound is stated without unfolding
any of the block shapes. -/
theorem right_offset (i : Fin m) : (Routes.R i).val = m + i.val := rfl

theorem left_offset_lt (i : Fin m) : (Routes.L i).val < 2*m := by
  have hi := i.isLt
  simp only [Routes.L]
  omega

theorem right_offset_lt (i : Fin m) : (Routes.R i).val < 2*m := by
  have hi := i.isLt
  simp only [Routes.R]
  omega

/-- Reduction modulo the interleaved bank size recovers a left seed index. -/
theorem idx_left (i : Fin m) : Routes.idx (Routes.L i) = i := by
  apply Fin.ext
  simp [Routes.idx, Routes.L, Nat.mod_eq_of_lt i.isLt]

/-- Reduction modulo the interleaved bank size recovers a right seed index. -/
theorem idx_right (i : Fin m) : Routes.idx (Routes.R i) = i := by
  apply Fin.ext
  simp [Routes.idx, Routes.R, Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]

/-- The two halves cover the abstract interleaved register-index range. -/
theorem index_split (j : Fin (2*m)) :
    (j.val < m) ∨ (m ≤ j.val ∧ j.val - m < m) := by
  have hj := j.isLt
  omega

/-- Right-half register indices are precisely offset by the abstract half-size. -/
theorem right_index_offset (i : Fin m) :
    (Routes.R i).val - m = i.val := by
  simp [Routes.R]

/-- Replacing a right-half register index by its local index is valid modulo
`m`, without expanding any routed shape size. -/
theorem local_index_bound (i : Fin m) : i.val % m = i.val :=
  Nat.mod_eq_of_lt i.isLt

/-- The atom-slot address model fits the corresponding EC seed-query block.
All parameters, including the register-bank edge count `e`, stay abstract. -/
theorem atom_spec (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (S : SeedData m) (i : Fin (2*m)) :
    Fits (atomN hd p T c S i) (atomRows hd p T c S i) := by
  exact atomN_Fits hd p T c S i

/-- The conversion address model fits the corresponding EC map block.
The proof is independent of the concrete graph edge-count expression. -/
theorem map_spec (hd : 1 ≤ d) (p b2 a1 a3 : ℕ)
    (i : Fin (2*m)) :
    Fits (mapN (m := m) hd p b2 a1 a3 i)
      (mapRows (m := m) hd p b2 a1 a3 i) := by
  exact mapN_Fits hd p b2 a1 a3 i

end DetDLP.S8M.AtomMapModel


