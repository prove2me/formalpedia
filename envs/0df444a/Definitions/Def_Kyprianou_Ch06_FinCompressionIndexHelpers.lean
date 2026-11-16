-- Prove2me | Definitions.Def_Kyprianou_Ch06_FinCompressionIndexHelpers
-- name    : Kyprianou_Ch06_FinCompressionIndexHelpers
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T21:39:40.435642+00:00
-- url     : https://prove2.me/theorems/9a4d2675-8997-4cbd-83b4-262afc03b7ef
-- title:
--   Finite-grid compression and endpoint index identities
-- statement:
--   Kernel-checkable finite-index value and endpoint identities for removing a repeated timestamp from a nondecreasing finite grid. Includes succAbove value and three exact endpoint index equations. Reusable within the Chapter 6 independent-increments compatibility bridge.
-- source:
--   Mathlib Fin.succAbove, Fin.val_succ, Fin.val_castSucc and elementary finite arithmetic. Source-preserving Chapter 6 Lévy-process interface bridge.

import Mathlib
set_option autoImplicit false

theorem Kyprianou.Ch06.succAboveValue
    (n : Nat) (k : Fin (n + 1)) (j : Fin n) :
    (k.succAbove j).val =
      if j.val < k.val then j.val else j.val + 1 := by
  have hiff : (j.castSucc : Fin (n + 1)) < k ↔ j.val < k.val := by
    rfl
  unfold Fin.succAbove
  simp only [hiff]
  split_ifs <;> simp_all [Fin.val_castSucc, Fin.val_succ]


theorem Kyprianou.Ch06.compressedGrid_endIndex
    (n : Nat) (k : Fin (n + 1)) (j : Fin n) :
    (k.succAbove j).succ = k.succ.succAbove j.succ := by
  apply Fin.ext
  simp only [Fin.val_succ, Kyprianou.Ch06.succAboveValue]
  split_ifs <;> omega

theorem Kyprianou.Ch06.compressedGrid_startIndex_ne
    (n : Nat) (k : Fin (n + 1)) (j : Fin n)
    (hjk : j.val ≠ k.val) :
    (k.succAbove j).castSucc = k.succ.succAbove j.castSucc := by
  apply Fin.ext
  simp only [Fin.val_castSucc, Fin.val_succ, Kyprianou.Ch06.succAboveValue]
  split_ifs <;> omega

theorem Kyprianou.Ch06.compressedGrid_startIndex_eq
    (n : Nat) (k : Fin (n + 1)) (j : Fin n)
    (hjk : j.val = k.val) :
    (k.succAbove j).castSucc = k.succ ∧
      k.succ.succAbove j.castSucc = k.castSucc := by
  constructor
  · apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ, Kyprianou.Ch06.succAboveValue]
    split_ifs <;> omega
  · apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ, Kyprianou.Ch06.succAboveValue]
    split_ifs <;> omega


