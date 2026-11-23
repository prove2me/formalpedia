-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:12.18864+00:00
-- url     : https://prove2.me/theorems/33704cb1-8d5b-41a4-a5e0-301d09081525
-- title:
--   Exists Udl Of Is Unit
-- statement:
--   Definitions and structural lemmas for Exists Udl Of Is Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUdlOfIsUnit.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]
def ex (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
def IsUp (I : Ideal R) {n : ℕ} (u : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, j < i → u i j = 0) ∧
    ∀ i, u i i = 1
def IsLo (I : Ideal R) {n : ℕ} (l : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, i < j → l i j = 0) ∧
    ∀ i, l i i = 1
def IsDi (I : Ideal R) {n : ℕ} (d : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ ∀ i j, i ≠ j → d i j = 0
end GlobalTheory.CompanionTheory.IwahoriUDL


