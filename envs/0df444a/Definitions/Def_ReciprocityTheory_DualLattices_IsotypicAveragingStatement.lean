-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_IsotypicAveragingStatement
-- name    : ReciprocityTheory_DualLattices_IsotypicAveragingStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:18.594816+00:00
-- url     : https://prove2.me/theorems/7aad79b4-5ca5-43fb-b15f-d179734d0d9d
-- title:
--   Isotypic Averaging Statement
-- statement:
--   Definitions and structural lemmas for Isotypic Averaging Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsotypicAveragingStatement.lean

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
def IsotypicAveragingStatement : Prop :=
  ∀ (S : Type) [CommRing S] (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) S)
    (E : Matrix (Ix g) (Ix g) S) (cp : S)
    (εT : Fin m → Matrix (Ix g) (Ix g) S) (εL : Fin m → Matrix (Fin g) (Fin g) S)
    (π : Equiv.Perm (Fin m)),
    (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    Btᵀ * Ht - Htᵀ * Bt = cp • E →
    let Bt' := ∑ i, εL i * Bt * εT i
    (Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E) ∧ (∀ i, Bt' * εT i = εL i * Bt') ∧
    (Matrix.fromRows Ht Bt').det ^ 2 = cp ^ (2 * g) * E.det
end ReciprocityTheory.PGsh.Up


