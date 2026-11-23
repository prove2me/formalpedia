-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
-- name    : ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:27.598358+00:00
-- url     : https://prove2.me/theorems/0c90e28a-56d5-48f2-9a98-b78f3181682a
-- title:
--   Exists Primitive Root
-- statement:
--   Definitions and structural lemmas for Exists Primitive Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsPrimitiveRoot.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
namespace ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
section Untilt
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
def ofRoots (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk (span {(p : O)}) (f n), fun n => by
    show (Ideal.Quotient.mk (span {(p : O)}) (f (n + 1))) ^ p = _
    rw [← map_pow, hf]⟩
end Untilt
section Roots
variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]
def rootSeq (r : O → O) (c : O) : ℕ → O
  | 0 => c
  | n + 1 => r (rootSeq r c n)
variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
end Roots
end ReciprocityTheory.PGsh


