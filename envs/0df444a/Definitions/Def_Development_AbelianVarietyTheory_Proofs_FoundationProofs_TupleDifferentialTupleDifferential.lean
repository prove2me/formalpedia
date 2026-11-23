-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:11.312499+00:00
-- url     : https://prove2.me/theorems/4b0e2074-d650-4732-bb97-68fa3ce6ae04
-- title:
--   Tuple Differential Tuple Differential
-- statement:
--   Definitions and structural lemmas for Tuple Differential Tuple Differential, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TupleDifferentialTupleDifferential.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finsupp
namespace GlobalTheory
variable {X : Type*}
def tupleCoface (a b : X) {n : ℕ} (i : Fin (n + 2)) (x : Fin n → X) : Fin (n + 1) → X :=
  fun j => (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → X)
    (if i ≤ j.castSucc then j.castSucc else j.succ)
variable (R : Type*) [Ring R] (N : Type*) [AddCommGroup N] [Module R N]
noncomputable def tupleDifferential (a b : X) (n : ℕ) :
    ((Fin n → X) →₀ N) →ₗ[R] ((Fin (n + 1) → X) →₀ N) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • lmapDomain N R (tupleCoface a b i)
noncomputable def tupleContraction (a : X) (n : ℕ) :
    ((Fin (n + 1) → X) →₀ N) →ₗ[R] ((Fin n → X) →₀ N) :=
  lcomapDomain (fun x => Fin.cons a x) (Fin.cons_right_injective (α := fun _ => X) a)
variable {R N}
end GlobalTheory


