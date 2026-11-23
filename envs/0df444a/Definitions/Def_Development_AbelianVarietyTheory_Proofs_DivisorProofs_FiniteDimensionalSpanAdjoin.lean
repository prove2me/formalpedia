-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:39.387432+00:00
-- url     : https://prove2.me/theorems/b3c986c8-3bcf-4333-9f43-dad801a9b899
-- title:
--   Finite Dimensional Span Adjoin
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Span Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoin.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
namespace GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def stabAlg (N : Submodule ℂ V) : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {T | ∀ v ∈ N, T v ∈ N}
  mul_mem' ha hb v hv := ha _ (hb v hv)
  add_mem' ha hb v hv := N.add_mem (ha v hv) (hb v hv)
  algebraMap_mem' r v hv := by
    rw [Module.algebraMap_end_apply]
    exact N.smul_mem r hv
def ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ k : Fin (d + 1), N.map (T ^ (k : ℕ))
end GlobalTheory.CycSpanFin


