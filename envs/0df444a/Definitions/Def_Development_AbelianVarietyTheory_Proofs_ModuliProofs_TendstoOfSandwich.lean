-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:27.96548+00:00
-- url     : https://prove2.me/theorems/3ce59313-c2aa-4725-b483-7bcdf71809cd
-- title:
--   Tendsto Of Sandwich
-- statement:
--   Definitions and structural lemmas for Tendsto Of Sandwich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.VolFin
open Module Filter Topology
section Alg
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}
def piece (R : ι → Subalgebra K F) (γ : ι → F) (e : ℕ) : Submodule K F where
  carrier := {f | ∀ i, f * γ i ^ e ∈ R i}
  add_mem' ha hb i := by rw [add_mul]; exact (R i).add_mem (ha i) (hb i)
  zero_mem' i := by rw [zero_mul]; exact (R i).zero_mem
  smul_mem' c a ha i := by rw [smul_mul_assoc]; exact (R i).smul_mem (ha i) c
def Den (R : ι → Subalgebra K F) (γ : ι → F) : Prop :=
  ∀ u : F, ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ q * u ∈ piece R γ c
variable [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] [Finite ι]
end Alg
end GlobalTheory.VolFin


